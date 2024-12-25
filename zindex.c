#include <ctype.h>
#include <dirent.h>
#include <fcntl.h>
#include <fnmatch.h>
#include <pthread.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>
#include <sys/stat.h>
#include <unistd.h>
#include <zstd.h>

#define AC_ALPHABET_SIZE 256
#define MAX_THREADS 12
#define ZSTD_CHUNK_SIZE (128 * 1024)  // Decompress in smallish blocks
#define ROLLING_BUF_SIZE (256 * 1024) // Rolling buffer for partial matches
#define FRAME_MAGIC 0xFD2FB528U
#define TAR_BLOCK_SIZE 512
#define MAX_FILENAME_LEN 512

// Assume only a single pattern, store its length here for overlap logic:
static size_t g_patternLen = 0; // set after building the Aho automaton

// struct for partial matches
typedef struct {
  char filename[MAX_FILENAME_LEN];
  off_t offset;
  int closenessScore;
  char preview[256];
  size_t filenameLen;
} SearchResult;

// structure for storing search hits in mem
typedef struct {
  SearchResult *results;
  size_t count;
  size_t capacity;
  pthread_mutex_t lock;
} ResultsList;

// Aho–Corasick data structures
typedef struct ACNode {
  struct ACNode *children[256];
  struct ACNode *fail;
  int output;
  int depth;
} ACNode;

// Aho trie node
static ACNode *create_node(void) {
  ACNode *node = (ACNode *)calloc(1, sizeof(ACNode));
  if (node) {
    node->fail = NULL;
    node->output = 0;
    node->depth = 0;
  }
  return node;
}

// 'closeness' or match scoring
static int compute_closeness(const char *haystack, const char *needle) {
  int best = 0, score = 0;
  while (*haystack && *needle) {
    if (tolower((unsigned char)*haystack) == tolower((unsigned char)*needle)) {
      score++;
      if (score > best)
        best = score;
    } else {
      score = 0;
    }
    haystack++;
    needle++;
  }
  return best;
}

// Aho automaton for a single pattern (case-insensitive).
// Also store the length of the pattern in g_patternLen for overlap logic.
static ACNode *build_aho_automaton(const char *pattern) {
  g_patternLen = strlen(pattern);

  ACNode *root = create_node();
  if (!root)
    return NULL;

  // Add pattern to trie
  ACNode *cur = root;
  for (size_t i = 0; i < g_patternLen; i++) {
    unsigned char c = (unsigned char)tolower((unsigned char)pattern[i]);
    if (!cur->children[c]) {
      cur->children[c] = create_node();
      if (!cur->children[c])
        return root;
      cur->children[c]->depth = cur->depth + 1;
    }
    cur = cur->children[c];
  }
  cur->output = 1; // Mark pattern end

  // Build failure links via BFS
  root->fail = root;

  // Modest queue cap, can adjust
  size_t queueCap = 256;
  ACNode **queue = (ACNode **)malloc(queueCap * sizeof(ACNode *));
  if (!queue)
    return root;

  int front = 0, back = 0;

  // Initialize children of root
  for (int c = 0; c < AC_ALPHABET_SIZE; c++) {
    if (root->children[c]) {
      root->children[c]->fail = root;

      // Enqueue, grow queue if needed
      queue[back++] = root->children[c];
      if ((size_t)back == queueCap) {
        queueCap *= 2;
        ACNode **newQ = (ACNode **)realloc(queue, queueCap * sizeof(ACNode *));
        if (!newQ) {
          free(queue);
          return root;
        }
        queue = newQ;
      }
    } else {
      root->children[c] = root; // missing child => loop back to root
    }
  }

  // BFS
  while (front < back) {
    ACNode *u = queue[front++];
    for (int c = 0; c < AC_ALPHABET_SIZE; c++) {
      ACNode *v = u->children[c];
      if (!v) {
        // If missing, redirect to fail’s child
        u->children[c] = u->fail->children[c];
        continue;
      }
      // Build fail link
      ACNode *f = u->fail;
      v->fail = f->children[c];
      // If fail node is output, propagate
      v->output |= v->fail->output;

      // Enqueue v
      queue[back++] = v;
      if ((size_t)back == queueCap) {
        queueCap *= 2;
        ACNode **newQ = (ACNode **)realloc(queue, queueCap * sizeof(ACNode *));
        if (!newQ) {
          free(queue);
          return root;
        }
        queue = newQ;
      }
    }
  }

  free(queue);
  return root;
}

static void results_add(ResultsList *rl, const char *filename, off_t offset,
                        int closenessScore, const char *preview) {
  pthread_mutex_lock(&rl->lock);
  if (rl->count == rl->capacity) {
    size_t new_cap = (rl->capacity == 0) ? 256 : (rl->capacity * 2);
    SearchResult *temp = realloc(rl->results, new_cap * sizeof(SearchResult));
    if (!temp) {
      pthread_mutex_unlock(&rl->lock);
      return;
    }
    rl->results = temp;
    rl->capacity = new_cap;
  }

  SearchResult *sr = &rl->results[rl->count++];

  if (filename) {
    strncpy(sr->filename, filename, MAX_FILENAME_LEN - 1);
    sr->filename[MAX_FILENAME_LEN - 1] = '\0';
    sr->filenameLen = strlen(sr->filename);
  } else {
    sr->filename[0] = '\0';
    sr->filenameLen = 0;
  }

  sr->offset = offset;
  sr->closenessScore = closenessScore;

  if (preview) {
    strncpy(sr->preview, preview, sizeof(sr->preview) - 1);
    sr->preview[sizeof(sr->preview) - 1] = '\0';
  } else {
    sr->preview[0] = '\0';
  }

  pthread_mutex_unlock(&rl->lock);
}

// Free entire AC automaton non-recursively
// Could've gone with a recursive approach, but it was causing segfaults
// Didn't feel like dealing with that headache for now :p
void free_aho_automaton(ACNode *root) {
  if (!root)
    return;

  // Sore up to all real nodes in a queue
  // Do a simple BFS queue + visited array for now
  // Can use hash set later if needed

  // BFS on-the-fly.
  size_t queueCap = 1024;
  ACNode **queue = (ACNode **)malloc(queueCap * sizeof(ACNode *));
  if (!queue)
    return;

  // A visited set.
  // AC automaton *could* have thousands or millions of nodes, so a
  // pointer-based hash set is better...or for small tries, a simple dynamic
  // array or something like a "uthash" would suffice. I'll just go with a
  // minimal approach with a dynamic array storing visited pointers.

  size_t visitedCap = 1024;
  ACNode **visited = (ACNode **)malloc(visitedCap * sizeof(ACNode *));
  if (!visited) {
    free(queue);
    return;
  }
  size_t visitedCount = 0;

  // BFS setup
  int front = 0, back = 0;
  queue[back++] = root;

  // Mark root => visited
  visited[visitedCount++] = root;

  while (front < back) {
    ACNode *u = queue[front++];
    // Enqueue all unique children that are not visited & not root
    for (int c = 0; c < 256; c++) {
      ACNode *child = u->children[c];
      if (!child)
        continue;
      if (child == root) {
        // skip => fallback link to avoid infinite loops!!!
        continue;
      }
      // Is child visited?
      bool alreadyVisited = false;
      for (size_t i = 0; i < visitedCount; i++) {
        if (visited[i] == child) {
          alreadyVisited = true;
          break;
        }
      }
      if (!alreadyVisited) {
        // If not visited, put in queue
        if ((size_t)back == queueCap) {
          queueCap *= 2;
          ACNode **newQ =
              (ACNode **)realloc(queue, queueCap * sizeof(ACNode *));
          if (!newQ) {
            // partial cleanup or just leak
            goto cleanup;
          }
          queue = newQ;
        }
        queue[back++] = child;

        // also mark as visited
        if (visitedCount == visitedCap) {
          visitedCap *= 2;
          ACNode **newV =
              (ACNode **)realloc(visited, visitedCap * sizeof(ACNode *));
          if (!newV) {
            goto cleanup;
          }
          visited = newV;
        }
        visited[visitedCount++] = child;
      }
    }
  }

  // Now visited[] has each unique node in BFS order.
  // Free in reverse BFS order or any order,
  // because no child->root loop will cause a double free.

  // free from last to first, or first to last:
  // (BFS or DFS order is whatever as long as no node is freed twice.)

  for (size_t i = visitedCount; i > 0; i--) {
    ACNode *n = visited[i - 1];
    free(n);
  }

cleanup:
  free(queue);
  free(visited);
}

// Process data with Aho–Corasick, storing results.
static void ac_feed_chunk(ACNode **curStatePtr, const char *data,
                          size_t dataLen, ACNode *root, off_t globalOffset,
                          const char *filename, ResultsList *results,
                          const char *searchStr) {
  if (!curStatePtr || !*curStatePtr || !data || !results || !searchStr) {
    fprintf(stderr, "Invalid parameters to ac_feed_chunk\n");
    return;
  }

  ACNode *st = *curStatePtr;
  size_t patLen = g_patternLen;

  for (size_t i = 0; i < dataLen; i++) {
    unsigned char c = (unsigned char)tolower((unsigned char)data[i]);
    st = st->children[c];
    if (st->output) {
      // 'i' is index of the last character in the matched pattern,
      // so the match actually starts at:
      size_t matchStart = (i >= patLen - 1) ? (i - (patLen - 1)) : 0;

      // Anchor the snippet around matchStart instead of i
      size_t snippetStart = (matchStart < 10) ? 0 : (matchStart - 10);

      // Check snippetStart isn't beyond dataLen
      if (snippetStart > dataLen) {
        snippetStart = dataLen;
      }

      // Snippet extends from snippetStart to the end of data
      size_t snippetSize = dataLen - snippetStart;
      if (snippetSize > 200)
        snippetSize = 200;

      char preview[256];
      memset(preview, 0, sizeof(preview));
      memcpy(preview, data + snippetStart, snippetSize);
      preview[snippetSize] = '\0';

      off_t matchOffset = globalOffset + matchStart;
      int closeness = compute_closeness(data + matchStart, searchStr);
      results_add(results, filename, matchOffset, closeness, preview);
    }
  }

  *curStatePtr = st;
}

// Results stuff
static void results_init(ResultsList *rl) {
  rl->results = NULL;
  rl->count = 0;
  rl->capacity = 0;
  pthread_mutex_init(&rl->lock, NULL);
}

static void results_destroy(ResultsList *rl) {
  free(rl->results);
  pthread_mutex_destroy(&rl->lock);
}

// TAR header
struct tar_header {
  char name[100];
  char mode[8];
  char uid[8];
  char gid[8];
  char size[12];
  char mtime[12];
  char chksum[8];
  char typeflag;
  char linkname[100];
  char magic[6];
  char version[2];
  char uname[32];
  char gname[32];
  char devmajor[8];
  char devminor[8];
  char prefix[155];
  char padding[12];
};

// Utility: Convert octal to size
static inline size_t octal_to_size(const char *str, size_t n) {
  size_t val = 0;
  for (size_t i = 0; i < n && str[i] >= '0' && str[i] <= '7'; i++) {
    val = (val << 3) + (str[i] - '0');
  }
  return val;
}

// Check if 512-byte block is all zeros => end of tar
static inline int is_end_of_archive(const unsigned char *block) {
  for (int i = 0; i < TAR_BLOCK_SIZE; i++) {
    if (block[i] != 0)
      return 0;
  }
  return 1;
}

// Gather offsets of all ZSTD frames (scanning for FRAME_MAGIC).
static void find_frame_offsets(const unsigned char *ptr, size_t size,
                               off_t **matches, size_t *count, size_t *cap) {
  for (size_t i = 0; i + 4 <= size; i++) {
    uint32_t val;
    memcpy(&val, ptr + i, 4);
    if (val == FRAME_MAGIC) {
      if (*count == *cap) {
        *cap = (*cap == 0) ? 256 : (*cap * 2);
        *matches = realloc(*matches, (*cap) * sizeof(off_t));
        if (!*matches)
          return;
      }
      (*matches)[(*count)++] = i;
    }
  }
}

// Ring buffer state (thread-local) for minimal memory usage.
typedef struct {
  char buffer[ROLLING_BUF_SIZE];
  size_t writePos;
  off_t globalOffset;
  ACNode *acState; // current Aho state
} RingBufState;

// Per-thread ring buffer:
static __thread RingBufState g_ring;

static void ringbuf_init(ACNode *root) {
  memset(g_ring.buffer, 0, ROLLING_BUF_SIZE);
  g_ring.writePos = 0;
  g_ring.globalOffset = 0;
  g_ring.acState = root;
}

static void ringbuf_feed(ResultsList *results, const char *filename,
                         ACNode *acRoot, const char *searchStr, const char *src,
                         size_t srcLen) {
  size_t srcOffset = 0;

  // Overlap size => (g_patternLen - 1), if patternLen > 0
  size_t overlap = (g_patternLen > 0) ? (g_patternLen - 1) : 0;
  if (overlap >= ROLLING_BUF_SIZE)
    overlap = 0; // sanity check

  while (srcLen > 0) {
    // If ring is full, feed it to AC, then keep last 'overlap' bytes
    if (g_ring.writePos >= ROLLING_BUF_SIZE) {
      // feed all
      ac_feed_chunk(&g_ring.acState, g_ring.buffer, g_ring.writePos, acRoot,
                    g_ring.globalOffset, filename, results, searchStr);

      // shift overlap
      if (overlap > g_ring.writePos)
        overlap = g_ring.writePos;
      memmove(g_ring.buffer, g_ring.buffer + (g_ring.writePos - overlap),
              overlap);
      g_ring.writePos = overlap;
      g_ring.globalOffset += (g_ring.writePos - overlap);
      // ^ might wanna adjust globalOffset here depending on offset tracking
      // strat
    }

    size_t space = ROLLING_BUF_SIZE - g_ring.writePos;
    if (space > srcLen)
      space = srcLen;

    memcpy(g_ring.buffer + g_ring.writePos, src + srcOffset, space);

    g_ring.writePos += space;
    g_ring.globalOffset += space;
    srcOffset += space;
    srcLen -= space;
  }
}

// After finishing all data, feed leftover to AC
static void ringbuf_flush(ResultsList *results, const char *filename,
                          ACNode *acRoot, const char *searchStr) {
  if (g_ring.writePos > 0) {
    ac_feed_chunk(&g_ring.acState, g_ring.buffer, g_ring.writePos, acRoot,
                  g_ring.globalOffset - g_ring.writePos, // offset to start
                  filename, results, searchStr);
  }
  g_ring.writePos = 0; // optional
}

// Processes an entire tar (one Zstd frame) using the ring buffer approach.
static void index_tar_entries_with_ring(ZSTD_DCtx *dctx, const void *mapped,
                                        size_t fileSize, off_t startOffset,
                                        ResultsList *results, ACNode *acRoot,
                                        const char *searchStr,
                                        const char *topFilename) {
  ZSTD_inBuffer zin;
  zin.src = (const char *)mapped + startOffset;
  zin.size = fileSize - startOffset;
  zin.pos = 0;

  // small decompression output
  char outBuf[ZSTD_CHUNK_SIZE];

  // Initialize ring for each frame
  ringbuf_init(acRoot);

  while (1) {
    ZSTD_outBuffer zout;
    zout.dst = outBuf;
    zout.size = ZSTD_CHUNK_SIZE;
    zout.pos = 0;

    size_t ret = ZSTD_decompressStream(dctx, &zout, &zin);
    if (ZSTD_isError(ret)) {
      fprintf(stderr, "ZSTD decompress error: %s\n", ZSTD_getErrorName(ret));
      break;
    }

    size_t gotBytes = zout.pos;
    if (gotBytes == 0 && ret == 0) {
      // end of frame
      break;
    }

    // feed into ring buffer
    ringbuf_feed(results, topFilename, acRoot, searchStr, outBuf, gotBytes);

    if (ret == 0) {
      // done with this frame
      break;
    }
  }

  // flush leftover
  ringbuf_flush(results, topFilename, acRoot, searchStr);
}

// Build index by scanning all zstd frames inside the file, searching for
// searchStr
static void build_index(const char *filename, ResultsList *results,
                        const char *searchStr, ACNode *acRoot) {
  int fd = open(filename, O_RDONLY);
  if (fd < 0)
    return;

  struct stat st;
  if (fstat(fd, &st) != 0 || st.st_size == 0) {
    close(fd);
    return;
  }

  void *mapped = mmap(NULL, st.st_size, PROT_READ, MAP_PRIVATE, fd, 0);
  close(fd);
  if (mapped == MAP_FAILED)
    return;

  ZSTD_DCtx *dctx = ZSTD_createDCtx();
  if (!dctx) {
    munmap(mapped, st.st_size);
    return;
  }

  off_t *matches = NULL;
  size_t matchCount = 0, matchCap = 0;
  find_frame_offsets((const unsigned char *)mapped, (size_t)st.st_size,
                     &matches, &matchCount, &matchCap);

  for (size_t i = 0; i < matchCount; i++) {
    if (!ZSTD_isError(ZSTD_initDStream(dctx))) {
      ZSTD_initDStream(dctx);
      // Use ring buffer approach
      index_tar_entries_with_ring(dctx, mapped, st.st_size, matches[i], results,
                                  acRoot, searchStr, filename);
    }
  }

  free(matches);
  ZSTD_freeDCtx(dctx);
  munmap(mapped, st.st_size);
}

// We'll gather files that match "batch_0000*.tar.zst" in the current directory.
typedef struct {
  ResultsList *results;
  char **files;
  int start;
  int end;
  const char *searchStr;
  ACNode *acRoot;
} WorkerArgs;

static void *worker_thread(void *arg) {
  WorkerArgs *w = (WorkerArgs *)arg;
  for (int i = w->start; i < w->end; i++) {
    build_index(w->files[i], w->results, w->searchStr, w->acRoot);
  }
  return NULL;
}

// Function for final sorting by closenessScore desc, then offset asc
static int compare_results(const void *a, const void *b) {
  const SearchResult *ra = (const SearchResult *)a;
  const SearchResult *rb = (const SearchResult *)b;
  if (rb->closenessScore != ra->closenessScore) {
    return rb->closenessScore - ra->closenessScore;
  }
  if (ra->offset < rb->offset)
    return -1;
  if (ra->offset > rb->offset)
    return 1;
  return 0;
}

// Main
int main(int argc, char **argv) {
  if (argc < 2) {
    fprintf(stderr, "Usage: %s <searchString>\n", argv[0]);
    return 1;
  }
  const char *searchStr = argv[1];

  // Build Aho–Corasick from searchStr
  ACNode *acRoot = build_aho_automaton(searchStr);
  if (!acRoot) {
    fprintf(stderr, "Failed to create Aho-Corasick automaton\n");
    return 1;
  }

  fprintf(stderr, "Searching for pattern: %s\n", searchStr);

  DIR *d = opendir(".");
  if (!d) {
    free_aho_automaton(acRoot);
    return 1;
  }

  char **files = NULL;
  size_t fileCount = 0, fileCap = 0;
  struct dirent *de;
  while ((de = readdir(d)) != NULL) {
    if (strncmp(de->d_name, "batch_0000", 10) == 0 &&
        strstr(de->d_name, ".tar.zst")) {
      if (fileCount == fileCap) {
        fileCap = fileCap ? fileCap * 2 : 32;
        char **temp = realloc(files, fileCap * sizeof(char *));
        if (!temp) {
          free(files);
          closedir(d);
          free_aho_automaton(acRoot);
          return 1;
        }
        files = temp;
      }
      files[fileCount++] = strdup(de->d_name);
    }
  }
  closedir(d);

  if (fileCount == 0) {
    fprintf(stderr, "No matching batch_0000*.tar.zst files found.\n");
    free(files);
    free_aho_automaton(acRoot);
    return 1;
  }

  ResultsList results;
  results_init(&results);

  // Multi-thread
  int threadCount = (fileCount > MAX_THREADS) ? MAX_THREADS : (int)fileCount;
  pthread_t tids[threadCount];
  WorkerArgs wargs[threadCount];

  int filesPerThread = (int)(fileCount / threadCount);
  int remainder = (int)(fileCount % threadCount);
  int start = 0;
  for (int i = 0; i < threadCount; i++) {
    int count = filesPerThread + (i < remainder ? 1 : 0);
    wargs[i].results = &results;
    wargs[i].files = files;
    wargs[i].start = start;
    wargs[i].end = start + count;
    wargs[i].searchStr = searchStr;
    wargs[i].acRoot = acRoot;

    pthread_create(&tids[i], NULL, worker_thread, &wargs[i]);
    start += count;
  }

  for (int i = 0; i < threadCount; i++) {
    pthread_join(tids[i], NULL);
  }

  // Sort final results
  pthread_mutex_lock(&results.lock);
  qsort(results.results, results.count, sizeof(SearchResult), compare_results);
  pthread_mutex_unlock(&results.lock);

  // Print
  for (size_t i = 0; i < results.count; i++) {
    SearchResult *r = &results.results[i];
    printf("{\"file\":\"%s\", \"offset\":%lld, \"score\":%d, "
           "\"preview\":\"%s\"}\n",
           r->filename, (long long)r->offset, r->closenessScore, r->preview);
  }

  // Cleanup
  for (size_t i = 0; i < fileCount; i++) {
    free(files[i]);
  }
  free(files);

  free_aho_automaton(acRoot);
  results_destroy(&results);
  return 0;
}
