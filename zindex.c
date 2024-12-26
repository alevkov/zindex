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
#define ZSTD_STATIC_LINKING_ONLY
#include <zstd.h>

#define AC_ALPHABET_SIZE 256
#define MAX_THREADS 12
#define ZSTD_CHUNK_SIZE (128 * 1024)  // Decompress in smallish blocks
#define ROLLING_BUF_SIZE (256 * 1024) // Rolling buffer for partial matches
#define FRAME_MAGIC 0xFD2FB528U
#define TAR_BLOCK_SIZE 512
#define MAX_FILENAME_LEN 512

// For single-pattern Aho–Corasick:
static size_t g_patternLen = 0; // set after building the Aho automaton

// -------------------------------------
// 1) SearchResult + PrintQueue
// -------------------------------------
typedef struct {
    char filename[MAX_FILENAME_LEN];
    off_t offset;
    int closenessScore;
    char preview[256];
} SearchResult;

// A singly-linked node for the queue
typedef struct PrintNode {
    SearchResult item;
    struct PrintNode *next;
} PrintNode;

// The queue itself
typedef struct {
    PrintNode *head;
    PrintNode *tail;
    size_t size;
    bool done;               // signals all workers are done
    pthread_mutex_t lock;
    pthread_cond_t cond;
} PrintQueue;

// Initialize the queue
static void printqueue_init(PrintQueue *q) {
    q->head = q->tail = NULL;
    q->size = 0;
    q->done = false;
    pthread_mutex_init(&q->lock, NULL);
    pthread_cond_init(&q->cond, NULL);
}

// Destroy the queue
static void printqueue_destroy(PrintQueue *q) {
    // Clear any leftover items
    PrintNode *cur = q->head;
    while (cur) {
        PrintNode *tmp = cur->next;
        free(cur);
        cur = tmp;
    }
    pthread_mutex_destroy(&q->lock);
    pthread_cond_destroy(&q->cond);
}

// Enqueue a search result
static void printqueue_push(PrintQueue *q, const SearchResult *res) {
    PrintNode *node = (PrintNode*)malloc(sizeof(PrintNode));
    if (!node) return; // ignoring oom

    node->item = *res;
    node->next = NULL;

    pthread_mutex_lock(&q->lock);
    if (q->tail) {
        q->tail->next = node;
        q->tail = node;
    } else {
        // queue was empty
        q->head = q->tail = node;
    }
    q->size++;
    // signal the printer thread
    pthread_cond_signal(&q->cond);
    pthread_mutex_unlock(&q->lock);
}

// Pop a search result (blocking)
static bool printqueue_pop(PrintQueue *q, SearchResult *out) {
    pthread_mutex_lock(&q->lock);
    // Wait until queue has an item or done is true
    while (q->size == 0 && !q->done) {
        pthread_cond_wait(&q->cond, &q->lock);
    }
    if (q->size == 0 && q->done) {
        // no items left, done
        pthread_mutex_unlock(&q->lock);
        return false;
    }
    // we have an item
    PrintNode *node = q->head;
    q->head = node->next;
    if (!q->head) q->tail = NULL;
    q->size--;
    *out = node->item;
    free(node);
    pthread_mutex_unlock(&q->lock);
    return true;
}

// Mark the queue as done
static void printqueue_mark_done(PrintQueue *q) {
    pthread_mutex_lock(&q->lock);
    q->done = true;
    // wake up any waiting threads
    pthread_cond_broadcast(&q->cond);
    pthread_mutex_unlock(&q->lock);
}

// -------------------------------------
// 2) Aho–Corasick
// -------------------------------------
typedef struct ACNode {
    struct ACNode *children[AC_ALPHABET_SIZE];
    struct ACNode *fail;
    int output; 
    int depth;  
} ACNode;

// Create a new ACNode
static ACNode *create_node(void) {
    ACNode *node = (ACNode*)calloc(1, sizeof(ACNode));
    if (node) {
        node->fail = NULL;
        node->output = 0;
        node->depth = 0;
    }
    return node;
}

// Example closeness
static int compute_closeness(const char *haystack, const char *needle) {
    int best = 0, score = 0;
    while (*haystack && *needle) {
        if (tolower((unsigned char)*haystack) == tolower((unsigned char)*needle)) {
            score++;
            if (score > best) best = score;
        } else {
            score = 0;
        }
        haystack++;
        needle++;
    }
    return best;
}

// Build Aho automaton for single pattern
static ACNode *build_aho_automaton(const char *pattern) {
    g_patternLen = strlen(pattern);

    ACNode *root = create_node();
    if (!root) return NULL;

    // Insert pattern into trie
    ACNode *cur = root;
    for (size_t i = 0; i < g_patternLen; i++) {
        unsigned char c = (unsigned char)tolower((unsigned char)pattern[i]);
        if (!cur->children[c]) {
            cur->children[c] = create_node();
            if (!cur->children[c]) return root;
            cur->children[c]->depth = cur->depth + 1;
        }
        cur = cur->children[c];
    }
    cur->output = 1;

    // BFS to build fail links
    root->fail = root;
    size_t queueCap = 256;
    ACNode **queue = (ACNode **)malloc(queueCap * sizeof(ACNode*));
    if (!queue) return root;

    int front = 0, back = 0;

    for (int c = 0; c < AC_ALPHABET_SIZE; c++) {
        if (root->children[c]) {
            root->children[c]->fail = root;
            queue[back++] = root->children[c];
            if ((size_t)back == queueCap) {
                queueCap *= 2;
                ACNode **newQ = (ACNode**)realloc(queue, queueCap*sizeof(ACNode*));
                if (!newQ) {
                    free(queue);
                    return root;
                }
                queue = newQ;
            }
        } else {
            root->children[c] = root; // missing => link back to root
        }
    }

    while (front < back) {
        ACNode *u = queue[front++];
        for (int c = 0; c < AC_ALPHABET_SIZE; c++) {
            ACNode *v = u->children[c];
            if (!v) {
                u->children[c] = u->fail->children[c];
                continue;
            }
            ACNode *f = u->fail;
            v->fail = f->children[c];
            v->output |= v->fail->output;

            queue[back++] = v;
            if ((size_t)back == queueCap) {
                queueCap *= 2;
                ACNode **newQ = (ACNode**)realloc(queue, queueCap*sizeof(ACNode*));
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

static int examine_frame_header(const unsigned char *ptr, size_t size) {
    ZSTD_frameHeader fHeader;
    size_t ret = ZSTD_getFrameHeader(&fHeader, ptr, size);
    if (ZSTD_isError(ret)) {
        fprintf(stderr, "Invalid frame header: %s\n", ZSTD_getErrorName(ret));
        return 0;
    }
    
    // Print frame details
    fprintf(stderr, "Frame details:\n");
    fprintf(stderr, "  Window Size: %zu\n", fHeader.windowSize);
    fprintf(stderr, "  Dict ID: %u\n", fHeader.dictID);
    fprintf(stderr, "  Content Size: %zu\n", fHeader.frameContentSize);
    fprintf(stderr, "  Has Checksum: %d\n", fHeader.checksumFlag);
    
    return 1;
}

// Non-recursive free (handles cycles in AC automaton)
static void free_aho_automaton(ACNode *root) {
    if (!root) return;
    size_t queueCap = 1024;
    ACNode **queue = (ACNode**)malloc(queueCap*sizeof(ACNode*));
    if (!queue) return;

    size_t visitedCap = 1024;
    ACNode **visited = (ACNode**)malloc(visitedCap*sizeof(ACNode*));
    if (!visited) {
        free(queue);
        return;
    }
    int front = 0, back = 0;
    size_t visitedCount = 0;

    queue[back++] = root;
    visited[visitedCount++] = root;

    while (front < back) {
        ACNode *u = queue[front++];
        for (int c = 0; c < AC_ALPHABET_SIZE; c++) {
            ACNode *child = u->children[c];
            if (!child || child == root) continue;
            bool alreadyVisited = false;
            for (size_t i=0; i<visitedCount; i++) {
                if (visited[i] == child) {
                    alreadyVisited = true;
                    break;
                }
            }
            if (!alreadyVisited) {
                if (back == (int)queueCap) {
                    queueCap *= 2;
                    ACNode **newQ = (ACNode**)realloc(queue, queueCap*sizeof(ACNode*));
                    if (!newQ) goto done;
                    queue = newQ;
                }
                queue[back++] = child;

                if (visitedCount == visitedCap) {
                    visitedCap *= 2;
                    ACNode **newV = (ACNode**)realloc(visited, visitedCap*sizeof(ACNode*));
                    if (!newV) goto done;
                    visited = newV;
                }
                visited[visitedCount++] = child;
            }
        }
    }

done:
    // free all visited
    for (size_t i=visitedCount; i>0; i--) {
        free(visited[i-1]);
    }
    free(visited);
    free(queue);
}

// -------------------------------------
// 3) Searching
// -------------------------------------

// If you want to *immediately* enqueue to the printer, we do so here
static void ac_feed_chunk(
    ACNode **curStatePtr,
    const char *data, size_t dataLen,
    ACNode *root,
    off_t globalOffset,
    const char *filename,
    PrintQueue *pqueue,        // <--- we push here
    const char *searchStr)
{
    if (!curStatePtr || !*curStatePtr || !data || !pqueue || !searchStr) {
        fprintf(stderr, "Invalid parameters to ac_feed_chunk\n");
        return;
    }
    ACNode *st = *curStatePtr;
    for (size_t i=0; i<dataLen; i++) {
        unsigned char c = (unsigned char)tolower((unsigned char)data[i]);
        st = st->children[c];
        if (st->output) {
            // match end at i
            size_t matchLen = g_patternLen;
            size_t matchStart = (i >= matchLen-1) ? (i - (matchLen-1)) : 0;

            size_t snippetStart = (matchStart < 50) ? 0 : (matchStart-50);
            if (snippetStart > dataLen) snippetStart = dataLen;

            size_t snippetSize = dataLen - snippetStart;
            if (snippetSize > 250) snippetSize = 250;

            char preview[512];
            memset(preview, 0, sizeof(preview));
            memcpy(preview, data + snippetStart, snippetSize);
            preview[snippetSize] = '\0';

            off_t matchOffset = globalOffset + matchStart;
            int closeness = compute_closeness(data + matchStart, searchStr);

            // Build the SearchResult
            SearchResult sr;
            strncpy(sr.filename, filename, sizeof(sr.filename)-1);
            sr.filename[sizeof(sr.filename)-1] = '\0';
            sr.offset = matchOffset;
            sr.closenessScore = closeness;
            strncpy(sr.preview, preview, sizeof(sr.preview)-1);
            sr.preview[sizeof(sr.preview)-1] = '\0';

            // Immediately enqueue for printing
            printqueue_push(pqueue, &sr);
        }
    }
    *curStatePtr = st;
}

// -------------------------------------
// For ring buffer streaming
// -------------------------------------
typedef struct {
    char buffer[ROLLING_BUF_SIZE];
    size_t writePos;
    off_t globalOffset;
    ACNode *acState;
} RingBufState;

static __thread RingBufState g_ring;

static void ringbuf_init(ACNode *root) {
    memset(g_ring.buffer, 0, ROLLING_BUF_SIZE);
    g_ring.writePos     = 0;
    g_ring.globalOffset = 0;
    g_ring.acState      = root;
}

static void ringbuf_feed(
    PrintQueue *pqueue,
    const char *filename,
    ACNode *acRoot,
    const char *searchStr,
    const char *src, size_t srcLen)
{
    size_t srcOffset = 0;
    size_t overlap = (g_patternLen>0)? (g_patternLen-1): 0;
    if (overlap >= ROLLING_BUF_SIZE) overlap = 0;

    while (srcLen>0) {
        if (g_ring.writePos >= ROLLING_BUF_SIZE) {
            // feed all to AC
            ac_feed_chunk(&g_ring.acState, g_ring.buffer, g_ring.writePos,
                          acRoot, (g_ring.globalOffset - g_ring.writePos),
                          filename, pqueue, searchStr);

            // keep overlap
            if (overlap>g_ring.writePos) overlap=g_ring.writePos;
            memmove(g_ring.buffer, g_ring.buffer+(g_ring.writePos-overlap), overlap);
            g_ring.writePos=overlap;
        }
        size_t space = ROLLING_BUF_SIZE - g_ring.writePos;
        if (space>srcLen) space=srcLen;

        memcpy(g_ring.buffer+g_ring.writePos, src+srcOffset, space);
        g_ring.writePos += space;
        g_ring.globalOffset += space;
        srcOffset += space;
        srcLen -= space;
    }
}

// flush leftover
static void ringbuf_flush(
    PrintQueue *pqueue,
    const char *filename,
    ACNode *acRoot,
    const char *searchStr)
{
    if (g_ring.writePos>0) {
        ac_feed_chunk(&g_ring.acState, g_ring.buffer, g_ring.writePos,
                      acRoot, (g_ring.globalOffset - g_ring.writePos),
                      filename, pqueue, searchStr);
    }
    g_ring.writePos=0;
}

static int is_valid_frame_header(const ZSTD_frameHeader *fHeader) {
    // Reasonable limits for frame validation
    const uint64_t MAX_WINDOW_SIZE = 1ULL << 31;    // 2GB max window
    const uint64_t MAX_CONTENT_SIZE = 1ULL << 40;   // 1TB max content
    
    // Print frame details for debugging
    // fprintf(stderr, "Validating frame:\n");
    // fprintf(stderr, "  Window Size: %zu\n", fHeader->windowSize);
    // fprintf(stderr, "  Dict ID: %u\n", fHeader->dictID);
    // fprintf(stderr, "  Content Size: %zu\n", fHeader->frameContentSize);
    
    // Basic sanity checks
    if (fHeader->windowSize > MAX_WINDOW_SIZE) {
        fprintf(stderr, "  Rejected: Window size too large\n");
        return 0;
    }
    
    if (fHeader->frameContentSize != ZSTD_CONTENTSIZE_UNKNOWN && 
        fHeader->frameContentSize > MAX_CONTENT_SIZE) {
        fprintf(stderr, "  Rejected: Content size too large\n");
        return 0;
    }
    
    if (fHeader->dictID != 0) {
        fprintf(stderr, "  Rejected: Dictionary required\n");
        return 0;
    }
    
    // fprintf(stderr, "  Frame accepted\n");
    return 1;
}

// -------------------------------------
// Tar / zstd scanning
// -------------------------------------
static inline size_t octal_to_size(const char *str, size_t n) {
    size_t val=0;
    for (size_t i=0; i<n && str[i]>='0' && str[i]<='7'; i++) {
        val=(val<<3)+(str[i]-'0');
    }
    return val;
}

static inline int is_end_of_archive(const unsigned char *block) {
    for (int i=0; i<TAR_BLOCK_SIZE; i++) {
        if (block[i]!=0) return 0;
    }
    return 1;
}

// The refined find_frame_offsets function
static void find_frame_offsets(const unsigned char *ptr,
                             size_t size,
                             off_t **matches,
                             size_t *count,
                             size_t *capacity)
{
    // Create a decompression context to get frame sizes
    ZSTD_DCtx* dctx = ZSTD_createDCtx();
    if (!dctx) return;

    for (size_t i = 0; i + 4 <= size; i++) {
        uint32_t val;
        memcpy(&val, ptr + i, 4);
        if (val == FRAME_MAGIC) {
            // fprintf(stderr, "\nFound potential frame at offset %zu\n", i);
            
            ZSTD_frameHeader fHeader;
            size_t headerSize = ZSTD_getFrameHeader(&fHeader, ptr + i, size - i);
            
            if (!ZSTD_isError(headerSize) && is_valid_frame_header(&fHeader)) {
                // Get the total frame size (compressed data + header)
                size_t frameSize = ZSTD_findFrameCompressedSize(ptr + i, size - i);
                if (ZSTD_isError(frameSize)) {
                    fprintf(stderr, "Error getting frame size: %s\n", ZSTD_getErrorName(frameSize));
                    continue;
                }

                // Store this valid frame offset
                if (*count == *capacity) {
                    size_t newCap = (*capacity == 0) ? 512 : (*capacity * 2);
                    off_t *newArr = (off_t *)realloc(*matches, newCap * sizeof(off_t));
                    if (!newArr) {
                        fprintf(stderr, "Out of memory in find_frame_offsets\n");
                        ZSTD_freeDCtx(dctx);
                        return;
                    }
                    *matches = newArr;
                    *capacity = newCap;
                }
                (*matches)[(*count)++] = i;
                
                // Skip past the ENTIRE frame, not just the header
                i += frameSize - 1;  // -1 because loop will increment
                
                // fprintf(stderr, "Frame accepted, size: %zu bytes\n", frameSize);
            }
        }
    }

    ZSTD_freeDCtx(dctx);
}

// process one zstd frame
static void index_tar_entries_with_ring(
    ZSTD_DCtx *dctx,
    const void *mapped,
    size_t fileSize,
    off_t startOffset,
    PrintQueue *pqueue,
    ACNode *acRoot,
    const char *searchStr,
    const char *topFilename)
{
    ZSTD_inBuffer zin;
    zin.src  = (const char*)mapped + startOffset;
    zin.size = fileSize - startOffset;
    zin.pos  = 0;

    char outBuf[ZSTD_CHUNK_SIZE];
    ringbuf_init(acRoot);

    while(1) {
        ZSTD_outBuffer zout;
        zout.dst=outBuf;
        zout.size=ZSTD_CHUNK_SIZE;
        zout.pos=0;

        size_t ret = ZSTD_decompressStream(dctx, &zout, &zin);
        if (ZSTD_isError(ret)) {
            fprintf(stderr, "ZSTD error: %s\n", ZSTD_getErrorName(ret));
            break;  // exit the while(1) for THIS offset, keep scanning next offsets
        }
        size_t chunkLen=zout.pos;
        if (chunkLen==0 && ret==0) {
            // end
            break;
        }
        ringbuf_feed(pqueue, topFilename, acRoot, searchStr, outBuf, chunkLen);
        if (ret==0) break;
    }
    // flush leftover
    ringbuf_flush(pqueue, topFilename, acRoot, searchStr);
}

// entire file
static void build_index(
    const char *filename,
    PrintQueue *pqueue,
    const char *searchStr,
    ACNode *acRoot)
{
    int fd=open(filename,O_RDONLY);
    if(fd<0) return;
    struct stat st;
    if(fstat(fd,&st)!=0 || st.st_size==0) {
        close(fd); 
        return;
    }
    void *mapped=mmap(NULL,st.st_size,PROT_READ,MAP_PRIVATE,fd,0);
    close(fd);
    if(mapped==MAP_FAILED) return;

    ZSTD_DCtx *dctx=ZSTD_createDCtx();
    if(!dctx) {
        munmap(mapped,st.st_size);
        return;
    }
    off_t *matches=NULL;
    size_t matchCount=0, matchCap=0;
    find_frame_offsets((const unsigned char*)mapped, (size_t)st.st_size,
                       &matches,&matchCount,&matchCap);
    // printf("File %s => found %zu frames\n", filename, matchCount);


    for(size_t i=0; i<matchCount; i++) {
        // fprintf(stderr, "Processing frame %zu at offset %lld\n", 
        //         i, (long long)matches[i]);
                
        size_t initRet = ZSTD_initDStream(dctx);
        if (ZSTD_isError(initRet)) {
            fprintf(stderr, "Error initDStream: %s\n", ZSTD_getErrorName(initRet));
            continue;  // Skip this frame but try the next one
        }
        
        index_tar_entries_with_ring(dctx, mapped, st.st_size,
                                  matches[i],
                                  pqueue, acRoot, searchStr,
                                  filename);
    }
    free(matches);
    ZSTD_freeDCtx(dctx);
    munmap(mapped,st.st_size);
}

// WorkerArgs
typedef struct {
    PrintQueue *pqueue;
    char **files;
    int start;
    int end;
    const char *searchStr;
    ACNode *acRoot;
} WorkerArgs;

// worker thread
static void *worker_thread(void *arg) {
    WorkerArgs *w = (WorkerArgs*)arg;
    for(int i=w->start; i<w->end; i++) {
        build_index(w->files[i], w->pqueue, w->searchStr, w->acRoot);
    }
    return NULL;
}

// -------------------------------------
// 4) Printer Thread
// -------------------------------------
static void *printer_thread(void *arg)
{
    PrintQueue *q = (PrintQueue*)arg;
    SearchResult sr;
    // pop until done
    while(printqueue_pop(q, &sr)) {
        // Print the result
        printf("{\"file\":\"%s\", \"offset\":%lld, \"score\":%d, \"preview\":\"%s\"}\n",
               sr.filename,
               (long long)sr.offset,
               sr.closenessScore,
               sr.preview);
        fflush(stdout);
    }
    return NULL;
}

// -------------------------------------
// main
// -------------------------------------
int main(int argc, char** argv)
{
    if(argc<2) {
        fprintf(stderr, "Usage: %s <searchString>\n",argv[0]);
        return 1;
    }
    const char *searchStr=argv[1];

    // Build the automaton
    ACNode *acRoot = build_aho_automaton(searchStr);
    if(!acRoot) {
        fprintf(stderr, "Failed to build Aho automaton\n");
        return 1;
    }

    // Gather files
    DIR *d=opendir(".");
    if(!d) {
        free_aho_automaton(acRoot);
        return 1;
    }

    char **files=NULL;
    size_t fileCount=0, fileCap=0;
    struct dirent *de;
    while((de=readdir(d))!=NULL) {
        // Use fnmatch for more flexible pattern matching
        if(fnmatch("batch_[0-9][0-9][0-9][0-9][0-9].tar.zst", de->d_name, 0) == 0) {
            if(fileCount==fileCap) {
                fileCap = fileCap ? fileCap*2 : 32;
                char **tmp = (char**)realloc(files, fileCap*sizeof(char*));
                if(!tmp) {
                    free(files);
                    closedir(d);
                    free_aho_automaton(acRoot);
                    return 1;
                }
                files = tmp;
            }
            files[fileCount++] = strdup(de->d_name);
        }
    }
    closedir(d);

    if(fileCount==0) {
        fprintf(stderr,"No matching .tar.zst files found.\n");
        free(files);
        free_aho_automaton(acRoot);
        return 1;
    }

    // After collecting all files, sort them
    if(fileCount > 1) {
        qsort(files, fileCount, sizeof(char*), (int (*)(const void*, const void*))strcmp);
    }

    printf("Found %zu files to process\n", fileCount);
    for(size_t i = 0; i < fileCount; i++) {
        printf("  %zu: %s\n", i+1, files[i]);
    }

    // 1) Initialize the PrintQueue
    PrintQueue pqueue;
    printqueue_init(&pqueue);

    // 2) Launch the printer thread
    pthread_t printerTid;
    pthread_create(&printerTid, NULL, printer_thread, &pqueue);

    // 3) Spawn worker threads to do the searching
    int threadCount=(fileCount>MAX_THREADS)?MAX_THREADS:(int)fileCount;
    pthread_t tids[threadCount];
    WorkerArgs wargs[threadCount];

    int filesPerThread=(int)(fileCount/threadCount);
    int remainder=(int)(fileCount%threadCount);
    int start=0;
    for(int i=0;i<threadCount;i++) {
        int cnt=filesPerThread+ (i<remainder?1:0);
        wargs[i].pqueue    = &pqueue;
        wargs[i].files     = files;
        wargs[i].start     = start;
        wargs[i].end       = start+cnt;
        wargs[i].searchStr = searchStr;
        wargs[i].acRoot    = acRoot;

        pthread_create(&tids[i], NULL, worker_thread, &wargs[i]);
        start+=cnt;
    }

    // 4) Wait for the worker threads to finish
    for(int i=0;i<threadCount;i++) {
        pthread_join(tids[i],NULL);
    }

    // 5) Mark queue done => signals printer to exit eventually
    printqueue_mark_done(&pqueue);

    // 6) Wait for printer thread
    pthread_join(printerTid, NULL);

    // Cleanup
    for(size_t i=0;i<fileCount;i++) {
        free(files[i]);
    }
    free(files);

    printqueue_destroy(&pqueue);
    free_aho_automaton(acRoot);
    return 0;
}
