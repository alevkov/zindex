#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <dirent.h>
#include <sys/mman.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <unistd.h>
#include <stdint.h>
#include <zstd.h>
#include <pthread.h>
#include <fnmatch.h>
#include <assert.h>

/*
   Compile (tested on ubuntu)
     clang -O3 -o zindex zindex.c -I/opt/homebrew/include -L/opt/homebrew/lib -lzstd -lpthread
   Run:
     ./zindex "pattern"
*/

#define FRAME_MAGIC 0xFD2FB528U // zstd 
#define TAR_BLOCK_SIZE 512
#define INDEX_SNIPPET_SIZE 2048 // adjust 
#define MAX_THREADS 12
#define CHUNK_SIZE (512 * 1024)

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

typedef struct {
    char filename[256];
    char snippet[INDEX_SNIPPET_SIZE+1];
} snippet_entry;

typedef struct {
    snippet_entry *entries;
    size_t count;
    size_t capacity;
    pthread_mutex_t lock;
} snippet_index;

static inline void snippet_index_init(snippet_index *idx) {
    idx->entries = NULL;
    idx->count = 0;
    idx->capacity = 0;
    pthread_mutex_init(&idx->lock, NULL);
}

static inline void snippet_index_destroy(snippet_index *idx) {
    free(idx->entries);
    pthread_mutex_destroy(&idx->lock);
}

static inline void add_snippet(snippet_index *idx, const char *filename, const char *text) {
    pthread_mutex_lock(&idx->lock);
    if (idx->count == idx->capacity) {
        size_t new_cap = idx->capacity == 0 ? 1024 : idx->capacity * 2;
        snippet_entry *new_entries = (snippet_entry *)realloc(idx->entries, new_cap * sizeof(snippet_entry));
        if (!new_entries) {
            pthread_mutex_unlock(&idx->lock);
            return;
        }
        idx->entries = new_entries;
        idx->capacity = new_cap;
    }
    strncpy(idx->entries[idx->count].filename, filename, sizeof(idx->entries[idx->count].filename)-1);
    idx->entries[idx->count].filename[sizeof(idx->entries[idx->count].filename)-1] = '\0';
    strncpy(idx->entries[idx->count].snippet, text, INDEX_SNIPPET_SIZE);
    idx->entries[idx->count].snippet[INDEX_SNIPPET_SIZE] = '\0';
    idx->count++;
    pthread_mutex_unlock(&idx->lock);
}

static inline size_t octal_to_size(const char *str, size_t n) {
    size_t val = 0;
    for (size_t i = 0; i < n && str[i] >= '0' && str[i] <= '7'; i++) {
        val = (val << 3) + (str[i] - '0');
    }
    return val;
}

static inline int is_end_of_archive(const unsigned char *block) {
    for (int i = 0; i < TAR_BLOCK_SIZE; i++) {
        if (block[i] != 0) return 0;
    }
    return 1;
}

static void index_tar_entries(ZSTD_DCtx *dctx, const void *base, size_t size, off_t start_offset, snippet_index *idx) {
    unsigned char *tar_data = (unsigned char*)malloc(CHUNK_SIZE * 8);
    if (!tar_data) return;
    size_t tar_data_cap = CHUNK_SIZE * 8;
    size_t tar_data_size = 0;

    char *out_buf = (char*)malloc(CHUNK_SIZE);
    if (!out_buf) {
        free(tar_data);
        return;
    }

    ZSTD_inBuffer zin = { (const char *)base + start_offset, size - start_offset, 0 };
    ZSTD_outBuffer zout = { out_buf, CHUNK_SIZE, 0 };
    size_t ret;

    for (;;) {
        zout.pos = 0;
        ret = ZSTD_decompressStream(dctx, &zout, &zin);
        if (ZSTD_isError(ret)) break;

        size_t new_data = zout.pos;
        if (tar_data_size + new_data > tar_data_cap) {
            tar_data_cap = tar_data_cap * 2 + new_data;
            unsigned char *new_ptr = (unsigned char*)realloc(tar_data, tar_data_cap);
            if (!new_ptr) break;
            tar_data = new_ptr;
        }
        memcpy(tar_data + tar_data_size, out_buf, new_data);
        tar_data_size += new_data;

        while (tar_data_size >= TAR_BLOCK_SIZE) {
            if (is_end_of_archive(tar_data)) {
                size_t rem = tar_data_size - TAR_BLOCK_SIZE;
                memmove(tar_data, tar_data + TAR_BLOCK_SIZE, rem);
                goto done;
            }

            struct tar_header *h = (struct tar_header *)tar_data;

            char filename[256];
            memset(filename, 0, sizeof(filename));
            if (h->prefix[0]) {
                size_t prefix_len = strnlen(h->prefix, sizeof(h->prefix));
                size_t name_len = strnlen(h->name, sizeof(h->name));
                if (prefix_len + name_len + 1 < sizeof(filename)) {
                    memcpy(filename, h->prefix, prefix_len);
                    filename[prefix_len] = '/';
                    memcpy(filename + prefix_len + 1, h->name, name_len);
                    filename[prefix_len + 1 + name_len] = '\0';
                } else {
                    // fallback
                    strncpy(filename, h->name, sizeof(h->name)-1);
                }
            } else {
                strncpy(filename, h->name, sizeof(h->name));
                filename[sizeof(filename)-1] = '\0';
            }

            for (int i = (int)strlen(filename)-1; i >= 0; i--) {
                if (filename[i] == ' ' || filename[i] == '\0') filename[i] = '\0'; else break;
            }

            size_t file_size = octal_to_size(h->size, sizeof(h->size));

            size_t rem = tar_data_size - TAR_BLOCK_SIZE;
            memmove(tar_data, tar_data + TAR_BLOCK_SIZE, rem);
            tar_data_size = rem;

            while (tar_data_size < file_size) {
                if (zin.pos == zin.size) goto done; 
                zout.pos = 0;
                ret = ZSTD_decompressStream(dctx, &zout, &zin);
                if (ZSTD_isError(ret)) goto done;
                if (tar_data_size + zout.pos > tar_data_cap) {
                    tar_data_cap = tar_data_cap * 2 + zout.pos;
                    unsigned char *new_ptr = (unsigned char*)realloc(tar_data, tar_data_cap);
                    if (!new_ptr) goto done;
                    tar_data = new_ptr;
                }
                memcpy(tar_data + tar_data_size, out_buf, zout.pos);
                tar_data_size += zout.pos;
                if (ret == 0 && tar_data_size < file_size) goto done;
            }

            size_t snippet_len = file_size < INDEX_SNIPPET_SIZE ? file_size : INDEX_SNIPPET_SIZE;
            char snippet[INDEX_SNIPPET_SIZE+1];
            memcpy(snippet, tar_data, snippet_len);
            snippet[snippet_len] = '\0';
            add_snippet(idx, filename, snippet);

            size_t skip = ((file_size + TAR_BLOCK_SIZE - 1) / TAR_BLOCK_SIZE) * TAR_BLOCK_SIZE;
            while (tar_data_size < skip && zin.pos < zin.size && ret != 0) {
                zout.pos = 0;
                ret = ZSTD_decompressStream(dctx, &zout, &zin);
                if (ZSTD_isError(ret)) goto done;
                if (tar_data_size + zout.pos > tar_data_cap) {
                    tar_data_cap = tar_data_cap * 2 + zout.pos;
                    unsigned char *new_ptr = (unsigned char*)realloc(tar_data, tar_data_cap);
                    if (!new_ptr) goto done;
                    tar_data = new_ptr;
                }
                memcpy(tar_data + tar_data_size, out_buf, zout.pos);
                tar_data_size += zout.pos;
            }
            if (skip <= tar_data_size) {
                memmove(tar_data, tar_data + skip, tar_data_size - skip);
                tar_data_size -= skip;
            } else {
                size_t diff = skip - tar_data_size;
                if (diff > 0) goto done;
            }
        }

        if (zin.pos == zin.size && tar_data_size < TAR_BLOCK_SIZE && ret == 0) {
            goto done;
        }

        if (ret == 0) {
            goto done;
        }
    }

done:
    free(tar_data);
    free(out_buf);
}

// linear scan for FRAME_MAGIC
static void find_frame_magic(const unsigned char *m, size_t size, uint32_t val, off_t **matches, size_t *match_count, size_t *match_capacity) {
    for (size_t i = 0; i + 4 <= size; i++) {
        uint32_t check;
        memcpy(&check, m+i, 4);
        if (check == val) {
            if (*match_count == *match_capacity) {
                *match_capacity = (*match_capacity == 0) ? 1024 : (*match_capacity * 2);
                *matches = (off_t*)realloc(*matches, (*match_capacity)*sizeof(off_t));
            }
            (*matches)[(*match_count)++] = i;
        }
    }
}

static void build_index(const char *filename, snippet_index *idx) {
    int fd = open(filename, O_RDONLY);
    if (fd < 0) return;

    struct stat st;
    if (fstat(fd, &st) != 0 || st.st_size == 0) {
        close(fd);
        return;
    }

    void *mapped = mmap(NULL, st.st_size, PROT_READ, MAP_PRIVATE, fd, 0);
    close(fd);
    if (mapped == MAP_FAILED) return;

    ZSTD_DCtx *dctx = ZSTD_createDCtx();
    if (!dctx) {
        munmap(mapped, st.st_size);
        return;
    }

    off_t *matches = NULL;
    size_t match_count = 0, match_capacity = 0;
    find_frame_magic((const unsigned char*)mapped, st.st_size, FRAME_MAGIC, &matches, &match_count, &match_capacity);

    for (size_t i = 0; i < match_count; i++) {
        if (!ZSTD_isError(ZSTD_initDStream(dctx))) {
            ZSTD_initDStream(dctx);
            index_tar_entries(dctx, mapped, st.st_size, matches[i], idx);
        }
    }

    free(matches);
    ZSTD_freeDCtx(dctx);
    munmap(mapped, st.st_size);
}

static void search_index(const snippet_index *idx, const char *pattern) {
    for (size_t i = 0; i < idx->count; i++) {
        // Use fnmatch to match the snippet against the given glob pattern
        // FNM_CASEFOLD for case-insensitive, TBD
        if (fnmatch(pattern, idx->entries[i].snippet, 0) == 0) {
            printf("Match in file: %s\nSnippet: %s\n",
                   idx->entries[i].filename, idx->entries[i].snippet);
        }
    }
}


typedef struct {
    snippet_index *idx;
    char **files;
    int start;
    int end;
} thread_arg;

static void* worker_thread(void *arg) {
    thread_arg *targ = (thread_arg*)arg;
    for (int i = targ->start; i < targ->end; i++) {
        build_index(targ->files[i], targ->idx);
    }
    return NULL;
}

int main(int argc, char **argv) {
    DIR *d = opendir(".");
    if (!d) return 1;

    char **files = NULL;
    size_t file_count = 0, file_cap = 0;
    struct dirent *de;
    while ((de = readdir(d)) != NULL) {
        if (strncmp(de->d_name, "batch_0000", 10) == 0 && strstr(de->d_name, ".tar.zst")) {
            if (file_count == file_cap) {
                file_cap = file_cap ? file_cap * 2 : 128;
                char **new_files = (char**)realloc(files, file_cap * sizeof(char*));
                if (!new_files) {
                    closedir(d);
                    free(files);
                    return 1;
                }
                files = new_files;
            }
            files[file_count] = strdup(de->d_name);
            file_count++;
        }
    }
    closedir(d);

    snippet_index idx;
    snippet_index_init(&idx);

    assert(file_count > 0);
    int thread_count = (int)(file_count > MAX_THREADS ? MAX_THREADS : file_count);
    pthread_t threads[MAX_THREADS];
    thread_arg targs[MAX_THREADS];

    int files_per_thread = (int)(file_count / thread_count);
    int remainder = (int)(file_count % thread_count);
    int start = 0;
    for (int i = 0; i < thread_count; i++) {
        int count = files_per_thread + (i < remainder ? 1 : 0);
        targs[i].idx = &idx;
        targs[i].files = files;
        targs[i].start = start;
        targs[i].end = start + count;
        start += count;
        pthread_create(&threads[i], NULL, worker_thread, &targs[i]);
    }

    for (int i = 0; i < thread_count; i++) {
        pthread_join(threads[i], NULL);
    }

    if (argc > 1) {
        search_index(&idx, argv[1]);
    }

    for (size_t i = 0; i < file_count; i++) {
        free(files[i]);
    }
    free(files);

    snippet_index_destroy(&idx);
    return 0;
}
