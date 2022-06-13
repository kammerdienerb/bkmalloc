#define BKMALLOC_HOOK
#include "bkmalloc.h"

#include <stdio.h>

struct Hooks {
    u64 hist[BK_NR_SIZE_CLASSES + 1];

    Hooks() : hist() { }

    void post_alloc(bk_Heap *heap, u64 n_bytes, u64 alignment, int zero_mem, void *addr) {
        bk_Block *block;
        u32       idx;

        block = ADDR_PARENT_BLOCK(addr);
        idx   = block->meta.size_class_idx;

        if (idx == BK_BIG_ALLOC_SIZE_CLASS_IDX) { idx = BK_NR_SIZE_CLASSES; }

        hist[idx] += 1;
    }

    ~Hooks() {
        u32 i;

        printf("%-10s %16s\n", "SIZE CLASS", "COUNT");
        printf("---------------------------\n");
        for (i = 0; i < BK_NR_SIZE_CLASSES + 1; i += 1) {
            if (i == BK_NR_SIZE_CLASSES) {
                printf("%-10s %16lu\n", "BIG", this->hist[i]);
            } else {
                printf("%-10lu %16lu\n", bk_size_class_idx_to_size(i), this->hist[i]);
            }
        }
    }
};

static Hooks hooks;

extern "C"
void bk_post_alloc_hook(bk_Heap *heap, u64 n_bytes, u64 alignment, int zero_mem, void *addr) {
    hooks.post_alloc(heap, n_bytes, alignment, zero_mem, addr);
}
