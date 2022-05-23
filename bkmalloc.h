#ifndef __BKMALLOC_H__
#define __BKMALLOC_H__

#include <stddef.h>

struct bk_Heap;


#ifdef __cplusplus
#define BK_THROW throw()
extern "C" {
#else
#define BK_THROW
#endif /* __cplusplus */

void * bk_heap_malloc(struct bk_Heap *heap, size_t n_bytes);
void * bk_heap_calloc(struct bk_Heap *heap, size_t count, size_t n_bytes);
void * bk_heap_realloc(struct bk_Heap *heap, void *addr, size_t n_bytes);
void * bk_heap_reallocf(struct bk_Heap *heap, void *addr, size_t n_bytes);
void * bk_heap_valloc(struct bk_Heap *heap, size_t n_bytes);
void * bk_heap_pvalloc(struct bk_Heap *heap, size_t n_bytes);
int    bk_heap_posix_memalign(struct bk_Heap *heap, void **memptr, size_t alignment, size_t size);
void * bk_heap_aligned_alloc(struct bk_Heap *heap, size_t alignment, size_t size);
void * bk_heap_memalign(struct bk_Heap *heap, size_t alignment, size_t size);

void * bk_malloc(size_t n_bytes);
void * bk_calloc(size_t count, size_t n_bytes);
void * bk_realloc(void *addr, size_t n_bytes);
void * bk_reallocf(void *addr, size_t n_bytes);
void * bk_valloc(size_t n_bytes);
void   bk_free(void *addr);
int    bk_posix_memalign(void **memptr, size_t alignment, size_t n_bytes);
void * bk_aligned_alloc(size_t alignment, size_t size);
size_t bk_malloc_size(void *addr);

void * malloc(size_t n_bytes) BK_THROW;
void * calloc(size_t count, size_t n_bytes) BK_THROW;
void * realloc(void *addr, size_t n_bytes) BK_THROW;
void * reallocf(void *addr, size_t n_bytes) BK_THROW;
void * valloc(size_t n_bytes) BK_THROW;
void * pvalloc(size_t n_bytes) BK_THROW;
void   free(void *addr) BK_THROW;
int    posix_memalign(void **memptr, size_t alignment, size_t size) BK_THROW;
void * aligned_alloc(size_t alignment, size_t size) BK_THROW;
void * memalign(size_t alignment, size_t size) BK_THROW;
size_t malloc_size(void *addr) BK_THROW;
size_t malloc_usable_size(void *addr) BK_THROW;
#ifdef __cplusplus
}
#endif /* __cplusplus */

#ifdef __cplusplus

#include <new>
#include <mutex>

void * operator new(std::size_t size);
void * operator new[](std::size_t size);
void * operator new(std::size_t size, const std::nothrow_t &) noexcept;
void * operator new[](std::size_t size, const std::nothrow_t &) noexcept;
void   operator delete(void *ptr) noexcept;
void   operator delete[](void *ptr) noexcept;
void   operator delete(void *ptr, const std::nothrow_t &) noexcept;
void   operator delete[](void *ptr, const std::nothrow_t &) noexcept;

#if __cpp_sized_deallocation >= 201309
/* C++14's sized-delete operators. */
void operator delete(void *ptr, std::size_t size) noexcept;
void operator delete[](void *ptr, std::size_t size) noexcept;
#endif

#if __cpp_aligned_new >= 201606
/* C++17's over-aligned operators. */
void * operator new(std::size_t size, std::align_val_t);
void * operator new(std::size_t size, std::align_val_t, const std::nothrow_t &) noexcept;
void * operator new[](std::size_t size, std::align_val_t);
void * operator new[](std::size_t size, std::align_val_t, const std::nothrow_t &) noexcept;
void   operator delete(void* ptr, std::align_val_t) noexcept;
void   operator delete(void* ptr, std::align_val_t, const std::nothrow_t &) noexcept;
void   operator delete(void* ptr, std::size_t size, std::align_val_t al) noexcept;
void   operator delete[](void* ptr, std::align_val_t) noexcept;
void   operator delete[](void* ptr, std::align_val_t, const std::nothrow_t &) noexcept;
void   operator delete[](void* ptr, std::size_t size, std::align_val_t al) noexcept;
#endif

static inline void *
bk_handle_OOM(std::size_t size, bool nothrow) {
    void *ptr;

    ptr = nullptr;

    while (ptr == nullptr) {
        std::new_handler handler;
        /* GCC-4.8 and clang 4.0 do not have std::get_new_handler. */
        {
            static std::mutex mtx;
            std::lock_guard<std::mutex> lock(mtx);

            handler = std::set_new_handler(nullptr);
            std::set_new_handler(handler);
        }
        if (handler == nullptr) {
            break;
        }

        try {
            handler();
        } catch (const std::bad_alloc &) {
            break;
        }

        ptr = bk_malloc(size);
    }

    if (ptr == nullptr && !nothrow) { std::__throw_bad_alloc(); }

    return ptr;
}

template <bool is_no_except>
static inline void *
bk_new_impl(std::size_t size) noexcept(is_no_except) {
    void *ptr;

    ptr = bk_malloc(size);
    if (__builtin_expect(ptr != nullptr, 1)) { return ptr; }

    return bk_handle_OOM(size, is_no_except);
}

void * operator new(std::size_t size)                                    { return bk_new_impl<false>(size); }
void * operator new[](std::size_t size)                                  { return bk_new_impl<false>(size); }
void * operator new(std::size_t size, const std::nothrow_t &) noexcept   { return bk_new_impl<true>(size);  }
void * operator new[](std::size_t size, const std::nothrow_t &) noexcept { return bk_new_impl<true>(size);  }

#if __cpp_aligned_new >= 201606

template <bool is_no_except>
static inline void *
bk_aligned_new_impl(std::size_t size, std::align_val_t alignment) noexcept(is_no_except) {
    void *ptr;

    ptr = bk_aligned_alloc(static_cast<std::size_t>(alignment), size);

    if (__builtin_expect(ptr != nullptr, 1)) {
        return ptr;
    }

    return bk_handle_OOM(size, is_no_except);
}

void * operator new(std::size_t size, std::align_val_t alignment)                                    { return bk_aligned_new_impl<false>(size, alignment); }
void * operator new[](std::size_t size, std::align_val_t alignment)                                  { return bk_aligned_new_impl<false>(size, alignment); }
void * operator new(std::size_t size, std::align_val_t alignment, const std::nothrow_t &) noexcept   { return bk_aligned_new_impl<true>(size, alignment);  }
void * operator new[](std::size_t size, std::align_val_t alignment, const std::nothrow_t &) noexcept { return bk_aligned_new_impl<true>(size, alignment);  }

#endif  /* __cpp_aligned_new */

void operator delete(void *ptr) noexcept                           { bk_free(ptr); }
void operator delete[](void *ptr) noexcept                         { bk_free(ptr); }
void operator delete(void *ptr, const std::nothrow_t &) noexcept   { bk_free(ptr); }
void operator delete[](void *ptr, const std::nothrow_t &) noexcept { bk_free(ptr); }

#if __cpp_sized_deallocation >= 201309

static inline void
bk_sized_delete_impl(void* ptr, std::size_t size) noexcept {
    (void)size;

    if (__builtin_expect(ptr == nullptr, 0)) {
        return;
    }
    bk_free(ptr);
}

void operator delete(void *ptr, std::size_t size) noexcept   { bk_sized_delete_impl(ptr, size); }
void operator delete[](void *ptr, std::size_t size) noexcept { bk_sized_delete_impl(ptr, size); }

#endif  /* __cpp_sized_deallocation */

#if __cpp_aligned_new >= 201606

static inline void
bk_aligned_sized_delete_impl(void* ptr, std::size_t size, std::align_val_t alignment) noexcept {
    if (__builtin_expect(ptr == nullptr, 0)) {
        return;
    }
    bk_free(ptr);
}

void operator delete(void* ptr, std::align_val_t) noexcept                               { bk_free(ptr);                                       }
void operator delete[](void* ptr, std::align_val_t) noexcept                             { bk_free(ptr);                                       }
void operator delete(void* ptr, std::align_val_t, const std::nothrow_t&) noexcept        { bk_free(ptr);                                       }
void operator delete[](void* ptr, std::align_val_t, const std::nothrow_t&) noexcept      { bk_free(ptr);                                       }
void operator delete(void* ptr, std::size_t size, std::align_val_t alignment) noexcept   { bk_aligned_sized_delete_impl(ptr, size, alignment); }
void operator delete[](void* ptr, std::size_t size, std::align_val_t alignment) noexcept { bk_aligned_sized_delete_impl(ptr, size, alignment); }

#endif  /* __cpp_aligned_new */
#endif /* __cplusplus */



/******************************* @impl *******************************/
#ifdef BKMALLOC_IMPL

#include <stdint.h>
#include <stdarg.h>
#include <stddef.h>
#include <string.h> /* memcpy(), memset() */

#define MIN_ALIGN                   (16ULL)
#define THREAD_MAX_ALLOC_SIZE       (KB(16) - 1)
#define BK_BLOCK_SIZE               (MB(1))
#define BK_BLOCK_ALIGN              (MB(1))
#define BK_BASE_SIZE_CLASS          (MIN_ALIGN)
#define BK_NR_SIZE_CLASSES          (LOG2_64BIT(BK_BLOCK_SIZE / BK_BASE_SIZE_CLASS) - 1)
#define BK_MAX_BLOCK_ALLOC_SIZE     (BK_BASE_SIZE_CLASS * (1 << (BK_NR_SIZE_CLASSES - 1)))
#define BK_BIG_ALLOC_SIZE_CLASS     (0xFFFFFFFF)
#define BK_BIG_ALLOC_SIZE_CLASS_IDX (0xFFFFFFFF)

static inline void bk_init(void);


/******************************* @@util *******************************/

#define likely(x)   (__builtin_expect(!!(x), 1))
#define unlikely(x) (__builtin_expect(!!(x), 0))

#define MIN(a, b) ((a) <= (b) ? (a) : (b))
#define MAX(a, b) ((a) >= (b) ? (a) : (b))

#define UINT(w) uint##w##_t
#define SINT(w) int##w##_t

#define u8  UINT(8 )
#define u16 UINT(16)
#define u32 UINT(32)
#define u64 UINT(64)

#define s8  SINT(8 )
#define s16 SINT(16)
#define s32 SINT(32)
#define s64 SINT(64)

#ifdef BK_DEBUG
#define BK_ALWAYS_INLINE
#else
#define BK_ALWAYS_INLINE __attribute__((always_inline))
#endif /* BK_DEBUG */

#define GLOBAL_ALIGN(_a) __attribute__((aligned((_a))))
#define FIELD_ALIGN(_a)  __attribute__((aligned((_a))))
#define PACKED           __attribute__((packed))
#define THREAD_LOCAL     __thread

#define XOR_SWAP_64(a, b) do {   \
    a = ((u64)(a)) ^ ((u64)(b)); \
    b = ((u64)(b)) ^ ((u64)(a)); \
    a = ((u64)(a)) ^ ((u64)(b)); \
} while (0);

#define XOR_SWAP_PTR(a, b) do {           \
    a = (void*)(((u64)(a)) ^ ((u64)(b))); \
    b = (void*)(((u64)(b)) ^ ((u64)(a))); \
    a = (void*)(((u64)(a)) ^ ((u64)(b))); \
} while (0);

#define ALIGN_UP(x, align)      ((__typeof(x))((((u64)(x)) + ((u64)align)) & ~(((u64)align) - 1ULL)))
#define ALIGN_DOWN(x, align)    ((__typeof(x))(((u64)(x)) & ~(((u64)align) - 1ULL)))
#define IS_ALIGNED(x, align)    (!(((u64)(x)) & (((u64)align) - 1ULL)))
#define IS_POWER_OF_TWO(x)      ((x) != 0 && IS_ALIGNED((x), (x)))

#define LOG2_8BIT(v)  (8 - 90/(((v)/4+14)|1) - 2/((v)/2+1))
#define LOG2_16BIT(v) (8*((v)>255) + LOG2_8BIT((v) >>8*((v)>255)))
#define LOG2_32BIT(v)                                        \
    (16*((v)>65535L) + LOG2_16BIT((v)*1L >>16*((v)>65535L)))
#define LOG2_64BIT(v)                                        \
    (32*((v)/2L>>31 > 0)                                     \
     + LOG2_32BIT((v)*1L >>16*((v)/2L>>31 > 0)               \
                         >>16*((v)/2L>>31 > 0)))

#define KB(x) ((x) * 1024ULL)
#define MB(x) ((x) * 1024ULL * KB(1ULL))
#define GB(x) ((x) * 1024ULL * MB(1ULL))
#define TB(x) ((x) * 1024ULL * GB(1ULL))

#define CAS(_ptr, _old, _new) (__sync_bool_compare_and_swap((_ptr), (_old), (_new)))
#define CLZ(_val)             (__builtin_clzll((_val) | 1ULL))
#define CTZ(_val)             (__builtin_ctzll((_val) | 1ULL))

#define CACHE_LINE     (64ULL)
#define PAGE_SIZE      (4096ULL)
#define LOG2_PAGE_SIZE (LOG2_64BIT(PAGE_SIZE))

static void bk_printf(const char *fmt, ...);

#ifdef BK_DO_ASSERTIONS
static void bk_assert_fail(const char *msg, const char *fname, int line, const char *cond_str) {
    volatile int *trap;

    bk_printf("Assertion failed -- %s\n"
              "at  %s :: line %d\n"
              "    Condition: '%s'\n"
              , msg, fname, line, cond_str);

    asm volatile ("" ::: "memory");

    trap = 0;
    (void)*trap;
}

#define BK_ASSERT(cond, msg)                        \
do { if (unlikely(!(cond))) {                       \
    bk_assert_fail(msg, __FILE__, __LINE__, #cond); \
} } while (0)
#else
#define BK_ASSERT(cond, mst) ;
#endif

/******************************* @@platform *******************************/
#if defined(unix) || defined(__unix__) || defined(__unix) || defined(__linux__) || defined(__APPLE__)
    #define BK_UNIX
    #include <unistd.h>
    #include <errno.h>
    #include <sys/mman.h>

    #if defined(__APPLE__)
        #define BK_APPLE
    #endif

    #if defined(__linux__)
        #define BK_LINUX
        #include <sys/syscall.h>
    #endif
#elif defined(_WIN64)
    #define BK_WIN
#endif

#if defined(BK_LINUX)
static inline u32 bk_get_nr_cpus_linux(void) {
    u32 nr_cpus;

    nr_cpus = sysconf(_SC_NPROCESSORS_ONLN);

    return nr_cpus;
}
#endif

BK_ALWAYS_INLINE
static inline u32 bk_get_nr_cpus(void) {
#if defined(BK_LINUX)
    return bk_get_nr_cpus_linux();
#else
    #error "platform missing implementation"
#endif
}

#if defined(BK_LINUX)
BK_ALWAYS_INLINE
static inline u32 bk_getcpu_linux(void) {
    unsigned cpu;

    syscall(SYS_getcpu, &cpu, NULL, NULL);

    return cpu;
}
#endif

BK_ALWAYS_INLINE
static inline u32 bk_getcpu(void) {
#if defined(BK_LINUX)
    return bk_getcpu_linux();
#else
    #error "platform missing implementation"
#endif
}

#if defined(BK_UNIX)
static inline void * bk_get_pages_unix(u64 n_pages) {
    u64   desired_size;
    void *pages;

    desired_size = n_pages * PAGE_SIZE;

    errno = 0;
    pages = mmap(NULL, desired_size,
                 PROT_READ   | PROT_WRITE,
                 MAP_PRIVATE | MAP_ANONYMOUS,
                 -1, (off_t)0);

    if (unlikely(pages == MAP_FAILED || pages == NULL)) {
        BK_ASSERT(0,
                  "mmap() failed");
        return NULL;
    }

    BK_ASSERT(errno == 0,
              "errno non-zero after mmap()");

    return pages;
}

static inline void bk_release_pages_unix(void *addr, u64 n_pages) {
    int err;

    (void)err;

    err = munmap(addr, n_pages * PAGE_SIZE);
    BK_ASSERT(err == 0,
              "munmap() failed");
}

#elif defined(BK_WIN)
#error "Windows is not supported yet."

static inline void * bk_get_pages_win(u64 n_pages)                 { return NULL; }
static inline void   bk_release_pages_win(void *addr, u64 n_pages) {              }

#else
#error "Unknown platform."
#endif



static inline void * bk_get_pages(u64 n_pages) {
    void *pages;

    BK_ASSERT(n_pages > 0,
              "n_pages is zero");

#if defined(BK_UNIX)
    pages = bk_get_pages_unix(n_pages);
#else
    #error "platform missing implementation"
#endif

    return pages;
}

static inline void bk_release_pages(void *addr, u64 n_pages) {
    BK_ASSERT(n_pages > 0,
              "n_pages is zero");

#if defined(BK_UNIX)
    bk_release_pages_unix(addr, n_pages);
#elif defined(BK_WIN)
    #error "need Windows release_pages"
#endif
}

static inline void * bk_get_aligned_pages(u64 n_pages, u64 alignment) {
    u64   desired_size;
    u64   first_map_size;
    void *mem_start;
    void *aligned_start;
    void *aligned_end;
    void *mem_end;

    alignment    = MAX(alignment, PAGE_SIZE);
    desired_size = n_pages * PAGE_SIZE;

    /* Ask for memory twice the desired size so that we can get aligned memory. */
    first_map_size = MAX(desired_size, alignment) << 1ULL;

    mem_start = bk_get_pages(first_map_size >> LOG2_PAGE_SIZE);

    aligned_start = ALIGN_UP(mem_start, alignment);
    aligned_end   = (void*)((u8*)aligned_start + desired_size);
    mem_end       = (void*)((u8*)mem_start + first_map_size);

    /* Trim off the edges we don't need. */
    if (mem_start != aligned_start) {
        bk_release_pages(mem_start, ((u8*)aligned_start - (u8*)mem_start) >> LOG2_PAGE_SIZE);
    }

    if (mem_end != aligned_end) {
        bk_release_pages(aligned_end, ((u8*)mem_end - (u8*)aligned_end) >> LOG2_PAGE_SIZE);
    }

    return aligned_start;
}


/******************************* @@printf *******************************/

#define BK_PR_RESET      "\e[0m"
#define BK_PR_FG_BLACK   "\e[30m"
#define BK_PR_FG_BLUE    "\e[34m"
#define BK_PR_FG_GREEN   "\e[32m"
#define BK_PR_FG_CYAN    "\e[36m"
#define BK_PR_FG_RED     "\e[31m"
#define BK_PR_FG_YELLOW  "\e[33m"
#define BK_PR_FG_MAGENTA "\e[35m"
#define BK_PR_BG_BLACK   "\e[40m"
#define BK_PR_BG_BLUE    "\e[44m"
#define BK_PR_BG_GREEN   "\e[42m"
#define BK_PR_BG_CYAN    "\e[46m"
#define BK_PR_BG_RED     "\e[41m"
#define BK_PR_BG_YELLOW  "\e[43m"
#define BK_PR_BG_MAGENTA "\e[45m"

#define BK_PUTC(_c)        \
do {                       \
    char c;                \
    int  x;                \
    c = (_c);              \
    x = write(1, &c, 1);   \
    (void)x;               \
} while (0)

static void bk_puts(const char *s) {
    while (*s) { BK_PUTC(*s); s += 1; }
}

static char * bk_atos(char *p, char c) {
    p[0] = c;
    p[1] = 0;
    return p;
}

static char * bk_dtos(char *p, s32 d) {
    int neg;

    neg = d < 0;

    if (neg) { d = -d; }

    p += 3 * sizeof(s32);
    *--p = 0;

    do {
        *--p = '0' + d % 10;
        d /= 10;
    } while (d);

    if (neg) { *--p = '-'; }

    return p;
}

static char * bk_Dtos(char *p, s64 d) {
    int neg;

    neg = d < 0;

    if (neg) { d = -d; }

    p += 3 * sizeof(s64);
    *--p = 0;

    do {
        *--p = '0' + d % 10;
        d /= 10;
    } while (d);

    if (neg) { *--p = '-'; }

    return p;
}

static char * bk_utos(char *p, u32 d) {
    p += 3 * sizeof(u32);
    *--p = 0;

    do {
        *--p = '0' + d % 10;
        d /= 10;
    } while (d);

    return p;
}

static char * bk_Utos(char *p, u64 d) {
    p += 3 * sizeof(u64);
    *--p = 0;

    do {
        *--p = '0' + d % 10;
        d /= 10;
    } while (d);

    return p;
}

static char * bk_xtos(char *p, u32 x) {
    const char *digits = "0123456789ABCDEF";

    if (x == 0) { *p = '0'; *(p + 1) = 0; return p; }

    p += 3 * sizeof(u32);
    *--p = 0;

    while (x) {
        *--p = digits[x & 0xf];
        x >>= 4;
    }

    return p;
}

static char * bk_Xtos(char *p, u64 x) {
    const char *digits = "0123456789ABCDEF";

    if (x == 0) { *p = '0'; *(p + 1) = 0; return p; }

    p += 3 * sizeof(u64);
    *--p = 0;

    while (x) {
        *--p = digits[x & 0xf];
        x >>= 4;
    }

    return p;
}

static const char * bk_eat_pad(const char *s, int *pad) {
    int neg;

    if (!*s) { return s; }

    *pad = 0;

    neg = *s == '-';

    if (neg || *s == '0') { s += 1; }

    while (*s >= '0' && *s <= '9') {
        *pad = 10 * *pad + (*s - '0');
        s += 1;
    }

    if (neg) { *pad = -*pad; }

    return s;
}

void bk_vprintf(const char *fmt, va_list args) {
    int   last_was_perc;
    char  c;
    int   pad;
    int   padz;
    char  buff[64];
    const char *p;
    int   p_len;

    last_was_perc = 0;

    while ((c = *fmt)) {
        if (c == '%' && !last_was_perc) {
            last_was_perc = 1;
            goto next;
        }

        if (last_was_perc) {
            pad = padz = 0;

            if (c == '-' || c == '0' || (c >= '1' && c <= '9')) {
                padz = c == '0';
                fmt = bk_eat_pad(fmt, &pad);
                c = *fmt;
            }

            switch (c) {
                case '%': p = "%";                               break;
                case '_': p = BK_PR_RESET;                       break;
                case 'k': p = BK_PR_FG_BLACK;                    break;
                case 'b': p = BK_PR_FG_BLUE;                     break;
                case 'g': p = BK_PR_FG_GREEN;                    break;
                case 'c': p = BK_PR_FG_CYAN;                     break;
                case 'r': p = BK_PR_FG_RED;                      break;
                case 'y': p = BK_PR_FG_YELLOW;                   break;
                case 'm': p = BK_PR_FG_MAGENTA;                  break;
                case 'K': p = BK_PR_BG_BLACK;                    break;
                case 'B': p = BK_PR_BG_BLUE;                     break;
                case 'G': p = BK_PR_BG_GREEN;                    break;
                case 'C': p = BK_PR_BG_CYAN;                     break;
                case 'R': p = BK_PR_BG_RED;                      break;
                case 'Y': p = BK_PR_BG_YELLOW;                   break;
                case 'M': p = BK_PR_BG_MAGENTA;                  break;
                case 'a': p = bk_atos(buff, va_arg(args, s32));  break;
                case 'd': p = bk_dtos(buff, va_arg(args, s32));  break;
                case 'D': p = bk_Dtos(buff, va_arg(args, s64));  break;
                case 'u': p = bk_utos(buff, va_arg(args, u32));  break;
                case 'U': p = bk_Utos(buff, va_arg(args, u64));  break;
                case 'x': p = bk_xtos(buff, va_arg(args, u32));  break;
                case 'X': p = bk_Xtos(buff, va_arg(args, u64));  break;
                case 's': p = va_arg(args, char*);               break;

                default: goto noprint;
            }

            for (p_len = 0; p[p_len]; p_len += 1);

            for (; pad - p_len > 0; pad -= 1) { BK_PUTC(padz ? '0' : ' '); }

            bk_puts(p);

            for (; pad + p_len < 0; pad += 1) { BK_PUTC(padz ? '0' : ' '); }

noprint:;
            last_was_perc = 0;
        } else {
            BK_PUTC(*fmt);
        }

next:;
        fmt += 1;
    }
}

void bk_printf(const char *fmt, ...) {
    va_list args;

    va_start(args, fmt);
    bk_vprintf(fmt, args);
    va_end(args);
}

/******************************* @@locks *******************************/

typedef struct {
    s32 val;
} bk_Spinlock;

#define BK_SPIN_UNLOCKED (0)
#define BK_SPIN_LOCKED   (1)
#define BK_STATIC_SPIN_LOCK_INIT ((bk_Spinlock){ BK_SPIN_UNLOCKED })

BK_ALWAYS_INLINE static inline void bk_spin_init(bk_Spinlock *spin)   { spin->val = BK_SPIN_UNLOCKED;   }
BK_ALWAYS_INLINE static inline void bk_spin_lock(bk_Spinlock *spin)   { while (!CAS(&spin->val, 0, 1)); }
BK_ALWAYS_INLINE static inline void bk_spin_unlock(bk_Spinlock *spin) { (void)CAS(&spin->val, 1, 0);    }


/******************************* @@blocks *******************************/


#define ADDR_PARENT_BLOCK(addr) \
    ((bk_Block*)(void*)(ALIGN_DOWN(((u64)addr), BK_BLOCK_ALIGN)))

#define BLOCK_GET_HEAP_PTR(b) \
    ((struct bk_Heap*)((b)->meta.heap))


enum {
    BK_CHUNK_IS_FREE,
    BK_CHUNK_IS_BIG, /* Lone, large allocation that isn't in a block or part of a list. */
};

typedef union {
    struct {
        u64 offset_prev  : 20;
        u64 offset_next  : 20;
        u64 size         : 21;
        u64 flags        : 3;
    };
    struct {
        u64 big_size     : 61;
        u64 big_flags    : 3;
    };
} bk_Chunk_Header;

typedef union {
    bk_Chunk_Header header;
    u64             __u64;
} bk_Chunk;

#define CHUNK_PREV(addr)                                                  \
    ((bk_Chunk*)(unlikely(((bk_Chunk*)(addr))->header.offset_prev == 0))  \
        ? NULL                                                            \
        :   ((u8*)(addr))                                                 \
          - (((bk_Chunk*)(addr))->header.offset_prev))

#define CHUNK_NEXT(addr)                                                  \
    ((bk_Chunk*)((unlikely(((bk_Chunk*)(addr))->header.offset_next == 0)) \
        ? NULL                                                            \
        :   ((u8*)(addr))                                                 \
          + (((bk_Chunk*)(addr))->header.offset_next)))

#define CHUNK_PREV_UNCHECKED(addr)                                        \
    ((bk_Chunk*)(((u8*)(addr))                                            \
        - (((bk_Chunk*)(addr))->header.offset_prev)))

#define CHUNK_NEXT_UNCHECKED(addr)                                        \
    ((bk_Chunk*)(((u8*)(addr))                                            \
        + (((bk_Chunk*)(addr))->header.offset_next)))

#define CHUNK_HAS_PREV(addr) (((bk_Chunk*)(addr))->header.offset_prev != 0)
#define CHUNK_HAS_NEXT(addr) (((bk_Chunk*)(addr))->header.offset_next != 0)

#define CHUNK_USER_MEM(addr) ((void*)(((u8*)(addr)) + sizeof(bk_Chunk)))

#define CHUNK_FROM_USER_MEM(addr) ((bk_Chunk*)(((u8*)(addr)) - sizeof(bk_Chunk)))

#define CHUNK_DISTANCE(a, b) (((u8*)(a)) - (((u8*)(b))))

#define CHUNK_PARENT_BLOCK(addr) \
    ADDR_PARENT_BLOCK(addr)


typedef struct {
    u64 regions_bitfield;
    u64 slots_bitfields[64];
    u32 n_allocations;
    u32 max_allocations;
} bk_Slots;

#define BK_REGION_FULL      (1ULL)
#define BK_SLOT_TAKEN       (1ULL)
#define BK_ALL_REGIONS_FULL (0xFFFFFFFFFFFFFFFF)
#define BK_ALL_SLOTS_TAKEN  (0xFFFFFFFFFFFFFFFF)

#define GET_REGION_BIT(_slots, _r) \
    (!!((_slots).regions_bitfield & (1ULL << (63ULL - (_r)))))
#define SET_REGION_BIT_FULL(_slots, _r) \
    ((_slots).regions_bitfield |= (BK_REGION_FULL << (63ULL - (_r))))
#define SET_REGION_BIT_NOT_FULL(_slots, _r) \
    ((_slots).regions_bitfield &= ~(BK_REGION_FULL << (63ULL - (_r))))

#define GET_SLOT_BIT(_slots, _r, _s) \
    (!!((_slots).slots_bitfields[(_r)] & (1ULL << (63ULL - (_s)))))
#define SET_SLOT_BIT_TAKEN(_slots, _r, _s) \
    ((_slots).slots_bitfields[(_r)] |= (BK_SLOT_TAKEN << (63ULL - (_s))))
#define SET_SLOT_BIT_FREE(_slots, _r, _s) \
    ((_slots).slots_bitfields[(_r)] &= ~(BK_SLOT_TAKEN << (63ULL - (_s))))


union bk_Block;

typedef struct PACKED {
    struct bk_Heap *heap;
    void           *end;
    union bk_Block *next;
    u32             size_class;
    u32             log2_size_class;
    u32             size_class_idx;
    u8              _pad1[4];
} bk_Block_Metadata;

#define BK_CHUNK_SPACE ((2 * BK_MAX_BLOCK_ALLOC_SIZE) - sizeof(bk_Block_Metadata) - sizeof(bk_Slots))
#define BK_SLOT_SPACE  (   BK_BLOCK_SIZE             \
                         - sizeof(bk_Block_Metadata) \
                         - BK_CHUNK_SPACE            \
                         - sizeof(bk_Slots))

typedef union PACKED bk_Block {
    struct PACKED {
        bk_Block_Metadata meta;
        u8                _chunk_space[BK_CHUNK_SPACE];
        bk_Slots          slots;
        u8                _slot_space[BK_SLOT_SPACE];
    } PACKED;
    u8 _bytes[BK_BLOCK_SIZE];
} PACKED bk_Block;

#define BK_BLOCK_FIRST_CHUNK(_block) \
    ((bk_Chunk*)((_block)->_bytes + offsetof(bk_Block, _chunk_space)))


/******************************* @@heaps *******************************/

/*
 * If a heap has neither BK_HEAP_THREAD or BK_HEAP_USER,
 * it is assumed to be the global heap. This allows us to
 * zero initialize the global heap.
 */
enum {
    BK_HEAP_THREAD,
    BK_HEAP_USER,
};

typedef struct bk_Heap {
    u32          flags;
    u32          hid;
    bk_Spinlock  block_list_locks[BK_NR_SIZE_CLASSES];
    bk_Block    *block_lists[BK_NR_SIZE_CLASSES];
} bk_Heap;


static bk_Heap _bk_global_heap;
#if 0 /* Equivalent to this initialization: */

static bk_Heap _bk_global_heap = {
    .flags            = 0,
    .hid              = 0,
    .block_list_locks = { BK_STATIC_SPIN_LOCK_INIT },
    .block_lists      = { NULL },
};

#endif

GLOBAL_ALIGN(CACHE_LINE)
static bk_Heap *bk_global_heap = &_bk_global_heap;

static inline void bk_init_heap(bk_Heap *heap, u32 kind) {
    u32 i;

    heap->flags |= 1 << kind;

    for (i = 0; i < BK_NR_SIZE_CLASSES; i += 1) {
        bk_spin_init(&heap->block_list_locks[i]);
    }
}


BK_ALWAYS_INLINE
static inline u32 bk_get_size_class_idx(u64 size) {
    u64 shift;
    u32 size_class_idx;

    shift          = 64ULL - 1 - CLZ(size);
    size_class_idx = ((size == (1ULL << shift)) ? shift : shift + 1ULL) - LOG2_64BIT(BK_BASE_SIZE_CLASS);

    BK_ASSERT(size_class_idx < BK_NR_SIZE_CLASSES, "invalid size class");

    return size_class_idx;
}

#define LOG2_SIZE_CLASS_FROM_IDX(_idx) ((_idx) + LOG2_64BIT(BK_BASE_SIZE_CLASS))

BK_ALWAYS_INLINE
static inline u64 bk_size_class_idx_to_size(u32 idx) {
    return (1ULL << (LOG2_SIZE_CLASS_FROM_IDX(idx)));
}

BK_ALWAYS_INLINE
static inline bk_Block * bk_make_block(bk_Heap *heap, u32 size_class_idx, u64 size) {
    bk_Block *block;
    bk_Chunk *first_chunk;

    BK_ASSERT(size >= BK_BLOCK_SIZE,
              "size too small for a block");

    block = (bk_Block*)bk_get_aligned_pages(size >> LOG2_PAGE_SIZE, BK_BLOCK_ALIGN);

    block->meta.heap = heap;
    block->meta.end  = ((u8*)block) + size;

    block->meta.size_class_idx = size_class_idx;

    if (unlikely(size_class_idx == BK_BIG_ALLOC_SIZE_CLASS_IDX)) {
        block->meta.size_class      = BK_BIG_ALLOC_SIZE_CLASS;
        block->meta.log2_size_class = 0;
    } else {
        block->meta.size_class      = bk_size_class_idx_to_size(size_class_idx);
        block->meta.log2_size_class = LOG2_SIZE_CLASS_FROM_IDX(size_class_idx);

        first_chunk = BK_BLOCK_FIRST_CHUNK(block);
        first_chunk->header.offset_prev = 0;
        first_chunk->header.offset_next = 0;
        first_chunk->header.size        = BK_CHUNK_SPACE - sizeof(bk_Chunk);
        first_chunk->header.flags       = 1ULL << BK_CHUNK_IS_FREE;
    }

/*     block->slots.max_allocations = 4096ULL << block->meta.log2_size_class; */
    block->slots.max_allocations = MIN(BK_SLOT_SPACE >> block->meta.log2_size_class, 4096ULL);

    return block;
}

static inline bk_Block * bk_add_block(bk_Heap *heap, u32 size_class_idx) {
    bk_Block *block;

    /* heap->block_list_locks[size_class_idx] must be locked. */

    block = bk_make_block(heap, size_class_idx, BK_BLOCK_SIZE);

    block->meta.next                  = heap->block_lists[size_class_idx];
    heap->block_lists[size_class_idx] = block;

    return block;
}

BK_ALWAYS_INLINE
static inline void bk_release_block(bk_Block *block) {
    bk_release_pages(block, ((u8*)block->meta.end - (u8*)block) >> LOG2_PAGE_SIZE);
}

static inline void * bk_big_alloc(bk_Heap *heap, u64 n_bytes, u64 alignment) {
    u64       request_size;
    bk_Block *block;
    u8       *mem_start;
    void     *aligned;
    bk_Chunk *chunk;


    BK_ASSERT(IS_POWER_OF_TWO(alignment),
              "alignment is not a power of two");
    BK_ASSERT(alignment <= BK_BLOCK_ALIGN / 2,
              "alignment is too large");

    n_bytes = ALIGN_UP(n_bytes, PAGE_SIZE) + PAGE_SIZE;

    /* Ask for memory twice the desired size so that we can get aligned memory. */
    request_size = MAX(n_bytes, alignment) << 1ULL;

    block = bk_make_block(heap, BK_BIG_ALLOC_SIZE_CLASS_IDX, MAX(request_size, BK_BLOCK_SIZE));

    mem_start = block->_chunk_space;

    aligned = ALIGN_UP(mem_start, alignment);

    BK_ASSERT((u8*)aligned + n_bytes <= (u8*)block->meta.end,
              "big alloc doesn't fit in its block");

    chunk = (bk_Chunk*)((u8*)aligned - sizeof(bk_Chunk));
    chunk->header.big_flags = 1ULL << BK_CHUNK_IS_BIG;
    chunk->header.big_size  = (u8*)block->meta.end - (u8*)aligned;

    BK_ASSERT(IS_ALIGNED(aligned, alignment),
              "did not align big alloc");

    return aligned;
}

static inline void bk_big_free(bk_Heap *heap, bk_Block *block, void *addr) {
    (void)heap;
    (void)addr;

    bk_release_block(block);
}

BK_ALWAYS_INLINE
static inline void * bk_alloc_chunk(bk_Heap *heap, bk_Block *block, u64 n_bytes, u64 alignment) {
    bk_Chunk *chunk;
    void     *addr;
    void     *aligned;
    void     *end;
    void     *used_end;
    bk_Chunk *next;
    bk_Chunk *split;

    BK_ASSERT(IS_ALIGNED(n_bytes, MIN_ALIGN),
              "n_bytes is not aligned to MIN_ALIGN");
    n_bytes += MIN_ALIGN - sizeof(bk_Chunk);

    chunk = BK_BLOCK_FIRST_CHUNK(block);

    while (chunk != NULL) {
        if (chunk->header.flags & (1ULL << BK_CHUNK_IS_FREE)) {
            addr     = CHUNK_USER_MEM(chunk);
            aligned  = IS_ALIGNED(addr, alignment) ? addr : ALIGN_UP(addr, alignment);
            end      = (void*)((u8*)addr + chunk->header.size);
            used_end = (u8*)aligned + n_bytes;

            if ((u8*)used_end <= (u8*)end) {
                if ((u64)((u8*)end - (u8*)used_end) >= sizeof(bk_Chunk) + block->meta.size_class) {
                    next  = CHUNK_NEXT(chunk);
                    split = CHUNK_FROM_USER_MEM(ALIGN_UP((u8*)used_end + sizeof(bk_Chunk), MIN_ALIGN));

                    if (next != NULL) {
                        split->header.offset_next = CHUNK_DISTANCE(next, split);
                        next->header.offset_prev  = CHUNK_DISTANCE(next, split);
                    } else {
                        split->header.offset_next = 0;
                    }

                    split->header.size        = ((u8*)end - (u8*)CHUNK_USER_MEM(split));
                    split->header.offset_prev = CHUNK_DISTANCE(split, chunk);
                    chunk->header.offset_next = CHUNK_DISTANCE(split, chunk);
                    chunk->header.size        = ((u8*)(void*)split - (u8*)CHUNK_USER_MEM(chunk));

                    BK_ASSERT(chunk->header.size >= n_bytes,
                              "split made chunk too small");
                }

                chunk->header.flags &= ~(1ULL << BK_CHUNK_IS_FREE);

                BK_ASSERT((u8*)CHUNK_USER_MEM(chunk) + chunk->header.size <= block->_chunk_space + BK_CHUNK_SPACE,
                          "chunk goes beyond chunk space");
                BK_ASSERT((u8*)aligned + n_bytes <= block->_chunk_space + BK_CHUNK_SPACE,
                          "chunk allocation goes beyond chunk space");

                return aligned;
            }
        }
        chunk = CHUNK_NEXT(chunk);
    }

    return NULL;
}

BK_ALWAYS_INLINE
static inline void bk_free_chunk(bk_Heap *heap, bk_Block *block, bk_Chunk *chunk) {
    BK_ASSERT(!(chunk->header.flags & (1ULL << BK_CHUNK_IS_FREE)),
              "double free");
    chunk->header.flags |= (1ULL << BK_CHUNK_IS_FREE);
}

BK_ALWAYS_INLINE
static inline void * bk_alloc_slot(bk_Heap *heap, bk_Block *block) {
    u64   r;
    u64   s;
    void *addr;

    if (block->slots.n_allocations == block->slots.max_allocations) {
        return NULL;
    }

    BK_ASSERT(block->slots.n_allocations < block->slots.max_allocations,
              "slots.n_allocations mismatch");

    block->slots.n_allocations += 1;

    BK_ASSERT(block->slots.regions_bitfield != BK_ALL_REGIONS_FULL,
              "slots remain, but all regions marked full");

    r = CLZ(~block->slots.regions_bitfield);
    s = CLZ(~block->slots.slots_bitfields[r]);

    BK_ASSERT(GET_SLOT_BIT(block->slots, r, s) != BK_SLOT_TAKEN,
              "slot already taken");

    SET_SLOT_BIT_TAKEN(block->slots, r, s);

    if (block->slots.slots_bitfields[r] == BK_ALL_SLOTS_TAKEN) {
        SET_REGION_BIT_FULL(block->slots, r);
    }

    addr = block->_slot_space + (((r << 6ULL) + s) << block->meta.log2_size_class);

    BK_ASSERT((u8*)addr + block->meta.size_class <= (u8*)block->meta.end,
              "slot goes beyond block");

    return addr;
}

BK_ALWAYS_INLINE
static inline void bk_free_slot(bk_Heap *heap, bk_Block *block, void *addr) {
    u32 idx;
    u32 region;
    u32 slot;

    idx    = ((u8*)addr - block->_slot_space) >> block->meta.log2_size_class;
    region = idx >> 6ULL;
    slot   = idx  & 63ULL;

    BK_ASSERT(GET_SLOT_BIT(block->slots, region, slot) == BK_SLOT_TAKEN,
              "slot was not taken");
    BK_ASSERT(block->slots.n_allocations != 0,
              "slot taken, but n_allocations is 0");

    SET_SLOT_BIT_FREE(block->slots, region, slot);
    SET_REGION_BIT_NOT_FULL(block->slots, region);
    block->slots.n_allocations -= 1;
}

BK_ALWAYS_INLINE
static inline void * bk_alloc_from_block(bk_Heap *heap, bk_Block *block, u64 n_bytes, u64 alignment) {
    void *mem;

    if (block->meta.size_class - n_bytes < CACHE_LINE
    &&  alignment <= block->meta.size_class) {

        if ((mem = bk_alloc_slot(heap, block))) { goto out; }
    }

    mem = bk_alloc_chunk(heap, block, n_bytes, alignment);

    BK_ASSERT((u8*)mem + n_bytes <= (u8*)block->meta.end,
              "allocation goes past block bounds");

out:;
    return mem;
}

BK_ALWAYS_INLINE
static inline void * bk_heap_alloc(bk_Heap *heap, u64 n_bytes, u64 alignment) {
    void     *mem;
    u32       size_class_idx;
    bk_Block *block;

    BK_ASSERT(IS_POWER_OF_TWO(alignment), "alignment not a power of two");

    mem = NULL;

    if (unlikely(n_bytes > BK_MAX_BLOCK_ALLOC_SIZE)) {
        return bk_big_alloc(heap, n_bytes, alignment);
    } else if (!IS_ALIGNED(n_bytes, MIN_ALIGN)) {
        n_bytes = ALIGN_UP(n_bytes, MIN_ALIGN);
    } else if (unlikely(n_bytes == 0)) {
        n_bytes = MIN_ALIGN;
    }

    size_class_idx = bk_get_size_class_idx(n_bytes);

    bk_spin_lock(&heap->block_list_locks[size_class_idx]);

    block = heap->block_lists[size_class_idx];

    while (block != NULL) {
        mem = bk_alloc_from_block(heap, block, n_bytes, alignment);
        if (mem != NULL) { goto out_unlock; }
        block = block->meta.next;
    }

    block = bk_add_block(heap, size_class_idx);
    mem   = bk_alloc_from_block(heap, block, n_bytes, alignment);

out_unlock:;
    bk_spin_unlock(&heap->block_list_locks[size_class_idx]);

    BK_ASSERT(mem != NULL,                "failed to get memory");
    BK_ASSERT(IS_ALIGNED(mem, alignment), "failed to align memory");

    return mem;
}

BK_ALWAYS_INLINE
static inline void bk_heap_free(bk_Heap *heap, void *addr) {
    bk_Block *block;

    block = ADDR_PARENT_BLOCK(addr);

    if (unlikely(block->meta.size_class_idx == BK_BIG_ALLOC_SIZE_CLASS_IDX)) {
        bk_big_free(heap, block, addr);
    } else {
        BK_ASSERT(    (addr >= (void*)block->_chunk_space
                    && addr <  (void*)(block->_chunk_space + BK_CHUNK_SPACE))
                  ||  (addr >= (void*)block->_slot_space
                    && addr <  (void*)(block->_slot_space + BK_SLOT_SPACE)),
                "addr is not in a valid location within the block");

        if (addr < (void*)&block->slots) {
            bk_free_chunk(heap, block, CHUNK_FROM_USER_MEM(addr));
        } else {
            bk_free_slot(heap, block, addr);
        }
    }
}

static void *bk_imalloc(u64 n_bytes) {
    return bk_heap_alloc(bk_global_heap, n_bytes, MIN_ALIGN);
}

static void  bk_ifree(void *addr)    {
    bk_Heap *heap;

    if (likely(addr != NULL)) {
        heap = BLOCK_GET_HEAP_PTR(ADDR_PARENT_BLOCK(addr));

        BK_ASSERT(heap != NULL, "attempting to free from block that doesn't have a heap\n");

        bk_heap_free(heap, addr);
    }
}


/******************************* @@threads *******************************/

typedef struct {
    bk_Heap heap;
    u32     cpuid;
    int     is_valid;
} bk_Thread_Data;


static bk_Thread_Data              *_bk_thread_datas;
static THREAD_LOCAL bk_Thread_Data *_bk_local_thr;

static inline void bk_init_threads(void) {
    u32 nr_cpus;

    nr_cpus          = bk_get_nr_cpus();
    _bk_thread_datas = (bk_Thread_Data*)bk_imalloc(nr_cpus * sizeof(bk_Thread_Data));
}

BK_ALWAYS_INLINE
static inline bk_Heap *bk_get_this_thread_heap(void) {
    u32 cpu;

    if (unlikely(_bk_local_thr == NULL)) {
        cpu           = bk_getcpu();
        _bk_local_thr = &_bk_thread_datas[cpu];

        if (!_bk_local_thr->is_valid) {
            bk_init_heap(&_bk_local_thr->heap, BK_HEAP_THREAD);
            _bk_local_thr->cpuid    = cpu;
            _bk_local_thr->is_valid = 1;
        }
    }

    return &(_bk_local_thr->heap);
}

/******************************* @@init *******************************/

static s32         bk_is_initialized;
static bk_Spinlock init_lock = BK_STATIC_SPIN_LOCK_INIT;

__attribute__((constructor))
static inline void bk_init(void) {
#ifdef BK_DO_ASSERTIONS
    bk_Block *test_block;
#endif

    /*
     * Thread-unsafe check for performance.
     * Could give a false positive.
     */
    if (unlikely(!bk_is_initialized)) {
        bk_spin_lock(&init_lock);

        /* Thread-safe check. */
        if (unlikely(bk_is_initialized)) {
            bk_spin_unlock(&init_lock);
            return;
        }

#ifdef BK_DO_ASSERTIONS
        test_block = bk_make_block(NULL, 0, BK_BLOCK_SIZE);

        BK_ASSERT(sizeof(bk_Chunk) == 8,
                  "chunk size incorrect");
        BK_ASSERT(sizeof(bk_Block) == BK_BLOCK_SIZE,
                  "bk_Block is not the right size");
        BK_ASSERT(IS_ALIGNED(test_block, BK_BLOCK_ALIGN),
                  "block is not aligned");
        BK_ASSERT((sizeof(bk_Block_Metadata) + BK_CHUNK_SPACE + sizeof(bk_Slots) + BK_SLOT_SPACE) == BK_BLOCK_SIZE,
                  "block packing issues");
        BK_ASSERT(test_block->_chunk_space - (u8*)test_block == sizeof(bk_Block_Metadata),
                  "_chunk_space offset incorrect");

        BK_ASSERT(IS_ALIGNED(test_block->_chunk_space + sizeof(bk_Chunk), MIN_ALIGN),
                  "block's first chunk is not aligned");

        BK_ASSERT(IS_ALIGNED(test_block->_slot_space, BK_MAX_BLOCK_ALLOC_SIZE),
                  "slot space isn't aligned");

        bk_release_block(test_block);
#else
        (void)test_block;
#endif

        bk_init_threads();

        bk_is_initialized = 1;

        bk_spin_unlock(&init_lock);
    }
}

/******************************* @@interface *******************************/

#ifdef __cplusplus
extern "C" {
#endif /* __cplusplus */

BK_ALWAYS_INLINE
inline void * bk_heap_malloc(struct bk_Heap *heap, size_t n_bytes) {
    return bk_heap_alloc(heap, n_bytes, MIN_ALIGN);
}

BK_ALWAYS_INLINE
inline void * bk_heap_calloc(struct bk_Heap *heap, size_t count, size_t n_bytes) {
    u64       new_n_bytes;
    void     *addr;
    bk_Block *block;

    new_n_bytes = count * n_bytes;
    addr        = bk_heap_alloc(heap, new_n_bytes, MIN_ALIGN);
    block       = ADDR_PARENT_BLOCK(addr);

    if (block->meta.size_class != BK_BIG_ALLOC_SIZE_CLASS) {
        memset(addr, 0, new_n_bytes);
    }

    return addr;
}


BK_ALWAYS_INLINE
inline void * bk_heap_realloc(struct bk_Heap *heap, void *addr, size_t n_bytes) {
    void *new_addr;
    u64   old_size;

    new_addr = NULL;

    if (addr == NULL) {
        new_addr = bk_heap_malloc(heap, n_bytes);
    } else {
        if (likely(n_bytes > 0)) {
            old_size = bk_malloc_size(addr);
            /*
             * This is done for us in heap_alloc, but we'll
             * need the aligned value when we get the copy length.
             */
            if (!IS_ALIGNED(n_bytes, MIN_ALIGN)) {
                n_bytes = ALIGN_UP(n_bytes, MIN_ALIGN);
            }

            /*
             * If it's already big enough, just leave it.
             * We won't worry about shrinking it.
             * Saves us an alloc, free, and memcpy.
             * Plus, we don't have to lock the thread.
             */
            if (old_size >= n_bytes) {
                return addr;
            }

            new_addr = bk_heap_malloc(heap, n_bytes);
            memcpy(new_addr, addr, old_size);
        }

        bk_heap_free(heap, addr);
    }

    return new_addr;
}

BK_ALWAYS_INLINE
inline void * bk_heap_reallocf(struct bk_Heap *heap, void *addr, size_t n_bytes) {
    return bk_heap_realloc(heap, addr, n_bytes);
}

BK_ALWAYS_INLINE
inline void * bk_heap_valloc(struct bk_Heap *heap, size_t n_bytes) {
    return bk_heap_alloc(heap, n_bytes, PAGE_SIZE);
}

BK_ALWAYS_INLINE
inline void * bk_heap_pvalloc(struct bk_Heap *heap, size_t n_bytes) {
    BK_ASSERT(0, "bk_heap_pvalloc");
    return NULL;
}


BK_ALWAYS_INLINE
inline int bk_heap_posix_memalign(struct bk_Heap *heap, void **memptr, size_t alignment, size_t size) {
    if (unlikely(!IS_POWER_OF_TWO(alignment)
    ||  alignment < sizeof(void*))) {
        return EINVAL;
    }

    *memptr = bk_heap_alloc(heap, size, alignment);

    if (unlikely(*memptr == NULL))    { return ENOMEM; }
    return 0;
}

BK_ALWAYS_INLINE
inline void * bk_heap_aligned_alloc(struct bk_Heap *heap, size_t alignment, size_t size) {
    return bk_heap_alloc(heap, size, alignment);
}

BK_ALWAYS_INLINE
inline void * bk_heap_memalign(struct bk_Heap *heap, size_t alignment, size_t size) {
    return bk_heap_alloc(heap, size, alignment);
}


#define GET_HEAP(_size)                                                \
    ((unlikely(!bk_is_initialized) || (_size) > THREAD_MAX_ALLOC_SIZE) \
        ? bk_global_heap                                               \
        : bk_get_this_thread_heap())

BK_ALWAYS_INLINE
inline void * bk_malloc(size_t n_bytes)               { return bk_heap_malloc(GET_HEAP(n_bytes), n_bytes);                }
BK_ALWAYS_INLINE
inline void * bk_calloc(size_t count, size_t n_bytes) { return bk_heap_calloc(GET_HEAP(count * n_bytes), count, n_bytes); }
BK_ALWAYS_INLINE
inline void * bk_realloc(void *addr, size_t n_bytes)  { return bk_heap_realloc(GET_HEAP(n_bytes), addr, n_bytes);         }
BK_ALWAYS_INLINE
inline void * bk_reallocf(void *addr, size_t n_bytes) { return bk_realloc(addr, n_bytes);                                 }
BK_ALWAYS_INLINE
inline void * bk_valloc(size_t n_bytes)               { return bk_heap_valloc(GET_HEAP(n_bytes), n_bytes);                }

BK_ALWAYS_INLINE
inline void bk_free(void *addr) {
    bk_Heap *heap;

    if (likely(addr != NULL)) {
        heap = BLOCK_GET_HEAP_PTR(ADDR_PARENT_BLOCK(addr));

        BK_ASSERT(heap != NULL, "attempting to free from block that doesn't have a heap\n");

        bk_heap_free(heap, addr);
    }
}

BK_ALWAYS_INLINE
inline int bk_posix_memalign(void **memptr, size_t alignment, size_t n_bytes) {
    return bk_heap_posix_memalign(GET_HEAP(n_bytes), memptr, alignment, n_bytes);
}

BK_ALWAYS_INLINE
inline void * bk_aligned_alloc(size_t alignment, size_t size) {
    return bk_heap_aligned_alloc(GET_HEAP(size), alignment, size);
}

BK_ALWAYS_INLINE
inline size_t bk_malloc_size(void *addr) {
    bk_Block *block;
    bk_Chunk *chunk;

    if (unlikely(addr == NULL)) { return 0; }

    block = ADDR_PARENT_BLOCK(addr);

    if (unlikely(block->meta.size_class == BK_BIG_ALLOC_SIZE_CLASS)) {
        chunk = CHUNK_FROM_USER_MEM(addr);
        return chunk->header.big_size;
    } else {
        if ((u8*)addr >= block->_slot_space) {
            return block->meta.size_class;
        } else {
            chunk = CHUNK_FROM_USER_MEM(addr);
            return chunk->header.size;
        }
    }

    return 0;
}


void * malloc(size_t n_bytes) BK_THROW                                       { return bk_malloc(n_bytes);                         }
void * calloc(size_t count, size_t n_bytes) BK_THROW                         { return bk_calloc(count, n_bytes);                  }
void * realloc(void *addr, size_t n_bytes) BK_THROW                          { return bk_realloc(addr, n_bytes);                  }
void * reallocf(void *addr, size_t n_bytes) BK_THROW                         { return bk_reallocf(addr, n_bytes);                 }
void * valloc(size_t n_bytes) BK_THROW                                       { return bk_valloc(n_bytes);                         }
void * pvalloc(size_t n_bytes) BK_THROW                                      { return NULL;                                       }
void   free(void *addr) BK_THROW                                             { bk_free(addr);                                     }
int    posix_memalign(void **memptr, size_t alignment, size_t size) BK_THROW { return bk_posix_memalign(memptr, alignment, size); }
void * aligned_alloc(size_t alignment, size_t size) BK_THROW                 { return bk_aligned_alloc(alignment, size);          }
void * memalign(size_t alignment, size_t size) BK_THROW                      { return NULL;                                       }
size_t malloc_size(void *addr) BK_THROW                                      { return bk_malloc_size(addr);                       }
size_t malloc_usable_size(void *addr) BK_THROW                               { return 0;                                          }

#ifdef __cplusplus
}
#endif /* __cplusplus */


#endif /* BKMALLOC_IMPL */

#endif /* __BKMALLOC_H__ */
