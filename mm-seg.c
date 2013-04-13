/*
 * mm.c - 64 bit Dynamic Memory Allocator
 * 
 * Design option: 
 *  Data structures to organize free blocks: Segregated free lists
 *  Algorithms to scan free blocks: Best fit/First fit
 *
 */

#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "mm.h"
#include "memlib.h"

/* For debug use */
#ifdef DEBUG
# define dbg_printf(...)    printf(__VA_ARGS__)
#else
# define dbg_printf(...)
#endif

/* do not change the following! */
#ifdef DRIVER	
/* create aliases for driver tests */	
#define malloc mm_malloc	
#define free mm_free	
#define realloc mm_realloc	
#define calloc mm_calloc 	
#endif /* def DRIVER */

/* $begin mallocmacros */
/* Basic constants and macros */
#define WSIZE       4           /* Word and header/footer size (bytes) */
#define DSIZE       8           /* Doubleword size (bytes) */
#define CHUNKSIZE   (1 << 9)    /* Extend heap by this amount (bytes) */
#define INITSIZE    (1 << 12)   /* Initially extend heap by this amount */
#define MIN_FREE_SIZE  16       /* Min free block size (bytes) */
#define MIN_ALLOC_SIZE  12      /* Min allocate block size (bytes) */

#define MAXLIST     9           /* Max seg list index */

#define IS_ALLOC    0x1         /* Current block is allocate */
#define IS_FREE     0x0         /* Current block is free */
#define PREV_ALLOC  0X2         /* Current block's prev block is allocate */

/* Doubleword (8) alignment */
#define ALIGNMENT   8

/* Find max one of two arguments */
#define MAX(x, y)   ((x) > (y) ? (x) : (y))

/* Round up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size_t)(size) + (ALIGNMENT - 1)) & ~0X7)

/* Pack a size and prev allocated bit, allocated bit into a word */
#define PACK(size, prev_alloc, alloc)   ((size) | (prev_alloc) | (alloc))

/* Read and write a word at address p */
#define GET(p)              (*(unsigned int *)(p))
#define PUT(p, val)         (*(unsigned int *)(p) = (val))

/* Read the size, allocated bit and prev allocated bit from address p */
#define GET_SIZE(p)         (GET(p) & ~0x7)
#define GET_ALLOC(p)        (GET(p) & 0x1)
#define GET_PREV_ALLOC(p)   (GET(p) & 0x2)

/* Set prev allocated bit to PREV_ALLOC or free */
#define ALLOC_PREV(p)       (PUT(p, (GET(p) | PREV_ALLOC)))
#define FREE_PREV(p)        (PUT(p, (GET(p) & (~PREV_ALLOC))))

/* Given a block pointer bp, compute address of its header and footer */
#define HDRP(bp)            ((char *)(bp) - WSIZE)
#define FTRP(bp)            ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* Given a block pointer bp, compute address of next and prev block */
#define NEXT_BLKP(bp)       ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp) 	    ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

/* Given a block pointer bp, return its next and prev pointer to free block */
#define NEXT_PTR(bp)        (bp)
#define PREV_PTR(bp)        ((char *)(bp) + WSIZE)

/* 
 * Given a block pointer bp, return addres of its next and prev free block 
 * in the free list 
 */
#define NEXT_FREE_BLKP(bp)  (base + (*(unsigned int *)(NEXT_PTR(bp))))
#define PREV_FREE_BLKP(bp)  (base + (*(unsigned int *)(PREV_PTR(bp))))
/* %end mallocmacros */

/* Global Variables */
static char *heap_listp = 0;
static char *base = 0;
static char *root = 0;
static char *epilogue = 0;

/* Function prototype for internal helper routines */
static void *extend_heap(size_t words);
static void place(void *bp, size_t asize);
static void *find_fit(size_t asize);
static void *coalesce(void *bp);
static void printblock(void *bp); 
static void checkblock(void *bp);

static inline void addBlock(void *bp, size_t index);
static inline void delBlock(void *bp);
static size_t find_list(size_t asize);


/*
 * Initialize: return -1 on error, 0 on success.
 */
int mm_init(void)
{
    /* Create initial empty heap */
    size_t init_size = (2 * (MAXLIST + 1) + 4) * WSIZE;
    size_t prologue_size = (2 * (MAXLIST + 1) + 2) * WSIZE;
    if ((heap_listp = mem_sbrk(init_size)) == (void *)-1) {
        return -1;
    }

    /* Get heap start address and list start address */
    base = heap_listp;
    root = heap_listp + DSIZE;
    
    /* Padding part (4 bytes) for alignment */
    PUT(heap_listp, PACK(0, IS_FREE, IS_FREE));

    /* Prologue part */
    heap_listp = heap_listp + WSIZE;    // move to prologue
    PUT(heap_listp, PACK(prologue_size, PREV_ALLOC, IS_ALLOC));

    /* 
     * Put each list's start in the following space,
     * and store the offset value for later query use
     */
    size_t offset;
    for (size_t i = 0; i <= MAXLIST; i++) {
        offset = (i + 1) * DSIZE;
        PUT(base + offset, offset);
        PUT(base + (offset + WSIZE), offset);
    }

    PUT(FTRP(heap_listp + WSIZE), PACK(prologue_size, PREV_ALLOC, IS_ALLOC));

    /* Epilogue part */
    PUT(FTRP(heap_listp + WSIZE) + WSIZE, PACK(0, PREV_ALLOC, IS_ALLOC));

    /* Extend the empty heap with a block of INITSIZE bytes */
    if (extend_heap(INITSIZE/WSIZE) == NULL) {
        return -1;
    }

    return 0;
}

/*
 * malloc
 */
void *malloc(size_t size)
{
    size_t asize;       /* Adjusted block size */
    size_t extendsize;  /* Amount to extend heap if no fit */
    char *bp;

    /* Ignore spurious requests */
    if (size <= 0) {
        return NULL;
    }

    /* Adjust block size to include alignment and overhead requirements */
    if (size <= MIN_ALLOC_SIZE) {
        asize = MIN_FREE_SIZE;
    }
    else {
        asize = DSIZE * ((size + WSIZE + (DSIZE - 1)) / DSIZE);
    }

    /* Search free lists to find fit */
    if ((bp = find_fit(asize)) != NULL) {
        place(bp, asize);
        return bp;
    }
    
    /* No fit found, get more memory and place the block */
    extendsize = MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap(extendsize/WSIZE)) == NULL) {
        return NULL;
    }

    place(bp, asize);
    return bp;
}

/*
 * free
 */
void free(void *bp)
{
    /* Ignore spurious request */
    if (bp == 0) {
        return;
    }

    size_t size = GET_SIZE(HDRP(bp));
    size_t is_prev_alloc = GET_PREV_ALLOC(HDRP(bp));

    /* Set alloc bit to 0 to free this block and maintain prev alloc info */
    PUT(HDRP(bp), PACK(size, is_prev_alloc, IS_FREE));
    PUT(FTRP(bp), PACK(size, IS_FREE, IS_FREE));

    coalesce(bp);
}

/*
 * extend_heap
 */
static void *extend_heap(size_t words)
{
    char *bp;
    size_t size;
    size_t is_prev_alloc;

    /* Allocate to maintain alignment requests */
    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;

    if ((long)(bp = mem_sbrk(size)) == -1) {
        return NULL;
    }

    is_prev_alloc = GET_PREV_ALLOC(HDRP(bp));

    /* Initialize free block header/footer and epilogue header */
    PUT(HDRP(bp), PACK(size, is_prev_alloc, IS_FREE));
    PUT(FTRP(bp), PACK(size, IS_FREE, IS_FREE));

    epilogue = HDRP(NEXT_BLKP(bp));
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, PREV_ALLOC, IS_ALLOC));

    return coalesce(bp);
}

static void *find_fit(size_t asize)
{
    void *bp;
    void *bpouter;
    // char *startlist;
    size_t index = find_list(asize);
    char *startlist = root + index * DSIZE;

    /* best fit */
    if (index >= 3) {
        void *min_bp = NULL;
        size_t best_size = 1 << (5 + (index - 1));
        for(bpouter = startlist; bpouter != root + (MAXLIST + 1) * DSIZE; 
            bpouter = (char *)bpouter + DSIZE) {
            for (bp = NEXT_FREE_BLKP(bpouter); bp != bpouter; 
                bp = NEXT_FREE_BLKP(bp)) {
                if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))) {
                    if (min_bp == NULL || GET_SIZE(HDRP(bp)) < best_size) {
                        min_bp = bp;
                        best_size = GET_SIZE(HDRP(bp));
                    }
                }
            }
        }

        return min_bp;
    }

    /* first fit */
    else {
        for (bpouter = startlist; bpouter != root + 80; 
            bpouter = (char *)bpouter + DSIZE) {
            for (bp = NEXT_FREE_BLKP(bpouter); bp != bpouter; 
                bp = NEXT_FREE_BLKP(bp)) {
                if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))) {
                    return bp;
                }
            }
        }
    }

    return NULL;
}

static inline void delBlock(void *bp)
{
    PUT(PREV_PTR(NEXT_FREE_BLKP(bp)), GET(PREV_PTR(bp)));
    PUT(NEXT_PTR(PREV_FREE_BLKP(bp)), GET(NEXT_PTR(bp)));
}

static inline void addBlock(void *bp, size_t index)
{
    PUT(NEXT_PTR(bp), GET(NEXT_PTR(root + index * DSIZE)));
    PUT(PREV_PTR(bp), GET(PREV_PTR(NEXT_FREE_BLKP(bp))));

    PUT(NEXT_PTR(root + index * DSIZE), (long)bp - (long)base);
    PUT(PREV_PTR(NEXT_FREE_BLKP(bp)), (long)bp - (long)base);
}

/*
 * place
 */
static void place(void *bp, size_t asize)
{
    size_t csize = GET_SIZE(HDRP(bp));
    size_t index;
    size_t is_prev_alloc = GET_PREV_ALLOC(HDRP(bp));

    if ((csize - asize) >= MIN_FREE_SIZE) {
        delBlock(bp);

        PUT(HDRP(bp), PACK(asize, is_prev_alloc, IS_ALLOC));
        
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(csize - asize, PREV_ALLOC, IS_FREE));
        PUT(FTRP(bp), PACK(csize - asize, IS_FREE, IS_FREE));

        index = find_list(csize - asize);

        addBlock(bp, index);
    }

    else {
        delBlock(bp);

        PUT(HDRP(bp), PACK(csize, is_prev_alloc, IS_ALLOC));

        ALLOC_PREV(HDRP(NEXT_BLKP(bp)));
    }
}

/*
 * realloc - you may want to look at mm-naive.c
 */

void *mm_realloc(void *ptr, size_t size)
{
    size_t oldsize;
    void *newptr;

    /* If size == 0 then this is just free, and we return NULL. */
    if(size == 0) {
        mm_free(ptr);
        return 0;
    }

    /* If oldptr is NULL, then this is just malloc. */
    if(ptr == NULL) {
        return mm_malloc(size);
    }

    newptr = mm_malloc(size);

    /* If realloc() fails the original block is left untouched  */
    if(!newptr) {
        return 0;
    }

    /* Copy the old data. */
    oldsize = GET_SIZE(HDRP(ptr));
    if(size < oldsize) oldsize = size;
    memcpy(newptr, ptr, oldsize);

    /* Free the old block. */
    mm_free(ptr);

    return newptr;
}

/*
 * coalesce
 */
static void *coalesce(void *bp)
{
	size_t prev_alloc = GET_PREV_ALLOC(HDRP(bp));
	size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
	size_t size = GET_SIZE(HDRP(bp));
	size_t index;
	
	if(prev_alloc && next_alloc) {
		index = find_list(size);
		addBlock(bp, index);
		FREE_PREV(HDRP(NEXT_BLKP(bp)));
		return bp;
	}
	else if(prev_alloc && !next_alloc) {
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
		index = find_list(size);
		delBlock(NEXT_BLKP(bp));
		
		PUT(HDRP(bp), PACK(size,prev_alloc,0));
        PUT(FTRP(bp), size);
		
		addBlock(bp, index);
		return bp;
	}
	
	else if(!prev_alloc && next_alloc) {
		size+= GET_SIZE(HDRP(PREV_BLKP(bp)));
        size_t previous = GET_PREV_ALLOC(HDRP(PREV_BLKP(bp)));
		index = find_list(size);
		delBlock(PREV_BLKP(bp));
		
		PUT(FTRP(bp), size);
        PUT(HDRP(PREV_BLKP(bp)),PACK(size,previous,0));
        FREE_PREV(HDRP(NEXT_BLKP(PREV_BLKP(bp))));
		
		addBlock(PREV_BLKP(bp), index);
		return (PREV_BLKP(bp));
	}
	else {
		size+= GET_SIZE(HDRP(PREV_BLKP(bp)))+GET_SIZE(FTRP(NEXT_BLKP(bp)));
        size_t previous = GET_PREV_ALLOC(HDRP(PREV_BLKP(bp)));
		index = find_list(size);
		delBlock(NEXT_BLKP(bp));
		delBlock(PREV_BLKP(bp));
		
		PUT(HDRP(PREV_BLKP(bp)),PACK(size,previous,0));
        PUT(FTRP(NEXT_BLKP(bp)),size);
		
		addBlock(PREV_BLKP(bp), index);
		return (PREV_BLKP(bp));
	}
}

/*
 * calloc - you may want to look at mm-naive.c
 * This function is not tested by mdriver, but it is
 * needed to run the traces.
 */

void *calloc (size_t nmemb, size_t size)
{
    size_t bytes = nmemb * size;
    void *newptr;

    newptr = malloc(bytes);
    memset(newptr, 0, bytes);

    return newptr;
}

static size_t find_list(size_t asize)
{
	if (asize == 16)
		return 0;
	else if (asize <= 31)
		return 1;
	else if (asize <= 63)
		return 2;
	else if (asize <= 127)
		return 3;
	else if (asize <= 255)
		return 4;
	else if (asize <= 511)
		return 5;
	else if (asize <= 1022)
		return 6;
	else if (asize <= 2055)
		return 7;
	else if (asize <= 4095)
		return 8;
	else
		return 9;
}

static void printblock(void *bp)
{
	bp = bp;
}

static void checkblock(void *bp)
{
	bp = bp;
}

void mm_checkheap(int verbose) {
	void *bp = NULL;
	printblock(bp);
	checkblock(bp);
	verbose = verbose;
}

