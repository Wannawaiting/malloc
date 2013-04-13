/*
 * mm.c - 64 bit Dynamic Memory Allocator
 * 
 * Design Option: 
 *  Data structures to organize free blocks: Segregated free lists
 *  Algorithms to scan free blocks: Best fit/First fit
 *
 * Design Details:
 *  (1) Block structure: 
 *  (2) Segregated free list structure:
 *  (3) Find fit strategy:
 *
 */
 
 /******************************************************
  * | padding            |            0|0|0| <--- base
  * | prologue header    |prologue_size|1|1|
  * | seg list #0 start  |          offset0| <--- root
  * | seg list #1 start  |          offset1|
  * | seg list #2 start  |          offset2|
  * | seg list #3 start  |          offset3|
  * | seg list #4 start  |          offset4|
  * | seg list #5 start  |          offset5|
  * | seg list #6 start  |          offset6|
  * | seg list #7 start  |          offset7|
  * | seg list #8 start  |          offset8|
  * | seg list #9 start  |          offset9|
  * | prologue footer    |prologue_size|1|1|
  * | epilogue           |            0|1|1|
  *******************************************************/

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
/** Basic constants and macros **/
#define WSIZE       4           /* Word and header/footer size (bytes) */
#define DSIZE       8           /* Doubleword size (bytes) */
#define CHUNKSIZE   (1 << 9)    /* Extend heap by this amount (bytes) */
#define INITSIZE    (1 << 12)   /* Initially extend heap by this amount */
#define MIN_FREE_SIZE  16       /* Min free block size (bytes) */
#define MIN_ALLOC_SIZE  12      /* Min allocate block size (bytes) */

#define MAXLIST     9           /* Max seg list index */
#define BIGLIST     4           /* Seg list index of big size */

#define IS_FREE     0x0         /* Current block is free */
#define IS_ALLOC    0x1         /* Current block is allocate */
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
 * Given a block pointer bp, return address of its next and prev free block 
 * in the free list 
 */
#define NEXT_FREE_BLKP(bp)  (base + (*(unsigned int *)(NEXT_PTR(bp))))
#define PREV_FREE_BLKP(bp)  (base + (*(unsigned int *)(PREV_PTR(bp))))
/* %end mallocmacros */

/** Global Variables **/
static char *heap_listp = 0;
static char *base = 0;
static char *root = 0;
static char *epilogue = 0;

/** Function prototype for internal helper routines **/
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
    heap_listp = heap_listp + WSIZE;    // move to prologue header
    PUT(heap_listp, PACK(prologue_size, PREV_ALLOC, IS_ALLOC));
    heap_listp = heap_listp + WSIZE; 

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

    PUT(FTRP(heap_listp), PACK(prologue_size, PREV_ALLOC, IS_ALLOC));

    /* Epilogue part */
    PUT(FTRP(heap_listp) + WSIZE, PACK(0, PREV_ALLOC, IS_ALLOC));

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
        asize = ALIGN(size + WSIZE);
    }

    /* Search free lists to find fit */
    if ((bp = find_fit(asize)) != NULL) {
        place(bp, asize);
        return bp;
    }
    
    /* No fit found, get more memory and place the block */
    // printf("epilogue prev free at %p\n", PREV_FREE_BLKP(epilogue));
    
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
    void *temp_list;
    size_t index = find_list(asize);
    char *cur_list = root + index * DSIZE;

    /* best fit */
    if (index >= BIGLIST) {
        void *min_bp = NULL;
        size_t best_size = MIN_FREE_SIZE * (1 << index);
        for(temp_list = cur_list; temp_list != root + (MAXLIST + 1) * DSIZE; 
            temp_list = (char *)temp_list + DSIZE) {
            for (bp = NEXT_FREE_BLKP(temp_list); bp != temp_list; 
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
        for (temp_list = cur_list; temp_list != root + 80; 
            temp_list = (char *)temp_list + DSIZE) {
            for (bp = NEXT_FREE_BLKP(temp_list); bp != temp_list; 
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
    /* Find bp's prev and next block is allocate or not */
	size_t prev_alloc = GET_PREV_ALLOC(HDRP(bp));
	size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    
    /* Initialize */
	size_t size = GET_SIZE(HDRP(bp));   // bp's size
	size_t index;                       // index used to find correct seg list
	
    /* 
     * Case 1 - both prev and next block is allocate 
     *   add bp into correct seg list
     *   update bp's next block's prev_alloc bit to IS_FREE
     */
	if(prev_alloc && next_alloc) {
		index = find_list(size);
		addBlock(bp, index);
		FREE_PREV(HDRP(NEXT_BLKP(bp)));
		return bp;
	}
    
    /* 
     * Case 2 - only prev block is allocate 
     *   find new size for new free block and correct seg list index
     *   delete next block from its seg list
     *   merge bp and next block together 
     *   update bp's prev_alloc bit to PREV_ALLOC
     *   add new free block into seglist
     */
	else if(prev_alloc && !next_alloc) {
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
		index = find_list(size);
        
		delBlock(NEXT_BLKP(bp));
		
		PUT(HDRP(bp), PACK(size,prev_alloc,0));
        PUT(FTRP(bp), size);
		
		addBlock(bp, index);
		return bp;
	}
	
    /* 
     * Case 3 - only next block is allocate 
     *   find new size for new free block and correct seg list index
     *   find bp's prev block's prev_alloc bit
     *   delete prev block from its seg list
     *   merge bp and prev block together 
     *   update bp's prev_alloc bit to bp's prev block's prev_alloc bit
     *   add new free block into seglist
     */
	else if(!prev_alloc && next_alloc) {
		size+= GET_SIZE(HDRP(PREV_BLKP(bp)));
		index = find_list(size);
        
        size_t prev_prev_alloc = GET_PREV_ALLOC(HDRP(PREV_BLKP(bp)));
        
		delBlock(PREV_BLKP(bp));
		
		PUT(FTRP(bp), size);
        PUT(HDRP(PREV_BLKP(bp)),PACK(size, prev_prev_alloc, IS_FREE));
        FREE_PREV(HDRP(NEXT_BLKP(PREV_BLKP(bp))));
		
		addBlock(PREV_BLKP(bp), index);
		return (PREV_BLKP(bp));
	}
    
    /* 
     * Case 4 - both prev and next block is free 
     *   find new size for new free block and correct seg list index
     *   find bp's prev block's prev_alloc bit
     *   delete prev and next block from its seg list
     *   merge bp, prev and next block together 
     *   update bp's prev_alloc bit to bp's prev block's prev_alloc bit
     *   add new free block into seglist
     */
	else {
		size += GET_SIZE(HDRP(PREV_BLKP(bp)))+GET_SIZE(FTRP(NEXT_BLKP(bp)));
		index = find_list(size);
        
        size_t prev_prev_alloc = GET_PREV_ALLOC(HDRP(PREV_BLKP(bp)));
        
		delBlock(NEXT_BLKP(bp));
		delBlock(PREV_BLKP(bp));
		
		PUT(HDRP(PREV_BLKP(bp)),PACK(size, prev_prev_alloc, IS_FREE));
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

/*
 * in_heap - Return whether the pointer is in the heap
 */
static int in_heap(const void *p) 
{
    return p <= mem_heap_hi() && p >= mem_heap_lo();
}

/*
 * aligned - Return whether the pointer is aligned.
 */
static long aligned(const void *p) 
{
    return (size_t)ALIGN(p) == (size_t)p;
}

/*
 * printblock - Print block information
 */
static void printblock(void *bp)
{
    /* Block size got from header and footer */
	size_t hsize = GET_SIZE(HDRP(bp));       
    size_t fsize = GET_SIZE(FTRP(bp)); 

    /* Block allocate/free info got from header and footer */
    size_t halloc = GET_ALLOC(HDRP(bp));    
    size_t falloc = GET_ALLOC(FTRP(bp));

    /* Block prev's allocate/free info got from header */
    size_t prev_alloc = GET_PREV_ALLOC(HDRP(bp));  
    
    /* Epilogue Case */
    if (hsize == 0) {
        printf("Epilogue at %p : (%zu, %c)\n", bp, hsize, 
                (halloc ? 'A' : 'F'));
    }
    /* Not epilogue */
    else {
        /* Allocate block info */
        if (halloc) {
            printf("Allocate block at %p: header (%zu, %c, %c)\n", bp, hsize, 
                    (halloc ? 'A' : 'F'), (prev_alloc ? 'A' : 'F'));
        }
        /* Free block info */
        else {
            printf("Free block at %p: header (%zu, %c, %c), footer (%zu, %c)\n", 
                bp, hsize, (prev_alloc ? 'A' : 'F'), (halloc ? 'A' : 'F'), 
                fsize, (falloc ? 'A' : 'F'));
        }
    }
}

static void checkblock(void *bp)
{
	/* Block size got from header and footer */
	size_t hsize = GET_SIZE(HDRP(bp));       
    size_t fsize = GET_SIZE(FTRP(bp)); 

    /* Block allocate/free info got from header and footer */
    size_t halloc = GET_ALLOC(HDRP(bp));    
    size_t falloc = GET_ALLOC(FTRP(bp));
    
    /* Check block is inside heap range or not */
    if (!in_heap(bp)) {
        printf("Error: Block at %p is outside heap range [%p, %p]\n", bp, 
                mem_heap_lo(), mem_heap_hi());
    }

    /* Check block address is aligned or not */
    if (!aligned(bp)) {
        printf("Error: Block at %p with size %zu is not doubleword aligned\n", 
                bp, hsize);
    }
    
    /* Check block size >= MIN_FREE_SIZE */
    if ((hsize < MIN_FREE_SIZE)) {
        printf("Error: Block at %p size %zu is smaller than minimun size %zu\n", bp, hsize, (size_t)MIN_FREE_SIZE);
    }

    /* Check free block's header and footer consistency */
    if ((!halloc) && ((hsize != fsize) || (halloc != falloc))) {
        printf("Error: Block at %p's header doesn't match footer\n", bp);
        printf("Block's header : (%zu, %c), footer : (%zu, %c)\n", 
                hsize, (halloc ? 'A' : 'F'), fsize, (falloc ? 'A' : 'F'));
    }         
}

void mm_checkheap(int verbose) {
	void *bp = NULL;
	printblock(bp);
	checkblock(bp);
	verbose = verbose;
}

