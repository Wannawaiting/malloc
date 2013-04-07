#include <stdio.h>
#include <string.h>
#include <stdlib.h>

#include "mm.h"
#include "memlib.h"

/* If you want debugging output, use the following macro.  When you hand
 * in, remove the #define DEBUG line. */
#define DEBUG
#ifdef DEBUG
# define dbg_printf(...) printf(__VA_ARGS__)
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

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)

/*
 * If NEXT_FIT defined use next fit search, else use first fit search 
 */
#define NEXT_FITx

/* $begin mallocmacros */
/* Basic constants and macros */
#define WSIZE       4       /* Word and header/footer size (bytes) */ //line:vm:mm:beginconst
#define DSIZE       8       /* Doubleword size (bytes) */
#define CHUNKSIZE  (1<<12)  /* Extend heap by this amount (bytes) */  //line:vm:mm:endconst 

#define MIN_BLK_SIZE	24	/* Min free block size (bytes) */
#define MIN_ALLOC_SIZE	20  /* Min allocated block size (bytes) */

#define MAX(x, y) ((x) > (y)? (x) : (y))  

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc)  ((size) | (alloc)) //line:vm:mm:pack

/* Read and write a word at address p */
#define GET(p)       (*(unsigned int *)(p))            //line:vm:mm:get
#define PUT(p, val)  (*(unsigned int *)(p) = (val))    //line:vm:mm:put

/* Read and write a pointer at address p */
#define GET_PTR(p)	 	((char *) *(unsigned int **)(p))
#define PUT_PTR(p, val)	(*(unsigned int **)(p) = (void *)(val))

/* Read the size and allocated fields from address p */
#define GET_SIZE(p)  (GET(p) & ~0x7)                   //line:vm:mm:getsize
#define GET_ALLOC(p) (GET(p) & 0x1)                    //line:vm:mm:getalloc

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp)       ((char *)(bp) - WSIZE)                      //line:vm:mm:hdrp
#define FTRP(bp)       ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE) //line:vm:mm:ftrp

/* Given block ptr bp, compute address of next and prev blocks */
#define NEXT_BLKP(bp)  ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE))) //line:vm:mm:nextblkp
#define PREV_BLKP(bp)  ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE))) //line:vm:mm:prevblkp

/* Given block ptr bp, compute address of next and prev free blocks */
#define NEXT_FREE_BLK(bp)	((char **)bp)
#define PREV_FREE_BLK(bp)	((char **)(bp + DSIZE))

/* Given block ptr bp, find its next and prev block is free or not */
#define NEXT_BLK_FREE	(!GET_ALLOC(HDRP(NEXT_BLKP(bp))))
#define PREV_BLK_FREE	!!((*(unsigned int*)HDRP(bp)) & 0x2)

#define MAKE_UNALLOC(bp) \
(*(unsigned int*)HDRP(bp) = (*(unsigned int*)HDRP(bp) | 0x2))

/* $end mallocmacros */

/* Global variables */
static char *heap_listp = 0;  /* Pointer to first block */  
#ifdef NEXT_FIT
static char *rover;           /* Next fit rover */
#endif

/* Function prototypes for internal helper routines */
static void *extend_heap(size_t words);
static void place(void *bp, size_t asize);
static void *find_fit(size_t asize);
static void *coalesce(void *bp);
static void printblock(void *bp); 
static void checkblock(void *bp);
void mm_checkheap(int verbose);

void printheap(void) 
{
	char *bp;
	for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) 
	{
		printblock(bp);
	}
}

/*
 * Initialize: return -1 on error, 0 on success.
 */
 int mm_init(void) 
{
	/* Create the initial empty heap */
    if ((heap_listp = mem_sbrk(WSIZE + 2 * MIN_BLK_SIZE)) == (void *)-1) //line:vm:mm:begininit
		return 1;
		
	/* Build the initial heap with padding, prologue and epilogue */
	/* Padding part */
	PUT(heap_listp, PACK(0, 0));		
	heap_listp += WSIZE;	// move heap_listp to prologue's header position
	
	/* Prologue part */
	//prologue header
	PUT(heap_listp, PACK(MIN_BLK_SIZE, 1));
	//prologue next ptr
	PUT_PTR(heap_listp + WSIZE, heap_listp + MIN_BLK_SIZE + WSIZE);		 //prologue prev ptr
	PUT_PTR(heap_listp + (WSIZE + DSIZE), NULL);	
	//prologue footer	
	PUT(heap_listp + (WSIZE + 2 * DSIZE), PACK(MIN_BLK_SIZE, 1));
	heap_listp += WSIZE;	// move heap_listp to prologue
	
	/* Epilogue part */
	char *epilogue = NEXT_BLKP(heap_listp);
	// epilogue header
	PUT(epilogue - WSIZE, PACK(0, 1));
	// epilogue footer
	PUT(epilogue + 2 * DSIZE, PACK(0, 1));	
	// epilogue next ptr
	PUT_PTR(epilogue, NULL);
	// epilogue prev ptr
	PUT_PTR(epilogue + DSIZE, heap_listp);
	
	/* Make epilogue header prev_free bit to 0 */
	//int mask = 0xFFFFFFFD;
	//int val = GET(HDRP(epilogue));
	//PUT(HDRP(epilogue), val & mask);
	char *epi_header = HDRP(NEXT_BLKP(heap_listp));
	*(unsigned int *) epi_header = (*(unsigned int *) epi_header) & 0xFFFFFFFD;
	
	
#ifdef NEXT_FIT
    rover = heap_listp;
#endif	
	
	/* Extend the empty heap with a free block of CHUNKSIZE bytes */
    if (extend_heap(CHUNKSIZE/WSIZE) == NULL) 
		return -1;
	
	/* test */
	place(heap_listp, WSIZE);
	char *tt = (char *)find_fit(WSIZE);
	tt = (char *)coalesce(heap_listp);
	
	return 0;
}

/*
 * malloc
 */
void *malloc (size_t size) 
{
	size_t asize;      /* Adjusted block size */
    size_t extendsize; /* Amount to extend heap if no fit */
    char *bp;  
	
	/* $end mmmalloc */
    if (heap_listp == 0){
		mm_init();
    }
	
	/* $begin mmmalloc */
    /* Ignore spurious requests */
    if (size <= 0)
		return NULL;
		
	/* Adjust block size to include overhead and alignment reqs. */
	if (size <= MIN_ALLOC_SIZE)
		asize = MIN_BLK_SIZE;
	else
		asize = ALIGN(size) + 2 * WSIZE;
		
	/* Search the free list for a fit */
	if ((bp = find_fit(asize)) != NULL) {
		place(bp, asize);
		// mm_checkheap(1);
		return bp;
	}
	
	/* No fit found. Get more memory and place the block */
	extendsize = MAX(asize, CHUNKSIZE);
	//line:vm:mm:growheap1
    if ((bp = extend_heap(extendsize/WSIZE)) == NULL)  
		return NULL;                                  //line:vm:mm:growheap2
		
    place(bp, asize);                                 //line:vm:mm:growheap3
    return bp;
}

/*
 * free
 */
void free (void *bp) {
	bp = bp;
}

/*
 * realloc - you may want to look at mm-naive.c
 */
void *realloc(void *ptr, size_t size) {
    size_t oldsize;
    void *newptr;

    /* If size == 0 then this is just free, and we return NULL. */
    if(size == 0) {
    free(ptr);
    return 0;
    }

    /* If oldptr is NULL, then this is just malloc. */
    if(ptr == NULL) {
    return malloc(size);
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
    free(ptr);

    return newptr;
}

/*
 * calloc - you may want to look at mm-naive.c
 * This function is not tested by mdriver, but it is
 * needed to run the traces.
 */
void *calloc (size_t nmemb, size_t size) {

  size_t bytes = nmemb * size;
  void *newptr;

  newptr = malloc(bytes);
  memset(newptr, 0, bytes);

  return newptr;
}


/* 
 * extend_heap - Extend heap with free block and return its block pointer
 */
/* $begin mmextendheap */
static void *extend_heap(size_t words) 
{
	char *bp;
	int prev_blk_free = 0;		// assume prev block is allocated
	
	/* Allocate a size is multiple of MIN_BLK_SIZE to maintain alignment */
	size_t size = (words % 6) ? 
				(words + (6 - words % 6)) * WSIZE: words * WSIZE;
	
	if ((long)(bp = mem_sbrk(size)) == -1)
		return NULL;
		
	/* Get bp's prev free block ptr */
	char *prev_free;
	prev_free = GET_PTR(bp - (WSIZE + DSIZE));
	
	/* Move bp to previous block */
	bp -= WSIZE + 2 * DSIZE;
	
	// ics method
	// PUT(HDRP(bp), PACK(size, 0));
	// PUT(FTRP(bp), PACK(size, 0));
	// PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));
	
	// TODO: check PREV_BLK_FREE
	int flag = !!((*(unsigned int*)HDRP(bp)) & 0x2);
	if (flag)
		prev_blk_free = 1;
		
	/* Initialize free block header/footer and the epilogue header */
	PUT(HDRP(bp), PACK(size, 0));		// free block header
	PUT(FTRP(bp), PACK(size, 0));		// free block footer
	
	/* Get heap_listp's next free block ptr */
	char *next_free_ptr = GET_PTR(NEXT_FREE_BLK(heap_listp));
	if (next_free_ptr == bp)
		next_free_ptr = NEXT_BLKP(bp);
		
	/* Insert bp at the front of free block list */
	PUT_PTR(PREV_FREE_BLK(bp), heap_listp);
	PUT_PTR(NEXT_FREE_BLK(bp), next_free_ptr);
	PUT_PTR(NEXT_FREE_BLK(heap_listp), bp);
	PUT_PTR(PREV_FREE_BLK(next_free_ptr), bp);
	
	if (prev_blk_free)
		MAKE_UNALLOC(bp);
	
	PUT_PTR(NEXT_FREE_BLK(prev_free), NEXT_BLKP(bp));
	
	/* Update new epilogue */
	PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));	// epilogue header
	PUT_PTR(NEXT_BLKP(bp), NULL);				// epilogue next ptr
	// epilogue prev ptr
	if (prev_free == heap_listp) {
		PUT_PTR((NEXT_BLKP(bp) + DSIZE), bp);
	}
	else {
		PUT_PTR((NEXT_BLKP(bp) + DSIZE), prev_free);
	}
	PUT((NEXT_BLKP(bp) + 2 *DSIZE), PACK(0, 1));
	
	MAKE_UNALLOC(NEXT_BLKP(bp));
	
	return bp;
}
/* $end mmextendheap */

/* 
 * place - Place block of asize bytes at start of free block bp 
 *         and split if remainder would be at least minimum block size
 */
/* $begin mmplace */
/* $begin mmplace-proto */
static void place(void *bp, size_t asize)
     /* $end mmplace-proto */
{
	bp = bp;
	asize = asize;
}
/* $end mmplace */

/* 
 * find_fit - Find a fit for a block with asize bytes 
 */
/* $begin mmfirstfit */
/* $begin mmfirstfit-proto */
static void *find_fit(size_t asize)
/* $end mmfirstfit-proto */
{
/* $end mmfirstfit */
	asize = asize;
	return NULL;
}

/*
 * coalesce - Boundary tag coalescing. Return ptr to coalesced block
 */
/* $begin mmfree */
static void *coalesce(void *bp) 
{
	bp = bp;
	return NULL;
}

static void printblock(void *bp) 
{
    int hsize, halloc, fsize, falloc;

    // mm_checkheap(0);
    hsize = GET_SIZE(HDRP(bp));
    halloc = GET_ALLOC(HDRP(bp));  
    fsize = GET_SIZE(FTRP(bp));
    falloc = GET_ALLOC(FTRP(bp));  

    // if (hsize == 0) {
		// printf("%p: EOL\n", bp);
		// return;
    // }

    printf("%p: header: [%d:%c] footer: [%d:%c]\n", bp, 
			hsize, (halloc ? 'a' : 'f'), 
			fsize, (falloc ? 'a' : 'f'));
	printf("prev free block at: %p\n", GET_PTR(PREV_FREE_BLK(bp)));
	printf("next free block at: %p\n", GET_PTR(NEXT_FREE_BLK(bp)));
}

static void checkblock(void *bp) 
{
    if ((size_t)bp % 8)
	printf("Error: %p is not doubleword aligned\n", bp);
    if (GET(HDRP(bp)) != GET(FTRP(bp)))
	printf("Error: header does not match footer\n");
}

/* 
 * mm_checkheap - Minimal check of the heap for consistency 
 */
void mm_checkheap(int verbose) 
{
	char *bp = heap_listp;

    if (verbose)
		printf("Heap (%p):\n", heap_listp);

    if ((GET_SIZE(HDRP(heap_listp)) != MIN_BLK_SIZE) 
	 || !GET_ALLOC(HDRP(heap_listp)))
		printf("Bad prologue header\n");
    checkblock(heap_listp);

    for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
		if (verbose) 
			printblock(bp);
		checkblock(bp);
    }

    if (verbose) {
		printblock(bp);
		printf("reached epilogue\n");
	}
	
    if ((GET_SIZE(HDRP(bp)) != 0) || !(GET_ALLOC(HDRP(bp))))
		printf("Bad epilogue header\n");
		
	for (bp = heap_listp;
		 GET_SIZE(HDRP(bp)) > 0; 
		 bp = GET_PTR(NEXT_FREE_BLK(bp))){
        printf("Next Free Block pointer : %p\n", GET_PTR(NEXT_FREE_BLK(bp)));
        printf("PREv free block pointer : %p\n",GET_PTR(PREV_FREE_BLK(bp)));
    }
    printf("reached Epilogue\n");
    printf("PREv free block pointer : %p\n",GET_PTR(PREV_FREE_BLK(bp)));
}