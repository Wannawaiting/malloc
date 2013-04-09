/* @Author : Xiaomin Wei (xiaominw)
 * mm.c
 *
 * explicit free list; boundary tag; next fit
 */
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include <limits.h>

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

/*
 * If NEXT_FIT defined use next fit search, else use first fit search 
 */
#define NEXT_FIT

/* $begin mallocmacros */
/* Basic constants and macros */
#define WSIZE       4       /* Word and header/footer size (bytes) */ 
#define DSIZE       8       /* Doubleword size (bytes) */
#define CHUNKSIZE  (1<<12)  /* Extend heap by this amount (bytes) */ 

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)

#define MIN_BLK_SIZE	24	/* Min free block size (bytes) */
#define MIN_ALLOC_SIZE	20  /* Min allocated block size (bytes) */

/* rounds up to the nearest multiple of ALIGNMENT */
//#define ALIGN(p) (((size_t)(p) + (ALIGNMENT-1)) & ~0x7)

#define MAX(x, y) ((x) > (y)? (x) : (y))  

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc)  ((size) | (alloc)) 

/* Read and write a word at address p */
#define GET(p)       (*(unsigned int *)(p))            //line:vm:mm:get
#define PUT(p, val)  (*(unsigned int *)(p) = (val))    //line:vm:mm:put

/* Read and write a pointer at address p */
#define GET_PTR(p)	 	((char *) *(unsigned int **)(p))
#define PUT_PTR(p, val)	(*(unsigned int **)(p) = (void *)(val))

/* Read the size and allocated fields from address p */
#define GET_SIZE(p)  	(GET(p) & ~0x7)                   //line:vm:mm:getsize
#define GET_ALLOC(p)	(GET(p) & 0x1)                    //line:vm:mm:getalloc                   

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp)       ((char *)(bp) - WSIZE)                      //line:vm:mm:hdrp
#define FTRP(bp)       ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE) //line:vm:mm:ftrp

/* Given block ptr bp, compute address of next and prev blocks */
#define NEXT_BLKP(bp)  ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE))) //line:vm:mm:nextblkp
#define PREV_BLKP(bp)  ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE))) //line:vm:mm:prevblkp

/* Given block ptr bp, compute address of next and prev free blocks */
#define NEXT_FREE_BLK(bp) ((char**)bp)
#define PREV_FREE_BLK(bp) ((char**)(bp + DSIZE))

/* Given block ptr bp, find its next and prev block is free or not */
#define NEXT_FREE(bp)  !GET_ALLOC(HDRP(NEXT_BLKP(bp)))
#define PREV_FREE(bp)  !!((*(unsigned int*)HDRP(bp)) & 0x2)

/* Given block ptr bp, set its prev_free bit to 1 */
#define SET_FREE(bp) (*(unsigned int*)HDRP(bp) = (*(unsigned int*)HDRP(bp) | 0x2))
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

// helper function: print heap
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
int mm_init(void) {

     /* Create the initial empty heap */
	 size_t init_size = WSIZE + 2 * MIN_BLK_SIZE;
    if ((heap_listp = mem_sbrk(init_size)) == (void *)-1) //line:vm:mm:begininit
		return -1;
    
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
	
	
    char* next_header = HDRP(NEXT_BLKP(heap_listp));
    *(unsigned int*) next_header = (*(unsigned int *) next_header) & 0xFFFFFFFD;

#ifdef NEXT_FIT
    rover = NEXT_BLKP(heap_listp);
#endif


    /* Extend the empty heap with a free block of CHUNKSIZE bytes */
    if (extend_heap(CHUNKSIZE/WSIZE) == NULL) 
		return -1;
    return 0;
}

/* 
 * mm_malloc - Allocate a block with at least size bytes of payload 
 */
/* $begin mmmalloc */
void *malloc (size_t size) 
{
   size_t asize;      /* Adjusted block size */
   size_t extendsize; /* Amount to extend heap if no fit */
   char *bp;            

	mm_checkheap(0);
/* $end mmmalloc */
	if (heap_listp == 0) {
		mm_init();
    }
/* $begin mmmalloc */
	/* Ignore spurious requests */
	if (size == 0) {
		return NULL;
	}

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
		return NULL;                     
	//line:vm:mm:growheap2
		
    place(bp, asize);                                 //line:vm:mm:growheap3
    return bp;
}

/*
 * mm_free - Free a block 
 */
/* $begin mmfree */
void free (void *bp) 
{
/* $end mmfree */
	mm_checkheap(0);
    int isprfree = 0;
    if(		bp == 0 
		 || bp <= (mem_heap_lo() + MIN_BLK_SIZE) 
		 || bp >= (mem_heap_hi() - MIN_BLK_SIZE)) 
		return;

    size_t size = GET_SIZE(HDRP(bp));

    if (heap_listp == 0){
		mm_init();
    }
    
    char* next_free = GET_PTR(NEXT_FREE_BLK(heap_listp));

    if(PREV_FREE(bp)){
        isprfree = 1;
    }

    PUT(HDRP(bp), PACK(size,0));
	PUT(FTRP(bp), PACK(size,0));
	
    if (isprfree){
		SET_FREE(bp);
    }
    
    PUT_PTR(PREV_FREE_BLK(bp),heap_listp);
    PUT_PTR(NEXT_FREE_BLK(bp),next_free);
    PUT_PTR(NEXT_FREE_BLK(heap_listp),bp);
    PUT_PTR(PREV_FREE_BLK(next_free),bp);
	
    SET_FREE(NEXT_BLKP(bp));
    mm_checkheap(0);

    coalesce(bp);
    mm_checkheap(0);
    return;
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
    int isprfree = 0;

    /* Allocate a size is multiple of MIN_BLK_SIZE to maintain alignment */
    size_t size = (words % 6) ? 
				(words + (6 - words % 6)) * WSIZE: words * WSIZE;
				
    if ((long)(bp = mem_sbrk(size)) == -1)  
		return NULL;                                       
    
	/* Get bp's prev free block ptr */
    char* prev_free = GET_PTR(bp - (WSIZE + DSIZE));
	
	/* Move bp to previous block */
	bp -= WSIZE + 2 * DSIZE;

    if (PREV_FREE(bp)){
        isprfree = 1;
    }

    /* Initialize free block header/footer and the epilogue header */
	PUT(HDRP(bp), PACK(size, 0));		// free block header
	PUT(FTRP(bp), PACK(size, 0));		// free block footer

	/* Get heap_listp's next free block ptr */
    char* next_free = GET_PTR(NEXT_FREE_BLK(heap_listp));
    if (next_free == bp){
        next_free = NEXT_BLKP(bp);
    }
	
	/* Insert bp at the front of free block list */  
	PUT_PTR(PREV_FREE_BLK(bp), heap_listp);
	PUT_PTR(NEXT_FREE_BLK(bp), next_free);
	PUT_PTR(NEXT_FREE_BLK(heap_listp), bp);
	PUT_PTR(PREV_FREE_BLK(next_free), bp);	

    if (isprfree){
        SET_FREE(bp);
    }
    PUT_PTR(NEXT_FREE_BLK(prev_free),NEXT_BLKP(bp));

	/* Update new epilogue */
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));	// epilogue header
	PUT_PTR(NEXT_BLKP(bp), NULL);			// epilogue next ptr
	
	
    if (prev_free != heap_listp){
      PUT_PTR(NEXT_BLKP(bp)+DSIZE, prev_free); 
    }
    else{
      PUT_PTR(NEXT_BLKP(bp)+DSIZE,bp);
    }
	
    PUT((NEXT_BLKP(bp)) + 2 * DSIZE, PACK(0,1)); 
    SET_FREE(NEXT_BLKP(bp));
    return coalesce(bp);
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
    size_t csize = GET_SIZE(HDRP(bp));  
	size_t free_size = csize - asize;
    char* prev_free = GET_PTR(PREV_FREE_BLK(bp));
    char* next_free =  GET_PTR(NEXT_FREE_BLK(bp));

	/* More space than required, split into two parts:
	 * first as allocated block, second as free block
	 */	
	if (free_size >= MIN_BLK_SIZE) { 
		/* Make first part as allocated block */
        PUT(HDRP(bp), PACK(asize, 1));
		
		/* Move to second part */
		bp = NEXT_BLKP(bp);
	
#ifdef NEXT_FIT 
	rover = bp;
#endif

		PUT(HDRP(bp), PACK(free_size, 0));
		PUT(FTRP(bp), PACK(free_size, 0));
		
		/* Insert second part into free list */
		PUT_PTR(NEXT_FREE_BLK(bp), next_free);
		PUT_PTR(PREV_FREE_BLK(bp), prev_free);
		
		PUT_PTR(NEXT_FREE_BLK(prev_free), bp);
		PUT_PTR(PREV_FREE_BLK(next_free), bp);
		
		SET_FREE(NEXT_BLKP(bp));
		
		// /* Make first as free block */
		// PUT(HDRP(bp), PACK(free_size, 0));
		// PUT(FTRP(bp), PACK(free_size, 0));
		
		// void *next_bp = NEXT_BLKP(bp);
		
		// PUT(HDRP(next_bp), PACK(asize, 1));
		// PUT(FTRP(next_bp), PACK(asize, 1));
		
		// SET_FREE(next_bp);
    }
	/* No spliting */
    else { 
#ifdef NEXT_FIT 
	rover = GET_PTR(NEXT_FREE_BLK(bp));
#endif
		/* Make this block as allocated */
		PUT(HDRP(bp), PACK(csize, 1));
		PUT(FTRP(bp), PACK(csize, 1));
		
		/* Remove this block from free list */
		PUT_PTR(NEXT_FREE_BLK(prev_free), next_free);
        PUT_PTR(PREV_FREE_BLK(next_free), prev_free); 
		
		/* Make next_header's prev_free bit to 0 */
		char* next_header = HDRP(NEXT_BLKP(bp));
        *(unsigned int*) next_header = (*(unsigned int *) next_header) & 0xFFFFFFFD;
    }
}
/* $end mmplace */

/* 
 * find_fit - Find a fit for a block with asize bytes 
 */
static void *find_fit(size_t asize)
{
	/* Decide when to use best-fit */
	if (asize > 16 * CHUNKSIZE) {
#define BEST_FIT

#ifdef BEST_FIT
	/* best fit */
	void *bp;
	void *min_p = NULL;
	size_t best_size = INT_MAX;
	
	for (bp = heap_listp;
		GET_SIZE(HDRP(bp)) > 0;
		bp = GET_PTR(NEXT_FREE_BLK(bp))) {
		if (asize <= GET_SIZE(HDRP(bp)) && bp != heap_listp) {
			if (asize == GET_SIZE(HDRP(bp))) {
				min_p = bp;
				return min_p;
			}
			else {
				if (min_p == NULL || GET_SIZE(HDRP(bp)) < best_size) {
					min_p = bp;
					best_size = GET_SIZE(HDRP(bp));
				}
			}
		}
	}
	return min_p;
	/* end best fit */
#endif
	}
    else {
#define NEXT_FIT
	}


#ifdef NEXT_FIT 
	/* Next fit search */
    char *oldrover = rover;
	
	/* Search from the rover to the end of list */
    for ( ; GET_SIZE(HDRP(rover)) > 0; rover = GET_PTR(NEXT_FREE_BLK(rover))) {
		if (asize <= GET_SIZE(HDRP(rover))) {
			return rover;
		}
	}
	
	/* search from start of list to old rover */
    for (rover = GET_PTR(NEXT_FREE_BLK(heap_listp)); 
		rover < oldrover; 
		rover = GET_PTR(NEXT_FREE_BLK(rover))) {
		if (asize <= GET_SIZE(HDRP(rover))) {
			return rover;
		}
	}
	
	return NULL;  /* no fit found */
#endif

// #ifdef BEST_FIT
	// /* best fit */
	// void *bp;
	// void *min_p = NULL;
	// size_t best_size = INT_MAX;
	
	// for (bp = heap_listp;
		// GET_SIZE(HDRP(bp)) > 0;
		// bp = GET_PTR(NEXT_FREE_BLK(bp))) {
		// if (asize <= GET_SIZE(HDRP(bp)) && bp != heap_listp) {
			// if (asize == GET_SIZE(HDRP(bp))) {
				// min_p = bp;
				// return min_p;
			// }
			// else {
				// if (min_p == NULL || GET_SIZE(HDRP(bp)) < best_size) {
					// min_p = bp;
					// best_size = GET_SIZE(HDRP(bp));
				// }
			// }
		// }
	// }
	// return min_p;
	// /* end best fit */

// #else
	
// /* $begin mmfirstfit */
    // /* First fit search */
    // void *bp;

    // for (bp = heap_listp; 
		// GET_SIZE(HDRP(bp)) > 0; 
		// bp = GET_PTR(NEXT_FREE_BLK(bp))) {
		// if (asize <= GET_SIZE(HDRP(bp)) && bp != heap_listp) {
			// return bp;
        // }
    // }
	
    // return NULL; /* No fit */
// /* $end mmfirstfit */
// #endif
}

/*
 * coalesce - Boundary tag coalescing. Return ptr to coalesced block
 */
static void *coalesce(void *bp) 
{
    size_t size = GET_SIZE(HDRP(bp));
	size_t next_size = GET_SIZE(HDRP(NEXT_BLKP(bp)));

	// printf("Next blk size: %d\n", (int)next_size);
	size_t new_size;
	
	int prev_flag = PREV_FREE(bp);
	int next_flag = NEXT_FREE(bp);

	/* Case 1: prev and next blocks are allocated */
    if (!prev_flag && !next_flag) {
        return bp;
    }

	/* Case 2: only prev block is allocated */
    else if (!prev_flag) {
		/*This means that the next adjecent block which is free 
		 * was orginally in the front of the explicit free list 
		 */
		char* nn_free = GET_PTR(NEXT_FREE_BLK(NEXT_BLKP(bp)));
        char* bb_free = GET_PTR(PREV_FREE_BLK(NEXT_BLKP(bp)));
		
		new_size = size + next_size;
		/* Merge bp with next block */
		PUT(HDRP(bp), PACK(new_size, 0));
        PUT(FTRP(bp), PACK(new_size, 0));
		
        if (NEXT_BLKP(bp) == GET_PTR(NEXT_FREE_BLK(bp))){
			
            // char* nn_free = GET_PTR(NEXT_FREE_BLK(NEXT_BLKP(bp)));
			
			// /* Merge bp with next block */
			// PUT(HDRP(bp), PACK(new_size, 0));
            // PUT(FTRP(bp), PACK(new_size, 0));
			
			/* Re-arrange free list */
            PUT_PTR(PREV_FREE_BLK(nn_free), bp);
            PUT_PTR(NEXT_FREE_BLK(bp),nn_free);

        }
        else{
            // char* nn_free = GET_PTR(NEXT_FREE_BLK(NEXT_BLKP(bp)));
            // char* bb_free = GET_PTR(PREV_FREE_BLK(NEXT_BLKP(bp)));
            //printf("next block at address %p next free block size is %d\n", NEXT_BLKP(bp),nfb_size );

			// /* Merge bp with next block */
			// PUT(HDRP(bp), PACK(new_size, 0));
            // PUT(FTRP(bp), PACK(new_size, 0));
			
			/* Re-arrange free list */
            PUT_PTR(NEXT_FREE_BLK(bb_free),nn_free);
            PUT_PTR(PREV_FREE_BLK(nn_free), bb_free);
        }
      //  SET_FREE(NEXT_BLKP(bp)); //should be already but just to make sure
    }
    /*This means that the previous adjecent block which is free 
    * was orginally in the front of the explicit free list 
    */

	/* Case 3: only next block is allocated */
    else if (!next_flag){
     //   printf("PREV IS FREE\n");
		size_t prev_size = GET_SIZE(HDRP(PREV_BLKP(bp)));
		
        if (PREV_BLKP(bp) == GET_PTR(NEXT_FREE_BLK(bp))){
          //  printf("prev thing was first thing in the list\n");
          char* nn_free = GET_PTR(NEXT_FREE_BLK(PREV_BLKP(bp)));

			
			//size += GET_SIZE(HDRP(PREV_BLKP(bp)));
			new_size = size + prev_size;
			// PUT(FTRP(bp),PACK(size,0));
			PUT(FTRP(bp),PACK(new_size,0));
			bp = PREV_BLKP(bp);

			// PUT(HDRP(bp),PACK(size,0));
			PUT(HDRP(bp),PACK(new_size,0));

			PUT_PTR(NEXT_FREE_BLK(bp), nn_free);
			PUT_PTR(PREV_FREE_BLK(bp), heap_listp);

			PUT_PTR(NEXT_FREE_BLK(heap_listp),bp);

			PUT_PTR(PREV_FREE_BLK(nn_free), bp);

        }
        else{
            char* next_free = GET_PTR(NEXT_FREE_BLK(bp));
            char* nn_free = GET_PTR(NEXT_FREE_BLK(PREV_BLKP(bp)));
            char* bb_free = GET_PTR(PREV_FREE_BLK(PREV_BLKP(bp)));
            size += GET_SIZE(HDRP(PREV_BLKP(bp)));
            
            PUT(FTRP(bp),PACK(size,0));

            bp = PREV_BLKP(bp);

            PUT(HDRP(bp),PACK(size,0));
            
            PUT_PTR(NEXT_FREE_BLK(bp), next_free);
            PUT_PTR(PREV_FREE_BLK(bp), heap_listp);

            PUT_PTR(NEXT_FREE_BLK(heap_listp),bp);

            PUT_PTR(PREV_FREE_BLK(next_free), bp);

            PUT_PTR(NEXT_FREE_BLK(bb_free),nn_free);
            PUT_PTR(PREV_FREE_BLK(nn_free),bb_free);
        }
       // SET_FREE(NEXT_BLKP(bp));
    }

	/* Case 4: prev and next blocks are free */
    else{
      //  printf("PREV and NEXT IS FREE\n");
        if(PREV_BLKP(bp) == GET_PTR(NEXT_FREE_BLK(bp))){
         //  printf("prev block was first\n");
          char* nn_free_f = GET_PTR(NEXT_FREE_BLK(NEXT_BLKP(bp)));
          char* bb_free_f = GET_PTR(PREV_FREE_BLK(NEXT_BLKP(bp)));

          PUT_PTR(NEXT_FREE_BLK(bb_free_f),nn_free_f);
          PUT_PTR(PREV_FREE_BLK(nn_free_f),bb_free_f);


          //char* next_free = GET_PTR(NEXT_FREE_BLK(bp));
          char* nn_free = GET_PTR(NEXT_FREE_BLK(PREV_BLKP(bp)));
          //char* bb_free = GET_PTR(PREV_FREE_BLK(PREV_BLKP(bp)));
          size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(HDRP(NEXT_BLKP(bp)));
          PUT(FTRP(NEXT_BLKP(bp)),PACK(size,0));

          bp = PREV_BLKP(bp);

          PUT(HDRP(bp),PACK(size,0));

          PUT_PTR(NEXT_FREE_BLK(bp), nn_free);
          PUT_PTR(PREV_FREE_BLK(bp), heap_listp);

          PUT_PTR(NEXT_FREE_BLK(heap_listp),bp);

          PUT_PTR(PREV_FREE_BLK(nn_free), bp);

        }
        else if (NEXT_BLKP(bp) == GET_PTR (NEXT_FREE_BLK(bp))){
//printf("Next block was first\n");
            char* nn_free = GET_PTR(NEXT_FREE_BLK(PREV_BLKP(bp)));
            char* bb_free = GET_PTR(PREV_FREE_BLK(PREV_BLKP(bp)));
            PUT_PTR(NEXT_FREE_BLK(bb_free),nn_free);
            PUT_PTR(PREV_FREE_BLK(nn_free), bb_free);

            char* nn_free_f = GET_PTR(NEXT_FREE_BLK(NEXT_BLKP(bp)));

            size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(HDRP(NEXT_BLKP(bp)));

            PUT(FTRP(NEXT_BLKP(bp)),PACK(size,0));

            bp = PREV_BLKP(bp);

            PUT(HDRP(bp),PACK(size,0));

            PUT_PTR(NEXT_FREE_BLK(bp), nn_free_f);
            PUT_PTR(PREV_FREE_BLK(bp), heap_listp);

            PUT_PTR(NEXT_FREE_BLK(heap_listp),bp);

            PUT_PTR(PREV_FREE_BLK(nn_free_f), bp);


        }
        else{
         //   printf("neither block was first\n");
            char* next_free = GET_PTR(NEXT_FREE_BLK(bp));

            char* nn_free = GET_PTR(NEXT_FREE_BLK(PREV_BLKP(bp)));
            char* bb_free = GET_PTR(PREV_FREE_BLK(PREV_BLKP(bp)));

            char* nn_free_f = GET_PTR(NEXT_FREE_BLK(NEXT_BLKP(bp)));
            char* bb_free_f = GET_PTR(PREV_FREE_BLK(NEXT_BLKP(bp)));

            if(nn_free == NEXT_BLKP(bp)) {
            //    printf("the next free block of previous free block is the 3rd block\n");
                PUT_PTR(NEXT_FREE_BLK(bb_free),nn_free_f);
                PUT_PTR(PREV_FREE_BLK(nn_free_f),bb_free);
            }

            else if (nn_free_f == PREV_BLKP(bp)) {
             //   printf("the previous free block of next free block is the 1st block\n");

           
                PUT_PTR(PREV_FREE_BLK(nn_free),bb_free_f);
                PUT_PTR(NEXT_FREE_BLK(bb_free_f),nn_free);

            }
            else{
             //   printf("its all goodd\n");
                PUT_PTR(NEXT_FREE_BLK(bb_free_f),nn_free_f);
                PUT_PTR(PREV_FREE_BLK(nn_free_f),bb_free_f);

                PUT_PTR(NEXT_FREE_BLK(bb_free),nn_free);
                PUT_PTR(PREV_FREE_BLK(nn_free), bb_free);
            }

            size += (GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(HDRP(NEXT_BLKP(bp))));
            PUT(FTRP(NEXT_BLKP(bp)),PACK(size,0));
            PUT(HDRP(PREV_BLKP(bp)),PACK(size,0));

            bp = PREV_BLKP(bp);

            PUT_PTR(NEXT_FREE_BLK(heap_listp),bp);

            PUT_PTR(NEXT_FREE_BLK(bp),next_free);
            PUT_PTR(PREV_FREE_BLK(bp),heap_listp);

            PUT_PTR(PREV_FREE_BLK(next_free),bp);

            SET_FREE(NEXT_BLKP(bp));
        }
    }
    //return bp;

/* $end mmfree */
#ifdef NEXT_FIT
    /* Make sure the rover isn't pointing into the free block */
    /* that we just coalesced */
    if ((rover > (char *)bp) && (rover < NEXT_BLKP(bp))) 
		rover = bp;
		
	return bp;
#endif
/* $begin mmfree */
    return bp;
}

static void printblock(void *bp) 
{
    int hsize, halloc, fsize, falloc;

    //mm_checkheap(0);
    hsize = GET_SIZE(HDRP(bp));
    halloc = GET_ALLOC(HDRP(bp)); 
    fsize = GET_SIZE(FTRP(bp));
    falloc = GET_ALLOC(FTRP(bp)); 
    
    if (hsize == 0) {
        printf("%p: EOL Epilogue Block follows:\n", bp);

        fsize = GET_SIZE((bp + 2*DSIZE));
        falloc = GET_ALLOC((bp + 2*DSIZE));

        printf("%p: header: [%d:%c] footer: [%d:%c] PrevFree = %d\n", bp, 
			hsize, (halloc ? 'a' : 'f'), 
			fsize, (falloc ? 'a' : 'f'), PREV_FREE(bp));

        return;
    }

    else if (halloc){
		printf("Allocated block ----  ");
		printf("%p: header: [%d:%c] PrevFree = %d\n", bp, 
			hsize, (halloc ? 'a' : 'f'), PREV_FREE(bp));
    } 
    else{
		printf("Unallocated block ----  ");
		printf("%p: header: [%d:%c] footer: [%d:%c]\n", bp, 
			hsize, (halloc ? 'a' : 'f'), 
			fsize, (falloc ? 'a' : 'f'));
		printf("Next free Pointer: %p  --- Prev free pointer: %p\n",
                    GET_PTR(NEXT_FREE_BLK(bp)),GET_PTR(PREV_FREE_BLK(bp)) );
    }
}

static void checkblock(void *bp) 
{
    int halloc;
    halloc = GET_ALLOC(HDRP(bp)); 
    if ((size_t)bp % 8)
        printf("Error: %p is not doubleword aligned\n", bp);
    if ((!halloc) && ((GET_SIZE(HDRP(bp)) != GET_SIZE(FTRP(bp))) || (GET_ALLOC(HDRP(bp)) != GET_ALLOC(FTRP(bp)))))
        printf("Error: header does not match footer for %p\n",bp);
}
/*
 * mm_checkheap
 */
void mm_checkheap(int verbose) {
    return;
    char *bp = heap_listp;
	bp = bp;
	
    if (verbose) {
		printf("Heap (%p):\n", heap_listp);
	}
	
	/* Check rover */
#ifdef NEXT_FIT
	if (!GET_ALLOC(HDRP(rover))) {
		printf("Invalid rover at %p\n", rover);
	}
#endif

	/* Check prologue */
    if ((GET_SIZE(HDRP(heap_listp)) != MIN_BLK_SIZE) 
	 || !GET_ALLOC(HDRP(heap_listp))) {
		printf("Invalid prologue header\n");
	}
    checkblock(heap_listp);

	/* Loop each block of the heap */
	if (verbose) {
		for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
			if (verbose) 
				printblock(bp);
			checkblock(bp);
		}
	}

	/* Check epilogue */
    if (verbose){
		printblock(bp);
		printf("reached epilogue\n");
	}
    if ((GET_SIZE(HDRP(bp)) != 0) || !(GET_ALLOC(HDRP(bp))))
		printf("Invalid epilogue header\n");

	/* Loop each block of free list */
	if (verbose) {
		for (bp = heap_listp; 
			GET_SIZE(HDRP(bp)) > 0; 
			bp = GET_PTR(NEXT_FREE_BLK(bp))){
			printf("Next Free Block pointer : %p\n", GET_PTR(NEXT_FREE_BLK(bp)));
			printf("PREv free block pointer : %p\n",GET_PTR(PREV_FREE_BLK(bp)));
		}
		
		printf("reached Epilogue\n");
		printf("Prev free block pointer : %p\n",GET_PTR(PREV_FREE_BLK(bp)));
	}

}
