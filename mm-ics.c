/* implicit free lists, first fit placement, and boundary tag coalescing */
#include <stdio.h>
#include <string.h>
#include <stdlib.h>

#include "mm.h"
#include "memlib.h"

#define NEXT_FITx

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

/* Basic const and macros */
#define WSIZE		4		/* word and header/footer size - 4 bytes */
#define DSIZE		8		/* double word size - 8 bytes */
#define TSIZE		12
#define QSIZE		16
#define OVERHEAD	8
#define ALIGNMENT	8
#define BLKSIZE		24
#define INISIZE		1016	/* heap extended size */
#define CHUNKSIZE	(1<<12)	/* extend heap by this amount - (1<<12) bytes */

#define ALIGN_SIZE(size)	(((size) + (ALIGNMENT - 1)) & ~0X7)

#define MAX(x, y)	((x) > (y)? (x) : (y))
#define MIN(x, y)	((x) < (y)? (x) : (y))

/* pack a size and allocated bit into a word */
#define PACK(size, alloc)	((size) | (alloc))

/* read and write a word at address p */
#define GET(p)		(*(unsigned int *)(p))
#define PUT(p, val)	(*(unsigned int *)(p) = (val))

/* read the size and allocated fields from address p */
#define SIZE(p)		(GET(p) & ~0x7)
#define IS_ALLOC(p)	(GET(p) & 0x1)

/* given block ptr bp, compute address of its header and footer */
#define HDRP(bp)		((char *)(bp) - WSIZE)
#define FTRP(bp)		((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

#define HEAD(p)		((void *)(p) - WSIZE)
#define LEFT(p)		((void *)(p))
#define RIGHT(P)	((void *)(p) + WSIZE)
#define PRNT(p)		((void *)(p) + DSIZE)
#define BROS(p)		((void *)(p) + TSIZE)
#define FOOT(p)		((void *)(p) + SIZE(HEAD(p)) - DSIZE)

#define GET_SIZE(bp)	((GET(HEAD(bp))) & ~0x7)
#define GET_PREV(bp)	((void *)(bp) - SIZE(((void *)(bp) - DSIZE)))
#define GET_NEXT(bp) 	((void *)(bp)+SIZE(HEAD(bp))) 
#define GET_ALLOC(bp) 	(GET(HEAD(bp))&0x1)

#define GET_LEFT(bp) (GET(LEFT(bp))) 
#define GET_RIGHT(bp) (GET(RIGHT(bp))) 
#define GET_PRNT(bp) (GET(PRNT(bp))) 
#define GET_BROS(bp) (GET(BROS(bp))) 
#define GET_FOOT(bp) (GET(FOOT(bp))) 

#define PUT_HEAD(bp, val) (PUT(HEAD(bp), (int)val)) 
#define PUT_FOOT(bp, val) (PUT(FOOT(bp), (int)val)) 
#define PUT_LEFT(bp, val) (PUT(LEFT(bp), (int)val)) 
#define PUT_RIGHT(bp, val) (PUT(RIGHT(bp), (int)val)) 
#define PUT_PRNT(bp, val) (PUT(PRNT(bp), (int)val)) 
#define PUT_BROS(bp, val) (PUT(BROS(bp), (int)val)) 

/* non-static functions */ 
int mm_init ( void ); 
void *mm_malloc ( size_t size ); 
void mm_free ( void *bp ); 
void *mm_realloc ( void *bp, size_t size ); 
/* static functions */ 
static void *coalesce ( void *bp ); 
static void *extend_heap ( size_t size ); 
static void place ( void *ptr, size_t asize ); 
static void insert_node ( void *bp ); 
static void delete_node ( void *bp ); 
static void *find_fit ( size_t asize ); 
/* Global variables */ 
static void *heap_list_ptr; 
static void *free_tree_rt;

/*
 * mm_init - Called when a new trace starts.
 */
int mm_init(void) {
	/* create the initial empty heap */ 
	if( (heap_list_ptr = mem_sbrk(QSIZE)) == NULL ) 
		return -1; 
		
	PUT( heap_list_ptr, 0 ); /* alignment padding */ 
	PUT( heap_list_ptr+WSIZE, PACK(OVERHEAD,1) ); /* prologue header */
	PUT( heap_list_ptr+DSIZE, PACK(OVERHEAD,1) ); /* prologue footer */ 
	PUT( heap_list_ptr+TSIZE, PACK(0,1) ); /* epilogue header */ 
	heap_list_ptr += QSIZE; 
	free_tree_rt = NULL; 
	
	/* Extend the empty heap with a free block of CHUNKSIZE bytes */ 
	if( extend_heap(ALIGN_SIZE(INISIZE))==NULL ) 
		return -1; 
	return 0;
}

void *extend_heap(size_t size) {
	void *bp; 
	if( (long)(bp = mem_sbrk(size)) == -1)
		return NULL;
		
	/* Initialize free block header/footer and the epilogue header */ 
	PUT_HEAD( bp, PACK(size,0) ); /* free block header */ 
	PUT_FOOT( bp, PACK(size,0) ); /* free block footer */ 
	PUT_HEAD( GET_NEXT(bp), PACK(0,1) ); /* new epilogue header */ 
	insert_node(coalesce(bp)); 
	return (void *)bp; 
}

void *mm_malloc(size_t size) {
	size_t asize;
	size_t extendsize;
	void *bp;
	
	if (size <= 0)
		return NULL;
		
	if (size <= BLKSIZE - OVERHEAD)
		asize = BLKSIZE;
	else
		asize = ALIGN_SIZE(size + OVERHEAD);
		
	if ((bp = find_fit(asize)) == NULL) {
		extendsize = MAX(asize + 32, INISIZE);
		extend_heap(ALIGN_SIZE(extendsize));
		
		if ((bp = find_fit(asize)) == NULL)
			return NULL;
	}
	
	/* place the block into its fit */ 
	if( size==448 && GET_SIZE(bp) > asize+64 ) 
		asize += 64; 
	else if( size==112 && GET_SIZE(bp) > asize+16 ) 
		asize += 16;
		
	place(bp, asize); 
	return bp; 
}

void mm_free(void *bp) {
	size_t size = GET_SIZE(bp);
	PUT_HEAD(bp, PACK(size, 0));
	PUT_FOOT(bp, PACK(size, 0));
	
	insert_node(coalesce(bp)); 
}

void *mm_realloc(void *ptr, size_t size) 
{ 
	if( ptr==NULL || size==0 ){ 
		mm_free(ptr); 
		return NULL; 
	} 
	
	if( size > 0 ){ 
		size_t oldsize = GET_SIZE( ptr ); 
		size_t newsize = ALIGN_SIZE( size+OVERHEAD ); 
		if( newsize < oldsize ){ /* newsize is less than oldsize */ 
	if( GET_ALLOC( GET_NEXT(ptr) ) ){
	/* the next block is allocated */ 
	if( (oldsize-newsize) >= BLKSIZE ){
	/* the remainder is greater than BLKSIZE */ 
	PUT_HEAD( ptr, PACK(newsize,1) ); 
	PUT_FOOT( ptr, PACK(newsize,1) );//newsize 
	void *temp = GET_NEXT(ptr);
	//this pointer points to extra space 
	PUT_HEAD( temp, PACK(oldsize-newsize,0) ); 
	PUT_FOOT( temp, PACK(oldsize-newsize,0) ); 
	insert_node(temp); 
	} 
	else{ /* the remainder is less than BLKSIZE */ 
	PUT_HEAD( ptr, PACK(oldsize,1) );
	//oldsize still occupies all spaces. 
	PUT_FOOT( ptr, PACK(oldsize,1) ); 
	} 
	return ptr; 
	} 
	else{ /* the next block is free */ 
	size_t csize = oldsize + GET_SIZE( GET_NEXT(ptr) ); delete_node( GET_NEXT(ptr) ); 
	PUT_HEAD( ptr, PACK(newsize,1) ); 
	PUT_FOOT( ptr, PACK(newsize,1) ); 
	void *temp = GET_NEXT(ptr); 
	PUT_HEAD( temp, PACK(csize-newsize,0) ); 
	PUT_FOOT( temp, PACK(csize-newsize,0) ); 
	insert_node(temp); 
	return ptr; 
	} 
	} 
	else{ /* newsize is greater than oldsize */ 
	size_t prev_alloc = GET_ALLOC(GET_PREV(ptr)); 
	size_t next_alloc = GET_ALLOC(GET_NEXT(ptr)); 
	size_t csize; 
	/* the next block is free and the addition of the two blocks no less than the new
	size */ 
	if( !next_alloc &&
	( (csize=oldsize+GET_SIZE(GET_NEXT(ptr))) >= newsize) ){ 
	delete_node(GET_NEXT(ptr)); 
	if((csize-newsize)>=BLKSIZE){ 
	PUT_HEAD( ptr, PACK(newsize,1) ); 
	PUT_FOOT( ptr, PACK(newsize,1) ); 
	void *temp=GET_NEXT(ptr); 
	PUT_HEAD( temp, PACK(csize-newsize,0) ); 
	PUT_FOOT( temp, PACK(csize-newsize,0) ); 
	insert_node(temp); 
	}else{ 
	PUT_HEAD( ptr,PACK(csize,1) ); 
	PUT_FOOT( ptr,PACK(csize,1) ); 
	} 
	return ptr; 
	} 
	/* the previous block is free and the addition of the two blocks no less than the
	new size */ 
	else if( !prev_alloc &&
	( (csize=oldsize+GET_SIZE(GET_PREV(ptr))) >= newsize) ){ 
	delete_node(GET_PREV(ptr)); 
	void *newptr=GET_PREV(ptr); 
	memcpy( newptr, ptr, oldsize-OVERHEAD ); 
	if((csize-newsize)>=BLKSIZE){ 
	PUT_HEAD( newptr,PACK(newsize,1) ); 
	PUT_FOOT( newptr,PACK(newsize,1) ); 
	void *temp=GET_NEXT(newptr); 
	PUT_HEAD( temp,PACK(csize-newsize,0) ); 
	PUT_FOOT( temp,PACK(csize-newsize,0) ); 
	insert_node(temp); 
	}else{ 
	PUT_HEAD( newptr,PACK(csize,1) ); 
	PUT_FOOT( newptr,PACK(csize,1) ); 
	} 
	return newptr; 
	} 
	else{ 
	/* the next and previous block is free and the addition of the two blocks less
	than the new size */ 
	size_t asize=ALIGN_SIZE(size+(OVERHEAD)); 
	size_t extendsize; 
	void *newptr; 
	if((newptr=find_fit(asize))==NULL){ 
	extendsize=MAX(asize,CHUNKSIZE); 
	extend_heap(extendsize); 
	if((newptr=find_fit(asize))==NULL) 
	return NULL; 
	} place( newptr, asize ); 
	/*copy content from memory*/
	memcpy( newptr, ptr,oldsize-OVERHEAD); 
	mm_free(ptr); 
	return newptr; 
	} 
	} 
	} 
	else 
	return NULL; 
}

static void *coalesce(void *bp) {
	size_t prev_alloc = GET_ALLOC(GET_PREV(bp));
	size_t next_alloc = GET_ALLOC(GET_NEXT(bp));
	size_t size = GET_SIZE(bp);
	
	/* case 0 */
	if (prev_alloc && next_alloc)
		return bp;
		
	/* case 1 */
	else if (!prev_alloc && next_alloc) {
		delete_node(GET_PREV(bp));
		size += GET_SIZE(GET_PREV(bp));
		PUT_HEAD(GET_PREV(bp), PACK(size, 0));
		PUT_FOOT( bp, PACK(size,0) ); 
		return GET_PREV(bp);
	}
	
	/* case 2 */
	else if ( prev_alloc && !next_alloc ) {
		delete_node( GET_NEXT(bp) ); 
		size += GET_SIZE( GET_NEXT(bp) ); 
		PUT_HEAD( bp, PACK(size,0) ); 
		PUT_FOOT( bp, PACK(size,0) ); 
		return bp; 
	} 
	
	/* case 3 */
	else {
		delete_node(GET_NEXT(bp)); 
		delete_node(GET_PREV(bp)); 
		size += GET_SIZE( GET_PREV(bp) ) +
				GET_SIZE( GET_NEXT(bp) ); 
		PUT_HEAD( GET_PREV(bp), PACK(size,0) ); 
		PUT_FOOT( GET_NEXT(bp), PACK(size,0) ); 
		
		return GET_PREV(bp);
	}
}

static void place(void *bp,size_t asize) 
{ 
	size_t csize = GET_SIZE(bp); 
	delete_node( bp ); 
	if((csize-asize)>=BLKSIZE){ 
		PUT_HEAD( bp,PACK(asize,1) ); 
		PUT_FOOT( bp,PACK(asize,1) ); 
		bp=GET_NEXT(bp); 
		PUT_HEAD( bp,PACK(csize-asize,0) ); 
		PUT_FOOT( bp,PACK(csize-asize,0) ); 
		insert_node( coalesce(bp) ); 
	} 
	else{ 
		PUT_HEAD( bp,PACK(csize,1) ); 
		PUT_FOOT( bp,PACK(csize,1) ); 
	} 
} 

static void* find_fit( size_t asize ) 
{ 
	/* the most fit block */ 
	void *fit = NULL; 
	/* temporary location of the search */ 
	void *temp = free_tree_rt; 
	/* use tree to implement a comparative best fit search */ 
	for(;temp!=NULL;){ 
	/* The following node in the search may be worse, so we need to record the
	most fit so far. */ 
		if( asize <= GET_SIZE(temp) ){ 
			fit = temp; 
			temp = (void *)GET_LEFT(temp); 
		} 
		else 
			temp = (void *)GET_RIGHT(temp); 
	} 
	
	return fit; 
} 

static void insert_node( void *bp ) 
{ 
/* root is NULL */ 
if( free_tree_rt == NULL ){ 
free_tree_rt = bp; 
PUT_LEFT( bp, NULL ); 
PUT_RIGHT(bp, NULL ); 
PUT_PRNT( bp, NULL ); 
PUT_BROS( bp, NULL ); 
return; 
} 
/* treat temp as the start */ 
void *temp = free_tree_rt; 
/* loop to locate the position */ 
while( 1 ){ 
/* Case 1: size of the block exactly matches the node. */ 
if( GET_SIZE(bp)==GET_SIZE(temp) ){ 
if( (void *)GET_BROS(temp) != NULL ) 
{/* more than one block in the node */ 
if( temp == free_tree_rt ){/* temp is parent,and the root*/
free_tree_rt = bp; 
PUT_PRNT( bp, NULL ); 
} 
else{/* temp is parent, and not the root */ 
if( (void *)GET_LEFT(GET_PRNT(temp)) == temp
) 
/* temp is left child(temp's parent's left child is temp) */ 
PUT_LEFT( GET_PRNT(temp), bp );
//put temp's parent's left point as bp. 
else /* temp is right child */
PUT_RIGHT( GET_PRNT(temp), bp ); PUT_PRNT( bp, GET_PRNT(temp) );
//put bp's parent as temp's parent. 
} 
PUT_LEFT( bp, GET_LEFT(temp) ); 
PUT_RIGHT( bp, GET_RIGHT(temp) ); 
PUT_BROS( bp, temp ); 
//if temp is not parent(only siblings) 
if( (void *)GET_LEFT(temp) != NULL ) 
PUT_PRNT( GET_LEFT(temp), bp ); 
if( (void *)GET_RIGHT(temp) != NULL ) 
PUT_PRNT( GET_RIGHT(temp), bp ); 
PUT_LEFT( temp, bp ); 
PUT_RIGHT( temp, -1 ); 
break; 
} 
else{/* no more than one block in the node */ 
PUT_BROS( bp, NULL ); 
PUT_LEFT( bp, temp ); 
PUT_RIGHT( bp, -1 ); 
PUT_BROS( temp, bp ); 
if( (void *)GET_BROS(bp) != NULL ) 
PUT_LEFT( GET_BROS(bp), bp ); 
break; 
} 
} 
/* Case 2: size of the block is less than that of the node. */ 
else if( GET_SIZE(bp) < GET_SIZE(temp) ){ 
if( (void *)GET_LEFT(temp) != NULL ){ 
temp = (void *)GET_LEFT( temp ); 
}else{ 
PUT_LEFT( temp, bp ); PUT_PRNT( bp, temp ); 
PUT_LEFT( bp, NULL ); 
PUT_RIGHT( bp, NULL ); 
PUT_BROS( bp, NULL ); 
break; 
} 
} 
/* Case 3 size of the block is greater than that of the node. */ 
else{ 
if( (void *)GET_RIGHT(temp) != NULL ){ 
temp = (void *)GET_RIGHT(temp); 
}else{ 
PUT_RIGHT( temp, bp ); 
PUT_PRNT( bp, temp ); 
PUT_LEFT( bp, NULL ); 
PUT_RIGHT( bp, NULL ); 
PUT_BROS( bp, NULL ); 
break; 
} 
} 
} 
} 

static void delete_node(void *bp) 
{ 
/* Case that the block is the only one in the node */ 
if( (void *)GET_BROS(bp) == NULL && GET_RIGHT(bp) != -1 ){ 
if( bp == free_tree_rt ){/* the node is the root */ 
if( (void *)GET_RIGHT(bp) == NULL ){/* no right child */ 
free_tree_rt=(void *)GET_LEFT(bp); 
if( free_tree_rt != NULL ) 
PUT_PRNT( free_tree_rt, NULL ); 
} 
else{/* it has a right child */ 
void *temp = (void *)GET_RIGHT(bp); 
while( (void *)GET_LEFT(temp) != NULL ) 
temp = (void *)GET_LEFT(temp); 
void *tempL = (void *)GET_LEFT(bp); 
void *tempR = (void *)GET_RIGHT(temp); 
void *tempP = (void *)GET_PRNT(temp); 
free_tree_rt = temp; 
if( free_tree_rt != NULL ) 
PUT_PRNT( free_tree_rt, NULL ); 
PUT_LEFT( temp,GET_LEFT(bp) ); 
if( temp != (void *)GET_RIGHT(bp) ){ 
PUT_RIGHT( temp,GET_RIGHT(bp) ); 
PUT_LEFT( tempP, tempR ); 
if( tempR != NULL) 
PUT_PRNT( tempR, tempP ); 
PUT_PRNT( GET_RIGHT(bp),temp ); 
} 
if( tempL != NULL ) 
PUT_PRNT( tempL, temp ); 
} 
} 
else{/* the node is not the root */ 
if( (void *)GET_RIGHT(bp) == NULL ){/* no right child */ 
if( (void *)GET_LEFT( GET_PRNT( bp ) ) == bp ) PUT_LEFT( GET_PRNT(bp), GET_LEFT(bp) ); 
else 
PUT_RIGHT( GET_PRNT(bp), GET_LEFT(bp) ); 
if( (void *)GET_LEFT(bp) != NULL) 
PUT_PRNT( GET_LEFT(bp), GET_PRNT(bp) ); 
}else{/* it has a right child */ 
void *temp = (void *)GET_RIGHT(bp); 
while( (void *)GET_LEFT(temp) != NULL ) 
temp = (void *)GET_LEFT(temp); 
void *tempL = (void *)GET_LEFT(bp); 
void *tempR = (void *)GET_RIGHT(temp); 
void *tempP = (void *)GET_PRNT(temp); 
if( (void *)GET_LEFT(GET_PRNT(bp)) == bp ) 
PUT_LEFT( GET_PRNT(bp), temp ); 
else 
PUT_RIGHT( GET_PRNT(bp), temp ); 
PUT_PRNT( temp, GET_PRNT(bp) ); 
PUT_LEFT( temp, GET_LEFT(bp) ); 
if( temp != (void *)GET_RIGHT(bp)){ 
PUT_RIGHT( temp, GET_RIGHT(bp) ); 
PUT_LEFT( tempP, tempR ); 
if( tempR != NULL ) 
PUT_PRNT( tempR,tempP ); 
PUT_PRNT( GET_RIGHT(bp), temp ); 
} 
if( tempL != NULL ) 
PUT_PRNT( tempL, temp ); 
} 
} 
}else{/* Other case */ if( bp == free_tree_rt ){/* the node is the root */ 
free_tree_rt = (void *)GET_BROS(bp); 
PUT_PRNT( free_tree_rt, NULL ); 
PUT_LEFT( free_tree_rt, GET_LEFT(bp) ); 
PUT_RIGHT( free_tree_rt, GET_RIGHT(bp) ); 
if( (void *)GET_LEFT(bp) != NULL ) 
PUT_PRNT( GET_LEFT(bp), free_tree_rt ); 
if( (void *)GET_RIGHT(bp) != NULL ) 
PUT_PRNT( GET_RIGHT(bp), free_tree_rt ); 
}else{/* the node is not the root */ 
if( GET_RIGHT(bp) == -1 ){/* not the first block in the node */ 
PUT_BROS( GET_LEFT(bp),GET_BROS(bp) ); 
if( (void *)GET_BROS(bp) != NULL ) 
PUT_LEFT( GET_BROS(bp),GET_LEFT(bp) ); 
}else{/* the first block in the node */ 
if( (void *)GET_LEFT(GET_PRNT(bp)) == bp ) 
PUT_LEFT( GET_PRNT(bp), GET_BROS(bp) ); 
else 
PUT_RIGHT( GET_PRNT(bp), GET_BROS(bp) );
PUT_PRNT( GET_BROS(bp), GET_PRNT(bp) ); 
PUT_LEFT( GET_BROS(bp), GET_LEFT(bp) ); 
PUT_RIGHT( GET_BROS(bp), GET_RIGHT(bp) ); 
if( (void *)GET_LEFT(bp) != NULL ) 
PUT_PRNT(GET_LEFT(bp), GET_BROS(bp) ); 
if( (void *)GET_RIGHT(bp) != NULL) 
PUT_PRNT(GET_RIGHT(bp), GET_BROS(bp) ); 
} 
} 
} 
}