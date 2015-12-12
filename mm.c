/*
 * mm.c
 *
 * NOTE TO STUDENTS: Replace this header comment with your own header
 * comment that gives a high level description of your solution.
 */
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

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
#define ALIGN(p) 			(((size_t)(p) + (ALIGNMENT-1)) & ~0x7)

#define WSIZE 		4
#define DSIZE		8
#define CHUNKSIZE  (1<<12)
#define SETW(addr, value)	(*(unsigned int *)(addr) = (value))
#define PACK(size, bits)	( (size) | (bits) )
#define GET_SIZE(p)			(GET(p) & ~0x7)
#define HDRP(bp)			((char *)(bp) - WSIZE)
#define FTRP(bp)			((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp) 		((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp) 		((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))
#defin Max(a, b) ((a > b)? a:b)
static char *heap_listp;

int heap_extend(int num);
static void* coalesce(void *bp);
static void* heap_extend(int num);


/*
 * Initialize: return -1 on error, 0 on success.
 */
int mm_init(void) 
{
	//setting up prologue

	//request for two DWORD
	if ( (heap_listp = (char *)mem_sbrk(4*WSIZE)) == (char *)-1 )
		return -1;
	SETW( heap_listp, 0);//padding
	SETW( heap_listp + WSIZE, PACK((WSIZE * 2), 1) );	//header
	SETW( heap_listp + 2*WSIZE, PACK((WSIZE * 2), 1) );	//footer

	//set up epilogue
	SETW( heap_listp + 3*WSIZE, PACK(0, 1) );
	// now extend the heap
	void *new_block = heap_extend(CHUNKSIZE/WSIZE);
	if (new_block == (void *) -1)
		return -1;
	heap_listp += (2*WSIZE);
    return 0;
}

/*
 * malloc
 */
void *malloc (size_t size) 
{
	if (heap_listp == 0)
	{
		mm_init();
	}
	size_t alloc_size;

	if (size <=0 )//ignore
		return NULL;
	if (size < 8)
		alloc_size = DSIZE * 2;
	else
		alloc_size = ALIGN(size + WSIZE);

	void *free_blk = find_free_block(alloc_size);
	if (free_blk == NULL)
	{
		size_t extendsize = MAX(asize, CHUNKSIZE); 
		if( (free_blk = heap_extend(extendsize)) == (void *)-1 )
			return NULL;
	}
	place(free_blk, size);
    return free_blk;
}

static void place(void *bp, size_t size)
{
	int original_size = GET_SIZE(bp);
	if (original_size - size < DWORD*2)
	{
		SETW(HDRP(bp), PACK(original_size, 1));
		SETW(FTRP(bp), PACK(original_size, 1));
	}
	else
	{
		SETW(HDRP(bp), PACK(size, 1));
		SETW(FTRP(bp), PACK(size, 1));
		bp = NEXT_BLKP(bp);
		SETW(HDRP(bp), PACK(original_size - size), 0);
		SETW(FTRP(bp), PACK(original_size - size), 0);
	}
}

/*
 * free
 */
void free (void *ptr) 
{
    if(!ptr) return;

    size_t size = GET_SIZE(ptr);
    SETW(HDRP(ptr), PACK(size, 0));
    SETW(FTRP(ptr), PACK(size, 0));
    coalesce(ptr);
}

/*
 * realloc - you may want to look at mm-naive.c
 */
void *realloc(void *oldptr, size_t size) 
{
	size_t oldsize;
	void *newptr;

	/* If size == 0 then this is just free, and we return NULL. */
	if(size == 0) {
	free(oldptr);
	return 0;
	}

	/* If oldptr is NULL, then this is just malloc. */
	if(oldptr == NULL) {
	return malloc(size);
	}

	newptr = malloc(size);

	/* If realloc() fails the original block is left untouched  */
	if(!newptr) {
	return 0;
	}

	/* Copy the old data. */
	oldsize = *SIZE_PTR(oldptr);
	if(size < oldsize) oldsize = size;
	memcpy(newptr, oldptr, oldsize);

	/* Free the old block. */
	free(oldptr);

	return newptr;
}

/*
 * calloc - you may want to look at mm-naive.c
 * This function is not tested by mdriver, but it is
 * needed to run the traces.
 */
void *calloc (size_t nmemb, size_t size) 
{
	size_t alloc_size = nmemb * size;
	void *bp = malloc(alloc_size);
	memset(bp, 0, alloc_size);
    return bp;
}


/*
 * Return whether the pointer is in the heap.
 * May be useful for debugging.
 */
static int in_heap(const void *p) {
    return p <= mem_heap_hi() && p >= mem_heap_lo();
}

/*
 * Return whether the pointer is aligned.
 * May be useful for debugging.
 */
static int aligned(const void *p) {
    return (size_t)ALIGN(p) == (size_t)p;
}


static void printblock(void *bp) 
{
    size_t hsize, halloc, fsize, falloc;

    checkheap(0);
    hsize = GET_SIZE(HDRP(bp));
    halloc = GET_ALLOC(HDRP(bp));  
    fsize = GET_SIZE(FTRP(bp));
    falloc = GET_ALLOC(FTRP(bp));  

    if (hsize == 0) {
        printf("%p: EOL\n", bp);
        return;
    }

    printf("%p: header: [%ld:%c] footer: [%ld:%c]\n", bp, 
           hsize, (halloc ? 'a' : 'f'), 
           fsize, (falloc ? 'a' : 'f')); 
}

static void checkblock(void *bp) 
{
    if ((size_t)bp % 8)
        printf("Error: %p is not doubleword aligned\n", bp);
    if (GET(HDRP(bp)) != GET(FTRP(bp)))
        printf("Error: header does not match footer\n");
}

/*
 * mm_checkheap
 */
void mm_checkheap(int verbose) 
{
    char *bp = heap_listp;

    if (verbose)
        printf("Heap (%p):\n", heap_listp);

    if ((GET_SIZE(HDRP(heap_listp)) != DSIZE) || !GET_ALLOC(HDRP(heap_listp)))
        printf("Bad prologue header\n");
    checkblock(heap_listp);

    for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
        if (verbose) 
            printblock(bp);
        checkblock(bp);
    }

    if (verbose)
        printblock(bp);
    if ((GET_SIZE(HDRP(bp)) != 0) || !(GET_ALLOC(HDRP(bp))))
        printf("Bad epilogue header\n");
}


/*
 * Extend the heap by num blocks
 */
static void* heap_extend(int num)
{
	size_t size = WSIZE * ( num%2 ? num+1 : num );
 	void *result = mem_sbrk(size);
 	if (result == (void *)-1)
 		return -1;
 	//set up a free block here
 	SETW( HDRP(result), WSIZE*num);
 	SETW( FTRP(result), WSIZE*num);
 	SETW( HDRP( NEXT_BLKP(result) ), PACK(0, 1));

 	return coalesce(bp);;
}

static void* coalesce(void *bp)
{
	size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));
    int condition = prev_alloc | (next_alloc << 1);

    switch(condition)
    {
    	case 3:
    		return bp;
    	case 2:
    		size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        	SETW(FTRP(bp), PACK(size, 0));
        	SETW(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        	bp = PREV_BLKP(bp);
        	break;
        case 1:
        	size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
	        SETW(HDRP(bp), PACK(size, 0));
	        SETW(FTRP(bp), PACK(size,0));
	        break;
	    case 0:
	    	size += GET_SIZE(HDRP(PREV_BLKP(bp))) + 
            GET_SIZE(FTRP(NEXT_BLKP(bp)));
	        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
	        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
	        bp = PREV_BLKP(bp);
	        break;
    }
    return bp;
}

static void * find_free_block(size_t asize)
{
	void *bp;

    for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
        if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))) {
            return bp;
        }
    }
    return NULL;
}
