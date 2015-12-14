/*
 * mm.c
 * ID:	1400012817

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
// #define DEBUG
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

/* constants for segregated list */ 
#define SIZE0 (3)
#define SIZE1 (1<<1)
#define SIZE2 (1<<2)
#define SIZE3 (1<<3)
#define SIZE4 (1<<4)
#define SIZE5 (1<<5)
#define SIZE6 (1<<6)
#define SIZE7 (1<<7)
#define SIZE8 (1<<8)
#define SIZE9 (1<<9)
#define SIZE10 (1<<10)
#define SIZE11 (1<<11)
#define SIZE12 (1<<12)
#define SIZE13 (1<<13)
#define SIZE14 (1<<14)
#define SIZE15 (1<<15)

#define SYS_WORD 8
#define PTR_NUM 16
#define PTRSEG 128//16*8

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(p) 			(((size_t)(p) + (ALIGNMENT-1)) & ~0x7)

#define WSIZE 		4
#define DSIZE		8
#define CHUNKSIZE  (1<<12)
#define SETW(addr, value)	(*(unsigned int *)(addr) = (value))
#define PACK(size, bits)	( (size) | (bits) )

#define GET(p)       		(*(unsigned int *)(p))
#define GET_ALLOC(p) 		(GET(p) & 0x1)
#define GET_SIZE(p)			(GET(p) & ~0x7)
#define HDRP(bp)			((char *)(bp) - WSIZE)
#define FTRP(bp)			((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp) 		((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp) 		((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))
#define MAX(a, b) 			((a > b)? a:b)

/* pointer operator */
#define PRED(bp)			((unsigned long *)bp)
#define SUCC(bp)			((unsigned long *)bp + 1)
#define SETD(addr, value)	(*(unsigned long *)(addr) = (unsigned long)(value))
#define GETD(addr)			(*(unsigned long *)(addr))

#define LIST_END	((unsigned long)-2)
#define GEN_ALLOCSIZE(cl)	( cl==0 ? 3:(1<<(cl+1)) )
#define GET_NEED_BLK(size)	( (size-1)/DSIZE +1 )
/* complex helper macro */
/* may be smaller than the actual size of bp */
#define CLASS_BP(bp)		(get_bp_class( GET_SIZE(HDRP(bp)) ))


typedef unsigned long * ptr_t;

static char *heap_listp = NULL;
static void *free_list = NULL;

static ptr_t ptrs = NULL;

static void* coalesce(void *bp);
static void* heap_extend(int block_num);
static void * find_free_block(int num);
static void place(void *bp, size_t size);
static void printblock(void *bp);
void mm_checkheap(int verbose);
static void checkblock(void *bp);
static int get_class(int block_num);
/* get the ptr to No.x list */
static ptr_t get_list_ptr(int num);
static void append(int list_num, void *bp);
static void list_remove(int list_num, void *bp);
static void print_list();

static int get_bp_class(int size)
{
	int valid_blk = size/DSIZE;
	if (valid_blk >= SIZE15)
	{
		return 15;
	}
	valid_blk++;
	return get_class(valid_blk)-1;
}

/*
 * Initialize: return -1 on error, 0 on success.
 */
int mm_init(void)
{
	//setting up prologue

	//request for the initial ptrs and initialized 0
	if ( ( ptrs = (ptr_t)mem_sbrk(PTRSEG) ) == (void *)-1 )
		return -1;

	/* set all to list end at first */
	int i;
	for (i = 0; i < PTR_NUM; ++i)
	{
		SETD( get_list_ptr(i), LIST_END);
	}


	if ( (heap_listp = (char *)mem_sbrk(4*WSIZE)) == (char *)-1 )
		return -1;
	SETW( heap_listp, 0);//padding
	SETW( heap_listp + WSIZE, PACK((WSIZE * 2), 1) );	//header
	SETW( heap_listp + 2*WSIZE, PACK((WSIZE * 2), 1) );	//footer

	//set up epilogue
	SETW( heap_listp + 3*WSIZE, PACK(0, 1) );
	// now extend the heap
	void *new_block = heap_extend(CHUNKSIZE/DSIZE);
	if (new_block == (void *) -1)
		return -1;
	heap_listp += (2*WSIZE);
	free_list = new_block;
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

	int needed_blks = GET_NEED_BLK(size + DSIZE);
	if (needed_blks < 3)
	{
		needed_blks = 3;
	}
	int class_num = get_class(needed_blks);
	
	alloc_size = needed_blks * DSIZE;

	/* Notice the semantic of find_free_block has changend */
	void *free_blk = find_free_block(class_num);

	if (free_blk == NULL)
	{
		size_t extendsize = MAX(alloc_size, CHUNKSIZE);
		if( (free_blk = heap_extend(extendsize/DSIZE)) == (void *)-1 )
			return NULL;
	}
	dbg_printf("\n [ Mallocing Block ] \nsize\t%ld\talloc_s\t%ld\n",size, alloc_size);

	place(free_blk, alloc_size);

    return free_blk;
}

static void place(void *bp, size_t size)
{
	int original_size = GET_SIZE(HDRP(bp));
	if (original_size - size < DSIZE*SIZE0)
	{
		SETW(HDRP(bp), PACK(original_size, 1));
		SETW(FTRP(bp), PACK(original_size, 1));
		int this_class = CLASS_BP(bp);
		list_remove(this_class, bp);
	}
	else
	{
		int this_class = CLASS_BP(bp);
		list_remove(this_class, bp);
		SETW(HDRP(bp), PACK(size, 1));
		SETW(FTRP(bp), PACK(size, 1));
		bp = NEXT_BLKP(bp);
		SETW(HDRP(bp), PACK(original_size - size, 0));
		SETW(FTRP(bp), PACK(original_size - size, 0));
		int next_class = CLASS_BP(bp);
		append(next_class, bp);
	}
}

/*
 * free
 */
void free (void *ptr)
{
	dbg_printf("\n [Freeing Block] \n");


    if((size_t) ptr<=0) return;

    size_t size = GET_SIZE(HDRP(ptr));
    SETW(HDRP(ptr), PACK(size, 0));
    SETW(FTRP(ptr), PACK(size, 0));
    append(CLASS_BP(ptr), ptr);
    coalesce(ptr);

    dbg_printf("\n [End OF Freeing] \n");
}

/*
 * realloc - you may want to look at mm-naive.c
 */
void *realloc(void *oldptr, size_t size)
{
	size_t oldsize;
	void *newptr;

	/* If size == 0 then this is just free, and we return NULL. */
	if(size == 0)
	{
		free(oldptr);
		return 0;
	}

	/* If oldptr is NULL, then this is just malloc. */
	if(oldptr == NULL)
	{
		return malloc(size);
	}

	newptr = malloc(size);

	/* If realloc() fails the original block is left untouched  */
	if(!newptr)
	{
		return 0;
	}

	/* Copy the old data. */
	oldsize = GET_SIZE(HDRP(oldptr));
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

/*
 * Extend the heap by num blocks
 * Modify To support explicit list
 */
static void* heap_extend(int block_num)
{
	size_t size = DSIZE * block_num;
 	void *result = mem_sbrk(size);
 	if (result == (void *)-1)
 		return (void *)-1;
 	//set up a free block here
 	//and set up ptrs
 	SETW( HDRP(result), size);
 	SETW( FTRP(result), size);
 	SETW( HDRP( NEXT_BLKP(result) ), PACK(0, 1));

 	/* determine which class */
 	int cata = CLASS_BP(result);

 	append(cata, result);
 	return coalesce(result);
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
    	case 2://next allocated
    		//remove pre
    		list_remove( CLASS_BP(PREV_BLKP(bp)), PREV_BLKP(bp) );
    		list_remove( CLASS_BP(bp), bp );
    		size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        	SETW(FTRP(bp), PACK(size, 0));
        	SETW(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        	bp = PREV_BLKP(bp);
        	break;
        case 1://pre allocated
        	//list_remove next
        	list_remove( CLASS_BP(NEXT_BLKP(bp)), NEXT_BLKP(bp) );
        	list_remove( CLASS_BP(bp), bp );
        	size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
	        SETW(HDRP(bp), PACK(size, 0));
	        SETW(FTRP(bp), PACK(size,0));
	        
	        break;
	    case 0://none allocated
		    list_remove( CLASS_BP(PREV_BLKP(bp)), PREV_BLKP(bp) );
		    list_remove( CLASS_BP(NEXT_BLKP(bp)), NEXT_BLKP(bp) );
		    list_remove( CLASS_BP(bp), bp );
	    	size += GET_SIZE(HDRP(PREV_BLKP(bp))) +
            GET_SIZE(FTRP(NEXT_BLKP(bp)));
	        SETW(HDRP(PREV_BLKP(bp)), PACK(size, 0));
	        SETW(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
	        bp = PREV_BLKP(bp);
	        break;
    }
    /* set up ptrs */
	append( CLASS_BP(bp), bp);

    return bp;
}

static void * find_free_block(int class_num)
{
	void *ptr = get_list_ptr(class_num);
	void *bp = (void *)GETD(ptr);
	int try_class = class_num;
	while((unsigned long)bp == LIST_END)
	{
		try_class++;
		ptr = get_list_ptr(try_class);
		bp = (void *)GETD(ptr);
		if (try_class >15 )
		{
			return NULL;
		}
	}
    return bp;
}

/* checked */
static int get_class(int block_num)
{
	if (block_num >= SIZE15)
	{
		return 15;
	}
	if (block_num <=3 )
	{
		return 0;
	}
	int res = block_num;
	res --;
	res |= res >> 1;
	res |= res >> 2;
	res |= res >> 4;
	res |= res >> 8;
	res |= res >> 16;
	res++;
	int cnt=0;
	while(res)
	{
		res>>=1;
		cnt++;
	}
	cnt--;
	return cnt;
}

/* actually insert */
/* checked */
static void append(int list_num, void *bp)
{
	ptr_t ptr = get_list_ptr(list_num);
	if (ptr == (ptr_t)-1)
	{
		dbg_printf("Pointer set Error\n");
		return;
	}

	/* add to the beginning of a list */
	if (GETD(ptr) == LIST_END)
	{
		SETD( ptr, bp );
		SETD(SUCC(bp), LIST_END);
		SETD(PRED(bp), ptr);
		return;
	}

	/* there is remaining list item in the list */
	/* insert to the head of the list */

	void *next_bp = (void *)GETD(ptr);
	SETD( SUCC(bp), next_bp);
	SETD( PRED(bp), ptr );
	SETD( PRED(next_bp), bp );
	SETD( ptr, bp );

}

/* get the ptr to No.x list */
/* checked */
static ptr_t get_list_ptr(int num)
{
	if (ptrs == NULL)
	{
		return (ptr_t)-1;
	}
	return (ptr_t)ptrs + num;
}

/* remove from list */
/* checked */
static void list_remove(int list_num, void *bp)
{
	ptr_t ptr = get_list_ptr(list_num);
	if (ptr == (ptr_t)-1)
	{
		dbg_printf("Pointer set Error\n");
		return;
	}

	void *crt_bp = (void *)GETD(ptr);
	while(1)
	{
		if ( crt_bp == bp)//item to remove
		{
			void* pre_bp = (void *)GETD(PRED(bp));
			/* 前驱是头表 */
			if ((ptr_t)pre_bp - (ptr_t)ptrs <16 )
				SETD( pre_bp, GETD( SUCC(crt_bp) ) );
			else
				SETD( SUCC(pre_bp), GETD( SUCC(crt_bp) ) );
			
			if ( GETD( SUCC(crt_bp) ) == LIST_END ) break;
			
			void *suc_bp = (void *)GETD( SUCC(crt_bp) );
			SETD( PRED(suc_bp), GETD( PRED(crt_bp) ) );

			break;
		}
		crt_bp = (void *)GETD(SUCC(crt_bp));
	}

}

static void printBlockDetail(void *bp)
{
	dbg_printf("Block\t0x%lx\nHeader\t0x%x\nSize\t0x%lx\n",
	 (unsigned long)bp, (unsigned)GET(HDRP(bp)), (unsigned long)GET_SIZE(HDRP(bp)));
    dbg_printf("FT ADDR\t0x%lx\n", (unsigned long)FTRP(bp));
    dbg_printf("Footer\t0x%x\n",(unsigned)GET(FTRP(bp)));
    dbg_printf("Class\t%d\n", CLASS_BP(bp));
    dbg_printf("PREV\t%lx\tSUCC\t%lx\n\n", GET(PRED(bp)), GET(SUCC(bp)));
}

static void printblock(void *bp)
{
    size_t hsize, halloc, fsize, falloc;

    mm_checkheap(0);
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
    printBlockDetail(bp);

}
static void dump_heap()
{
	void *bp;
	dbg_printf("\n [Start Dumping Heap]\n");
	for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) 
	{
	 	printBlockDetail(bp);
    }
    dbg_printf("\n [Dumping Complete] \n");
}

static void checkblock(void *bp)
{
    if ((size_t)bp % 8)
        printf("Error: 0x%lx is not doubleword aligned\n", (unsigned long)bp);

   	if ( GET(HDRP(bp)) != GET(FTRP(bp)))
   	{
   		dump_heap();
   		printf("Error: header does not match footer\n");
   	}

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

static void print_list()
{
	dbg_printf("[Printing List]\n");
    if (1)
    {
    	int i;
    	for (i = 0; i < 16; ++i)
    	{
    		ptr_t crt = (ptr_t)GETD(get_list_ptr(i));
    		while(crt != LIST_END)
    		{
    			dbg_printf("[List %d]\n",i);
    			printblock(crt);
    			crt = GETD(SUCC(crt));
    		}
    	}
    }
    dbg_printf("[End of printing list]\n");
}
