/*
 * mm.c -  Simple allocator based on implicit free lists,
 *         first fit placement, and boundary tag coalescing.
 *
 * Each block has header and footer of the form:
 *
 *      63       32   31        1   0
 *      --------------------------------
 *     |   unused   | block_size | a/f |
 *      --------------------------------
 *
 * a/f is 1 iff the block is allocated. The list has the following form:
 *
 * begin                                       end
 * heap                                       heap
 *  ----------------------------------------------
 * | hdr(8:a) | zero or more usr blks | hdr(0:a) |
 *  ----------------------------------------------
 * | prologue |                       | epilogue |
 * | block    |                       | block    |
 *
 * The allocated prologue and epilogue blocks are overhead that
 * eliminate edge conditions during coalescing.
 */
#include "memlib.h"
#include "mm.h"
#include <assert.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

 /* Your info */
team_t team = {
    /* First and last name */
    "Bill Tran",
    /* UID */
    "505604257",
    /* Custom message (16 chars) */
    "",
};

//MACROS FROM TEXTBOOK but changed word size

/* Basic constants and macros */
#define WSIZE 8 /* Word and header/footer size (bytes) */
#define DSIZE 16 /* Double word size (bytes) */

#define MAX(x, y) ((x) > (y)? (x) : (y))

 /* Pack a size and allocated bit into a word */
#define PACK(size, alloc) ((size) | (alloc))

/* Read and write a word at address p */
#define GET(p) (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p) = (val))

/* Read the size and allocated fields from address p */
#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp) ((block_t *)(bp) - WSIZE)
#define FTRP(bp) ((block_t *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp) ((block_t *)(bp) + GET_SIZE(((block_t *)(bp) - WSIZE)))
#define PREV_BLKP(bp) ((block_t *)(bp) - GET_SIZE(((block_t *)(bp) - DSIZE)))

/* Given block ptr bp, get the next and previous block pointers (next stored first, then prev)*/
#define GET_NEXT(bp)   (bp->body.next)
#define GET_PREV(bp)   (bp->body.prev)

/* Given block ptr bp, set the next and previous block pointers to pointer np */
#define SET_NEXT(bp, np)   (GET_NEXT(bp) = np)
#define SET_PREV(bp, np)   (GET_PREV(bp) = np)

typedef struct {
    uint32_t allocated : 1;
    uint32_t block_size : 31;
    uint32_t _;
} header_t;

typedef header_t footer_t;

typedef struct block_t {
    uint32_t allocated : 1;
    uint32_t block_size : 31;
    uint32_t _;
    union {
        struct {
            struct block_t* next;
            struct block_t* prev;
        };
        int payload[0];
    } body;
} block_t;

/* This enum can be used to set the allocated bit in the block */
enum block_state {
    FREE,
    ALLOC
};

#define CHUNKSIZE (1 << 16) /* initial heap size (bytes) */
#define OVERHEAD (sizeof(header_t) + sizeof(footer_t)) /* overhead of the header and footer of an allocated block */
#define MIN_BLOCK_SIZE (32) /* the minimum block size needed to keep in a freelist (header + footer + next pointer + prev pointer) */

/* Global variables */
static block_t* prologue; /* pointer to first block */
static block_t* freerootptr; /* pointer to first free block of explicit list*/

/* function prototypes for internal helper routines */
static block_t* extend_heap(size_t words);
static void place(block_t* block, size_t asize);
static block_t* find_fit(size_t asize);
static block_t* coalesce(block_t* block);
static footer_t* get_footer(block_t* block);
static void printblock(block_t* block);
static void checkblock(block_t* block);

/*
 * mm_init - Initialize the memory manager
 */
 /* $begin mminit */
int mm_init(void) {
    /* create the initial empty heap */
    if ((prologue = mem_sbrk(CHUNKSIZE)) == (void*)-1)
        return -1;
    /* initialize the prologue */
    prologue->allocated = ALLOC;
    prologue->block_size = sizeof(header_t);
    /* initialize the first free block */
    block_t* init_block = (void*)prologue + sizeof(header_t);
    init_block->allocated = FREE;
    init_block->block_size = CHUNKSIZE - OVERHEAD;
    freerootptr = init_block;
    freerootptr->body.next = NULL;
    freerootptr->body.prev = NULL;
    footer_t* init_footer = get_footer(init_block);
    init_footer->allocated = FREE;
    init_footer->block_size = init_block->block_size;
    /* initialize the epilogue - block size 0 will be used as a terminating condition */
    block_t* epilogue = (void*)init_block + init_block->block_size;
    epilogue->allocated = ALLOC;
    epilogue->block_size = 0;
    return 0;
}
/* $end mminit */

/*
 * mm_malloc - Allocate a block with at least size bytes of payload
 */
 /* $begin mmmalloc */
void* mm_malloc(size_t size) {
    uint32_t asize;       /* adjusted block size */
    uint32_t extendsize;  /* amount to extend heap if no fit */
    uint32_t extendwords; /* number of words to extend heap if no fit */
    block_t* block;

    /* Ignore spurious requests */
    if (size == 0)
        return NULL;

    /* Adjust block size to include overhead and alignment reqs. */
    size += OVERHEAD;

    asize = ((size + 7) >> 3) << 3; /* align to multiple of 8 */

    if (asize < MIN_BLOCK_SIZE) {
        asize = MIN_BLOCK_SIZE;
    }

    /* Search the free list for a fit */
    if ((block = find_fit(asize)) != NULL) {
        place(block, asize);
        return block->body.payload;
    }

    /* No fit found. Get more memory and place the block */
    extendsize = (asize > CHUNKSIZE) // extend by the larger of the two
        ? asize
        : CHUNKSIZE;
    extendwords = extendsize >> 3; // extendsize/8
    if ((block = extend_heap(extendwords)) != NULL) {
        place(block, asize);
        return block->body.payload;
    }
    /* no more memory :( */
    return NULL;
}
/* $end mmmalloc */

/*
 * mm_free - Free a block
 */
 /* $begin mmfree */
void mm_free(void* payload) {
    block_t* block = payload - sizeof(header_t);
    block->allocated = FREE;
    footer_t* footer = get_footer(block);
    footer->allocated = FREE;
    coalesce(block);
}

/* $end mmfree */

/*
 * mm_realloc - naive implementation of mm_realloc
 * NO NEED TO CHANGE THIS CODE!
 */
void* mm_realloc(void* ptr, size_t size) {
    void* newp;
    size_t copySize;

    if ((newp = mm_malloc(size)) == NULL) {
        printf("ERROR: mm_malloc failed in mm_realloc\n");
        exit(1);
    }
    block_t* block = ptr - sizeof(header_t);
    copySize = block->block_size;
    if (size < copySize)
        copySize = size;
    memcpy(newp, ptr, copySize);
    mm_free(ptr);
    return newp;
}

/*
 * mm_checkheap - Check the heap for consistency
 */
void mm_checkheap(int verbose) {
    block_t* block = prologue;

    if (verbose)
        printf("Heap (%p):\n", prologue);

    if (block->block_size != sizeof(header_t) || !block->allocated)
        printf("Bad prologue header\n");
    checkblock(prologue);

    /* iterate through the heap (both free and allocated blocks will be present) */
    for (block = (void*)prologue + prologue->block_size; block->block_size > 0; block = (void*)block + block->block_size) {
        if (verbose)
            printblock(block);
        checkblock(block);
    }

    if (verbose)
        printblock(block);
    if (block->block_size != 0 || !block->allocated)
        printf("Bad epilogue header\n");
}

/* The remaining routines are internal helper routines */

/*
 * extend_heap - Extend heap with free block and return its block pointer
 */
 /* $begin mmextendheap */
static block_t* extend_heap(size_t words) {
    block_t* block;
    uint32_t size;
    size = words << 3; // words*8
    if (size == 0 || (block = mem_sbrk(size)) == (void*)-1)
        return NULL;
    /* The newly acquired region will start directly after the epilogue block */
    /* Initialize free block header/footer and the new epilogue header */
    /* use old epilogue as new free block header */
    block = (void*)block - sizeof(header_t);
    block->allocated = FREE;
    block->block_size = size;
    /* free block footer */
    footer_t* block_footer = get_footer(block);
    block_footer->allocated = FREE;
    block_footer->block_size = block->block_size;
    /* new epilogue header */
    header_t* new_epilogue = (void*)block_footer + sizeof(header_t);
    new_epilogue->allocated = ALLOC;
    new_epilogue->block_size = 0;
    if (freerootptr == NULL)
    {
        freerootptr = block;
        SET_NEXT(block, NULL);
        SET_PREV(block, NULL);
    }
    /* Coalesce if the previous block was free */
    return coalesce(block);
}
/* $end mmextendheap */

/*
 * place - Place block of asize bytes at start of free block block
 *         and split if remainder would be at least minimum block size
 */
 /* $begin mmplace */
static void place(block_t* block, size_t asize) {

    size_t split_size = block->block_size - asize;

    if (split_size >= MIN_BLOCK_SIZE) {

        /* split the block by updating the header and marking it allocated*/
        block->block_size = asize;
        block->allocated = ALLOC;
        /* set footer of allocated block*/
        footer_t* footer = get_footer(block);
        footer->block_size = asize;
        footer->allocated = ALLOC;


        /* update the header of the new free block */
        block_t* new_block = (void*)block + block->block_size;
        new_block->block_size = split_size;
        new_block->allocated = FREE;
        /* update the footer of the new free block */
        footer_t* new_footer = get_footer(new_block);
        new_footer->block_size = split_size;
        new_footer->allocated = FREE;


        if (GET_PREV(block) != NULL)
            SET_NEXT(GET_PREV(block), new_block);
        if (GET_NEXT(block) != NULL)
            SET_PREV(GET_NEXT(block), new_block);
        SET_NEXT(new_block, GET_NEXT(block));
        SET_PREV(new_block, GET_PREV(block));
        SET_NEXT(block, NULL);
        SET_PREV(block, NULL);
        if (GET_PREV(new_block) == NULL)
            freerootptr = new_block;
    }
    else {
        /* splitting the block will cause a splinter so we just include it in the allocated block */
        block->allocated = ALLOC;
        footer_t* footer = get_footer(block);
        footer->allocated = ALLOC;

        if (GET_PREV(block) != NULL)
            SET_NEXT(GET_PREV(block), block->body.next);

        if (GET_NEXT(block) != NULL)
            SET_PREV(GET_NEXT(block), block->body.prev);

        if ((GET_PREV(block) == NULL) && (GET_NEXT(block) != NULL))
            freerootptr = GET_NEXT(block);

        if ((GET_PREV(block) == NULL) && (GET_NEXT(block) == NULL))
            freerootptr = NULL;

        SET_NEXT(block, NULL);
        SET_PREV(block, NULL);
    }
}
/* $end mmplace */

/*
 * find_fit - Find a fit for a block with asize bytes
 */
static block_t* find_fit(size_t asize) {
    /* first fit search */
    block_t* b;

    for (b = freerootptr; b != NULL; b = b->body.next) {
        /* block must be free and the size must be large enough to hold the request */
        if (asize <= b->block_size) {
            return b;
        }
    }
    return NULL; /* no fit */
}

/*
 * coalesce - boundary tag coalescing. Return ptr to coalesced block
 */
static block_t* coalesce(block_t* block) {
    footer_t* prev_footer = (void*)block - sizeof(header_t);
    header_t* next_header = (void*)block + block->block_size;
    bool prev_alloc = prev_footer->allocated;
    bool next_alloc = next_header->allocated;

    if (prev_alloc && next_alloc) { /* Case 1 */
        if (freerootptr == NULL || freerootptr == block)
        {
            freerootptr = block;
            SET_NEXT(freerootptr, NULL);
            SET_PREV(freerootptr, NULL);
        }
        else
        {
            SET_NEXT(block, freerootptr);
            SET_PREV(freerootptr, block);
            freerootptr = block;
            SET_PREV(block, NULL);
        }
        /* no coalesceing */
        return block;
    }

    else if (prev_alloc && !next_alloc)
    { /* Case 2 */
        block_t* next_block = (void*)block + block->block_size;

        if (GET_PREV(next_block) != NULL)
            SET_NEXT(GET_PREV(next_block), GET_NEXT(next_block));
        if (GET_NEXT(next_block) != NULL)
            SET_PREV(GET_NEXT(next_block), GET_PREV(next_block));

        if (GET_NEXT(next_block) != NULL && next_block == freerootptr) {
            SET_NEXT(block, GET_NEXT(next_block));
            SET_PREV(GET_NEXT(next_block), block);
            freerootptr = block;
            SET_PREV(block, NULL);
            SET_NEXT(next_block, NULL);
        }
        else if (GET_NEXT(next_block) == NULL && next_block == freerootptr)
        {
            freerootptr = block;
            SET_PREV(block, NULL);
            SET_NEXT(block, NULL);
        }
        else
        {
            SET_NEXT(block, freerootptr);
            SET_PREV(freerootptr, block);
            freerootptr = block;
            SET_PREV(block, NULL);
        }

        SET_NEXT(next_block, NULL);
        SET_PREV(next_block, NULL);



        block->block_size += next_header->block_size;
        footer_t* next_footer = get_footer(block);
        next_footer->block_size = block->block_size;

    }

    else if (!prev_alloc && next_alloc)
    { /* Case 3 */
        block_t* prev_block = (void*)prev_footer - prev_footer->block_size + sizeof(header_t);

        if (GET_PREV(prev_block) != NULL)
            SET_NEXT(GET_PREV(prev_block), GET_NEXT(prev_block));
        if (GET_NEXT(prev_block) != NULL)
            SET_PREV(GET_NEXT(prev_block), GET_PREV(prev_block));

        if (GET_NEXT(prev_block) != NULL && prev_block == freerootptr)
        {
            SET_PREV(GET_NEXT(freerootptr), prev_block);
        }
        else if (GET_NEXT(prev_block) == NULL && prev_block == freerootptr) {}
        else
        {
            SET_NEXT(prev_block, freerootptr);
            SET_PREV(freerootptr, prev_block);
            freerootptr = prev_block;
        }
        SET_PREV(prev_block, NULL);
        SET_PREV(block, NULL);
        SET_NEXT(block, NULL);

        prev_block->block_size += block->block_size;
        footer_t* footer = get_footer(prev_block);
        footer->block_size = prev_block->block_size;
        block = prev_block;
    }

    else { /* Case 4 */

        block_t* next_block = (void*)block + block->block_size;

        block_t* prev_block = (void*)prev_footer - prev_footer->block_size + sizeof(header_t);



        if (GET_NEXT(prev_block) == next_block)
        {
            if (GET_PREV(prev_block) != NULL)
            {
                SET_NEXT(GET_PREV(prev_block), GET_NEXT(next_block));
            }
            if (GET_NEXT(next_block) != NULL)
            {
                SET_PREV(GET_NEXT(next_block), GET_PREV(prev_block));
            }
            if (prev_block == freerootptr && GET_NEXT(next_block) != NULL)
            {
                freerootptr = GET_NEXT(next_block);
            }

            SET_NEXT(prev_block, NULL);
            SET_PREV(next_block, NULL);

            if (prev_block->body.prev == NULL && next_block->body.next == NULL) {}
            else
            {
                SET_NEXT(prev_block, freerootptr);
                SET_PREV(freerootptr, prev_block);
                freerootptr = prev_block;
                SET_PREV(freerootptr, NULL);
            }

            SET_NEXT(next_block, NULL);

        }
        else if (GET_NEXT(next_block) == prev_block)
        {
            if (GET_PREV(next_block) != NULL)
            {
                SET_NEXT(GET_PREV(next_block), GET_NEXT(prev_block));
            }
            if (GET_NEXT(prev_block) != NULL)
            {
                SET_PREV(GET_NEXT(prev_block), GET_PREV(next_block));
            }
            if (next_block == freerootptr && GET_NEXT(prev_block) != NULL)
            {
                freerootptr = GET_NEXT(prev_block);
            }


            SET_NEXT(next_block, NULL);
            SET_PREV(prev_block, NULL);

            if (GET_PREV(next_block) == NULL && GET_NEXT(prev_block) == NULL)
            {
                freerootptr = prev_block;
            }
            else if (GET_PREV(next_block) == NULL && GET_NEXT(prev_block) != NULL)
            {
                freerootptr = prev_block;
                SET_PREV(GET_NEXT(prev_block), prev_block);
            }
            else
            {
                SET_NEXT(prev_block, freerootptr);
                SET_PREV(freerootptr, prev_block);
                freerootptr = prev_block;
                SET_PREV(freerootptr, NULL);
            }

            SET_PREV(next_block, NULL);

        }
        else
        {
            if (GET_PREV(next_block) != NULL)
            {
                SET_NEXT(GET_PREV(next_block), GET_NEXT(next_block));
            }
            if (GET_NEXT(next_block) != NULL)
            {
                SET_PREV(GET_NEXT(next_block), GET_PREV(next_block));
            }

            if (GET_PREV(prev_block) != NULL)
            {
                SET_NEXT(GET_PREV(prev_block), GET_NEXT(prev_block));
            }
            if (GET_NEXT(prev_block) != NULL)
            {
                SET_PREV(GET_NEXT(prev_block), GET_PREV(prev_block));
            }


            if (prev_block != freerootptr && next_block != freerootptr)
            {
                SET_NEXT(prev_block, freerootptr);
                SET_PREV(freerootptr, prev_block);
                freerootptr = prev_block;
                SET_PREV(freerootptr, NULL);
            }

            else if (prev_block == freerootptr && next_block != freerootptr)
            {
                freerootptr->body.next->body.prev = prev_block;
                SET_PREV(GET_NEXT(freerootptr), prev_block);
                SET_PREV(freerootptr, NULL);
            }

            else if (prev_block != freerootptr && next_block == freerootptr)
            {
                SET_NEXT(prev_block, GET_NEXT(next_block));
                SET_PREV(GET_NEXT(next_block), prev_block);
                freerootptr = prev_block;
                SET_PREV(freerootptr, NULL);
            }



        }







        prev_block->block_size += block->block_size + next_header->block_size;
        /* Update footer of next block to reflect new size */
        footer_t* next_footer = get_footer(prev_block);
        next_footer->block_size = prev_block->block_size;
        block = prev_block;



    }

    return block;
}

static footer_t* get_footer(block_t* block) {
    return (void*)block + block->block_size - sizeof(footer_t);
}

static void printblock(block_t* block) {
    uint32_t hsize, halloc, fsize, falloc;

    hsize = block->block_size;
    halloc = block->allocated;
    footer_t* footer = get_footer(block);
    fsize = footer->block_size;
    falloc = footer->allocated;

    if (hsize == 0) {
        printf("%p: EOL\n", block);
        return;
    }

    printf("%p: header: [%d:%c] footer: [%d:%c]\n", block, hsize,
        (halloc ? 'a' : 'f'), fsize, (falloc ? 'a' : 'f'));
}

static void checkblock(block_t* block) {
    if ((uint64_t)block->body.payload % 8) {
        printf("Error: payload for block at %p is not aligned\n", block);
    }
    footer_t* footer = get_footer(block);
    if (block->block_size != footer->block_size) {
        printf("Error: header does not match footer\n");
    }
}
