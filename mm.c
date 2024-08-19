/*
 * mm-naive.c - The fastest, least memory-efficient malloc package.
 *
 * In this naive approach, a block is allocated by simply incrementing
 * the brk pointer.  A block is pure payload. There are no headers or
 * footers.  Blocks are never coalesced or reused. Realloc is
 * implemented directly using mm_malloc and mm_free.
 *
 * NOTE TO STUDENTS: Replace this header comment with your own header
 * comment that gives a high level description of your solution.
 */
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
    /* Team name */
    "ateam",
    /* First member's full name */
    "Harry Bovik",
    /* First member's email address */
    "bovik@cs.cmu.edu",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~0x7)

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

// basic constants and macros
#define WSIZE 4             // word and header/footer size
#define DSIZE 8             // double word size
#define CHUNKSIZE (1 << 12) // heap을 4kb로 늘린다

#define MAX(x, y) ((x) > (y) ? (x) : (y)) // x,y 중 큰 값을 가진다

#define GET(p) (*(unsigned int *)(p))              // 포인터를 써서 p를 참조한다
#define PUT(p, val) (*(unsigned int *)(p) = (val)) // 포인터를 써서 p를 참조한다. 주소와 값을 알 수 있다. 다른 블록을 가리키거나 이동할 때 쓸 수 있다.

#define PACK(size, alloc) ((size) | (alloc)) // size 와 alloc 을 비트 OR 연산으로 결합하여 하나의 값을 만든다. 메모리 할당기에서 블록의 크기와 할당 상태를 함께 저장할 때 사용

#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

/* 새로운 free block ptr bp, header와 footer의 주소를 계산*/
#define HDRP(bp) ((char *)(bp) - WSIZE) // bp가 어디에 있던 상관없이 WSIZE 앞에 위치한다
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/*Given block ptr bp, compute address of next and previous blocks*/
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE))) // 그 다음 블록의 bp위치로 이동
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE))) // 그 전 블록의 bp위치로 이동
static char *heap_listp;
static char *recently_alloc;

static void *extend_heap(size_t words);
static void *coalesce(void *bp);

static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);

/*
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    // 힙을 초기 사이즈 만큼 세팅한다.//
    if ((heap_listp = mem_sbrk(4 * WSIZE)) == (void *)-1)
        return -1;
    PUT(heap_listp, 0);                            // 가용 리스트에 패딩을 넣는다 //
    PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1)); // 가용 리스트에 프롤로그 헤더를 넣는다.
    PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1)); // 가용 리스트에 프롤로그 푸터를 넣는다.
    PUT(heap_listp + (3 * WSIZE), PACK(0, 1));     // 가용 리스트에 에필로그 헤더를 넣는다.
    heap_listp += (2 * WSIZE);                     // 이제 포인터를 옮긴다. 다른 블록으로 이동해서 값을 넣어주려고

    if (extend_heap(CHUNKSIZE / WSIZE) == NULL)
        return -1;

    return 0;
}

/*
    extend_heap 구현
    mm_init()함수 도중에 heap을 특정사이즈 만큼 증가시키는 함수를 만들것이다.
*/

static void *extend_heap(size_t words)
{
    char *bp; // block pointer
    size_t size;
    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE; // (word%2) 홀수이면 (words+1) *WSIZE이고 , (word%2) 짝수이면 words * WSIZE이다.

    if ((long)(bp = mem_sbrk(size)) == -1) // bp를 mem_sbrk 반환값으로 옮긴다
    {
        return NULL;
    }

    PUT(HDRP(bp), PACK(size, 0));         // free block header 생성.
    PUT(FTRP(bp), PACK(size, 0));         // free block footer 생성.
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); // 블록을 추가했으니 epilogue header를 새롭게 위치 조정해줌

    return coalesce(bp);
}

static void *coalesce(void *bp)
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    if (prev_alloc && next_alloc) // 이전과 다음 블록이 모두 할당되어있다
    {
        return bp;
    }
    else if (prev_alloc && !next_alloc) // CASE 1) 다음 블록만 가용블록인 상태
    {
        size += GET_SIZE(HDRP(NEXT_BLKP(bp))); // 다음 블록의 헤더를 보고 그 블록의 크기 만큼 size를 추가해준다.
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }
    else if (!prev_alloc && next_alloc) // CASE 2) 이전 블록만 가용블록인 상태
    {
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    else // CASE 3) 이전 블록과 다음 블록 모두 가용 블록인 상태
    {
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    recently_alloc = bp;
    return bp;
}

/*
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    size_t asize;
    size_t extendsize;
    char *bp;

    if (size == 0)
        return NULL;
    // 사이즈 조정
    if (size <= DSIZE)
    {
        asize = 2 * DSIZE;
    }
    else
    {
        // asize = DSIZE * ((size + (DSIZE) + (DSIZE - 1)) / DSIZE);
        asize = ALIGN(size + SIZE_T_SIZE);
    }

    // fit에 맞는 free 리스트를 찾는다
    if ((bp = find_fit(asize)) != NULL)
    {
        place(bp, asize);
        return bp;
    }

    // fit 맞는게 없어! 힙 메모리를 확장시켜서 block 를 위치시킨다
    extendsize = MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap(extendsize / WSIZE)) == NULL)
    {
        return NULL;
    }
    place(bp, asize);
    return bp;
}

static void *find_fit(size_t asize) // first fit 검색 수행 -> next fit 검색
{
    void *bp;
    if (recently_alloc == NULL)
    {
        recently_alloc = heap_listp;
    }

    for (bp = recently_alloc; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp))
    {
        if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp))))
        {
            recently_alloc = bp;
            return bp;
        }
    }

    for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp))
    {
        if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp))))
        {
            return bp;
        }
    }
    return NULL;
}

static void place(void *bp, size_t asize)
{
    size_t csize = GET_SIZE(HDRP(bp)); // 현재 블록의 사이즈 구하기

    if ((csize - asize) >= (2 * DSIZE))
    {
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(csize - asize, 0));
        PUT(FTRP(bp), PACK(csize - asize, 0));
    }
    else
    {
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *bp)
{
    size_t size = GET_SIZE(HDRP(bp));
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    coalesce(bp);
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *bp, size_t size)
{
    if (size <= 0)
    {
        mm_free(bp);
        return 0;
    }

    if (bp == NULL)
    {
        return mm_malloc(size);
    }

    void *newp = mm_malloc(size);
    if (newp == NULL)
    {
        return 0;
    }
    size_t oldsize = GET_SIZE(HDRP(bp));
    if (size < oldsize)
    {
        oldsize = size;
    }
    memcpy(newp, bp, oldsize);
    mm_free(bp);
    return newp;
}