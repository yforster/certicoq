#include <string.h>
#include <stdlib.h>
#include <stdio.h>
#include <assert.h>
#include "config.h"
#include "values.h"
#include "gc.h"

/* This is an alternate implementation of the gc.h interface,
   that does no garbage collection.  Useful for debugging 
   both programs and proofs. */

#define SIZE (1<<21)  /* 2 million words */

struct heap {
  value *start, *next, *limit;
  value space [SIZE];
};


void resume(struct fun_info *fi, struct thread_info *ti)
/* When the garbage collector is all done, it does not "return"
   to the mutator; instead, it uses this function (which does not return)
   to resume the mutator by invoking the continuation, fi->fun.  
   But first, "resume" informs the mutator
   of the new values for the alloc and limit pointers.
*/
 {
  void (*f)(void);
  struct heap *h = ti->heap;
  value *lo, *hi;
  assert (h);
  lo = h->start;
  hi = h->limit;
  if (hi-lo < fi->num_allocs) {
    fprintf(stderr, "Heap is too small for function's num_allocs\n");
    exit(1);
  }
  f = fi->fun;
  *ti->alloc = lo;
  *ti->limit = hi;
  (*f)();
}  

void garbage_collect(struct fun_info *fi, struct thread_info *ti) {
  struct heap *h = ti->heap;
  if (h==NULL) {
    /* If the heap has not yet been initialized, create it and resume */
    h = (struct heap *) malloc (sizeof *h);
    h->start = h->space;
    h->next = h->space;
    h->limit = h->space+SIZE;
    ti->heap = h;
    resume(fi,ti);
  } else {
    fprintf(stderr, "Ran out of heap, and no garbage collector present!\n");
    exit(1);
  }
}
  

void free_heap(struct heap *h) {
  free(h);
}

void reset_heap(struct heap *h) {
  h->next = h->start;
}
