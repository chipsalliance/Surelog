/* -*- mode: C++; c-file-style: "gnu-mode" -*- */
/* BEEBS vector benchmark

   Copyright (C) 2013 Embecosm Limited and University of Bristol

   Contributor: James Pallister <james.pallister@bristol.ac.uk>

   This file is part of the Bristol/Embecosm Embedded Benchmark Suite.

   This program is free software: you can redistribute it and/or modify
   it under the terms of the GNU General Public License as published by
   the Free Software Foundation, either version 3 of the License, or
   (at your option) any later version.

   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
   GNU General Public License for more details.

   You should have received a copy of the GNU General Public License
   along with this program. If not, see <http://www.gnu.org/licenses/>. */

#include "support.h"

/* This scale factor will be changed to equalise the runtime of the
   benchmarks. */
#define SCALE_FACTOR    (REPEAT_FACTOR >> 0)

typedef struct {
  int a, b;
} pair;

/* BEEBS heap is just an array */

#include <stddef.h>

#define HEAP_SIZE 8192
static char heap[HEAP_SIZE];
static void *heap_ptr;
static void *heap_end;

/* Initialize the BEEBS heap pointers */

static void
init_heap ()
{
    heap_ptr = (void *) heap;
    heap_end = heap_ptr + HEAP_SIZE;
}

/* BEEBS version of malloc.

   This is primarily to reduce library and OS dependencies. Malloc is
   generally not used in embedded code, or if it is, only in well defined
   contexts to pre-allocate a fixed amount of memory. So this simplistic
   implementation is just fine. */

static void *
malloc_beebs (size_t size)
{
    void *new_ptr = heap_ptr;

    if (((heap_ptr + size) > heap_end) || (0 == size))
	return NULL;
    else
	{
	    heap_ptr += size;
	    return new_ptr;
	}
}

/* BEEBS version of free.

   For our simplified version of memory handling, free can just do nothing. */

static void
free_beebs (void *ptr)
{
}

#ifdef CTL_VECTOR
#include "vector.h"

/* Create vector functions for different types.  */
MAKE_VECTOR(int)
MAKE_VECTOR(pair)

/* Container types.  */
typedef ctl_intVector int_container;
typedef ctl_pairVector pair_container;

#define CTL_INIT(type) ctl_##type##VectorInit ()
#define CTL_PUSH(type, vec, val) ctl_ ## type ## VectorPush_Back(vec, val)
#define CTL_DELETE(type, vec, a, b) ctl_ ## type ## VectorDelete(vec, a, b)
#define CTL_POP(type, vec, res) ctl_ ## type ## VectorPop_Back(vec, res)
#define CTL_FREE(type, vec) ctl_ ## type ## VectorFree(vec)

#elif defined CTL_STACK
#include "stack.h"

/* Create stack functions for different types.  */
MAKE_STACK(int)
MAKE_STACK(pair)

/* Container types.  */
typedef ctl_intStack int_container;
typedef ctl_pairStack pair_container;

#define CTL_INIT(type) ctl_ ## type ## StackInit ()
#define CTL_PUSH(type, stk, val) ctl_ ## type ## StackPush (stk, val)
#define CTL_POP(type, stk, res) ctl_ ## type ## StackPop (stk, res)
#define CTL_FREE(type, stk) ctl_ ## type ## StackFree (stk)

/* There's no DELETE for stacks.  */
#define CTL_DELETE(type, vec, a, b) do { } while (0)


#else
#error "Expected CTL_VECTOR or CTL_STACK to be defined"
#endif

static int init;
static int lim;
static int fact;
static int begin;
static int end;
static int end2;

int
benchmark (void)
{
  int_container *v;
  pair_container *v2;

  int cnt=0, i;

  v = CTL_INIT (int);

  for (i = init; i <= lim; ++i)
    CTL_PUSH (int, v, i * fact);

  CTL_DELETE (int, v, begin, end);

  while(v->size > 0)
  {
    int k;

    CTL_POP (int, v, &k);

    cnt += k;
  }

  CTL_FREE (int, v);

  v2 = CTL_INIT (pair);

  for (i = init; i <= lim; ++i)
  {
    pair p = {i, i*i};
    CTL_PUSH (pair, v2, p);
  }

  CTL_DELETE (pair, v2, begin, end2);

  while(v2->size > 0)
  {
    pair k;

    CTL_POP (pair, v2, &k);

    cnt += k.a*k.b;
  }

  CTL_FREE (pair, v2);

  return cnt;
}

void initialise_benchmark() {
  init = 1;
  lim = 100;
  fact = 11;
  begin = 4;
  end = 50;
  end2 = 8;
  init_heap ();
}

int verify_benchmark(int r)
{
#ifdef CTL_VECTOR
  int expected = 25542939;
#elif defined CTL_STACK
  int expected = 25558050;
#else
#error "Expected CTL_VECTOR or CTL_STACK to be defined"
#endif
  if (r != expected)
    return 0;
  return 1;
}


