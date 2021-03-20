/* This file is part of the Bristol/Embecosm Embedded Benchmark Suite.

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

/* The original LICENCE file that
 * accompanied this source file:
 **********************************
 *                                *
 * Matt hacked this together.     *
 *                                *
 * It is GPL'ed.                  *
 *                                *
 **********************************/

#include <stdio.h>
#include <stdlib.h>

#include "support.h"

/* This scale factor will be changed to equalise the runtime of the
   benchmarks. */
#define SCALE_FACTOR    (REPEAT_FACTOR >> 9)

#define NUM_NODES                          10
#define NONE                               9999

struct _NODE
{
   int iDist;
   int iPrev;
};
typedef struct _NODE NODE;

struct _QITEM
{
   int iNode;
   int iDist;
   int iPrev;
   struct _QITEM *qNext;
};
typedef struct _QITEM QITEM;

QITEM *qHead = NULL;

int AdjMatrix[NUM_NODES][NUM_NODES] = {{32,  32,  54,  12,  52,  56,  8,   30,  44,  94},
   {76,  54,  65,  14,  89,  69,  4,   16,  24,  47},
   {38,  31,  75,  40,  61,  21,  84,  51,  86,  41},
   {80,  16,  53,  14,  94,  29,  77,  99,  16,  29},
   {59,  7,   14,  78,  79,  45,  54,  83,  8,   94},
   {94,  41,  3,   61,  27,  19,  33,  35,  78,  38},
   {3,   55,  41,  76,  49,  68,  83,  23,  67,  15},
   {68,  28,  47,  12,  82,  6,   26,  96,  98,  75},
   {7,   1,   46,  39,  12,  68,  41,  28,  31,  0},
   {82,  97,  72,  61,  39,  48,  11,  99,  38,  49}};

int g_qCount = 0;
NODE rgnNodes[NUM_NODES];
int ch;
int iPrev, iNode;
int i, iCost, iDist;


/* BEEBS heap is just an array */

#include <stddef.h>

#define QHEAP_SIZE (8192 / sizeof (QITEM))
static QITEM qheap[QHEAP_SIZE];
static QITEM *qfree_list;

/* Initialize the BEEBS heap.

   Because we know the size of objects is always the same, we have a
   specially hacked version of malloc */

static void
qinit_heap (void)
{
  qfree_list = NULL;
  int  i;

  for (i = 0; i < QHEAP_SIZE; i++)
    {
      qheap[i].qNext = qfree_list;
      qfree_list = &(qheap[i]);
    }
}

/* BEEBS version of malloc.

   This is primarily to reduce library and OS dependencies. This is unusual
   for an embedded program in its dynamic use of malloc and free.  However we
   know that malloc is always used with the same sized object, so we cheat. */

static void *
qmalloc_beebs (size_t size)
{
  if ((size != sizeof(QITEM)) || (0 == size))
    return NULL;

  QITEM *new_ptr = qfree_list;

  if (new_ptr != NULL)
    {
      qfree_list = new_ptr->qNext;
    }

  return (void *) new_ptr;
}

/* BEEBS version of free.

   Even our simplified version has to work correctly, or we'll run out of
   memory. Assume we are given a valid pointer to a QITEM - there is no way
   to check. */

static void
qfree_beebs (void *ptr)
{
  QITEM *qptr = (QITEM *) ptr;

  qptr->qNext = qfree_list;
  qfree_list = qptr;
}


void enqueue (int iNode, int iDist, int iPrev)
{
   QITEM *qNew = (QITEM *) qmalloc_beebs(sizeof(QITEM));
   QITEM *qLast = qHead;

   qNew->iNode = iNode;
   qNew->iDist = iDist;
   qNew->iPrev = iPrev;
   qNew->qNext = NULL;

   if (!qLast)
   {
      qHead = qNew;
   }
   else
   {
      while (qLast->qNext) qLast = qLast->qNext;
      qLast->qNext = qNew;
   }
   g_qCount++;
}


QITEM* dequeue (int *piNode, int *piDist, int *piPrev)
{
   QITEM *qKill = qHead;

   if (qHead != 0)
   {
      *piNode = qHead->iNode;
      *piDist = qHead->iDist;
      *piPrev = qHead->iPrev;
      qHead = qHead->qNext;
      g_qCount--;
      return qKill;
   }
   return 0;
}


int qcount (void)
{
   return(g_qCount);
}

int dijkstra(int chStart, int chEnd)
{
   for (ch = 0; ch < NUM_NODES; ch++)
   {
      rgnNodes[ch].iDist = NONE;
      rgnNodes[ch].iPrev = NONE;
   }

   if (chStart == chEnd)
   {
      return 0;
   }
   else
   {
      rgnNodes[chStart].iDist = 0;
      rgnNodes[chStart].iPrev = NONE;

      enqueue (chStart, 0, NONE);

      while (qcount() > 0)
      {
         QITEM *tmp = dequeue (&iNode, &iDist, &iPrev);
         if(tmp != 0)
            qfree_beebs(tmp);
         for (i = 0; i < NUM_NODES; i++)
         {
            iCost = AdjMatrix[iNode][i];
            if (iCost != NONE)
            {
               if ((NONE == rgnNodes[i].iDist) ||
                     (rgnNodes[i].iDist > (iCost + iDist)))
               {
                  rgnNodes[i].iDist = iDist + iCost;
                  rgnNodes[i].iPrev = iNode;
                  enqueue (i, iDist + iCost, iNode);
               }
            }
         }
      }
   }

   return rgnNodes[chEnd].iDist;
}

int output[NUM_NODES * NUM_NODES];
int output_count = 0;

void
initialise_benchmark (void)
{
  qinit_heap ();		/* Set up the BEEBS QITEM heap */
}



int benchmark() {
   int i,j;

   output_count = 0;

   /* finds 10 shortest paths between nodes */
   for(j = 0; j < NUM_NODES; j++) {
      for (i=0; i < NUM_NODES; i++) {
         output[output_count] = dijkstra(i,j);
         output_count++;
      }
   }

   return 0;
}

int verify_benchmark(int unused) {
   int expected[] = {0, 7, 38, 23, 14, 36, 3, 29, 7, 14, 28, 0, 31, 16, 7, 34,
   31, 28, 1, 39, 39, 25, 0, 32, 14, 3, 32, 9, 26, 43, 12, 14, 40, 0, 21, 43,
   15, 12, 15, 26, 40, 36, 48, 28, 0, 27, 43, 33, 12, 39, 36, 22, 21, 29, 29,
   0, 29, 6, 23, 40, 8, 4, 35, 20, 11, 33, 0, 26, 5, 11, 30, 16, 47, 32, 23,
   35, 23, 0, 17, 34, 28, 24, 55, 16, 8, 35, 31, 28, 0, 38, 23, 19, 41, 16, 8,
   35, 15, 28, 0, 0};
   int i;
   for (i=0; i<NUM_NODES*NUM_NODES; i++) {
      if (output[i] != expected[i]) {
         return 0;
      }
//      printf("%d, ", output[i]);
   }
   return 1;
}

/* vim: set ts=3 sw=3 et: */
