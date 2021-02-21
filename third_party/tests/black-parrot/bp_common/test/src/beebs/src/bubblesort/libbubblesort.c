/* BEEBS bsort100 benchmark

   Copyright (C) 2014 Embecosm Limited and University of Bristol

   Contributor James Pallister <james.pallister@bristol.ac.uk>

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
#define SCALE_FACTOR    (REPEAT_FACTOR >> 4)

#define WORSTCASE 1
#define FALSE 0
#define TRUE 1
#define NUMELEMS 100
#define MAXDIM   (NUMELEMS+1)

// void Initialize(int Array []);
void BubbleSort(int Array []);

/* BUBBLESORT BENCHMARK PROGRAM:
 * This program tests the basic loop constructs, integer comparisons,
 * and simple array handling of compilers by sorting 10 arrays of
 * randomly generated integers.
 */

int Array[MAXDIM], Seed;
int factor;

void BubbleSort(int Array[]);
// void Initialize(int Array[]);

int benchmark()
{
   BubbleSort(Array);
   return 0;
}


void initialise_benchmark()
/*
 * Initializes given array with randomly generated integers.
 */
{
   int  Index, fact;

#ifdef WORSTCASE
   factor = -1;
#else
   factor = 1;
#endif

fact = factor;
for (Index = 0; Index < NUMELEMS; Index ++)
    Array[Index] = Index*fact;
}



void BubbleSort(int Array[])
/*
 * Sorts an array of integers of size NUMELEMS in ascending order.
 */
{
   int Sorted = FALSE;
   int Temp, Index, i;

   for (i = 0; i < NUMELEMS; i++)
   {
      Sorted = TRUE;
      for (Index = 0; Index < NUMELEMS; Index ++) {
         if (Index >= NUMELEMS-i)
            break;
         if (Array[Index] > Array[Index + 1])
         {
            Temp = Array[Index];
            Array[Index] = Array[Index+1];
            Array[Index+1] = Temp;
            Sorted = FALSE;
         }
      }

      if (Sorted)
         break;
   }
}

int verify_benchmark(int result) {
   int expected[NUMELEMS] = {-99, -98, -97, -96, -95, -94, -93, -92,
                             -91, -90, -89, -88, -87, -86, -85, -84, -83, -82,
                             -81, -80, -79, -78, -77, -76, -75, -74, -73, -72,
                             -71, -70, -69, -68, -67, -66, -65, -64, -63, -62,
                             -61, -60, -59, -58, -57, -56, -55, -54, -53, -52,
                             -51, -50, -49, -48, -47, -46, -45, -44, -43, -42,
                             -41, -40, -39, -38, -37, -36, -35, -34, -33, -32,
                             -31, -30, -29, -28, -27, -26, -25, -24, -23, -22,
                             -21, -20, -19, -18, -17, -16, -15, -14, -13, -12,
                             -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0};
   int i;
   for (i=0; i<NUMELEMS; i++) {
      if (Array[i] != expected[i])
         return 0;
   }
   return 1;
}

