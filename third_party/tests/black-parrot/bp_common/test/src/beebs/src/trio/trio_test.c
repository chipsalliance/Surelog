
/* BEEBS template benchmark

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
#include "trio.h"

/* This scale factor will be changed to equalise the runtime of the
   benchmarks. */
#define SCALE_FACTOR    (REPEAT_FACTOR >> 0)

#ifdef TRIO_SNPRINTF

/* This version of the benchmark does not support verification */

int
verify_benchmark (int res __attribute ((unused)) )
{
  return -1;
}


void
initialise_benchmark (void)
{
  init_heap ();			/* BEEBS memory allocator */
}


int
benchmark (void)
{
  char output[50];

  trio_snprintf(output, 50, "%d", 123);
  trio_snprintf(output, 50, "%ld", 123);
  trio_snprintf(output, 50, "%5d", 123);
  trio_snprintf(output, 50, "%05x", 123);
  trio_snprintf(output, 50, "%*d", 5, 10);

  return 0;
}
#elif TRIO_SSCANF

/* Global variables, so calls in BENCHMARK are not optimised away.  */
volatile int int_dest;
volatile char char_dest [20];


void
initialise_benchmark (void)
{
}


int
benchmark (void)
{
  trio_sscanf("123", "%d", &int_dest);
  trio_sscanf("123 456", "%d %d", &int_dest, &int_dest);
  trio_sscanf("000000123", "%d", &int_dest);
  trio_sscanf("abcdefg", "%x", &int_dest);
  trio_sscanf("FF", "%x",&int_dest);
  trio_sscanf("abcdefg", "%[^f]%xg", char_dest, &int_dest);

  return 0;
}

int verify_benchmark(int unused) {
  int expected = 15;
  if (int_dest != expected)
    return 0;
  return 1;
}
#else
#error "Missing a TRIO_SSCANF or TRIO_SNPRINTF macro"
#endif


