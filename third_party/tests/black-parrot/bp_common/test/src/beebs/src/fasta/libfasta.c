/* BEEBS fasta benchmark

   Copyright (C) 2014 Embecosm Limited and University of Bristol

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

/* The original source code for this benchmark can be found here:

     http://benchmarksgame.alioth.debian.org/

   and was released under the following licence, disclaimers, and
   copyright:

   Revised BSD license

   This is a specific instance of the Open Source Initiative (OSI) BSD
   license template http://www.opensource.org/licenses/bsd-license.php

   Copyright 2004-2009 Brent Fulgham
   All rights reserved.

   Redistribution and use in source and binary forms, with or without
   modification, are permitted provided that the following conditions
   are met:

   Redistributions of source code must retain the above copyright
   notice, this list of conditions and the following disclaimer.

   Redistributions in binary form must reproduce the above copyright
   notice, this list of conditions and the following disclaimer in the
   documentation and/or other materials provided with the
   distribution.

   Neither the name of "The Computer Language Benchmarks Game" nor the
   name of "The Computer Language Shootout Benchmarks" nor the names
   of its contributors may be used to endorse or promote products
   derived from this software without specific prior written
   permission.

   THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
   "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
   LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS
   FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE
   COPYRIGHT OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT,
   INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
   (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
   SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
   HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT,
   STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE)
   ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED
   OF THE POSSIBILITY OF SUCH DAMAGE.  */

#include <string.h>
#include <stdlib.h>

#include "support.h"

#define SCALE_FACTOR   (REPEAT_FACTOR >> 6)

#define WIDTH 60
#define MIN(a,b) ((a) <= (b) ? (a) : (b))
#define NELEMENTS(x) (sizeof (x) / sizeof ((x)[0]))

typedef struct {
    float p;
    char c;
} aminoacid_t;

static inline float myrandom (float max) {
    unsigned long const IM = 139968;
    unsigned long const IA = 3877;
    unsigned long const IC = 29573;
    static unsigned long last = 42;
    last = (last * IA + IC) % IM;
    /*Integer to float conversions are faster if the integer is signed*/
    return max * (long) last / IM;
}

static inline void accumulate_probabilities (aminoacid_t *genelist, size_t len) {
    float cp = 0.0;
    size_t i;
    for (i = 0; i < len; i++) {
        cp += genelist[i].p;
        genelist[i].p = cp;
    }
}

/* This function prints the characters of the string s. When it */
/* reaches the end of the string, it goes back to the beginning */
/* It stops when the total number of characters printed is count. */
/* Between each WIDTH consecutive characters it prints a newline */
/* This function assumes that WIDTH <= strlen (s) + 1 */
static void repeat_fasta (char const *s, size_t count) {
    size_t pos = 0;
    size_t len = strlen (s);
    /* BEEBS uses alloca, to avoid library and OS dependencies
       char *s2 = malloc (len + WIDTH); */
    char *s2 = alloca (len + WIDTH);
    memcpy (s2, s, len);
    memcpy (s2 + len, s, WIDTH);
    do {
     	size_t line = MIN(WIDTH, count);
        /*fwrite_unlocked (s2 + pos,1,line,stdout);
          putchar_unlocked ('\n'); */
     	pos += line;
     	if (pos >= len) pos -= len;
     	count -= line;
    } while (count);
    /* Since BEEBS uses alloca don't try to free!
       free (s2);*/
}

/* This function takes a pointer to the first element of an array */
/* Each element of the array is a struct with a character and */
/* a float number p between 0 and 1. */
/* The function generates a random float number r and */
/* finds the first array element such that p >= r. */
/* This is a weighted random selection. */
/* The function then prints the character of the array element. */
/* This is done count times. */
/* Between each WIDTH consecutive characters, the function prints a newline */
static void random_fasta (aminoacid_t const *genelist, size_t count) {
    do {
	size_t line = MIN(WIDTH, count);
	size_t pos = 0;
	char buf[WIDTH + 1];
	do {
	    float r = myrandom (1.0);
	    size_t i = 0;
	    while (genelist[i].p < r)
		++i; /* Linear search */
	    buf[pos++] = genelist[i].c;
	} while (pos < line);
	buf[line] = '\n';
	/*fwrite_unlocked (buf, 1, line + 1, stdout);    */
	(void) buf; /* Silence compiler warning about unused 'buf'.  */
	count -= line;
    } while (count);
}


/* This benchmark does not support verification */

int
verify_benchmark (int res __attribute ((unused)) )
{
  return -1;
}


void
initialise_benchmark (void)
{
}



int benchmark () {
  const int n = 1000;

    static aminoacid_t iub[] = {
	{ 0.27, 'a' },
	{ 0.12, 'c' },
	{ 0.12, 'g' },
	{ 0.27, 't' },
	{ 0.02, 'B' },
	{ 0.02, 'D' },
	{ 0.02, 'H' },
	{ 0.02, 'K' },
	{ 0.02, 'M' },
	{ 0.02, 'N' },
	{ 0.02, 'R' },
	{ 0.02, 'S' },
	{ 0.02, 'V' },
	{ 0.02, 'W' },
	{ 0.02, 'Y' }};

    static aminoacid_t homosapiens[] = {
	{ 0.3029549426680, 'a' },
	{ 0.1979883004921, 'c' },
	{ 0.1975473066391, 'g' },
	{ 0.3015094502008, 't' }};

    accumulate_probabilities (iub, NELEMENTS(iub));
    accumulate_probabilities (homosapiens, NELEMENTS(homosapiens));

    static char const *const alu ="\
GGCCGGGCGCGGTGGCTCACGCCTGTAATCCCAGCACTTTGG\
GAGGCCGAGGCGGGCGGATCACCTGAGGTCAGGAGTTCGAGA\
CCAGCCTGGCCAACATGGTGAAACCCCGTCTCTACTAAAAAT\
ACAAAAATTAGCCGGGCGTGGTGGCGCGCGCCTGTAATCCCA\
GCTACTCGGGAGGCTGAGGCAGGAGAATCGCTTGAACCCGGG\
AGGCGGAGGTTGCAGTGAGCCGAGATCGCGCCACTGCACTCC\
AGCCTGGGCGACAGAGCGAGACTCCGTCTCAAAAA";

    /*fputs_unlocked (">ONE Homo sapiens alu\n", stdout);*/
    repeat_fasta (alu, 2 * n);
    /*fputs_unlocked (">TWO IUB ambiguity codes\n", stdout);*/
    random_fasta (iub, 3 * n);
    /*fputs_unlocked (">THREE Homo sapiens frequency\n", stdout);*/
    random_fasta (homosapiens, 5 * n);
    return 0;
}

