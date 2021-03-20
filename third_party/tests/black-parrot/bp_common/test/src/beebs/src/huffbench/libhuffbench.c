/* BEEBS cover benchmark

    huffbench
    Standard C version
    17 April 2003

    Written by Scott Robert Ladd (scott@coyotegulch.com)
    No rights reserved. This is public domain software, for use by anyone.

    A data compression benchmark that can also be used as a fitness test
    for evolving optimal compiler options via genetic algorithm.

    This program implements the Huffman compression algorithm. The code
    is not the tightest or fastest possible C code; rather, it is a
    relatively straight-forward implementation of the algorithm,
    providing opportunities for an optimizer to "do its thing."

    Note that the code herein is design for the purpose of testing
    computational performance; error handling and other such "niceties"
    is virtually non-existent.

    Actual benchmark results can be found at:
            http://www.coyotegulch.com

    Please do not use this information or algorithm in any way that might
    upset the balance of the universe or otherwise cause the creation of
    singularities.

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
   along with this program. If not, see <http://www.gnu.org/licenses/>.

*/

#include <string.h>
#include <stdio.h>
#include <stdlib.h>
#include <stddef.h>
#include <stdbool.h>
#include <math.h>

#include "support.h"

/* This scale factor will be changed to equalise the runtime of the
   benchmarks. */
#define SCALE_FACTOR    (REPEAT_FACTOR >> 0)


/* BEEBS heap is just an array */

#include <stddef.h>

#define HEAP_SIZE 8192
static char heap[HEAP_SIZE];
static void *heap_ptr;
static void *heap_end;

/* Initialize the BEEBS heap pointers */

static void
init_heap (void)
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

// embedded random number generator; ala Park and Miller
static       long seed = 1325;
static const long IA   = 16807;
static const long IM   = 2147483647;
static const long IQ   = 127773;
static const long IR   = 2836;
static const long MASK = 123459876;

// return index between 0 and 3
static size_t random4()
{
    long k;
    size_t result;

    seed ^= MASK;
    k = seed / IQ;
    seed = IA * (seed - k * IQ) - IR * k;

    if (seed < 0L)
        seed += IM;

    result = (size_t)(seed % 32L);
    seed ^= MASK;

    return result;
}


static const int TEST_SIZE =  500;

typedef unsigned long bits32;
typedef unsigned char byte;

// compressed (encoded) data

byte * generate_test_data(size_t n)
{
    char * codes = "ABCDEFGHIJKLMNOPQRSTUVWXYZ012345";

    byte * result = (byte *)malloc_beebs(n);
    byte * ptr = result;

    int i;
    for (i = 0; i < n; ++i)
    {
        *ptr = (byte)codes[random4()];
        ++ptr;
    }

    return result;
}

// utility function for processing compression trie
static void heap_adjust(size_t * freq, size_t * heap, int n, int k)
{
    // this function compares the values in the array
    // 'freq' to order the elements of 'heap' according
    // in an inverse heap. See the chapter on priority
    // queues and heaps for more explanation.
    int j;

    --heap;

    int v = heap[k];

    while (k <= (n / 2))
    {
        j = k + k;

        if ((j < n) && (freq[heap[j]] > freq[heap[j+1]]))
            ++j;

        if (freq[v] < freq[heap[j]])
            break;

        heap[k] = heap[j];
        k = j;
    }

    heap[k] = v;
}

// Huffman compression/decompression function
void compdecomp(byte * data, size_t data_len)
{
    size_t i, j, n, mask;
    bits32 k, t;
    byte   c;
    byte * cptr;
    byte * dptr = data;

    /*
        COMPRESSION
    */

    // allocate data space
    byte * comp = (byte *)malloc_beebs(data_len + 1);

    size_t freq[512];   // allocate frequency table
    size_t heap[256];   // allocate heap
    int    link[512];   // allocate link array
    bits32 code[256];   // huffman codes
    byte   clen[256];   // bit lengths of codes

    memset(comp,0,sizeof(byte)   * (data_len + 1));
    memset(freq,0,sizeof(size_t) * 512);
    memset(heap,0,sizeof(size_t) * 256);
    memset(link,0,sizeof(int)    * 512);
    memset(code,0,sizeof(bits32) * 256);
    memset(clen,0,sizeof(byte)   * 256);

    // count frequencies
    for (i = 0; i < data_len; ++i)
    {
        ++freq[(size_t)(*dptr)];
        ++dptr;
    }

    // create indirect heap based on frequencies
    n = 0;

    for (i = 0; i < 256; ++i)
    {
        if (freq[i])
        {
            heap[n] = i;
            ++n;
        }
    }

    for (i = n; i > 0; --i)
        heap_adjust(freq,heap,n,i);

    // generate a trie from heap
    size_t temp;

    // at this point, n contains the number of characters
    // that occur in the data array
    while (n > 1)
    {
        // take first item from top of heap
        --n;
        temp    = heap[0];
        heap[0] = heap[n];

        // adjust the heap to maintain properties
        heap_adjust(freq,heap,n,1);

        // in upper half of freq array, store sums of
        // the two smallest frequencies from the heap
        freq[256 + n] = freq[heap[0]] + freq[temp];
        link[temp]    =  256 + n; // parent
        link[heap[0]] = -256 - n; // left child
        heap[0]       =  256 + n; // right child

        // adjust the heap again
        heap_adjust(freq,heap,n,1);
    }

    link[256 + n] = 0;

    // generate codes
    size_t m, x, maxx = 0, maxi = 0;
    int l;

    for (m = 0; m < 256; ++m)
    {
        if (!freq[m]) // character does not occur
        {
            code[m] = 0;
            clen[m] = 0;
        }
        else
        {
            i = 0;       // length of current code
            j = 1;       // bit being set in code
            x = 0;       // code being built
            l = link[m]; // link in trie

            while (l) // while not at end of trie
            {
                if (l < 0) // left link (negative)
                {
                    x +=  j; // insert 1 into code
                    l  = -l; // reverse sign
                }

                l  = link[l]; // move to next link
                j <<= 1;      // next bit to be set
                ++i;          // increment code length
            }

            code[m] = (unsigned long)x; // save code
            clen[m] = (unsigned char)i; // save code len

            // keep track of biggest key
            if (x > maxx)
                maxx = x;

            // keep track of longest key
            if (i > maxi)
                maxi = i;
        }
    }

    // make sure longest codes fit in unsigned long-bits
    if (maxi > (sizeof(unsigned long) * 8))
    {
        return;
    }

    // encode data
    size_t comp_len =  0;   // number of data_len output
    char   bout =  0;   // byte of encoded data
    int    bit  = -1;   // count of bits stored in bout
    dptr = data;

    // watch for one-value file!
    if (maxx == 0)
    {
        return;
    }

    for (j = 0; j < data_len; ++j)
    {
        // start copying at first bit of code
        mask = 1 << (clen[(*dptr)] - 1);

        // copy code bits
        for (i = 0; i < clen[(*dptr)]; ++i)
        {
            if (bit == 7)
            {
                // store full output byte
                comp[comp_len] = bout;
                ++comp_len;

                // check for output longer than input!
                if (comp_len == data_len)
                {
                    return;
                }

                bit  = 0;
                bout = 0;
            }
            else
            {
                // move to next bit
                ++bit;
                bout <<= 1;
            }

            if (code[(*dptr)] & mask)
                bout |= 1;

            mask >>= 1;
        }

        ++dptr;
    }

    // output any incomplete data_len and bits
    bout <<= (7 - bit);
    comp[comp_len] = bout;
    ++comp_len;

    // printf("data len = %u\n",data_len);
    // printf("comp len = %u\n",comp_len);

    /*
        DECOMPRESSION
    */

    // allocate heap2
    bits32 heap2[256];

    // allocate output character buffer
    char outc[256];

    // initialize work areas
    memset(heap2,0,256 * sizeof(bits32));

    // create decode table as trie heap2
    char * optr = outc;

    for (j = 0; j < 256; ++j)
    {
        (*optr) = (char)j;
        ++optr;

        // if code exists for this byte
        if (code[j] | clen[j])
        {
            // begin at first code bit
            k = 0;
            mask = 1 << (clen[j] - 1);

            // find proper node, using bits in
            // code as path.
            for (i = 0; i < clen[j]; ++i)
            {
                k = k * 2 + 1; // right link

                if (code[j] & mask)
                    ++k; // go left

                mask >>= 1; // next bit
            }

            heap2[j] = k; // store link in heap2
        }
    }

    // sort outc based on heap2
    for (i = 1; i < 256; ++i)
    {
        t = heap2[i];
        c = outc[i];
        j = i;

        while ((j) && (heap2[j-1] > t))
        {
            heap2[j] = heap2[j - 1];
            outc[j] = outc[j - 1];
            --j;
        }

        heap2[j] = t;
        outc[j] = c;
    }

    // find first character in table
    for (j = 0; heap2[j] == 0; ++j) ;

    // decode data
    k    = 0; // link in trie
    i    = j;
    mask = 0x80;
    n    = 0;
    cptr = comp;
    dptr = data;

    while (n < data_len)
    {
        k = k * 2 + 1; // right link

        if ((*cptr) & mask)
            ++k; // left link if bit on

        // search heap2 until link >= k
        while (heap2[i] < k)
            ++i;

        // code matches, character found
        if (k == heap2[i])
        {
            (*dptr) = outc[i];
            ++dptr;
            ++n;
            k = 0;
            i = j;
        }

        // move to next bit
        if (mask > 1)
            mask >>= 1;
        else // code extends into next byte
        {
            mask = 0x80;
            ++cptr;
        }
    }

    // remove work areas
    free_beebs(comp);
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
  init_heap ();
}



int benchmark()
{
    // initialization
    byte * test_data = generate_test_data(TEST_SIZE);

    // what we're timing
    compdecomp(test_data,TEST_SIZE);

    // release resources
    free_beebs(test_data);

    // done
    return 0;
}
