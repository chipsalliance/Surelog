/* BEEBS miniz benchmark

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

#include "miniz.h"
#include <string.h>

/* This scale factor will be changed to equalise the runtime of the
   benchmarks. */
#define SCALE_FACTOR    (REPEAT_FACTOR >> 0)

// Like compress() but with more control, level may range from 0 (storing) to 9 (max. compression)
int mz_compress2(unsigned char *pDest, unsigned long *pDest_len, const unsigned char *pSource, unsigned long source_len, int level);

// Returns Z_OK on success, or one of the error codes from inflate() on failure.
int uncompresmz_s(unsigned char *pDest, unsigned long *pDest_len, const unsigned char *pSource, unsigned long source_len);

const char *text="Since the ancients (as we are told by Pappas), made great account of the science of mechanics in the investigation of natural things; and the moderns, lying aside substantial forms and occult qualities, have endeavoured to subject the phï¿½nomena of nature to the laws of mathematics, I have in this treatise cultivated mathematics so far as it regards philosophy. The ancients considered mechanics in a twofold respect; as rational, which proceeds accurately by demonstration; and practical. To practical mechanics all the manual arts belong, from which mechanics took its name. But as artificers do not work with perfect accuracy, it comes to pass that mechanics is so distinguished from geometry, that what is perfectly accurate is called geometrical; what is less so, is called mechanical. But the errors are not in the art, but in the artificers. He that works with less accuracy is an imperfect mechanic; and if any could work with perfect accuracy, he would be the most perfect mechanic of all; for the description of right lines and circles, upon which geometry is founded, belongs to mechanics.";

unsigned char tocompress[1200];
unsigned char compressed[1200];


/* This benchmark does not support verification */

int
verify_benchmark (int res __attribute ((unused)) )
{
  return -1;
}


extern void  init_heap (void);

void
initialise_benchmark (void)
{
  init_heap ();			/* Set up BEEBS heap */
}



int benchmark()
{
	volatile int cnt=0;
	int len = strlen(text);
	unsigned long slen, dlen;

	dlen = 1200;
	mz_compress2(compressed, &dlen, (const unsigned char *) text, len, 1);
	slen = 1200;
	mz_uncompress(tocompress, &slen, compressed, dlen);

	dlen = 1200;
	mz_compress2(compressed, &dlen, (const unsigned char *) text, len, 7);
	slen = 1200;
	mz_uncompress(tocompress, &slen, compressed, dlen);

	return cnt;

}

