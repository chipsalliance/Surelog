/* BEEBS miniz benchmark

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

/* For more compatibility with zlib, miniz.c uses unsigned long for
   some parameters/struct members. Beware: mz_ulong can be either 32
   or 64-bits!  */
typedef unsigned long mz_ulong;

/* Forward declaration of function: Single-call decompression.
   Returns MZ_OK on success, or one of the error codes from
   mz_inflate() on failure.  */
int mz_uncompress(unsigned char *pDest, mz_ulong *pDest_len,
		  const unsigned char *pSource, mz_ulong source_len);
