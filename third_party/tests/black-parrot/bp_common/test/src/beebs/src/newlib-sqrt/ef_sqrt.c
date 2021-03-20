/* BEEBS newlib ef_sqrt implementation

   ====================================================
   Copyright (C) 1993 by Sun Microsystems, Inc. All rights reserved.

   Developed at SunPro, a Sun Microsystems, Inc. business.
   Permission to use, copy, modify, and distribute this
   software is freely granted, provided that this notice
   is preserved.
   ====================================================

   Copyright (C) 2014 Embecosm Limited and University of Bristol

   Contributor Pierre Langlois <pierre.langlois@embecosm.com>

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
#include <stdint.h>

typedef union
{
  float value;
  uint32_t word;
} ieee_float_shape_type;

#define GET_FLOAT_WORD(i,d)					\
  ieee_float_shape_type gf_u;					\
  gf_u.value = (d);						\
  (i) = gf_u.word;

#define SET_FLOAT_WORD(d,i)					\
  ieee_float_shape_type sf_u;					\
  sf_u.word = (i);						\
  (d) = sf_u.value;

#define FLT_UWORD_IS_FINITE(x) ((x)<0x7f800000L)
#define FLT_UWORD_IS_NAN(x) ((x)>0x7f800000L)
#define FLT_UWORD_IS_INFINITE(x) ((x)==0x7f800000L)
#define FLT_UWORD_IS_ZERO(x) ((x)==0)
#define FLT_UWORD_IS_SUBNORMAL(x) ((x)<0x00800000L)

static	const float	one	= 1.0, tiny=1.0e-30;

	float __ieee754_sqrtf(float x)
{
	float z;
	uint32_t r,hx;
	int32_t ix,s,q,m,t,i;

	GET_FLOAT_WORD(ix,x);
	hx = ix&0x7fffffff;

    /* take care of Inf and NaN */
	if(!FLT_UWORD_IS_FINITE(hx))
	    return x*x+x;		/* sqrt(NaN)=NaN, sqrt(+inf)=+inf
					   sqrt(-inf)=sNaN */
    /* take care of zero and -ves */
	if(FLT_UWORD_IS_ZERO(hx)) return x;/* sqrt(+-0) = +-0 */
	if(ix<0) return (x-x)/(x-x);		/* sqrt(-ve) = sNaN */

    /* normalize x */
	m = (ix>>23);
	if(FLT_UWORD_IS_SUBNORMAL(hx)) {		/* subnormal x */
	    for(i=0;(ix&0x00800000L)==0;i++) ix<<=1;
	    m -= i-1;
	}
	m -= 127;	/* unbias exponent */
	ix = (ix&0x007fffffL)|0x00800000L;
	if(m&1)	/* odd m, double x to make it even */
	    ix += ix;
	m >>= 1;	/* m = [m/2] */

    /* generate sqrt(x) bit by bit */
	ix += ix;
	q = s = 0;		/* q = sqrt(x) */
	r = 0x01000000L;		/* r = moving bit from right to left */

	while(r!=0) {
	    t = s+r;
	    if(t<=ix) {
		s    = t+r;
		ix  -= t;
		q   += r;
	    }
	    ix += ix;
	    r>>=1;
	}

    /* use floating add to find out rounding direction */
	if(ix!=0) {
	    z = one-tiny; /* trigger inexact flag */
	    if (z>=one) {
	        z = one+tiny;
		if (z>one)
		    q += 2;
		else
		    q += (q&1);
	    }
	}
	ix = (q>>1)+0x3f000000L;
	ix += (m <<23);
	SET_FLOAT_WORD(z,ix);
	return z;
}

/* This scale factor will be changed to equalise the runtime of the
   benchmarks. */
#define SCALE_FACTOR    (REPEAT_FACTOR >> 0)

/* Tell the compiler not to optimize out calls in BENCHMARK. */
volatile float result[6];
static int a, b, c, d, e, f;

int
benchmark (void)
{
  result[0] = __ieee754_sqrtf(a);
  result[1] = __ieee754_sqrtf(b);
  result[2] = __ieee754_sqrtf(c);
  result[3] = __ieee754_sqrtf(d);
  result[4] = __ieee754_sqrtf(e);
  result[5] = __ieee754_sqrtf(f);
  return 0;
}

void initialise_benchmark() {
  a = 2;
  b = 3;
  c = 5;
  d = 6;
  e = 7;
  f = 8;
}

int verify_benchmark(int unused)
{
  float exp[] = {1.41421353816986083984375,
                1.73205077648162841796875,
                2.2360680103302001953125,
                2.4494898319244384765625,
                2.6457512378692626953125,
                2.8284270763397216796875};
  //printf("{%f, %f, %f, %f, %f, %f};", result[0], result[1], result[2], result[3], result[4], result[5]);
  int i;
  for (i=0; i<6; i++)
    if (result[i] != exp[i])
      return 0;
  return 1;
}
