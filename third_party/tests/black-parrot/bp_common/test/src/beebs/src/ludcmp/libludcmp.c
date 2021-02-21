
/* BEEBS ludcmp benchmark

   MDH WCET BENCHMARK SUITE.

   *************************************************************************
   *                                                                       *
   *   SNU-RT Benchmark Suite for Worst Case Timing Analysis               *
   *   =====================================================               *
   *                              Collected and Modified by S.-S. Lim      *
   *                                           sslim@archi.snu.ac.kr       *
   *                                         Real-Time Research Group      *
   *                                        Seoul National University      *
   *                                                                       *
   *                                                                       *
   *        < Features > - restrictions for our experimental environment   *
   *                                                                       *
   *          1. Completely structured.                                    *
   *               - There are no unconditional jumps.                     *
   *               - There are no exit from loop bodies.                   *
   *                 (There are no 'break' or 'return' in loop bodies)     *
   *          2. No 'switch' statements.                                   *
   *          3. No 'do..while' statements.                                *
   *          4. Expressions are restricted.                               *
   *               - There are no multiple expressions joined by 'or',     *
   *                'and' operations.                                      *
   *          5. No library calls.                                         *
   *               - All the functions needed are implemented in the       *
   *                 source file.                                          *
   *                                                                       *
   *                                                                       *
   *************************************************************************
   *                                                                       *
   *  FILE: ludcmp.c                                                       *
   *  SOURCE : Turbo C Programming for Engineering                         *
   *                                                                       *
   *  DESCRIPTION :                                                        *
   *                                                                       *
   *     Simultaneous linear equations by LU decomposition.                *
   *     The arrays a[][] and b[] are input and the array x[] is output    *
   *     row vector.                                                       *
   *     The variable n is the number of equations.                        *
   *     The input arrays are initialized in function main.                *
   *                                                                       *
   *                                                                       *
   *  REMARK :                                                             *
   *                                                                       *
   *  EXECUTION TIME :                                                     *
   *                                                                       *
   *                                                                       *
   *************************************************************************

   Benchmark Suite for Real-Time Applications, by Sung-Soo Lim

      III-4. ludcmp.c : Simultaneous Linear Equations by LU Decomposition
                   (from the book C Programming for EEs by Hyun Soon Ahn)

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

/* This scale factor will be changed to equalise the runtime of the
   benchmarks. */
#define SCALE_FACTOR    (REPEAT_FACTOR >> 0)

/* NOTE: These arrays were all originally size 5 in every dimension.
   However, the code below is either broken, or very smart in how is
   accesses the data.  The compiler is warnings that there might be
   accesses beyond the bounds of the arrays, I've increased the array sizes
   to remove the warnings, but we should investigate the code below to
   ensure that the algorithm is doing the right thing.  */
float          a[8][9], b[6], x[6];

int             ludcmp( /* int nmax, */ int n, float eps);


static float
ludcmp_fabs(float n)
{
	float          f;

	if (n >= 0)
		f = n;
	else
		f = -n;
	return f;
}

int
ludcmp( /* int nmax, */ int n, float eps)
{

	int             i, j, k;
	float          w, y[10];

	if (n > 99 || eps <= 0.0)
		return (999);
	for (i = 0; i < n; i++) {
		if (ludcmp_fabs(a[i][i]) <= eps)
			return (1);
		for (j = i + 1; j <= n; j++) {
			w = a[j][i];
			if (i != 0)
				for (k = 0; k < i; k++)
					w -= a[j][k] * a[k][i];
			a[j][i] = w / a[i][i];
		}
		for (j = i + 1; j <= n; j++) {
			w = a[i + 1][j];
			for (k = 0; k <= i; k++)
				w -= a[i + 1][k] * a[k][j];
			a[i + 1][j] = w;
		}
	}
	y[0] = b[0];
	for (i = 1; i <= n; i++) {
		w = b[i];
		for (j = 0; j < i; j++)
			w -= a[i][j] * y[j];
		y[i] = w;
	}
	x[n] = y[n] / a[n][n];
	for (i = n - 1; i >= 0; i--) {
		w = y[i];
		for (j = i + 1; j <= n; j++)
			w -= a[i][j] * x[j];
		x[i] = w / a[i][i];
	}
	return (0);

}

/* Write to CHKERR from BENCHMARK to ensure that the core call within
   BENCHMARK is not optimised away.  */
volatile int chkerr;


void
initialise_benchmark (void)
{
}


int
benchmark (void)
{
  int             i, j/*, nmax = 50*/, n = 5;
  float          eps, w;

  eps = 1.0e-6;

  for (i = 0; i <= n; i++) {
          w = 0.0;
          for (j = 0; j <= n; j++) {
                  a[i][j] = (i + 1) + (j + 1);
                  if (i == j)
                          a[i][j] *= 10.0;
                  w += a[i][j];
          }
          b[i] = w;
  }

  chkerr = ludcmp( /* nmax, */ n, eps);
  return 0;
}

int verify_benchmark(int unused)
{
  float exp_a[8][9] = {{20.000000000000000000000000000000, 3.000000000000000000000000000000, 4.000000000000000000000000000000, 5.000000000000000000000000000000, 6.000000000000000000000000000000, 7.000000000000000000000000000000, 0.000000000000000000000000000000, 0.000000000000000000000000000000, 0.000000000000000000000000000000},
{0.150000005960464477539062500000, 39.549999237060546875000000000000, 4.400000095367431640625000000000, 5.250000000000000000000000000000, 6.099999904632568359375000000000, 6.949999809265136718750000000000, 0.000000000000000000000000000000, 0.000000000000000000000000000000, 0.000000000000000000000000000000},
{0.200000002980232238769531250000, 0.111251585185527801513671875000, 58.710494995117187500000000000000, 5.415929317474365234375000000000, 6.121365547180175781250000000000, 6.826801300048828125000000000000, 0.000000000000000000000000000000, 0.000000000000000000000000000000, 0.000000000000000000000000000000},
{0.250000000000000000000000000000, 0.132743358612060546875000000000, 0.092248059809207916259765625000, 77.553489685058593750000000000000, 6.125581741333007812500000000000, 6.697674274444580078125000000000, 0.000000000000000000000000000000, 0.000000000000000000000000000000, 0.000000000000000000000000000000},
{0.300000011920928955078125000000, 0.154235139489173889160156250000, 0.104263566434383392333984375000, 0.078985251486301422119140625000, 96.137092590332031250000000000000, 6.587261199951171875000000000000, 0.000000000000000000000000000000, 0.000000000000000000000000000000, 0.000000000000000000000000000000},
{0.349999994039535522460937500000, 0.175726920366287231445312500000, 0.116279065608978271484375000000, 0.086361996829509735107421875000, 0.068519458174705505371093750000, 114.505111694335937500000000000000, 0.000000000000000000000000000000, 0.000000000000000000000000000000, 0.000000000000000000000000000000},
{0.000000000000000000000000000000, 0.000000000000000000000000000000, 0.000000000000000000000000000000, 0.000000000000000000000000000000, 0.000000000000000000000000000000, 0.000000000000000000000000000000, 0.000000000000000000000000000000, 0.000000000000000000000000000000, 0.000000000000000000000000000000},
{0.000000000000000000000000000000, 0.000000000000000000000000000000, 0.000000000000000000000000000000, 0.000000000000000000000000000000, 0.000000000000000000000000000000, 0.000000000000000000000000000000, 0.000000000000000000000000000000, 0.000000000000000000000000000000, 0.000000000000000000000000000000}};
  float exp_b[] = {45.000000, 69.000000, 93.000000, 117.000000, 141.000000, 165.000000};
  float exp_x[] = {1, 1, 0.999999821186065673828125, 1, 1.00000011920928955078125, 1};
  int i, j;
  for (i=0; i<6; i++) {
    if (b[i] != exp_b[i])
      return 0;
    if (x[i] != exp_x[i])
      return 0;
  }
  for (i=0; i<8; i++)
    for (j=0; j<9; j++)
      if (a[i][j] != exp_a[i][j])
        return 0;

  return 1;
}
