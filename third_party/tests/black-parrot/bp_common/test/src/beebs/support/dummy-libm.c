/* Dummy standard C math library for the benchmarks

   Copyright (C) 2018 Embecosm Limited

   Contributor: Jeremy Bennett <jeremy.bennett@embecosm.com>

   This file is part of the Bristol/Embecosm Embedded Benchmark Suite.

   This program is free software: you can redistribute it and/or modify
   it under the terms of the GNU General Public License as published by
   the Free Software Foundation, either version 3 of the License, or
   (at your option) any later version.

   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License for more details.

   You should have received a copy of the GNU General Public License
   along with this program.  If not, see <http://www.gnu.org/licenses/>.

   SPDX-License-Identifier: GPL-3.0-or-later */

/* The purpose of this library is to measure the size of code excluding target
   dependent C library code. It only makes sense if it is used with
   -gc-sections. */

double
acos (double x __attribute__ ((unused)) )
{
  return  0.0;
}


double
atan (double x __attribute__ ((unused)) )
{
  return 0.0;
}


double
cos (double x __attribute__ ((unused)) )
{
  return  0.0;
}


double
sin (double x __attribute__ ((unused)) )
{
  return 0.0;
}


double
pow (double x __attribute__ ((unused)),
     double y __attribute__ ((unused)) )
{
  return  0.0;
}


double sqrt (double x __attribute__ ((unused)) )
{
  return  0.0;
}


float
sqrtf (float x __attribute__ ((unused)) )
{
  return 0.0;
}


double
floor (double x __attribute__ ((unused)) )
{
  return 0.0;
}


float
floorf (float x __attribute__ ((unused)) )
{
  return 0.0;
}


double
exp (double x __attribute__ ((unused)) )
{
  return 0.0;
}

double
log (double x __attribute__ ((unused)) )
{
  return 0.0;
}

/*
   Local Variables:
   mode: C++
   c-file-style: "gnu"
   End:
*/
