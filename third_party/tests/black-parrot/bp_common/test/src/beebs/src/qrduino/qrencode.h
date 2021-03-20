/* BEEBS qrduino benchmark

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

/* Original code from: https://github.com/tz1/qrduino */

#define PROGMEM
#define memcpy_P memcpy
#define __LPM(x) *x
#define pgm_read_word(x) *x

// malloc-ed by initframe, free manually
extern unsigned char *strinbuf; // string iput buffer
extern unsigned char *qrframe;
// setup the base frame structure - can be reused
void initframe(void);
// free the basic frame malloced structures
void freeframe(void);
// these resturn maximum string size to send in
unsigned initeccsize(unsigned char ecc, unsigned size);
unsigned initecc(unsigned char level,unsigned char version);

extern unsigned char  WD, WDB;
#include "qrbits.h"

// strinbuf in, qrframe out
void qrencode(void);

void freeecc();
