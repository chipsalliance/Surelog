/* Copyright (C) 2014 Embecosm Limited and University of Bristol

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

#include <support.h>
#include <avr/io.h>
#include <avr/xmega.h>

void initialise_board()
{
  PROTECTED_WRITE(OSC_CTRL, 0x3);
  while((OSC_STATUS & 2) == 0);
  PROTECTED_WRITE(CLK_PSCTRL, 0xC);
  PROTECTED_WRITE(CLK_CTRL, 0x1);
  PIN_INIT(A, 0);
}

void start_trigger()
{
  PIN_SET(A, 0);
}

void stop_trigger()
{
  PIN_CLEAR(A, 0);
}
