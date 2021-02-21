/* Copyright (C) 2017 Embecosm Limited and University of Bristol

   Contributor Graham Markall <graham.markall@embecosm.com>

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

void initialise_board()
{
  asm volatile ("li a0, 0" : : : "a0");
}

void start_trigger()
{
  // Use 91 as a syscall to print the clock at the start trigger
  register long a7 asm("a7") = 91;
  asm volatile ("ecall" : : "r"(a7) );
}

void stop_trigger()
{
  // Use 92 as a syscall to print the clock at the stop trigger
  register long a7 asm("a7") = 92;
  asm volatile ("ecall" : : "r"(a7) );
}


