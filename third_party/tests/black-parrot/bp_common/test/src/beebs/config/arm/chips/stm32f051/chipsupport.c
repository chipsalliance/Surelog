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

#include <string.h>

// This file is needed to copy the initialised data from flash to RAM

extern unsigned char __data_start__;
extern unsigned char __data_end__;
extern unsigned char _data_loadaddr;

extern unsigned char __bss_start__;
extern unsigned char __bss_end__;

void software_init_hook()
{
    memcpy(&__data_start__, &_data_loadaddr, 
        (unsigned)&__data_end__ - (unsigned)&__data_start__);
}

