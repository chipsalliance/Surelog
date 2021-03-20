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

#define FLASH_ACR  (*((unsigned *)0x40022000))
#define RCC  (*((volatile unsigned volatile *)0x40021000))
#define RCC_CFGR  (*((volatile unsigned  volatile*)0x4002100C))

void setup_flash(int pre_read, int disab_buf, int prefetch, int latency)
{
    FLASH_ACR = (pre_read << 6) | (disab_buf << 5) | (prefetch << 1) | latency;
}

void setup_clock_hsi16(int div4, int pll_mul, int pll_div, int use_pll)
{
    // Set to normal HSI16
    RCC = 0x00000001;

    // Wait for PLL to stop
    while((RCC & 0x02000000) != 0);

    RCC_CFGR = 0x00000001;
    
    // Apply div4 flag
    RCC |= div4 << 3;

    if(use_pll)
    {
        RCC_CFGR = (pll_div << 22) | (pll_mul << 18) | 1; 

        RCC |= 1 << 24;

        // Wait for PLL lock
        while((RCC & 0x02000000) == 0);

        // Switch to PLL clock
        RCC_CFGR |= 0x3;
    }
}

#define PLLMUL_3    0x0
#define PLLMUL_4    0x1
#define PLLMUL_6    0x2
#define PLLMUL_8    0x3
#define PLLMUL_12   0x4
#define PLLMUL_16   0x5
#define PLLMUL_24   0x6
#define PLLMUL_32   0x7
#define PLLMUL_48   0x8

#define PLLDIV_2    0x1
#define PLLDIV_3    0x2
#define PLLDIV_4    0x3

void initialise_board()
{
    setup_flash(1, 0, 1, 1);

// 16 MHz
    setup_clock_hsi16(0, PLLMUL_3, PLLDIV_3, 1);
//    setup_clock_hsi16(0, PLLMUL_4, PLLDIV_4, 1);
//    setup_clock_hsi16(1, PLLMUL_8, PLLDIV_2, 1);
//    setup_clock_hsi16(1, PLLMUL_12, PLLDIV_3, 1);
//    setup_clock_hsi16(1, PLLMUL_16, PLLDIV_4, 1);
//
// 32 Mhz
//    setup_clock_hsi16(0, PLLMUL_4, PLLDIV_2, 1);
//    setup_clock_hsi16(1, PLLMUL_16, PLLDIV_2, 1);
//    setup_clock_hsi16(1, PLLMUL_24, PLLDIV_3, 1);

    PIN_INIT(2);
}

void start_trigger()
{
    PIN_SET(2);
}

void stop_trigger()
{
    PIN_CLEAR(2);
}
