/* Chip support for ARM stm32f100.

   Copyright (C) 2014 Embecosm Limited and the University of Bristol

   Contributor James Pallister <james.pallister@bristol.ac.uk>

   This file is part of BEEBS

   This program is free software; you can redistribute it and/or modify it
   under the terms of the GNU General Public License as published by the Free
   Software Foundation; either version 3 of the License, or (at your option)
   any later version.

   This program is distributed in the hope that it will be useful, but WITHOUT
   ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
   FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
   more details.

   You should have received a copy of the GNU General Public License along with
   this program.  If not, see <http://www.gnu.org/licenses/>.  */

#ifndef CHIPSUPPORT_H
#define CHIPSUPPORT_H

// Define the registers we need to do a pin toggle
#define ADDR(x)     (*((unsigned long*)(x)))

// These registers define clocks, RCC (Reset and clock control)
#define RCC_BASE        0x40021000
#define RCC_APB2ENR     ADDR(RCC_BASE + 0x18)

#define GPIOC_BASE      0x40011000
#define GPIOC_CRL       ADDR(GPIOC_BASE + 0x00)
#define GPIOC_BSRR      ADDR(GPIOC_BASE + 0x10)


// Provide a macros to do the pin toggling ////////////////////////////////////

// Initialise the pin + clocks
#define PIN_INIT(number)                \
    do {                                \
        /* Turn on GPIO C Clock */      \
        RCC_APB2ENR |= 1<<4;            \
        /* Turn on GPIO C */            \
        GPIOC_CRL &= ~(0xF << (number * 4));  \
        GPIOC_CRL |= (0x1 << (number * 4));   \
        /* Pull low GPIO C */           \
        GPIOC_BSRR |= 1 << (number+16); \
    } while(0)

// Set the pin to high
#define PIN_SET(number)                 \
    do {                                \
        /* Pull low GPIO C */           \
        GPIOC_BSRR |= 1 << number;      \
    } while(0)

// Set the pin to low
#define PIN_CLEAR(number)               \
    do {                                \
        /* Pull low GPIO C */           \
        GPIOC_BSRR |= 1 << (number+16); \
    } while(0)

#endif /* CHIPSUPPORT_H */
