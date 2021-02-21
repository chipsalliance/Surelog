/* Chip support for ARM stm32f051.

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

// Define the registers we need to do a pin toggle ////////////////////////////

#define ADDR(x)     (*((unsigned long*)(x)))

// These registers define clocks, RCC (Reset and clock control)
#define RCC_BASE        0x40021000
#define RCC_IOPENR      ADDR(RCC_BASE + 0x2C)

#define GPIOB_BASE      0x50000400
#define GPIOB_MODER     ADDR(GPIOB_BASE + 0x00)
#define GPIOB_BSRR      ADDR(GPIOB_BASE + 0x18)


// Provide a macros to do the pin toggling ////////////////////////////////////

// Initialise the pin + clocks
#define PIN_INIT(number)                \
    do {                                \
        /* Turn on GPIO B Clock */      \
        RCC_IOPENR |= 1<<1;             \
        /* Turn on GPIO B */            \
        GPIOB_MODER &= ~(3 << number*2);\
        GPIOB_MODER |= 1 << number*2;   \
        /* Pull low GPIO B */           \
        GPIOB_BSRR |= 1 << (number+16); \
    } while(0)

// Set the pin to high
#define PIN_SET(number)                 \
    do {                                \
        /* Pull low GPIO B */           \
        GPIOB_BSRR |= 1 << number;      \
    } while(0)

// Set the pin to low
#define PIN_CLEAR(number)               \
    do {                                \
        /* Pull low GPIO B */           \
        GPIOB_BSRR |= 1 << (number+16); \
    } while(0)

#endif /* CHIPSUPPORT_H */
