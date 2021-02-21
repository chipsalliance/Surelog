/* Chip support for ARM NRF51822.

   Copyright (C) 2019 Technical University - Sofia

   Contributor Lubomir Bogdanov <lbogdanov@tu-sofia.bg>

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
#define GPIO_BASE			*(volatile unsigned long *)0x50000000UL //GPIO port direction register base address
#define GPIO_OUTSET			*(volatile unsigned long *)0x50000508UL //GPIO pin set register
#define GPIO_OUTCLR			*(volatile unsigned long *)0x5000050CUL //GPIO pin clear register
#define GPIO_CNF_25			*(volatile unsigned long *)0x50000764UL //GPIO pin 25 configuration register base address
#define GPIO_PIN_25			0x2000000				//GPIO pin 25 mask

// Provide macros to do the pin toggling ////////////////////////////////////

// Initialize the pin + clocks
#define PIN_INIT(number)                                        \
    do {                                                        \
        switch(number){                                         \
        case 25:                                                \
            /* Set as output GPIO 25 */                         \
            GPIO_CNF_25 |= 0x01;                                \
            /* Pull low GPIO 25 */                              \
            GPIO_OUTCLR |= GPIO_PIN_25;                         \
            break;                                              \
        }                                                       \
    } while(0)

// Set the pin to high
#define PIN_SET(number)                         \
    do {                                        \
        switch(number){                         \
        case 25:                                \
            /* Set pin 25 */                    \
            GPIO_OUTSET |= GPIO_PIN_25;         \
            break;                              \
        }                                       \
    } while(0)                                  \

// Set the pin to low
#define PIN_CLEAR(number)                       \
    do {                                        \
        switch(number){                         \
        case 25:                                \
            /* Clear pin 25 */                  \
            GPIO_OUTCLR |= GPIO_PIN_25;         \
            break;                              \
        }                                       \
    } while(0)                                  \

#endif /* CHIPSUPPORT_H */
