/* Chip support for ARM tm4c123g.

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
#define ADDR(x)     (*((unsigned long*)(x)))
#define SYSCTL_GPIO_ENABLE     *(volatile unsigned long *)0x400FE608
#define SYSCTL_GPIO_READY      *(volatile unsigned long *)0x400FEA08

#define SYSCTL_GPIOK_MASK      0x0200
#define GPIO_PORTK_DIR         *(volatile unsigned long *)0x40061400 //GPIO Port K direction register base address
#define GPIO_PORTK_DATA        *(volatile unsigned long *)0x400613FC //GPIO Port K data register base address
#define GPIO_PORTK_DIG_PIN     *(volatile unsigned long *)0x4006151C //GPIO Port K digital pin enable register base address
#define GPIO_PINMASK_0         0x01                                  //GPIO pin PK0 mask

#define SYSCTL_GPIOA_MASK      0x0001
#define GPIO_PORTA_DIR         *(volatile unsigned long *)0x40004400 //GPIO Port A direction register base address
#define GPIO_PORTA_DATA        *(volatile unsigned long *)0x400043FC //GPIO Port A data register base address
#define GPIO_PORTA_DIG_PIN     *(volatile unsigned long *)0x4000451C //GPIO Port A digital pin enable register base address
#define GPIO_PINMASK_7         0x80                                  //GPIO pin PA7 mask

// Provide macros to do the pin toggling ////////////////////////////////////

// Initialize the pin + clocks
#define PIN_INIT(number)                                        \
    do {                                                        \
        switch(number){                                         \
        case 0:                                                 \
            /* Turn on GPIO K Clock */                          \
            SYSCTL_GPIO_ENABLE |= SYSCTL_GPIOK_MASK;            \
            /* Wait for GPIO K ready */                         \
            while(!(SYSCTL_GPIO_READY & SYSCTL_GPIOK_MASK)){ }  \
            /* Set as output GPIO PK0 */                        \
            GPIO_PORTK_DIR |= GPIO_PINMASK_0;                   \
            GPIO_PORTK_DIG_PIN |= GPIO_PINMASK_0;               \
            /* Pull low GPIO PK0 */                             \
            GPIO_PORTK_DATA &= ~GPIO_PINMASK_0;                 \
            break;                                              \
         case 7:                                                \
            /* Turn on GPIO A Clock */                          \
            SYSCTL_GPIO_ENABLE |= SYSCTL_GPIOA_MASK;            \
            /* Wait for GPIO A ready */                         \
            while(!(SYSCTL_GPIO_READY & SYSCTL_GPIOA_MASK)){ }  \
            /* Set as output GPIO PA7 */                        \
            GPIO_PORTA_DIR |= GPIO_PINMASK_7;                   \
            GPIO_PORTA_DIG_PIN |= GPIO_PINMASK_7;               \
            /* Pull low GPIO PA7 */                             \
            GPIO_PORTA_DATA &= ~GPIO_PINMASK_7;                 \
            break;                                              \
        }                                                       \
    } while(0)

// Set the pin to high
#define PIN_SET(number)                         \
    do {                                        \
        switch(number){                         \
        case 0:                                 \
            /* Set PK0 */                       \
            GPIO_PORTK_DATA |= GPIO_PINMASK_0;  \
            break;                              \
        case 7:                                 \
            /* Set PA7 */                       \
            GPIO_PORTA_DATA |= GPIO_PINMASK_7;  \
            break;                              \
        }                                       \
    } while(0)                                  \

// Set the pin to low
#define PIN_CLEAR(number)                       \
    do {                                        \
        switch(number){                         \
        case 0:                                 \
            /* Clear PK0 */                     \
            GPIO_PORTK_DATA &= ~GPIO_PINMASK_0; \
            break;                              \
        case 7:                                 \
            /* Clear PA7 */                     \
            GPIO_PORTA_DATA &= ~GPIO_PINMASK_7; \
            break;                              \
        }                                       \
    } while(0)                                  \

#endif /* CHIPSUPPORT_H */
