/*
* Copyright (c) 2018, Shawn D'silva <shawn.dsilva_97@protonmail.com>
* All rights reserved.
*
*  This file is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * This file is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with this library.  If not, see <http://www.gnu.org/licenses/>.
*
* File:			TM4C123GH6PHM.ld
* Author:		Shawn D'silva <https://shawn-dsilva.github.io>.
* Version:		1.0.0.
* Description:	linker file for the TM4C Launchpad
*
* Modified by lbogdanov@tu-sofia.bg to support heap
*/

MEMORY
{
    FLASH (rx) : ORIGIN = 0x00000000, LENGTH = 256K /* FLASH size 256KB */
    RAM (rwx) : ORIGIN = 0x20000000, LENGTH = 32K/* RAM size 32KB */

}

SECTIONS
{


    /* 
     * initial stack pointer pointing to top of stack,starts from higher addresses
     * i.e ORIGIN(RAM) + LENGTH(RAM)-1 in this case 0x20007FFF to lower addesses i.e
     * those lesser than 0x20007FFF to 0x2000000,which is the origina address of RAM,
     * until it comes in contact with .bss or .data in which case a buffer overflow occurs
    */
    PROVIDE( _stack_ptr = ORIGIN(RAM) + LENGTH(RAM));

    /* constants  and other code stored in FLASH */
    .text :
    {
        _text = .;               /* beginning of .text segment,also called code memory */
        KEEP(*(.vector_table)) /* vector table defined in startup.c to be included */
        *(.text*)                   /* other code */
        *(.rodata*)                /* constants go here */
        _etext = .;             /* end of .text segment */
    } > FLASH

    /* data, initialized variables, to be copied to RAM upon <RESET> by startup.c */
    .data : 
    {
        _data = .;          /* beginning of .data segment */        
        *(.data*)           /* data goes here */
        _edata = .;         /* end of .data segment */
    } > RAM AT >FLASH   /* .data segment starts directly after the .text section in FLASH */

    /* uninitialized data which is initialized to 0 upon <RESET> by startup.c */
    .bss :
    {
        _bss = .;       /* beginning of .bss segment */
        *(.bss*)        /* .bss content goes here */
        *(COMMON)       
        _ebss = .;      /* end of .bss segment */
    } > RAM

    .heap :
    {
        _heap = .;       /* beginning of .heap segment */
        end = _heap;     /* for the _sbrk function */
        *(.heap*)        /* .heap content goes here */       
        _eheap = .;      /* end of .bss segment */
    } > RAM


}
