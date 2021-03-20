/* Copyright (C) 2019 Technical University - Sofia

   Contributor Lubomir Bogdanov <lbogdanov@tu-sofia.bg>

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
#include <stdint.h>

void software_init_hook(void);
static void nmi_handler(void);
static void hard_fault_handler(void);
static void default_int_handler(void);

extern int _stack_ptr;
extern int _etext;
extern int _data;
extern int _edata;
extern int _bss;
extern int _ebss;

extern int main(void);

__attribute__ ((section(".vector_table")))
void (* const vector_table[])(void) = {
    (void (*)(void))((uint32_t)&_stack_ptr),// The initial stack pointer
    software_init_hook,                     // The reset handler
    nmi_handler,                            // The NMI handler
    hard_fault_handler,                     // The hard fault handler
    0,                                      //Reserved
    0,                                      //Reserved
    0,                                      //Reserved
    0,                                      //Reserved
    0,                                      //Reserved
    0,                                      //Reserved
    0,                                      //Reserved
    default_int_handler,                    //SVC_Handler
    0,                                      //Reserved
    0,                                      //Reserved
    default_int_handler,                    //PendSV_Handler
    default_int_handler,                    //SysTick_Handler
    default_int_handler,                    //POWER_CLOCK_IRQHandler
    default_int_handler,                    //RADIO_IRQHandler
    default_int_handler,                    //UART0_IRQHandler
    default_int_handler,                    //SPI0_TWI0_IRQHandler
    default_int_handler,                    //SPI1_TWI1_IRQHandler
    0,                                      //Reserved
    default_int_handler,                    //GPIOTE_IRQHandler
    default_int_handler,                    //ADC_IRQHandler
    default_int_handler,                    //TIMER0_IRQHandler
    default_int_handler,                    //TIMER1_IRQHandler
    default_int_handler,                    //TIMER2_IRQHandler
    default_int_handler,                    //RTC0_IRQHandler
    default_int_handler,                    //TEMP_IRQHandler
    default_int_handler,                    //RNG_IRQHandler
    default_int_handler,                    //ECB_IRQHandler
    default_int_handler,                    //CCM_AAR_IRQHandler
    default_int_handler,                    //WDT_IRQHandler
    default_int_handler,                    //RTC1_IRQHandler
    default_int_handler,                    //QDEC_IRQHandler
    default_int_handler,                    //LPCOMP_IRQHandler
    default_int_handler,                    //SWI0_IRQHandler
    default_int_handler,                    //SWI1_IRQHandler
    default_int_handler,                    //SWI2_IRQHandler
    default_int_handler,                    //SWI3_IRQHandler
    default_int_handler,                    //SWI4_IRQHandler
    default_int_handler,                    //SWI5_IRQHandler
    0,                                      //Reserved
    0,                                      //Reserved
    0,                                      //Reserved
    0,                                      //Reserved
    0,                                      //Reserved
    0,                                      //Reserved
};

void software_init_hook(){
    int *src, *dest;

    src = &_etext;
    for(dest = &_data; dest < &_edata; ){
        *dest++ = *src++;
    }

    for(dest = &_bss; dest < &_ebss; ){
        *dest++ = 0x00000000;
    }

    main();

    while(1){ }
}

static void nmi_handler(void){
    while(1){ }
}

static void hard_fault_handler(void){
    while(1){ }
}

static void default_int_handler(void){
    while(1){ }
}

