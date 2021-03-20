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
    (void (*)(void))((uint32_t)&_stack_ptr),
                                            // The initial stack pointer
    software_init_hook,                     // The reset handler
    nmi_handler,                                  // The NMI handler
    hard_fault_handler,                               // The hard fault handler
    default_int_handler,                      // The MPU fault handler
    default_int_handler,                      // The bus fault handler
    default_int_handler,                      // The usage fault handler
    0,                                      // Reserved
    0,                                      // Reserved
    0,                                      // Reserved
    0,                                      // Reserved
    default_int_handler,                      // SVCall handler
    default_int_handler,                      // Debug monitor handler
    0,                                      // Reserved
    default_int_handler,                      // The PendSV handler
    default_int_handler,                      // The SysTick handler
    default_int_handler,                      // GPIO Port A
    default_int_handler,                      // GPIO Port B
    default_int_handler,                      // GPIO Port C
    default_int_handler,                      // GPIO Port D
    default_int_handler,                      // GPIO Port E
    default_int_handler,                      // UART0 Rx and Tx
    default_int_handler,                      // UART1 Rx and Tx
    default_int_handler,                      // SSI0 Rx and Tx
    default_int_handler,                      // I2C0 Master and Slave
    default_int_handler,                      // PWM Fault
    default_int_handler,                      // PWM Generator 0
    default_int_handler,                      // PWM Generator 1
    default_int_handler,                      // PWM Generator 2
    default_int_handler,                      // Quadrature Encoder 0
    default_int_handler,                      // ADC Sequence 0
    default_int_handler,                      // ADC Sequence 1
    default_int_handler,                      // ADC Sequence 2
    default_int_handler,                      // ADC Sequence 3
    default_int_handler,                      // Watchdog timer
    default_int_handler,                      // Timer 0 subtimer A
    default_int_handler,                      // Timer 0 subtimer B
    default_int_handler,                      // Timer 1 subtimer A
    default_int_handler,                      // Timer 1 subtimer B
    default_int_handler,                      // Timer 2 subtimer A
    default_int_handler,                      // Timer 2 subtimer B
    default_int_handler,                      // Analog Comparator 0
    default_int_handler,                      // Analog Comparator 1
    default_int_handler,                      // Analog Comparator 2
    default_int_handler,                      // System Control (PLL, OSC, BO)
    default_int_handler,                      // FLASH Control
    default_int_handler,                      // GPIO Port F
    default_int_handler,                      // GPIO Port G
    default_int_handler,                      // GPIO Port H
    default_int_handler,                      // UART2 Rx and Tx
    default_int_handler,                      // SSI1 Rx and Tx
    default_int_handler,                      // Timer 3 subtimer A
    default_int_handler,                      // Timer 3 subtimer B
    default_int_handler,                      // I2C1 Master and Slave
    default_int_handler,                      // Quadrature Encoder 1
    default_int_handler,                      // CAN0
    default_int_handler,                      // CAN1
    0,                                      // Reserved
    0,                                      // Reserved
    default_int_handler,                      // Hibernate
    default_int_handler,                      // USB0
    default_int_handler,                      // PWM Generator 3
    default_int_handler,                      // uDMA Software Transfer
    default_int_handler,                      // uDMA Error
    default_int_handler,                      // ADC1 Sequence 0
    default_int_handler,                      // ADC1 Sequence 1
    default_int_handler,                      // ADC1 Sequence 2
    default_int_handler,                      // ADC1 Sequence 3
    0,                                      // Reserved
    0,                                      // Reserved
    default_int_handler,                      // GPIO Port J
    default_int_handler,                      // GPIO Port K
    default_int_handler,                      // GPIO Port L
    default_int_handler,                      // SSI2 Rx and Tx
    default_int_handler,                      // SSI3 Rx and Tx
    default_int_handler,                      // UART3 Rx and Tx
    default_int_handler,                      // UART4 Rx and Tx
    default_int_handler,                      // UART5 Rx and Tx
    default_int_handler,                      // UART6 Rx and Tx
    default_int_handler,                      // UART7 Rx and Tx
    0,                                      // Reserved
    0,                                      // Reserved
    0,                                      // Reserved
    0,                                      // Reserved
    default_int_handler,                      // I2C2 Master and Slave
    default_int_handler,                      // I2C3 Master and Slave
    default_int_handler,                      // Timer 4 subtimer A
    default_int_handler,                      // Timer 4 subtimer B
    0,                                      // Reserved
    0,                                      // Reserved
    0,                                      // Reserved
    0,                                      // Reserved
    0,                                      // Reserved
    0,                                      // Reserved
    0,                                      // Reserved
    0,                                      // Reserved
    0,                                      // Reserved
    0,                                      // Reserved
    0,                                      // Reserved
    0,                                      // Reserved
    0,                                      // Reserved
    0,                                      // Reserved
    0,                                      // Reserved
    0,                                      // Reserved
    0,                                      // Reserved
    0,                                      // Reserved
    0,                                      // Reserved
    0,                                      // Reserved
    default_int_handler,                      // Timer 5 subtimer A
    default_int_handler,                      // Timer 5 subtimer B
    default_int_handler,                      // Wide Timer 0 subtimer A
    default_int_handler,                      // Wide Timer 0 subtimer B
    default_int_handler,                      // Wide Timer 1 subtimer A
    default_int_handler,                      // Wide Timer 1 subtimer B
    default_int_handler,                      // Wide Timer 2 subtimer A
    default_int_handler,                      // Wide Timer 2 subtimer B
    default_int_handler,                      // Wide Timer 3 subtimer A
    default_int_handler,                      // Wide Timer 3 subtimer B
    default_int_handler,                      // Wide Timer 4 subtimer A
    default_int_handler,                      // Wide Timer 4 subtimer B
    default_int_handler,                      // Wide Timer 5 subtimer A
    default_int_handler,                      // Wide Timer 5 subtimer B
    default_int_handler,                      // FPU
    0,                                      // Reserved
    0,                                      // Reserved
    default_int_handler,                      // I2C4 Master and Slave
    default_int_handler,                      // I2C5 Master and Slave
    default_int_handler,                      // GPIO Port M
    default_int_handler,                      // GPIO Port N
    default_int_handler,                      // Quadrature Encoder 2
    0,                                      // Reserved
    0,                                      // Reserved
    default_int_handler,                      // GPIO Port P (Summary or P0)
    default_int_handler,                      // GPIO Port P1
    default_int_handler,                      // GPIO Port P2
    default_int_handler,                      // GPIO Port P3
    default_int_handler,                      // GPIO Port P4
    default_int_handler,                      // GPIO Port P5
    default_int_handler,                      // GPIO Port P6
    default_int_handler,                      // GPIO Port P7
    default_int_handler,                      // GPIO Port Q (Summary or Q0)
    default_int_handler,                      // GPIO Port Q1
    default_int_handler,                      // GPIO Port Q2
    default_int_handler,                      // GPIO Port Q3
    default_int_handler,                      // GPIO Port Q4
    default_int_handler,                      // GPIO Port Q5
    default_int_handler,                      // GPIO Port Q6
    default_int_handler,                      // GPIO Port Q7
    default_int_handler,                      // GPIO Port R
    default_int_handler,                      // GPIO Port S
    default_int_handler,                      // PWM 1 Generator 0
    default_int_handler,                      // PWM 1 Generator 1
    default_int_handler,                      // PWM 1 Generator 2
    default_int_handler,                      // PWM 1 Generator 3
    default_int_handler                       // PWM 1 Fault
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

