/*
 * SPDX-License-Identifier: BSD-2-Clause
 *
 * Copyright (c) 2019 Western Digital Corporation or its affiliates.
 */

#include <sbi/riscv_asm.h>
#include <sbi/riscv_encoding.h>
#include <sbi/sbi_const.h>
#include <sbi/sbi_platform.h>

#include <libfdt.h>
#include <sbi_utils/fdt/fdt_fixup.h>
#include <sbi_utils/fdt/fdt_helper.h>
#include <sbi_utils/irqchip/fdt_irqchip.h>
#include <sbi_utils/serial/fdt_serial.h>
#include <sbi_utils/timer/fdt_timer.h>
#include <sbi_utils/ipi/fdt_ipi.h>
#include <sbi_utils/reset/fdt_reset.h>

/*
 * Include these files as needed.
 * See config.mk PLATFORM_xxx configuration parameters.
 */
#include <sbi_utils/irqchip/plic.h>
#include <sbi_utils/serial/uart8250.h>
#include <sbi_utils/sys/clint.h>

uint64_t* getchar_ptr  = (uint64_t*)(0x00100000);
uint64_t* putchar_ptr  = (uint64_t*)(0x00101000);
uint64_t* poweroff_ptr = (uint64_t*)(0x00102000);

/*
 * Platform early initialization.
 */
static int platform_early_init(bool cold_boot)
{
	return 0;
}

/*
 * Platform final initialization.
 */
static int platform_final_init(bool cold_boot)
{
	return 0;
}

/*
 * Initialize the platform console.
 */
static int platform_console_init(void)
{
	return 0;
}

/*
 * Write a character to the platform console output.
 */
static void platform_console_putc(char ch)
{
	*putchar_ptr = ch;
}

/*
 * Read a character from the platform console input.
 */
static int platform_console_getc(void)
{
	int ch = *getchar_ptr;
	return ch;
}

/*
 * Initialize the platform interrupt controller for current HART.
 */
static int platform_irqchip_init(bool cold_boot)
{
	return 0;
}

/*
 * Initialize IPI for current HART.
 */
/*
static int platform_ipi_init(bool cold_boot)
{
	return 0;
} */

/*
 * Send IPI to a target HART
 */
static void platform_ipi_send(u32 target_hart)
{
	/* Example if the generic CLINT driver is used */
	clint_ipi_send(target_hart);
}

/*
 * Clear IPI for a target HART.
 */
static void platform_ipi_clear(u32 target_hart)
{
	/* Example if the generic CLINT driver is used */
	clint_ipi_clear(target_hart);
}

/*
 * Initialize platform timer for current HART.
 */
/*
static int platform_timer_init(bool cold_boot)
{
	return 0;
} */

/*
 * Get platform timer value.
 */
static u64 platform_timer_value(void)
{
	/* Example if the generic CLINT driver is used */
	return clint_timer_value();
}

/*
 * Start platform timer event for current HART.
 */
static void platform_timer_event_start(u64 next_event)
{
	/* Example if the generic CLINT driver is used */
	clint_timer_event_start(next_event);
}

/*
 * Stop platform timer event for current HART.
 */
static void platform_timer_event_stop(void)
{
	/* Example if the generic CLINT driver is used */
	clint_timer_event_stop();
}

/*
 * Reset the platform.
 */
static int platform_system_reset(u32 type)
{
	*poweroff_ptr = type;
	return 0;
}

/*
 * Platform descriptor.
 */
const struct sbi_platform_operations platform_ops = {
	.early_init		= platform_early_init,
	.final_init		= platform_final_init,
	.console_putc		= platform_console_putc,
	.console_getc		= platform_console_getc,
	.console_init		= platform_console_init,
	.irqchip_init		= platform_irqchip_init,
	.ipi_send		= platform_ipi_send,
	.ipi_clear		= platform_ipi_clear,
	.ipi_init		= fdt_ipi_init,
	.timer_value		= platform_timer_value,
	.timer_event_stop	= platform_timer_event_stop,
	.timer_event_start	= platform_timer_event_start,
	.timer_init		= fdt_timer_init,
	.system_reset		= platform_system_reset
};
const struct sbi_platform platform = {
	.opensbi_version	= OPENSBI_VERSION,
	.platform_version	= SBI_PLATFORM_VERSION(0x0, 0x00),
	.name			= "BlackParrot",
	.features		= SBI_PLATFORM_DEFAULT_FEATURES,
	.hart_count		= 1,
	.hart_stack_size	= SBI_PLATFORM_DEFAULT_HART_STACK_SIZE,
	.platform_ops_addr	= (unsigned long)&platform_ops
};
