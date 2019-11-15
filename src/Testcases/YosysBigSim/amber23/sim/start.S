	.section .text
	.extern main

start:
	/* Switch to User Mode */
	/* and unset interrupt mask bits */
	mov  r0, #0x00000000
	teqp pc, r0 

	/* Enable the cache */
	mov  r0, #0x00000001 /* (only set 1st 2MB block as cacheable) */
	mcr  15, 0, r0, cr3, cr0, 0   /* cacheable area */
	mov  r0, #1
	mcr  15, 0, r0, cr2, cr0, 0   /* cache enable */

	/* initialize the stack pointer to end of 64kB memeory */
	mov  sp, #0x00010000

	/* jump to main */
	bl main

	/* freeze in endless loop */
endloop:
	b endloop
