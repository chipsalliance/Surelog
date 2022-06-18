
OUTPUT_ARCH( "riscv" )
ENTRY(_start)

SECTIONS {
  .text   : { *(.text*) }
 _end = .;
  . = 0xd0580000;
  .data.io   : { *(.data.io) }
  . = 0xf0040000;
  .data  :  { *(.*data) *(.rodata*) *(.*bss) STACK = ALIGN(16) + 0x1000;}
  . = 0xfffffff8;
  .data.ctl : { LONG(0xf0040000); LONG(STACK) }
}
