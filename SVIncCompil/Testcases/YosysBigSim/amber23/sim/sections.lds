SECTIONS {
	.memory : {
		. = 0x000000;
		start*(.text);
		*(.text*);
		*(.data*);
		*(.rodata*);
 		*(.bss*);
		__stack = .;
	}
}

