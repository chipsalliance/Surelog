## uart_csr

* byte_size
    * 32

|name|offset_address|
|:--|:--|
|[rbr](#uart_csr-rbr)|0x00|
|[thr](#uart_csr-thr)|0x00|
|[ier](#uart_csr-ier)|0x04|
|[iir](#uart_csr-iir)|0x08|
|[fcr](#uart_csr-fcr)|0x08|
|[lcr](#uart_csr-lcr)|0x0c|
|[mrc](#uart_csr-mrc)|0x10|
|[lsr](#uart_csr-lsr)|0x14|
|[msr](#uart_csr-msr)|0x18|
|[scratch](#uart_csr-scratch)|0x1c|
|[dll](#uart_csr-dll)|0x00|
|[dlm](#uart_csr-dlm)|0x04|

### <div id="uart_csr-rbr"></div>rbr

* offset_address
    * 0x00
* type
    * indirect
* index_bit_fields
    * lcr.dlab: 0
* comment
    * Receiver Buffer Register

|name|bit_assignments|type|initial_value|reference|labels|comment|
|:--|:--|:--|:--|:--|:--|:--|
|rbr|[7:0]|rotrg|||||

### <div id="uart_csr-thr"></div>thr

* offset_address
    * 0x00
* type
    * indirect
* index_bit_fields
    * lcr.dlab: 0
* comment
    * Transmitter Holding Register

|name|bit_assignments|type|initial_value|reference|labels|comment|
|:--|:--|:--|:--|:--|:--|:--|
|thr|[7:0]|wotrg|0xff||||

### <div id="uart_csr-ier"></div>ier

* offset_address
    * 0x04
* type
    * indirect
* index_bit_fields
    * lcr.dlab: 0
* comment
    * Interrupt Enable Register

|name|bit_assignments|type|initial_value|reference|labels|comment|
|:--|:--|:--|:--|:--|:--|:--|
|erbfi|[0]|rw|0x0|||Enable Received Data Available Interrupt<br>0: Disables Received Data Available Interrupts<br>1: Enables Received Data Available Interrupts|
|etbei|[1]|rw|0x0|||Enable Transmitter Holding Register Empty Interrupt<br>0: Disables Transmitter Holding Register Empty Interrupts<br>1: Enables Transmitter Holding Register Interrupts|
|elsi|[2]|rw|0x0|||Enable Receiver Line Status Interrupt<br>0: Disables Receiver Line Status Interrupts<br>1: Enables Receiver Line Status Interrupts|
|edssi|[3]|rw|0x0|||Enable Modem Status Interrupt<br>0: Disables Modem Status Interrupts<br>1: Enables Modem Status Interrupts|

### <div id="uart_csr-iir"></div>iir

* offset_address
    * 0x08
* type
    * default
* comment
    * Interrupt Identification Register

|name|bit_assignments|type|initial_value|reference|labels|comment|
|:--|:--|:--|:--|:--|:--|:--|
|intpend|[0]|ro|0x1|||0: Interrupt is pending<br>1: No interrupt is pending|
|intid2|[3:1]|ro|0x0|||Interrupt ID<br>011: Receiver Line Status (Highest)<br>010: Received Data Available (Second)<br>110: Character Timeout (Second)<br>001: Transmitter Holding Register Empty (Third)<br>000: Modem Status (Fourth)|

### <div id="uart_csr-fcr"></div>fcr

* offset_address
    * 0x08
* type
    * default
* comment
    * FIFO Control Register

|name|bit_assignments|type|initial_value|reference|labels|comment|
|:--|:--|:--|:--|:--|:--|:--|
|fifoen|[0]|wo|0x0|||FIFO Enable<br>1: Enables FIFOs|
|rcvr_fifo_reset|[1]|w1trg||||Receiver FIFO Reset<br>1: Resets RCVR FIFO|
|xmit_fifo_reset|[2]|w1trg||||Transmitter FIFO Reset<br>1: Resets XMIT FIFO|
|dma_mode_select|[3]|wo|0x0|||DMA Mode Select<br>0: Mode 0<br>1: Mode 1|
|rcvr_fifo_trigger_level|[7:6]|wo|0x0|||RCVR FIFO Trigger Level<br>0b00: 1 byte<br>0b01: 4 bytes<br>0b10: 8 bytes<br>0b11: 14 bytes|

### <div id="uart_csr-lcr"></div>lcr

* offset_address
    * 0x0c
* type
    * default
* comment
    * line control register

|name|bit_assignments|type|initial_value|reference|labels|comment|
|:--|:--|:--|:--|:--|:--|:--|
|wls|[1:0]|rw|0x3|||Word Length Select<br>0b00: 5 bits/character<br>0b01: 6 bits/character<br>0b10: 7 bits/character<br>0b11: 8 bits/character|
|stb|[2]|rw|0x0|||Number of Stop Bits<br>0: 1 Stop bit<br>1: 2 Stop bits or 1.5, if 5 bits/character selected|
|pen|[3]|rw|0x0|||Parity Enable<br>1: Enables parity<br>0: Disables parity|
|eps|[4]|rw|0x0|||Even Parity Select<br>1: Selects Even parity<br>0: Selects Odd parity|
|stick_parity|[5]|rw|0x0|||Stick Parity<br>1: Stick Parity is enabled<br>0: Stick Parity is disabled|
|set_break|[6]|rw|0x0|||Set Break<br>1: Enables break condition<br>0: Disables break condition|
|dlab|[7]|rw|0x0|||Divisor Latch Access Bit.<br>1: Allows access to the Divisor Latch Registers and reading of the FIFO Control Register<br>0: Allows access to RBR, THR, IER and IIR registers|

### <div id="uart_csr-mrc"></div>mrc

* offset_address
    * 0x10
* type
    * default
* comment
    * Modem Control Register

|name|bit_assignments|type|initial_value|reference|labels|comment|
|:--|:--|:--|:--|:--|:--|:--|
|dtr|[0]|rw|0x0|||Data Terminal Ready<br>1: Drives DTRN Low<br>0: Drives DTRN High|
|rts|[1]|rw|0x0|||Request To Send<br>1: Drives RTSN Low<br>0: Drives RTSN High|
|out1|[2]|rw|0x0|||User Output 1<br>1: Drives OUT1N Low<br>0: Drives OUT1N High|
|out2|[3]|rw|0x0|||User Output 2<br>1: Drives OUT1N Low<br>0: Drives OUT1N High|
|loop|[4]|rw|0x0|||Loop Back<br>1: Enables loop back|

### <div id="uart_csr-lsr"></div>lsr

* offset_address
    * 0x14
* type
    * default
* comment
    * Line Status Register

|name|bit_assignments|type|initial_value|reference|labels|comment|
|:--|:--|:--|:--|:--|:--|:--|
|dr|[0]|ro|0x0|||Data Ready<br>0: All the data in RBR or FIFO is read<br>1: Complete incoming character has been received and transferred into the RBR of FIFO|
|oe|[1]|rotrg|0x0|||Overrun Error|
|pe|[2]|rotrg|0x0|||Parity Error|
|fe|[3]|rotrg|0x0|||Framing Error|
|bi|[4]|rotrg|0x0|||Break Interrupt|
|thre|[5]|ro|0x0|||Transmitter Holding Register Empty<br>0: THR or Transmitter FIFO has data to transmit<br>1: THR and Transmitter FIFO are empty|
|temt|[6]|ro|0x0|||Transmitter Empty:<br>0: THR or Transmitter shift register contains data<br>1: THR, Transmitter FIFO and Transmitter shift register are empty|
|error_in_rcvr_fifo|[7]|ro|0x0|||RCVR FIFO contains at least one receiver error (Parity, Framing, Break condition)|

### <div id="uart_csr-msr"></div>msr

* offset_address
    * 0x18
* type
    * default
* comment
    * Modem Status Register

|name|bit_assignments|type|initial_value|reference|labels|comment|
|:--|:--|:--|:--|:--|:--|:--|
|dcts|[0]|rotrg|0x0|||Delta Clear To Send<br>Change in CTSN after last MSR read|
|ddsr|[1]|rotrg|0x0|||Delta Data Set Ready<br>Change in DSRN after last MSR read|
|teri|[2]|ro|0x0|||Trailing Edge Ring Indicator<br>RIN has changed from a Low to a High|
|ddcd|[3]|rotrg|0x0|||Delta Data Carrier Detect<br>Change in DCDN after last MSR read|
|cts|[4]|ro||||Clear To Send<br>Complement of CTSN input|
|dsr|[5]|ro||||Data Set Ready<br>Complement of DSRN input|
|ri|[6]|ro||||Ring Indicator<br>Complement of RIN input|
|dcd|[7]|ro||||Data Carrier Detect<br>Complement of DCDN input|

### <div id="uart_csr-scratch"></div>scratch

* offset_address
    * 0x1c
* type
    * default
* comment
    * Scratch Register

|name|bit_assignments|type|initial_value|reference|labels|comment|
|:--|:--|:--|:--|:--|:--|:--|
|scratch|[7:0]|rw|0x00||||

### <div id="uart_csr-dll"></div>dll

* offset_address
    * 0x00
* type
    * indirect
* index_bit_fields
    * lcr.dlab: 1
* comment
    * Divisor Latch (Least Significant Byte) Register

|name|bit_assignments|type|initial_value|reference|labels|comment|
|:--|:--|:--|:--|:--|:--|:--|
|dll|[7:0]|rw|default: 0x00||||

### <div id="uart_csr-dlm"></div>dlm

* offset_address
    * 0x04
* type
    * indirect
* index_bit_fields
    * lcr.dlab: 1
* comment
    * Divisor Latch (Most Significant Byte) Register

|name|bit_assignments|type|initial_value|reference|labels|comment|
|:--|:--|:--|:--|:--|:--|:--|
|dlm|[7:0]|rw|default: 0x00||||
