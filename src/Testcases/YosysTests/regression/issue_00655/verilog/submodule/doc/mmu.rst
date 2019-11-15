
LatticeMico32 Memory Managerment Unit
=====================================

:Author: Yann Sionneau
:Contact: yann.sionneau@gmail.com
:Version: 1.0
:Date: June 2013
:Copyright: Permission is granted to copy, distribute and/or modify this
            document under the terms of the BSD License.


Overview
--------

This document describes the LatticeMico32 MMU (Memory Management Unit)
features and how it can be configured.

This MMU is not part of the original LatticeMico32 CPU, it has been added
by Yann Sionneau with the help of the Milkymist community in general and
Michael Walle in particular.

The LM32 MMU has been designed with "simplicity" in head, KISS (Keep It
Simple Stupid) is the motto.

Only the minimum has been implemented to have the minimalistic features
which would allow a modern Operating System like Linux or \*BSD to run,
providing virtual memory and memory protection.

The Caches are designed to be VIPT (Virtually Indexed Physically Tagged) to
allow the TLB lookup to take place in parallel of the cache lookup so that
we don't need to stale the pipeline.


Features
--------

 * 1024 entries ITLB (Instruction Translation Lookaside Buffer)
 * 1024 entries DTLB (Data Translation Lookaside Buffer)
 * CPU exceptions generated upon

   * ITLB miss
   * DTLB miss
   * DTLB page fault (writing to a read-only page)

 * I/D TLB lookup in parallel of the I/D Cache lookup to avoid lookup penalties
 * 4 kB pages

As you can see, it is quite minimalistic, here is a list of what's not
featured by this MMU:

 * No hardware page tree walker
 * No dirty or present bit
 * No ASID (Address Space Identifier)
 * No lockable TLB entries
 * Only 1 page size supported: 4 kB


TLB Layout
----------

Let's name our 32 bits virtual address "vaddr".

Let's name our 32 bits physical address "paddr".

Let's say vaddr[0] is the Lowest Significant Bit and vaddr[31] the Most
Significant Bit.

Let's say vaddr[11:0] is the part of vaddr represented by its 12 Lowest
Significant Bits.

Deep inside, the TLB is a **Direct-mapped**, **VIVT** (Virtually Indexed
Virtually Tagged) Cache.

When the LM32 core is synthetized with MMU support, the CPU pipeline Data
and Instruction Caches turn into **VIPT** (Virtually Indexed Physically
Tagged) Caches.

The TLB is indexed by vaddr[21:12]: The bottom 10 LSB of the virtual PFN
(Page Frame Number).

A TLB entry holds: Physical PFN, Physical Tag, Cache inhibit flag (for
DTLB), Read-only flag (for DTLB), Valid entry tag

More precisely:

 * A valid DTLB entry: paddr[31:12], vaddr[31:22], paddr[2], paddr[1], 1
 * An invalid DTLB entry: paddr[31:12], vaddr[21:22], paddr[2], paddr[1], 0
 * A valid ITLB entry: paddr[31:12], vaddr[31:22], 1
 * An invalid ITLB entry: paddr[31:12], vaddr[31:22], 0

The meaning of paddr[2] and paddr[1] will be explained later on in the
section which explains how to program the MMU using LM32 assembly
instructions.


Interact with the TLB
---------------------

In order to interact with the TLB, three CSR (Control and Status Registers)
have been added to the LM32 CPU:

+-------------+--------------------------------------------------+--------+
| CSR         | Description                                      | R/W    |
+=============+==================================================+========+
| TLBVADDR    | You can write the virtual pfn of the entry you   | R/W    |
|             | want to update or invalidate or cause a TLB      |        |
|             | flush. You can read the virtual pfn causing a    |        |
|             | TLB miss or fault.                               |        |
+-------------+--------------------------------------------------+--------+
| TLBPADDR    | Your can write the physical pfn of the entry you | W only |
|             | want to update.                                  |        |
+-------------+--------------------------------------------------+--------+
| TLBBADVADDR | You can read the virtual address which caused    | R only |
|             | the TLB exception.                               |        |
+-------------+--------------------------------------------------+--------+

 * TLBVADDR: holds a virtual address
 * TLBPADDR: holds a physical address

A CSR register can be written to like this:

The following code writes the content of the R1 register to TLBVADDR CSR::

  wcsr TLBVADDR, r1

A CSR register can be read from like this:

The following code writes the content of TLBPADDR CSR to the R1 register::

  rcsr r1, TLBPADDR


Add or Update a TLB entry
~~~~~~~~~~~~~~~~~~~~~~~~~

First, make sure vaddr[2:0] == "000" (or 3'b0 in verilog) as those 3 bits
will be used for other TLB operations.

Then, write the virtual address to the TLBVADDR CSR.

Then you need to do a logical "OR" operation on the physical address to set
paddr[2:0] according to your needs:

 * paddr[2] set to 1 means the page won't be cached by LM32 Data Cache
   (only for Data Cache / DTLB)
 * paddr[1] set to 1 means the Page is Read-only (only valid for DTLB)
 * paddr[0] set to 1 means you want to update DTLB, use 0 for ITLB

Then, you need to write the OR'ed physical address to the TLBPADDR CSR.

The TLB entry update will be triggered by the write to TLBPADDR CSR.

Code samples::

  #define PAGE_SIZE (1 << 12)
  #define PAGE_MASK (PAGE_SIZE - 1)

  void update_dtlb_entry(unsigned int vaddr, unsigned int paddr,
                         bool read-only, bool not_cached)
  {
    paddr &= ~PAGE_MASK; /* Make sure page offset is zeroed */
    vaddr &= ~PAGE_MASK; /* Make sure page offset is zeroed */
    paddr |= 1; /* This means we are addressing DTLB */

    if (read-only)
        paddr |= 2;

    if (not_cached)
        paddr |= 4;

    asm volatile("wcsr TLBVADDR, %0" :: "r"(vaddr) : );
    asm volatile("wcsr TLBPADDR, %0" :: "r"(paddr) : );
  }

  void update_itlb_entry(unsigned int vaddr, unsigned int paddr)
  {
    paddr &= ~PAGE_MASK; /* Make sure page offset is zeroed */
    vaddr &= ~PAGE_MASK; /* Make sure page offset is zeroed */
    /* We don't set paddr[0] which means we are addressing ITLB */

    asm volatile("wcsr TLBVADDR, %0" :: "r"(vaddr) : );
    asm volatile("wcsr TLBPADDR, %0" :: "r"(paddr) : );
  }


Invalidate a TLB entry or flush the entire TLB
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

First, you need to do a logical "OR" operation on the virtual address to
set vaddr[2:0] according to your needs:

 * vaddr[2] set to 1 will trigger a flush of the entire selected TLB
 * vaddr[1] set to 1 will trigger the invalidation of the entry indexed by
   vaddr[21:12] inside the selected TLB
 * vaddr[0] set to 1 means you want to operate on DTLB, use 0 for ITLB

The action is triggered upon the write of the OR'ed virtual address to the
TLBVADDR CSR.

Code samples::

  #define PAGE_SIZE (1 << 12)
  #define PAGE_MASK (PAGE_SIZE - 1)

  void invalidate_dtlb_entry(unsigned int vaddr)
  {
    vaddr &= ~PAGE_MASK; /* Make sure page offset is zeroed */
    /*
     * 1 because we are addressing DTLB
     * 2 because we want to invalidate a specific line
     */
    vaddr |= 1 | 2;

    asm volatile("wcsr TLBVADDR, %0" :: "r"(vaddr) : );
  }

  void invalidate_itlb_entry(unsigned int vaddr)
  {
    vaddr &= ~PAGE_MASK; /* Make sure page offset is zeroed */
    vaddr |= 2; /* 2 because we want to invalidate a specific line */

    asm volatile("wcsr TLBVADDR, %0" :: "r"(vaddr) : );
  }

  void flush_dtlb(void)
  {
    unsigned int cmd = 1 | 4;
    asm volatile("wcsr TLBVADDR, %0" :: "r"(cmd) : );
  }

  void flush_itlb(void)
  {
    unsigned int cmd = 4;
    asm volatile("wcsr TLBVADDR, %0" :: "r"(cmd) : );
  }


A sum up of TLB actions
~~~~~~~~~~~~~~~~~~~~~~~

To summarize all possible TLB actions:

 * Writing to TLBPADDR triggers the update of a TLB entry according to the
   content of TLBVADDR and TLBPADDR
 * Writing to TLBVADDR either prepares for updating a TLB entry if it is
   followed by a write operation to TLBPADDR or immediately triggers an
   action determined by bits vaddr[2:0] written to TLBVADDR. In the latter
   case, the action is performed on the TLB entry indexed by vaddr[21:12].

Possible actions triggered by writing to TLBVADDR:

+------------+------------------------------------------------------------+
| vaddr[2:0] | action                                                     |
+============+============================================================+
| 000        | No Operation, used for updating TLB entry by writting to   |
|            | TLBPADDR                                                   |
+------------+------------------------------------------------------------+
| 011        | Invalidate DTLB entry indexed by vaddr[21:12]              |
+------------+------------------------------------------------------------+
| 010        | Invalidate ITLB entry indexed by vaddr[21:12]              |
+------------+------------------------------------------------------------+
| 101        | Flush DTLB                                                 |
+------------+------------------------------------------------------------+
| 100        | Flush ITLB                                                 |
+------------+------------------------------------------------------------+
| 11x        | Not deterministic, do not use untill it's defined by a     |
|            | future MMU revision                                        |
+------------+------------------------------------------------------------+


Interact with the MMU
---------------------

In order to interact with the MMU, a new CSR (Control and Status Register)
has been added: PSW (Processor Status Word)

+-------+--------+--------------------------------------------------------+
| Bits  | Name   | Description                                            |
+=======+========+========================================================+
| 31:12 |        | *unused*                                               |
+-------+--------+--------------------------------------------------------+
| 11    | BUSR   | Breakpoint backup of USR                               |
+-------+--------+--------------------------------------------------------+
| 10    | EUSR   | Exception backup of USR                                |
+-------+--------+--------------------------------------------------------+
| 9     | USR    | User mode bit                                          |
+-------+--------+--------------------------------------------------------+
| 8     | BDTLBE | Breakpoint backup of DTLBE                             |
+-------+--------+--------------------------------------------------------+
| 7     | EDTLBE | Exception backup of DTLBE                              |
+-------+--------+--------------------------------------------------------+
| 6     | DTLBE  | DTLB enabled                                           |
+-------+--------+--------------------------------------------------------+
| 5     | BITLBE | Breakpoint backup of ITLBE                             |
+-------+--------+--------------------------------------------------------+
| 4     | EITLBE | Exception backup of ITLBE                              |
+-------+--------+--------------------------------------------------------+
| 3     | ITLBE  | ITLB enabled                                           |
+-------+--------+--------------------------------------------------------+
| 2     | IE.BIE | See note below                                         |
+-------+--------+                                                        |
| 1     | IE.EIE |                                                        |
+-------+--------+                                                        |
| 0     | IE.IE  |                                                        |
+-------+--------+--------------------------------------------------------+

.. Note::

  PSW[2:0] is a real mirror of IE[2:0] as described in the LatticeMico32
  Processor Reference Manual p. 10 Table 5 "Fields of the IE CSR". In any
  condition: PSW[2:0] == IE[2:0]. IE CSR is mirrored in the lower bits of
  PSW CSR for compatibility reasons. Old programs (ignorant of the MMU)
  will keep using IE CSR, newer programs can use PSW to deal with MMU and
  interrupts.


Activate the MMU
~~~~~~~~~~~~~~~~

Activating the MMU is done by activating each TLB by writing 1 into
PSW[ITLBE] and PSW[DTLBE]::

  void enable_mmu(void)
  {
    asm volatile("rcsr r1, PSW\n\t"
                 "ori r1, r1, 72\n\t"
                 "wcsr PSW, r1" ::: "r1");
  }


Deactivate the MMU
~~~~~~~~~~~~~~~~~~

Deactivating the MMU is done by deactivating each TLB by writing 0 into
PSW[ITLBE] and PSW[DTLBE]::

  void disable_mmu(void)
  {
    unsigned int mask = ~(72);
    asm volatile("rcsr r1, PSW\n\t"
                 "and r1, r1, %0\n\t"
                 "wcsr PSW, r1" :: "r"(mask) : "r1");
  }


TLB lookups
-----------

This section explains in details how the TLB lookup takes place: what
happens in which condition.

If the TLBs are disabled, nothing special happens, LM32 will behave as if
it has been synthetized without MMU support (except for the presence of
PSW, TLBVADDR and TLBPADDR).

If DTLB is enabled:

In parallel of the Data Cache lookup, the DTLB lookup happens.

DTLB is indexed by vaddr[21:11].

If the DTLB entry is invalid (i.e. invalid bit is set), then the DTLB
generates a DTLB miss exception.

If the DTLB entry is valid, the DTLB compares vaddr[31:22] with the DTLB
entry tag, if this comparison fails: the DTLB generates a DTLB miss
exception as well.

If the DTLB entry is valid and the vaddr[31:22] matches the DTLB entry tag:

 * Then if the memory access was a READ (lb, lbu, lh, lhu, lw)

   * the Data Cache compares the tag of its selected line with the
     paddr[31:12] extracted from the DTLB to check if we Hit or Miss the
     Data Cache
   * Then the usual Cache refill happens (using the physical address) in
     case of a cache miss
   * Then if the memory access was a WRITE (sb, sh, sw)

     * The read-only bit flag contained in the DTLB entry is checked
     * If it is set: it triggers a DTLB fault CPU exception
     * If it's not set: The Data Cache does the same tag comparison as with
       the READ operation to check for Cache Hit/Miss

All these behaviours are summed up in the following table:

+------------+-----+------------------------------------------------------+
| Exception  | EID | Condition                                            |
+------------+-----+------------------------------------------------------+
| ITLB miss  | 8   | If **any** of these conditions holds:                |
|            |     |                                                      |
|            |     | * ITLB entry is invalid                              |
|            |     | * ITLB entry tag does not match vaddr[31:22]         |
+------------+-----+------------------------------------------------------+
| DTLB miss  | 9   | If **any** of these conditions holds:                |
|            |     |                                                      |
|            |     | * DTLB entry is invalid                              |
|            |     | * DTLB entry tag does not match vaddr[31:22]         |
+------------+-----+------------------------------------------------------+
| DTLB fault | 10  | If **all** of these conditions holds:                |
|            |     |                                                      |
|            |     | * DTLB entry is valid                                |
|            |     | * the tag entry matches vaddr[31:22]                 |
|            |     | * the read-only bit is set                           |
|            |     | * the CPU is doing a memory store                    |
+------------+-----+------------------------------------------------------+
| Privilege  | 11  | If PSW[USR] == 1 and one of these instructions is    |
|            |     | exeucted:                                            |
|            |     |                                                      |
|            |     | * iret                                               |
|            |     | * bret                                               |
|            |     | * wcsr                                               |
+------------+-----+------------------------------------------------------+


CSR registers special behaviours
--------------------------------

Upon any exception, PSW CSR is modified automatically by the CPU pipeline
itself:

 * PSW[ITLBE] is saved in PSW[EITLBE] and the former is cleared
 * PSW[DTLBE] is saved in PSW[EDTLBE] and the former is cleared
 * PSW[USR] is saved in PSW[EUSR] and the former is cleared
 * TLBVADDR is pre-charged with the virtual PFN (page frame number) which
   caused an exception (in case of TLB miss or fault only)

   * TLBVADDR[0] is set to 1 when then exception is caused by DTLB, else it
     is clear
   * In case of DTLB miss or fault, TLBVADDR[31:12] is pre-charged the
     virtual PFN whose load or store operation caused the exception
   * In case of ITLB miss, TLBVADDR[31:12] is pre-charged with the virtual
     PFN of the instruction whose fetch caused the exception
   * This mechanism allows for faster TLB miss handling because TLBVADDR is
     already pre-charged with the right value
   * Since TLBVADDR is pre-charged with the virtual PFN: page offset bits
     (TLBVADDR[11:1]) are not set

 * TLBBADVADDR\ :sup:`\*\*` is written with a virtual address when an
   exception is caused by a TLB miss

   * In case of ITLB miss, TLBBADVADDR[31:2] contains the PC address whose
     fetch triggered the ITLB miss exception. Instructions being 32 bits
     aligned, PC[1:0] is always 00.
   * In case of DTLB miss or fault, TLBBADVADDR[31:0] contains the virtual
     address whose load or store operation caused the exception
   * Unlike TLBVADDR, TLBBADVADDR page offset bits are set according to
     what caused the exception

(\*) In LM32 pipeline, exception happens in the e\ **X**\ ecute stage, even
though they may be triggered in the **F**\ etch or **M**\ emory stage for
example. Load and Store instructions therefore stall the pipeline for 1
cycle during the e\ **X**\ ecute stage if the DTLB is activated.

(\*\*) TLBBADVADDR is the same CSR ID as TLBPADDR. The former is read-only
and the latter is write-only.

Upon any breakpoint hit, PSW CSR is also modified by the CPU pipeline:

 * PSW[ITLBE] is saved in PSW[BITLBE] and the former is cleared
 * PSW[DTLBE] is saved in PSW[BDTLBE] and the former is cleared
 * PSW[USR] is saved in PSW[BUSR] and the former is cleared

This means MMU is **turned off** upon CPU exception or breakpoint hit.

Upon return from exception (**iret** instruction), PSW CSR is also modified
by the CPU pipeline:

 * PSW[ITLBE] is restored using the value from PSW[EITLBE]
 * PSW[DTLBE] is restored using the value from PSW[EDTLBE]
 * PSW[USR] is restored using the value from PSW[EUSR]

Upon return from breakpoint (\textbf{bret} instruction), PSW CSR is also
modified by the CPU pipeline:

 * PSW[ITLBE] is restored using the value from PSW[BITLBE]
 * PSW[DTLBE] is restored using the value from PSW[BDTLBE]
 * PSW[USR] is restored using the value from PSW[BUSR]
