Software
========

This section describes the programmers model for WDDR. As described earlier, the WDDR Physical Interface (PHY) IP includes an intergrated RISC-V MCU and dedicated SRAM for ITCM and DTCM. A software binary for the MCU is included with the WDDR hardware release.

MCU subsystem
-------------

* MCU core is lowRISC 32 bit ibex core (https://github.com/lowRISC/ibex)
* 64 kB ITCM
* 64 kB DTCM
* Mailbox communication with HOST

  * HOST to MCU mailbox
  * MCU to HOST mailbox

* Control registers for MCU

The high level description of MCU subsystem from software point of view is shown below.

.. figure:: mcu_subsystem.png
  :align:    center

  MCU subsystem

Mailbox Communication
---------------------

A four-register mailbox is supported to allow a HOST to send messages to the MCU:

* WAV_MCU__MCUINTF__HOST2MCU_MSG_DATA
* WAV_MCU__MCUINTF__HOST2MCU_MSG_ID
* WAV_MCU__MCUINTF__HOST2MCU_MSG_REQ
* WAV_MCU__MCUINTF__HOST2MCU_MSG_ACK

A four-register mailbox is supported to allow the MCU to send messages to a HOST:

* WAV_MCU__MCUINTF__MCU2HOST_MSG_DATA
* WAV_MCU__MCUINTF__MCU2HOST_MSG_ID
* WAV_MCU__MCUINTF__MCU2HOST_MSG_REQ
* WAV_MCU__MCUINTF__MCU2HOST_MSG_ACK

.. figure:: mcu_mailbox.png
  :align:    center

  MCU MailBox

The procedure to send a message from HOST to MCU is listed below:

#. HOST sets registers ``HOST2MCU_MSG_ID`` and ``HOST2MCU_MSG_DATA`` with required ID and DATA (list of supported ID/DATA is described below).
#. HOST sets ``HOST2MCU_MSG_REQ=0x1`` to inticate that MCU mailbox has a message.
#. MCU will read ``HOST2MCU_MSG_ID`` and ``HOST2MCU_MSG_DATA``.
#. MCU will clear ``HOST2MCU_MSG_REQ=0x0`` and set ``HOST2MCU_MSG_ACK=0x1`` acknowledging to the HOST that message has been received.
#. HOST need to clear ``HOST2MCU_MSG_ACK=0x0``.

Supported Messages
------------------

Messages from HOST to MCU
+++++++++++++++++++++++++

.. table::
  :widths: 20 20 20 80

  ============================= ================= ================= ========================================
  Name                          HOST2MCU_MSG_ID   HOST2MCU_MSG_DATA Description
  ============================= ================= ================= ========================================
  N/A                           0x0               N/A               Intentionally ommitted message
  Firmware Version Request      0x2               N/A               HOST is requesting Firmware version
  Hardware Version Request      0x4               N/A               HOST is requesting HW version
  MCU Boot Request              0x6               N/A               HOST is requesting to perform boot procedure
  ============================= ================= ================= ========================================

Messages from MCU to HOST
+++++++++++++++++++++++++

.. table::
  :widths: 20 20 20 80

  ================================= ================= ================= ========================================
  Name                              MCU2HOST_MSG_ID   MCU2HOST_MSG_DATA Description
  ================================= ================= ================= ========================================
  Message Interface Ready Response  0x1               N/A               MCU indicates messaging interface is ready to be used
  Firmware Version Response         0x3               $version          MCU is returning Firmware $version currentlly running on MCU
  Hardware Version Response         0x5               $version          MCU is returning HW $version
  MCU Boot Response                 0x7               $ret              MCU is responding boot has been complete ($ret = 0x0, SUCCESS; $ret = 0x1, FAILED)
  ================================= ================= ================= ========================================

Boot procedure (from HOST level)
--------------------------------

The boot procedure is listed in the order below:

#. Clear reset to WDDR.
#. Move ITCM image to ITCM address ``0x10000``.
#. Move DTCM image to DTCM address ``0x50000``.
#. Enable MCU by setting ``FETCH_EN=0x1`` within ``WAV_MCU__MCUTOP__CFG``.
#. Wait until mesage ``Message Interface Ready Response`` is received.
#. If desired, send ``Firmware/HW Version Request`` message and wait for MCU to respond.
#. Send ``MCU Boot Request`` message to MCU.
#. Wait till ``MCU Boot Response`` message is received.

Note, with current version of Firmware, MCU is performing boot automatically and messaging is not supported.
