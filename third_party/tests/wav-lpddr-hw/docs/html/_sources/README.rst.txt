https://github.com/waviousllc/wav-lpddr-hw

.. figure :: wavious_logo.png
  :align:    center

WDDR PHY
========
The Wavious DDR (WDDR) Physical interface (PHY) is designed to be a scalable DDR PHY IP that meets high performance, low area, and low power
requirements across multiple JEDEC DRAM protocols. Initially targeting LPDDR4x and LPDDR5, the WDDR PHY supports LPDDR JEDEC protocols and a DFIv5
compliant interface.

Features
++++++++
* LPDDR4x @4266 Gbps
* LPDDR5 @6400 Gbps
* Dual rank support
* DFI5.0 compliant Memory Controller interface
* Integrated MicroController Unit (MCU) with embedded SRAM
* Embedded training buffer
* Embedded calibration logic
* Embedded high-performance and low jitter PLL
* Per-bit deskew

Tools Required
--------------
The WDDR UVM testbench has been developed with Cadence VIP and simulators. Users must encuse that IP and tools have been installed.

Run your first sim
------------------
Ensure that Cadence VIPs and Xcelium (20.09.003) are installed. Update verif/run/simulate.sh variables are needed.

::

  cd verif/run
  ./simulate.sh
