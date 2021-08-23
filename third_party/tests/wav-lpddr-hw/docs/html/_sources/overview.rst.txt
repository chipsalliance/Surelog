Overview
========

In modern System-On-Chip (SoC) platforms a low-latency and high-bandwidth path to DRAM is critical to meet CPU, GPU, and NPU workloads and performance requirements.

The DDR Physical Interface (PHY) IP provides an interface to external DRAM and is an important component to meet system performance requirements.

.. figure:: system_diagram.png
  :align:    center

  System Block Diagram

The Wavious DDR PHY (WDDR) is designed to be a scalable, high performance, low power, and low area PHY that is compliant to multiple JEDEC specifications.

.. figure:: top_level_diagram.png
  :align:    center

  DDR PHY Top Level Block Diagram

Features
--------

The DDR PHY supports the following features:

* LPDDR4x compliant interface @4266Mbps
* LPDDR5 compliant interface @6400Mbps
* DFIv5.0 compliant Memory Controller interface
* AHB-Lite configuration interface
* Fast frequency switching
* Embedded low-jitter PLL
* Embedded RISC-V MCU + SRAM
* Self-contained training and calibration
* Easily portable to various technology nodes
* Parameterizable pipeline stages for ease of timing closure
* Power states and clock gating
