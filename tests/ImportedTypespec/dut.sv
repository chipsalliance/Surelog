package spi_device_pkg;
   parameter int unsigned SramAw = 10;
   typedef logic [SramAw-1:0] sram_addr_t;
endpackage // spi_device_pkg

module top(output int o);
   import spi_device_pkg::*;

   assign o = $bits(sram_addr_t);
endmodule

