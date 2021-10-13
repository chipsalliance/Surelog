package spi_device_reg_pkg;
   parameter int unsigned NumCmdInfo = 24;
endpackage // spi_device_reg_pkg

package spi_device_pkg;
   typedef enum int unsigned {
      CmdInfoReserveEnd = spi_device_reg_pkg::NumCmdInfo
   } cmd_info_index_e;
endpackage // spi_device_pkg

