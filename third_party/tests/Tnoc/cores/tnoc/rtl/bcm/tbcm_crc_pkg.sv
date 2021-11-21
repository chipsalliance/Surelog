package tbcm_crc_pkg;
  typedef enum {
    TBCM_CRC_8_CCITT,
    TBCM_CRC_16_CCITT,
    TBCM_CRC_16,
    TBCM_CRC_32,
    TBCM_CRC_32C,
    TBCM_CRC_32K
  } tbcm_crc_type;

  function automatic int get_crc_width(tbcm_crc_type crc_type);
    case (crc_type)
      TBCM_CRC_8_CCITT:   return 8;
      TBCM_CRC_16_CCITT:  return 16;
      TBCM_CRC_16:        return 16;
      TBCM_CRC_32:        return 32;
      TBCM_CRC_32C:       return 32;
      TBCM_CRC_32K:       return 32;
      default:            return 0;
    endcase
  endfunction

  function automatic bit [31:0] get_crc_polynomial(tbcm_crc_type crc_type);
    case (crc_type)
      TBCM_CRC_8_CCITT:   return 'b0000_0000_0000_0000_0000_0000_1000_1101; //  x8 + x7 + x3 + x2 + 1
      TBCM_CRC_16_CCITT:  return 'b0000_0000_0000_0000_0001_0000_0010_0001; //  x16 + x12 + x5 + 1
      TBCM_CRC_16:        return 'b0000_0000_0000_0000_1000_0000_0000_0101; //  x16 + x15 + x2 + 1
      TBCM_CRC_32:        return 'b0000_0100_1100_0001_0001_1101_1011_0111; //  x32 + x26 + x23 + x22 + x16 + x12 + x11 + x10 + x8 + x7 + x5 + x4 + x2 + x + 1
      TBCM_CRC_32C:       return 'b0001_1110_1101_1100_0110_1111_0100_0001; //  x32 + x28 + x27 + x26 + x25 + x23 + x22 + x20 + x19 + x18 + x14 + x13 + x11 + x10 + x9 + x8 + x6 + 1
      TBCM_CRC_32K:       return 'b0111_0100_0001_1011_1000_1100_1101_0111; //  x32 + x30 + x29 + x28 + x26 + x20 + x19 + x17 + x16 + x15 + x11 + x10 + x7 + x6 + x4 + x2 + x + 1
      default:            return '0;
    endcase
  endfunction
endpackage
