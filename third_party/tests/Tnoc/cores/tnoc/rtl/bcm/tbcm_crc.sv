interface tbcm_crc
  import  tbcm_crc_pkg::*;
#(
  parameter int           DATA_WIDTH      = 8,
  parameter tbcm_crc_type CRC_TYPE        = TBCM_CRC_32,
  parameter int           CRC_WIDTH       = get_crc_width(CRC_TYPE),
  parameter bit [31:0]    CRC_POLYNOMIAL  = get_crc_polynomial(CRC_TYPE)
);
  localparam  int WORK_WIDTH  = DATA_WIDTH + CRC_WIDTH;

  function automatic bit [CRC_WIDTH-1:0] mod2(
    bit [WORK_WIDTH-1:0]  value,
    bit [CRC_WIDTH-1:0]   polynomial
  );
    bit [WORK_WIDTH-1:0]  work;

    work  = value;
    for (int i = WORK_WIDTH - 1;i >= CRC_WIDTH;--i) begin
      if (work[i]) begin
        work[i-1-:CRC_WIDTH]  ^= polynomial;
      end
    end

    return work[CRC_WIDTH-1:0];
  endfunction

  function automatic bit [CRC_WIDTH-1:0][DATA_WIDTH-1:0] get_crc_matrix();
    bit [CRC_WIDTH-1:0][DATA_WIDTH-1:0] matrix;

    for (int i = 0;i < DATA_WIDTH;++i) begin
      bit [CRC_WIDTH-1:0] remainder;

      remainder = mod2(WORK_WIDTH'(2**(i + CRC_WIDTH)), CRC_POLYNOMIAL);
      for (int j = 0;j < CRC_WIDTH;++j) begin
        matrix[j][i]  = remainder[j];
      end
    end

    return matrix;
  endfunction

  localparam  bit [CRC_WIDTH-1:0][DATA_WIDTH-1:0] CRC_MATRIX  = get_crc_matrix();

  function logic [CRC_WIDTH-1:0] get(logic [DATA_WIDTH-1:0] data);
    logic [CRC_WIDTH-1:0] crc;

    for (int i = 0;i < CRC_WIDTH;++i) begin
      crc[i]  = ^(data & CRC_MATRIX[i]);
    end

    return crc;
  endfunction
endinterface
