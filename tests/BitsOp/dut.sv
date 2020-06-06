 module dut( );

  typedef logic [31:0] sha_word_t;
  localparam int WordByte = $bits(sha_word_t)/8;

  typedef struct {
    logic valid;
    bit [8:1] data;
    } MyType;

  typedef bit[$bits(MyType):1] MyBits; //same as typedef bit [9:1] MyBits;
  MyBits b;
  

endmodule


module dmi_jtag ();

  typedef struct packed {
    logic [6:0]  address;
    logic [31:0] data;
    logic [1:0]  op;
  } dmi_t;

  logic [$bits(dmi_t)-1:0] dr_d, dr_q;
  
  dmi_t  dmi;
  assign dmi          = dmi_t'(dr_q);
  
  always_comb begin : p_shift

    if (shift_dr) begin
      if (dmi_access) begin
        dr_d = {dmi_tdi, dr_q[$bits(dr_q)-1:1]};
      end
    end

  end

endmodule : dmi_jtag
