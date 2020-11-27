package prim_pkg;

  // Implementation target specialization
  typedef enum integer {
    ImplGeneric = 1,
    ImplXilinx  = 0
  } impl_e;

endpackage

module prim_diff_decode ();
  parameter prim_pkg::impl_e Impl = prim_pkg::ImplGeneric;


    import prim_pkg::*;

    if (Impl == ImplGeneric) begin : gen_pad_generic

    always_comb begin : p_diff_fsm
     
      unique case (state_q)
        // we remain here as long as
        // the diff pair is correctly encoded
        IsSkewed: begin
            state_d = IsStd;
        end
        default : ;
      endcase
    end

  end

endmodule // prim_diff_decode



package riscv;

    localparam logic [63:0] SSTATUS_UIE  = 64'h00000001;
    localparam logic [63:0] SSTATUS_SIE  = 64'h00000002;
    localparam logic [63:0] SSTATUS_SPIE = 64'h00000020;
    localparam logic [63:0] SSTATUS_SPP  = 64'h00000100;
    localparam logic [63:0] SSTATUS_FS   = 64'h00006000;
    localparam logic [63:0] SSTATUS_XS   = 64'h00018000;
    localparam logic [63:0] SSTATUS_SUM  = 64'h00040000;
    localparam logic [63:0] SSTATUS_MXR  = 64'h00080000;
    localparam logic [63:0] SSTATUS_UPIE = 64'h00000010;
    localparam logic [63:0] SSTATUS_UXL  = 64'h0000000300000000;
    localparam logic [63:0] SSTATUS64_SD = 64'h8000000000000000;
    localparam logic [63:0] SSTATUS32_SD = 64'h80000000;


endpackage

package ariane_pkg;


   localparam logic [63:0] SMODE_STATUS_READ_MASK = riscv::SSTATUS_UIE
                                                   | riscv::SSTATUS_SIE
                                                   | riscv::SSTATUS_SPIE
                                                   | riscv::SSTATUS_SPP
                                                   | riscv::SSTATUS_FS
                                                   | riscv::SSTATUS_XS
                                                   | riscv::SSTATUS_SUM
                                                   | riscv::SSTATUS_MXR
                                                   | riscv::SSTATUS_UPIE
                                                   | riscv::SSTATUS_SPIE
                                                   | riscv::SSTATUS_UXL
                                                   | riscv::SSTATUS64_SD;


endpackage
