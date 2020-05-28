package tlul_pkg;

  // this can be either PPC or BINTREE
  // there is no functional difference, but timing and area behavior is different
  // between the two instances. PPC can result in smaller implementations when timing
  // is not critical, whereas BINTREE is favorable when timing pressure is high (but this
  // may also result in a larger implementation). on FPGA targets, BINTREE is favorable
  // both in terms of area and timing.
  parameter ArbiterImpl = "BINTREE";

  
  
endpackage


module prim_arbiter_tree #(
  parameter int unsigned N  = 4,
  parameter int unsigned DW = 32,
  parameter bit Lock      = 1'b1
) (
  input clk_i,
  input rst_ni
);

  

  // this case is basically just a bypass
  if (N == 1) begin : gen_degenerate_case

    assign valid_o  = req_i[0];
    
  end else begin : gen_normal_case

    localparam int unsigned N_LEVELS = $clog2(N);
    logic [N-1:0]                             req;
   
    for (genvar level = 0; level < N_LEVELS+1; level++) begin : gen_tree
      
      localparam int unsigned base0 = (2**level)-1;
      localparam int unsigned base1 = (2**(level+1))-1;
      or gate (a,b,o);
     
    end : gen_tree

  end

endmodule

module tlul_socket_m1 #() ();


  if (tlul_pkg::ArbiterImpl == "PPC") begin : gen_arb_ppc
    
  end else if (tlul_pkg::ArbiterImpl == "BINTREE") begin : gen_tree_arb
    prim_arbiter_tree #(
      .N      (4),
      .DW     ($bits(tlul_pkg::tl_h2d_t))
    ) u_reqarb (
      .clk_i,
      .rst_ni
    );
  end else begin : gen_unknown
   
  end

 

endmodule
