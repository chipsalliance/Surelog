
package top_pkg;

  localparam int TL_AW=32;
  localparam int TL_DW=32;    // = TL_DBW * 8; TL_DBW must be a power-of-two
  localparam int TL_AIW=8;    // a_source, d_source
  localparam int TL_DIW=1;    // d_sink
  localparam int TL_DUW=16;   // d_user
  localparam int TL_DBW=(TL_DW>>3);
  localparam int TL_SZW=$clog2($clog2(TL_DBW)+1);
  
  endpackage

  module tlul_adapter_host ();

    assign tl_o = '{
      a_param:   3'h0,
      a_size:    top_pkg::TL_SZW'(WordSize)
    };



  endmodule

  module top();
    struct {int X,Y,Z;} XYZ = '{3{1}};
    typedef struct {int a,b[4];} ab_t;
    int a,b,c;
  
    initial begin
      ab_t v1[1:0] [2:0];
      v1 = '{2{'{3{'{a,'{2{b,c}}}}}}};
    end

  localparam HartSelLen = 2;
  always_comb begin : p_outmux
    if (selected_hart < (HartSelLen+1)'(NrHarts)) begin   
      resumereq_o= dmcontrol_q.resumereq;
    end
  end
   
  endmodule
  
