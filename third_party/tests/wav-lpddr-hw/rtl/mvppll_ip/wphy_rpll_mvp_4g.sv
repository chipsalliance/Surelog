/*********************************************************************************
Copyright (c) 2021 Wavious LLC

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.

*********************************************************************************/

`ifdef SYNTHESIS
`else 
// Verilog netlist of
// "wphy_rpll_mvp_4g"

// HDL models

// HDL file - wavshared_gf12lp_dig_lib, INV_D1_GL16_LVT, systemVerilog.

//systemVerilog HDL for "wavshared_tsmc12ffc_lib", "INV_D1_GL16_LVT" "systemVerilog"

module wphy_rpll_mvp_4g_INV_D1_GL16_LVT( in, out
`ifdef WLOGIC_MODEL_NO_TIE
`else
,tielo, tiehi
`endif //WLOGIC_MODEL_NO_TIE
`ifdef WLOGIC_MODEL_NO_PG
`else
, vdd, vss
`endif //WLOGIC_MODEL_NO_PG
);

  input in;
  output out;
`ifdef WLOGIC_MODEL_NO_TIE
`else
  input tiehi;
  input tielo;
`endif //WLOGIC_MODEL_NO_TIE
`ifdef WLOGIC_MODEL_NO_PG
`else
  inout vdd;
  inout vss;
`endif //WLOGIC_MODEL_NO_PG

`ifdef WLOGIC_MODEL_NO_TIE
`else

`ifdef WLOGIC_TIE_CHECK
  wire   signals_ok;
  assign signals_ok = tiehi & ~tielo;
  
  assign out = (signals_ok) ? 1'bz : 1'bx;
`endif // WLOGIC_TIE_CHECK

`endif //WLOGIC_MODEL_NO_TIE

`ifdef WLOGIC_MODEL_NO_PG
`else

`ifdef WLOGIC_PWR_CHECK
  wire   power_ok;
  assign power_ok = ~vss & vdd;
  
  assign out = (power_ok) ? 1'bz : 1'bx;

`endif //WLOGIC_PWR_CHECK

`endif //WLOGIC_MODEL_NO_PG

   assign out =  ~in;

endmodule

// HDL file - wavshared_gf12lp_dig_lib, LAT_D1_GL16_RVT, systemVerilog.

//systemVerilog HDL for "wavshared_tsmc12ffc_lib", "LAT_D1_GL16_RVT" "systemVerilog"

`timescale 1ps/1ps
module wphy_rpll_mvp_4g_LAT_D1_GL16_RVT( q, clk, clkb, d
`ifdef WLOGIC_MODEL_NO_TIE
`else
, tiehi, tielo
`endif //WLOGIC_MODEL_NO_TIE
`ifdef WLOGIC_MODEL_NO_PG
`else
, vss, vdd 
`endif //WLOGIC_MODEL_NO_PG
);
 
  input clk;
  output q;  
  input d;
  input clkb;
`ifdef WLOGIC_MODEL_NO_TIE
`else
  input tiehi;
  input tielo;
`endif //WLOGIC_MODEL_NO_TIE
`ifdef WLOGIC_MODEL_NO_PG
`else
  inout vdd;
  inout vss;
`endif //WLOGIC_MODEL_NO_PG


  wire #0 polarity_ok = clk^clkb;

`ifdef WLOGIC_MODEL_NO_TIE
`else

`ifdef WLOGIC_TIE_CHECK
  wire signals_ok;
  assign signals_ok = tiehi & ~tielo ;

  assign q = (signals_ok) ? 1'bz : 1'bx;
`endif // WLOGIC_TIE_CHECK

`endif //WLOGIC_MODEL_NO_TIE

`ifdef WLOGIC_MODEL_NO_PG
`else

`ifdef WLOGIC_PWR_CHECK
  wire   power_ok;
  assign power_ok = ~vss & vdd ;

  assign q = (power_ok) ? 1'bz : 1'bx;
  
`endif //WLOGIC_PWR_CHECK

`endif //WLOGIC_MODEL_NO_PG


assign #1  q = polarity_ok ?
                           (clkb) ?
                                  (d===1'bx) ? $random : d
                                  : q
                           : 1'bx;

endmodule

// HDL file - wavshared_gf12lp_dig_lib, PD_D1_GL16_RVT, systemVerilog.

//systemVerilog HDL for "wavshared_tsmc12ffc_lib", "PD_D1_GL16_RVT" "systemVerilog"

module wphy_rpll_mvp_4g_PD_D1_GL16_RVT( enb, y
`ifdef WLOGIC_MODEL_NO_PG
`else
, vss
`endif //WLOGIC_MODEL_NO_PG
); 

  input y;
  input enb;

`ifdef WLOGIC_MODEL_NO_PG
`else
  inout vss;
`endif //WLOGIC_MODEL_NO_PG

`ifdef WLOGIC_MODEL_NO_PG
`else

`ifdef WLOGIC_PWR_CHECK
  wire   power_ok;
  assign power_ok = ~vss ;
  
  assign y = (power_ok) ? 1'bz : 1'bx;

`endif //WLOGIC_PWR_CHECK

`endif //WLOGIC_MODEL_NO_PG

  assign y =  enb ? 1'b0 : 1'bz;

endmodule

// HDL file - wavshared_gf12lp_dig_lib, INV_D1_GL16_RVT_Mmod_nomodel, systemVerilog.

//systemVerilog HDL for "wavshared_tsmc12ffc_lib", "INV_D1_GL16_RVT_Mmod_nomodel"
//"systemVerilog"


module wphy_rpll_mvp_4g_INV_D1_GL16_RVT_Mmod_nomodel ( in, out, tiehi, tielo
`ifdef WLOGIC_MODEL_NO_PG
`else
, vdd, vss
`endif //WLOGIC_MODEL_NO_PG
);

  input in;
  output out;
  input tiehi;
  input tielo;
`ifdef WLOGIC_MODEL_NO_PG
`else
  inout vdd;
  inout vss;
`endif //WLOGIC_MODEL_NO_PG

endmodule

// HDL file - wavshared_gf12lp_dig_lib, XG_D1_GL16_RVT, systemVerilog.

//systemVerilog HDL for "wavshared_tsmc12ffc_lib", "XG_D1_GL16_RVT" "systemVerilog"


module wphy_rpll_mvp_4g_XG_D1_GL16_RVT ( y, en, enb, a
`ifdef WLOGIC_MODEL_NO_PG
`else
, vss, vdd 
`endif //WLOGIC_MODEL_NO_PG
); 

  input a;
  input en;
  output y;
  input enb;
`ifdef WLOGIC_MODEL_NO_PG
`else
  inout vdd;
  inout vss;
`endif //WLOGIC_MODEL_NO_PG

`ifdef WLOGIC_MODEL_NO_PG
`else

`ifdef WLOGIC_PWR_CHECK
  wire   power_ok;
  assign power_ok = ~vss & vdd;
  
  assign y = (power_ok) ? 1'bz : 1'bx;

`endif //WLOGIC_PWR_CHECK

`endif //WLOGIC_MODEL_NO_PG


assign y = (en && ~enb) ? a:1'bz;

endmodule

// HDL file - wavshared_gf12lp_dig_lib, PU_D1_GL16_RVT, systemVerilog.

//systemVerilog HDL for "wavshared_tsmc12ffc_lib", "PU_D1_GL16_RVT" "systemVerilog"


module wphy_rpll_mvp_4g_PU_D1_GL16_RVT ( en, y
`ifdef WLOGIC_MODEL_NO_PG
`else
, vdd 
`endif //WLOGIC_MODEL_NO_PG
);

  input y;
  input en;
`ifdef WLOGIC_MODEL_NO_PG
`else
  inout vdd;
`endif //WLOGIC_MODEL_NO_PG

`ifdef WLOGIC_MODEL_NO_PG
`else

`ifdef WLOGIC_PWR_CHECK
  wire   power_ok;
  assign power_ok = vdd;
  
  assign y = (power_ok) ? 1'bz : 1'bx;

`endif //WLOGIC_PWR_CHECK

`endif //WLOGIC_MODEL_NO_PG

 assign y = en ? 1'bz : 1'b1;

endmodule

// HDL file - wavshared_gf12lp_dig_lib, DUM_D1_GL16_RVT, behavioral.

//Verilog HDL for "wavshared_gf12lp_dig_lib", "DUM_D1_GL16_RVT" "behavioral"


module wphy_rpll_mvp_4g_DUM_D1_GL16_RVT ( vdd, vss, tielo, tiehi );

  input tiehi;
  input tielo;
  inout vdd;
  inout vss;
endmodule

// HDL file - wavshared_gf12lp_dig_lib, NOR2_D1_GL16_RVT, systemVerilog.

//systemVerilog HDL for "wavshared_tsmc12ffc_lib", "NOR2_D1_GL16_RVT" "systemVerilog"


module wphy_rpll_mvp_4g_NOR2_D1_GL16_RVT ( y, a, b
`ifdef WLOGIC_MODEL_NO_TIE
`else
,tielo, tiehi
`endif //WLOGIC_MODEL_NO_TIE
`ifdef WLOGIC_MODEL_NO_PG
`else
, vss, vdd 
`endif //WLOGIC_MODEL_NO_PG
); 

  input b;
  input a;
  output y;
`ifdef WLOGIC_MODEL_NO_TIE
`else
  input tiehi;
  input tielo;
`endif //WLOGIC_MODEL_NO_TIE
`ifdef WLOGIC_MODEL_NO_PG
`else
  inout vdd;
  inout vss;
`endif //WLOGIC_MODEL_NO_PG

`ifdef WLOGIC_MODEL_NO_TIE
`else

`ifdef WLOGIC_TIE_CHECK
  wire   signals_ok;
  assign signals_ok = tiehi & ~tielo;
  
  assign y = (signals_ok) ? 1'bz : 1'bx;
`endif // WLOGIC_TIE_CHECK

`endif //WLOGIC_MODEL_NO_TIE

`ifdef WLOGIC_MODEL_NO_PG
`else

`ifdef WLOGIC_PWR_CHECK
  wire   power_ok;
  assign power_ok = ~vss & vdd;
  
  assign y = (power_ok) ? 1'bz : 1'bx;

`endif //WLOGIC_PWR_CHECK

`endif //WLOGIC_MODEL_NO_PG


  assign y=~(a|b);

endmodule

// HDL file - wavshared_gf12lp_dig_lib, DUMLOAD_D1_GL16_RVT, systemVerilog.

//systemVerilog HDL for "wavshared_tsmc12ffc_lib", "DUMLOAD_D1_GL16_RVT" "systemVerilog"


module wphy_rpll_mvp_4g_DUMLOAD_D1_GL16_RVT ( inp, inn
`ifdef WLOGIC_MODEL_NO_PG
`else
, vss, vdd 
`endif //WLOGIC_MODEL_NO_PG
); 

  input inp;
  input inn;
`ifdef WLOGIC_MODEL_NO_PG
`else
  inout vdd;
  inout vss;
`endif //WLOGIC_MODEL_NO_PG

endmodule

// HDL file - wavshared_gf12lp_dig_lib, NAND2_D1_GL16_RVT, systemVerilog.




module wphy_rpll_mvp_4g_NAND2_D1_GL16_RVT ( y, a, b
`ifdef WLOGIC_MODEL_NO_TIE
`else
,tielo, tiehi
`endif //WLOGIC_MODEL_NO_TIE
`ifdef WLOGIC_MODEL_NO_PG
`else
, vss, vdd 
`endif //WLOGIC_MODEL_NO_PG
); 

  input b;
  input a;
  output y;
`ifdef WLOGIC_MODEL_NO_TIE
`else
  input tiehi;
  input tielo;
`endif //WLOGIC_MODEL_NO_TIE
`ifdef WLOGIC_MODEL_NO_PG
`else
  inout vdd;
  inout vss;
`endif //WLOGIC_MODEL_NO_PG

`ifdef WLOGIC_MODEL_NO_TIE
`else

`ifdef WLOGIC_TIE_CHECK
  wire   signals_ok;
  assign signals_ok = tiehi & ~tielo;
  
  assign y = (signals_ok) ? 1'bz : 1'bx;
`endif // WLOGIC_TIE_CHECK

`endif //WLOGIC_MODEL_NO_TIE

`ifdef WLOGIC_MODEL_NO_PG
`else

`ifdef WLOGIC_PWR_CHECK
  wire   power_ok;
  assign power_ok = ~vss & vdd;
  
  assign y = (power_ok) ? 1'bz : 1'bx;

`endif //WLOGIC_PWR_CHECK

`endif //WLOGIC_MODEL_NO_PG


 assign y = ~(a&b);

endmodule

// HDL file - wavshared_gf12lp_dig_lib, INV_D1_GL16_LVT_Mmod_delay, systemVerilog.

//systemVerilog HDL for "wavshared_tsmc12ffc_lib", "INV_D1_GL16_LVT_Mmod_delay"
//"systemVerilog"

`timescale 1ns/1ps

module wphy_rpll_mvp_4g_INV_D1_GL16_LVT_Mmod_delay( in, out, tiehi, tielo
`ifdef WLOGIC_MODEL_NO_PG
`else
, vdd, vss
`endif //WLOGIC_MODEL_NO_PG
);

  input in;
  output out;
  input tiehi;
  input tielo;
`ifdef WLOGIC_MODEL_NO_PG
`else
  inout vdd;
  inout vss;
`endif //WLOGIC_MODEL_NO_PG

  wire out;

`ifdef WLOGIC_MODEL_NO_PG
`else

`ifdef WLOGIC_PWR_CHECK
  wire   power_ok;
  assign power_ok = ~vss & vdd & tiehi & ~tielo;
  
  assign out = (power_ok) ? 1'bz : 1'bx;

`endif //WLOGIC_PWR_CHECK

`endif //WLOGIC_MODEL_NO_PG

   assign #0.01 out = ~in;

endmodule

// HDL file - wavshared_gf12lp_dig_lib, FF_D1_GL16_LVT, systemVerilog.

//systemVerilog HDL for "wavshared_tsmc12ffc_lib", "FF_D1_GL16_LVT" "systemVerilog"

module wphy_rpll_mvp_4g_FF_D1_GL16_LVT( q, clk, clkb, d
`ifdef WLOGIC_MODEL_NO_TIE
`else
,tielo, tiehi
`endif //WLOGIC_MODEL_NO_TIE
`ifdef WLOGIC_MODEL_NO_PG
`else
, vss, vdd
`endif //WLOGIC_MODEL_NO_PG
); 

  input clk;
  output q;
  input d;
  input clkb; 
`ifdef WLOGIC_MODEL_NO_TIE
`else
  input tiehi;
  input tielo;
`endif //WLOGIC_MODEL_NO_TIE
`ifdef WLOGIC_MODEL_NO_PG
`else
  inout vdd;
  inout vss;
`endif //WLOGIC_MODEL_NO_PG

  reg q_int;
  wire q;

`ifdef WLOGIC_MODEL_NO_TIE
`else

`ifdef WLOGIC_TIE_CHECK
  wire   signals_ok;
  assign signals_ok = tiehi & ~tielo;

  initial  begin
       q_int = (signals_ok) ? 1'bz : 1'bx;
  end
  always @(*) begin
       q_int = (signals_ok) ? 1'bz : 1'bx;
  end
`endif // WLOGIC_TIE_CHECK

`endif //WLOGIC_MODEL_NO_TIE

`ifdef WLOGIC_MODEL_NO_PG
`else

`ifdef WLOGIC_PWR_CHECK
  wire   power_ok;
  assign power_ok = ~vss & vdd;
  
  initial  begin
       q_int = (power_ok) ? 1'bz : 1'bx;
  end
  always @(*) begin
       q_int = (power_ok) ? 1'bz : 1'bx;
  end
`endif //WLOGIC_PWR_CHECK

`endif //WLOGIC_MODEL_NO_PG


  assign q= q_int;

  initial begin
    q_int = $random;
  end

always @ (posedge clk) q_int<= (d === 1'bx) ? $random : d;

endmodule


// HDL file - wavshared_gf12lp_dig_lib, FFRES_D1_GL16_LVT, systemVerilog.

//systemVerilog HDL for "wavshared_tsmc12ffc_lib", "FFRES_D1_GL16_LVT" "systemVerilog"

module wphy_rpll_mvp_4g_FFRES_D1_GL16_LVT( q, clk, clkb, d, rst, rstb
`ifdef WLOGIC_MODEL_NO_TIE
`else
,tielo, tiehi
`endif //WLOGIC_MODEL_NO_TIE
`ifdef WLOGIC_MODEL_NO_PG
`else
, vss, vdd 
`endif //WLOGIC_MODEL_NO_PG
); 

  input clk;
  input rst;
  input rstb;
  output q;
  input d;
  input clkb; 
`ifdef WLOGIC_MODEL_NO_TIE
`else
  input tiehi;
  input tielo;
`endif //WLOGIC_MODEL_NO_TIE
  reg q;
`ifdef WLOGIC_MODEL_NO_PG
`else
  inout vdd;
  inout vss;
`endif //WLOGIC_MODEL_NO_PG

`ifdef WLOGIC_MODEL_NO_TIE
`else

`ifdef WLOGIC_TIE_CHECK
  wire   signals_ok;
  assign signals_ok = tiehi & ~tielo;

  initial  begin
       q = (signals_ok) ? 1'bz : 1'bx;
  end
  always @(*) begin
       q = (signals_ok) ? 1'bz : 1'bx;
  end
`endif // WLOGIC_TIE_CHECK

`endif //WLOGIC_MODEL_NO_TIE


`ifdef WLOGIC_MODEL_NO_PG
`else

`ifdef WLOGIC_PWR_CHECK
  wire   power_ok;
  assign power_ok = ~vss & vdd;
  
  initial  begin
       q = (power_ok) ? 1'bz : 1'bx;
  end
  always @(*) begin
       q = (power_ok) ? 1'bz : 1'bx;
  end
`endif //WLOGIC_PWR_CHECK

`endif //WLOGIC_MODEL_NO_PG

  initial begin
    q = $random;
  end

  always @(posedge clk or posedge rst) begin
   if(rst) begin
       q <= 1'b0;
    end else begin
       q <= d;
    end
  end

endmodule

// HDL file - wavshared_gf12lp_dig_lib, PU_D1_GL16_LVT, systemVerilog.

//systemVerilog HDL for "wavshared_tsmc12ffc_lib", "PU_D1_GL16_LVT" "systemVerilog"


module wphy_rpll_mvp_4g_PU_D1_GL16_LVT ( en, y
`ifdef WLOGIC_MODEL_NO_PG
`else
, vdd 
`endif //WLOGIC_MODEL_NO_PG
);

  input y;
  input en;
`ifdef WLOGIC_MODEL_NO_PG
`else
  inout vdd;
`endif //WLOGIC_MODEL_NO_PG

`ifdef WLOGIC_MODEL_NO_PG
`else

`ifdef WLOGIC_PWR_CHECK
  wire   power_ok;
  assign power_ok = vdd;
  
  assign y = (power_ok) ? 1'bz : 1'bx;

`endif //WLOGIC_PWR_CHECK

`endif //WLOGIC_MODEL_NO_PG

 assign y = en ? 1'bz : 1'b1;

endmodule

// HDL file - wavshared_gf12lp_dig_lib, INV_D1_GL16_LVT_Mmod_nomodel, systemVerilog.

//systemVerilog HDL for "wavshared_tsmc12ffc_lib", "INV_D1_GL16_LVT_Mmod_nomodel"
//"systemVerilog"


module wphy_rpll_mvp_4g_INV_D1_GL16_LVT_Mmod_nomodel ( in, out, tiehi, tielo
`ifdef WLOGIC_MODEL_NO_PG
`else
, vdd, vss
`endif //WLOGIC_MODEL_NO_PG
);

  input in;
  output out;
  input tiehi;
  input tielo;
`ifdef WLOGIC_MODEL_NO_PG
`else
  inout vdd;
  inout vss;
`endif //WLOGIC_MODEL_NO_PG

endmodule

// HDL file - wavshared_gf12lp_dig_lib, XG_D1_GL16_LVT, systemVerilog.

//systemVerilog HDL for "wavshared_tsmc12ffc_lib", "XG_D1_GL16_LVT" "systemVerilog"


module wphy_rpll_mvp_4g_XG_D1_GL16_LVT ( y, en, enb, a
`ifdef WLOGIC_MODEL_NO_PG
`else
, vss, vdd 
`endif //WLOGIC_MODEL_NO_PG
); 

  input a;
  input en;
  output y;
  input enb;
`ifdef WLOGIC_MODEL_NO_PG
`else
  inout vdd;
  inout vss;
`endif //WLOGIC_MODEL_NO_PG

`ifdef WLOGIC_MODEL_NO_PG
`else

`ifdef WLOGIC_PWR_CHECK
  wire   power_ok;
  assign power_ok = ~vss & vdd;
  
  assign y = (power_ok) ? 1'bz : 1'bx;

`endif //WLOGIC_PWR_CHECK

`endif //WLOGIC_MODEL_NO_PG


assign y = (en && ~enb) ? a:1'bz;

endmodule

// HDL file - wavshared_gf12lp_dig_lib, PD_D1_GL16_LVT, systemVerilog.

//systemVerilog HDL for "wavshared_tsmc12ffc_lib", "PD_D1_GL16_LVT" "systemVerilog"

module wphy_rpll_mvp_4g_PD_D1_GL16_LVT( enb, y
`ifdef WLOGIC_MODEL_NO_PG
`else
, vss
`endif //WLOGIC_MODEL_NO_PG
); 

  input y;
  input enb;

`ifdef WLOGIC_MODEL_NO_PG
`else
  inout vss;
`endif //WLOGIC_MODEL_NO_PG

`ifdef WLOGIC_MODEL_NO_PG
`else

`ifdef WLOGIC_PWR_CHECK
  wire   power_ok;
  assign power_ok = ~vss ;
  
  assign y = (power_ok) ? 1'bz : 1'bx;

`endif //WLOGIC_PWR_CHECK

`endif //WLOGIC_MODEL_NO_PG

  assign y =  enb ? 1'b0 : 1'bz;

endmodule

// HDL file - wavshared_gf12lp_dig_lib, NAND3_D1_GL16_LVT, systemVerilog.

//systemVerilog HDL for "wavshared_tsmc12ffc_lib", "NAND3_D1_GL16_LVT" "systemVerilog"


module wphy_rpll_mvp_4g_NAND3_D1_GL16_LVT ( y, a, b, c
`ifdef WLOGIC_MODEL_NO_TIE
`else
,tielo, tiehi
`endif //WLOGIC_MODEL_NO_TIE
`ifdef WLOGIC_MODEL_NO_PG
`else
, vss, vdd 
`endif //WLOGIC_MODEL_NO_PG
); 

  input c;
  input b;
  input a;
  output y;
`ifdef WLOGIC_MODEL_NO_TIE
`else
  input tiehi;
  input tielo;
`endif //WLOGIC_MODEL_NO_TIE
`ifdef WLOGIC_MODEL_NO_PG
`else
  inout vdd;
  inout vss;
`endif //WLOGIC_MODEL_NO_PG

`ifdef WLOGIC_MODEL_NO_TIE
`else

`ifdef WLOGIC_TIE_CHECK
  wire   signals_ok;
  assign signals_ok = tiehi & ~tielo;
  
  assign y = (signals_ok) ? 1'bz : 1'bx;
`endif // WLOGIC_TIE_CHECK

`endif //WLOGIC_MODEL_NO_TIE

`ifdef WLOGIC_MODEL_NO_PG
`else

`ifdef WLOGIC_PWR_CHECK
  wire   power_ok;
  assign power_ok = ~vss & vdd;
  
  assign y = (power_ok) ? 1'bz : 1'bx;

`endif //WLOGIC_PWR_CHECK

`endif //WLOGIC_MODEL_NO_PG

 assign y = ~(a&b&c);
endmodule

// HDL file - wavshared_gf12lp_dig_lib, NAND2_D1_GL16_LVT, systemVerilog.

//systemVerilog HDL for "wavshared_tsmc12ffc_lib", "NAND2_D1_GL16_LVT" "systemVerilog"


module wphy_rpll_mvp_4g_NAND2_D1_GL16_LVT ( y, a, b
`ifdef WLOGIC_MODEL_NO_TIE
`else
,tielo, tiehi
`endif //WLOGIC_MODEL_NO_TIE
`ifdef WLOGIC_MODEL_NO_PG
`else
, vss, vdd 
`endif //WLOGIC_MODEL_NO_PG
); 

  input b;
  input a;
  output y;
`ifdef WLOGIC_MODEL_NO_TIE
`else
  input tiehi;
  input tielo;
`endif //WLOGIC_MODEL_NO_TIE
`ifdef WLOGIC_MODEL_NO_PG
`else
  inout vdd;
  inout vss;
`endif //WLOGIC_MODEL_NO_PG

`ifdef WLOGIC_MODEL_NO_TIE
`else

`ifdef WLOGIC_TIE_CHECK
  wire   signals_ok;
  assign signals_ok = tiehi & ~tielo;
  
  assign y = (signals_ok) ? 1'bz : 1'bx;
`endif // WLOGIC_TIE_CHECK

`endif //WLOGIC_MODEL_NO_TIE

`ifdef WLOGIC_MODEL_NO_PG
`else

`ifdef WLOGIC_PWR_CHECK
  wire   power_ok;
  assign power_ok = ~vss & vdd;
  
  assign y = (power_ok) ? 1'bz : 1'bx;

`endif //WLOGIC_PWR_CHECK

`endif //WLOGIC_MODEL_NO_PG


 assign y = ~(a&b);

endmodule

// HDL file - wavshared_gf12lp_dig_lib, FFSETRES_D1_GL16_LVT, systemVerilog.

//systemVerilog HDL for "wavshared_tsmc12ffc_lib", "FFSETRES_D1_GL16_LVT" "systemVerilog"

`timescale 1ps/1ps

module wphy_rpll_mvp_4g_FFSETRES_D1_GL16_LVT( q, clk, clkb, d, prst, prstb, rst, rstb
`ifdef WLOGIC_MODEL_NO_TIE
`else
,tielo, tiehi
`endif //WLOGIC_MODEL_NO_TIE
`ifdef WLOGIC_MODEL_NO_PG
`else
, vdd, vss 
`endif //WLOGIC_MODEL_NO_PG
);

  input prst;
  input rst;
  input rstb;
  output reg q;
  input prstb;
  input d;
  input clk;
  input clkb; 
`ifdef WLOGIC_MODEL_NO_TIE
`else
  input tiehi;
  input tielo;
`endif //WLOGIC_MODEL_NO_TIE
`ifdef WLOGIC_MODEL_NO_PG
`else
  inout vdd;
  inout vss;
`endif //WLOGIC_MODEL_NO_PG

`ifdef WLOGIC_MODEL_NO_TIE
`else

`ifdef WLOGIC_TIE_CHECK
  wire   signals_ok;
  assign signals_ok = tiehi & ~tielo;

  initial  begin
       q = (signals_ok) ? 1'bz : 1'bx;
  end
  always @(*) begin
       q = (signals_ok) ? 1'bz : 1'bx;
  end
`endif // WLOGIC_TIE_CHECK

`endif //WLOGIC_MODEL_NO_TIE


`ifdef WLOGIC_MODEL_NO_PG
`else

`ifdef WLOGIC_PWR_CHECK
  wire   power_ok;
  assign power_ok = ~vss & vdd;
  
  initial  begin
       q = (power_ok) ? 1'bz : 1'bx;
  end
  always @(*) begin
       q = (power_ok) ? 1'bz : 1'bx;
  end
`endif //WLOGIC_PWR_CHECK

`endif //WLOGIC_MODEL_NO_PG

  initial begin
   q= $random;
  end
  
  always @(posedge clk or posedge rst or posedge prst) begin
   if(rst & prst) begin
      q <= 1'bx;
    end else if(prst) begin
      q <= 1'b1;
    end else if(rst) begin
        q <= 1'b0;
    end else begin
      q <= d;
    end
  end
endmodule

// HDL file - wavshared_gf12lp_dig_lib, MUXT2_D2_GL16_LVT, systemVerilog.

//systemVerilog HDL for "wavshared_tsmc12ffc_lib", "MUXT2_D2_GL16_LVT" "systemVerilog"

module wphy_rpll_mvp_4g_MUXT2_D2_GL16_LVT( yb, a, b, s, sb
`ifdef WLOGIC_MODEL_NO_PG
`else
, vss, vdd 
`endif //WLOGIC_MODEL_NO_PG
); 

  input a; 
  input sb;
  input s;
  output yb;
  input b;
`ifdef WLOGIC_MODEL_NO_PG
`else
  inout vdd;
  inout vss;
`endif //WLOGIC_MODEL_NO_PG

  wire yb;

`ifdef WLOGIC_MODEL_NO_PG
`else

`ifdef WLOGIC_PWR_CHECK
  wire   power_ok;
  assign power_ok = ~vss & vdd;
  
  assign yb = (power_ok) ? 1'bz : 1'bx;

`endif //WLOGIC_PWR_CHECK

`endif //WLOGIC_MODEL_NO_PG

  assign yb = (s && ~sb) ? ~b:~a;



endmodule

// HDL file - wavshared_gf12lp_dig_lib, INV_D2_GL16_LVT, systemVerilog.

//systemVerilog HDL for "wavshared_tsmc12ffc_lib", "INV_D2_GL16_LVT" "systemVerilog"

`timescale 1ps/1ps

module wphy_rpll_mvp_4g_INV_D2_GL16_LVT( in, out
`ifdef WLOGIC_MODEL_NO_PG
`else
, vdd, vss
`endif //WLOGIC_MODEL_NO_PG
);

  input in;
  output out;
`ifdef WLOGIC_MODEL_NO_PG
`else
  inout vdd;
  inout vss;
`endif //WLOGIC_MODEL_NO_PG

`ifdef WLOGIC_MODEL_NO_PG
`else

`ifdef WLOGIC_PWR_CHECK
  wire   power_ok;
  assign power_ok = ~vss & vdd;
  
  assign out = (power_ok) ? 1'bz : 1'bx;

`endif //WLOGIC_PWR_CHECK

`endif //WLOGIC_MODEL_NO_PG

    assign  out = ~in;

endmodule

// HDL file - wavshared_gf12lp_dig_lib, NOR2_D1_GL16_LVT, systemVerilog.

//systemVerilog HDL for "wavshared_tsmc12ffc_lib", "NOR2_D1_GL16_LVT" "systemVerilog"


module wphy_rpll_mvp_4g_NOR2_D1_GL16_LVT ( y, a, b
`ifdef WLOGIC_MODEL_NO_TIE
`else
,tielo, tiehi
`endif //WLOGIC_MODEL_NO_TIE
`ifdef WLOGIC_MODEL_NO_PG
`else
, vss, vdd 
`endif //WLOGIC_MODEL_NO_PG
); 

  input b;
  input a;
  output y;
`ifdef WLOGIC_MODEL_NO_TIE
`else
  input tiehi;
  input tielo;
`endif //WLOGIC_MODEL_NO_TIE
`ifdef WLOGIC_MODEL_NO_PG
`else
  inout vdd;
  inout vss;
`endif //WLOGIC_MODEL_NO_PG

`ifdef WLOGIC_MODEL_NO_TIE
`else

`ifdef WLOGIC_TIE_CHECK
  wire   signals_ok;
  assign signals_ok = tiehi & ~tielo;
  
  assign y = (signals_ok) ? 1'bz : 1'bx;
`endif // WLOGIC_TIE_CHECK

`endif //WLOGIC_MODEL_NO_TIE

`ifdef WLOGIC_MODEL_NO_PG
`else

`ifdef WLOGIC_PWR_CHECK
  wire   power_ok;
  assign power_ok = ~vss & vdd;
  
  assign y = (power_ok) ? 1'bz : 1'bx;

`endif //WLOGIC_PWR_CHECK

`endif //WLOGIC_MODEL_NO_PG


  assign y=~(a|b);


endmodule

// HDL file - wavshared_gf12lp_dig_lib, DUM_D1_GL16_LVT, behavioral.

//Verilog HDL for "wavshared_tsmc12ffc_lib", "DUM_D1_GL16_LVT" "functional"


module wphy_rpll_mvp_4g_DUM_D1_GL16_LVT ( tiehi, tielo, vdd, vss );

  input tiehi;
  input tielo;
  inout vdd;
  inout vss;
endmodule

// HDL file - gf12lp_rpll_lib, rpll_filter_cap_20pF, systemVerilog.

//systemVerilog HDL for "wphy_pll_lib", "wphy_rpll_filter_cap_10pF" "systemVerilog"


`timescale 1ns / 1ps 

module wphy_rpll_mvp_4g_rpll_filter_cap_20pF (  
  input   var real iup,
  input   var real idn,
  input   wire     ena,
  input   wire     vdda,
  input   wire     vss,
  output  var real vcap
);


wire en_int = ena & vdda & ~vss;
real Ts;
real Ts_time;
real d0, d1;
real FpFilt;
real   			 Fp              = 200e6;
parameter real		Vint_scale		= 0.45;
parameter real		C_int			= 20e-12;		//Capacitance for int path
real Vint, Vint_old;
parameter real    PI2             = 6.283185;

bit   force_pll;
initial begin
  if ($value$plusargs("RING_PLL_SAMPLE_TIME=%f", Ts)) begin   
  end else begin
    Ts          = 50e-12;
  end 
  if ($value$plusargs("RING_PLL_CUTOFF_FREQ=%f", FpFilt)) begin   
  end else begin
    FpFilt      = Fp;
  end
  
  if ($test$plusargs("MVP_FORCE_PLL")) begin   
    force_pll = 1;
  end 
  
  Ts_time 		  = force_pll ? 1e9 : Ts/1e-9;
  d0 = 1 + (2 / (PI2 * FpFilt * Ts));  
  d1 = 1 - (2 / (PI2 * FpFilt * Ts));
end


always #(Ts_time) begin
  if(en_int && ~force_pll) begin
	  Vint        = Vint_old + (((iup - idn) * Ts) / C_int); 
    Vint_old		= Vint;
  end else begin
    Vint        = 0; 
    Vint_old		= 0;
  end
end

assign vcap = Vint;

endmodule

// HDL file - gf12lp_rpll_lib, rpll_14g_filter_int, systemVerilog.

//systemVerilog HDL for "wphy_ln08lpu_rpll_lib", "wphy_rpll_filter_int" "systemVerilog"

`timescale 1ns / 1ps 

module wphy_rpll_mvp_4g_rpll_14g_filter_int (
  input  var real   iup_int,
  input  var real   iupb_int,
  input  var real   idn_int,
  input  var real   idnb_int,
  input  wire   vdbl,
  input  wire   vdda,
  input  wire   vss,
  
  output var real  iout_up,
  output var real  iout_dn
);

parameter real  Fp  = 20e6;
parameter real  PI2 = 6.283185;

wire power_good = vdda & ~vss;

real iout_up_int;
real iout_dn_int;

real d0, d1;
real Ts;
real Ts_time;
bit  force_pll;
initial begin
  if ($value$plusargs("RING_PLL_SAMPLE_TIME=%f", Ts)) begin   
  end else begin
    Ts          = 50e-12;
  end 
  
  if ($test$plusargs("MVP_FORCE_PLL")) begin   
    force_pll = 1;
  end 
  
  Ts_time 		  = force_pll ? 1e9 : Ts/1e-9;
  d0 = 1 + (2 / (PI2 * Fp * Ts));  
  d1 = 1 - (2 / (PI2 * Fp * Ts));
end


assign iout_up_int = power_good ? iup_int / 256 : 0;
assign iout_dn_int = power_good ? idn_int / 256 : 0;


real up_filt, up_filt_in, up_filt_old;
real dn_filt, dn_filt_in, dn_filt_old;

always #(Ts_time) begin
  if(power_good && ~force_pll) begin
    // UP
    up_filt_in      = iout_up_int;
    up_filt         = (up_filt_in + up_filt_old - (up_filt*d1)) / d0;
    up_filt_old     = up_filt_in;
    
    // DN
    dn_filt_in      = iout_dn_int;
    dn_filt         = (dn_filt_in + dn_filt_old - (dn_filt*d1)) / d0;
    dn_filt_old     = dn_filt_in;
  end
end

assign iout_up = up_filt;
assign iout_dn = dn_filt;

endmodule

// HDL file - gf12lp_rpll_lib, rpll_14g_chp_prop_dac, systemVerilog.

//systemVerilog HDL for "wphy_ln08lpu_rpll_lib", "wphy_rpll_chp_prop_dac" "systemVerilog"

`timescale 1ns / 1ps 

module wphy_rpll_mvp_4g_rpll_14g_chp_prop_dac (
  input  wire       vdda,
  input  wire       vss,
  input  var real   iup_prop,
  input  var real   iupb_prop,
  input  var real   idn_prop,
  input  var real   idnb_prop,
  
  input  wire [1:0] c_ctrl,
  input  wire [1:0] r_ctrl,
  
  input  wire [4:0] ctrl,
  
  output var real   iout_prop
);

parameter real  PI2           = 6.283185;
          real  Fp            = 20e6;

wire power_good = vdda & ~vss;
real Ts;
real Ts_time;
real d0, d1;
real prop_scale_fac, up_prop, dn_prop, iprop, iprop_filt, iprop_scale, iprop_scale_old;
real FpFilt;
bit  force_pll;
initial begin
  if ($value$plusargs("RING_PLL_SAMPLE_TIME=%f", Ts)) begin   
  end else begin
    Ts          = 50e-12;
  end 
  
  if ($value$plusargs("RING_PLL_PROP_SCALE_FAC=%f", prop_scale_fac)) begin   //percentage
  end else begin
    prop_scale_fac      = (1 + $random % (4 - 1));
  end
  
  if ($value$plusargs("RING_PLL_CUTOFF_FREQ=%f", FpFilt)) begin   
  end else begin
    FpFilt      = Fp;
  end
  
  if ($test$plusargs("MVP_FORCE_PLL")) begin   
    force_pll = 1;
  end 
  
  Ts_time 		  = force_pll ? 1e9 : Ts/1e-9;
  d0 = 1 + (2 / (PI2 * FpFilt * Ts));  
  d1 = 1 - (2 / (PI2 * FpFilt * Ts));
end


//RC 
// always @(*) begin
//   Fp = 6e6 + ({r_ctrl, c_ctrl} * 1e6);
//   d0 = 1 + (2 / (PI2 * FpFilt * Ts));  
//   d1 = 1 - (2 / (PI2 * FpFilt * Ts));
// end


//Current diff from Up/Down and with scaling factor
always @(*) begin
  iprop		    = ((iup_prop * ctrl)/8.0) - ((idn_prop * ctrl)/8.0);
end

// Filter
always #(Ts_time) begin
  if(power_good && ~force_pll) begin
    iprop_scale     = iprop;

    iprop_filt      = (iprop_scale + iprop_scale_old - (iprop_filt*d1)) / d0;
    iprop_scale_old = iprop_scale;
  end
end

assign iout_prop = iprop_filt;

endmodule

// HDL file - gf12lp_rpll_lib, rpll_bias, functional.

//Verilog HDL for "wmx_rpll_lib", "rpll_14g_bias" "functional"




`timescale 1ns / 1ns 

module wphy_rpll_mvp_4g_rpll_bias ( nbias_cp, bias_lvl, en, vdda, vss );


  output  reg nbias_cp;

  input  en ;
  inout vdda, vss;

  input [3:0]  bias_lvl;

	real bias_delay;

  wire en_int = en & vdda & ~vss;

  
  integer seed;
  initial begin
	  if ($value$plusargs("SEED=%d", seed)) begin   
    end
    else 
  	  seed = $random;
  end
  
  
  always @(*) begin
  	if(en_int) begin
    	bias_delay								  = 20 + {$random(seed)}%(100-20);			//random delay of 20-100ns
    	#(bias_delay)			nbias_cp  =	en_int ; 
                        
    end else begin
    										nbias_cp  = 1'b0;
                        
    end
  end

endmodule

// HDL file - gf12lp_rpll_lib, rpll_14g_chp_diff, systemVerilog.

//systemVerilog HDL for "wphy_ln08lpu_rpll_lib", "wphy_rpll_chp_diff" "systemVerilog"


module wphy_rpll_mvp_4g_rpll_14g_chp_diff ( out, outb, vdda, vss, bcrnt_en, ictrl, in, inb,
nbias );
  input bcrnt_en;
  input in;
  inout vdda;
  output var real out;
  input  [4:0] ictrl;
  output var real outb;
  input nbias;
  input inb;
  inout vss;

parameter CTRL_AMP = 1.5e-6;

wire power_good = vdda & ~vss;
wire bias_good  = nbias && (bcrnt_en === 0 || bcrnt_en === 1);

assign out  = in  && bias_good ? (ictrl * CTRL_AMP) : 0;
assign outb = inb && bias_good ? (ictrl * CTRL_AMP) : 0;

endmodule

// HDL file - wavshared_gf12lp_dig_lib, INV_D4_GL16_RVT, systemVerilog.

//systemVerilog HDL for "wavshared_ln08lpu_dig_lib", "INV_D4_GL16_RVT" "systemVerilog"


module wphy_rpll_mvp_4g_INV_D4_GL16_RVT ( in, out
`ifdef WLOGIC_MODEL_NO_PG
`else
, vdd, vss
`endif //WLOGIC_MODEL_NO_PG
);

  input in;
  output out;
`ifdef WLOGIC_MODEL_NO_PG
`else
  inout vdd;
  inout vss;
`endif //WLOGIC_MODEL_NO_PG

`ifdef WLOGIC_MODEL_NO_PG
`else

`ifdef WLOGIC_PWR_CHECK
  wire   power_ok;
  assign power_ok = ~vss & vdd;
  
  assign out = (power_ok) ? 1'bz : 1'bx;

`endif //WLOGIC_PWR_CHECK

`endif //WLOGIC_MODEL_NO_PG

   assign out = ~in;


endmodule

// HDL file - gf12lp_rpll_lib, mvp_pll_demux4, systemVerilog.

//systemVerilog HDL for "wphy_pll_lib", "mvp_pll_demux4" "systemVerilog"


module wphy_rpll_mvp_4g_mvp_pll_demux4 ( 
  output var real   out0, 
  output var real  out1, 
  output var real  out2, 
  output var real  out3, 
  inout   vdd, 
  inout   vss, 
  input var real  in, 
  input  [1:0] sel 
);

assign out0 = sel == 0 ? in : 0;
assign out1 = sel == 1 ? in : 0;
assign out2 = sel == 2 ? in : 0;
assign out3 = sel == 3 ? in : 0;

endmodule

// HDL file - gf12lp_rpll_lib, mvp_vco_4GHz_wcdac, systemVerilog.

//systemVerilog HDL for "wphy_ln08lpu_rpll_lib", "mvp_vco_4GHz_wcdac" "systemVerilog"

`timescale 1ns/1fs

module wphy_rpll_mvp_4g_mvp_vco_4GHz_wcdac ( clk0, clk90, clk180, clk270, vdda, vss, course,
en, vgate, vring, fine );

  input var real 	vring;		//proportional
  input var real 	vgate;		//integral
  inout wire		vdda;
  output wire       clk270;
  output wire       clk90;
  input  wire [5:0] course;
  output wire       clk180;
  output wire       clk0;
  input  wire       en;
  input  wire [5:0] fine;
  inout  wire       vss;



parameter real	  	freerun		= 10e6;
// V - vgate
// IP - vring(proportional)
//F= (A1*V^2+B1*V+C1) + (A2*V^2+B2*V+C2)*IP

bit     force_pll;
string  this_inst;
int     last_char;
string  check_str;
bit     is_vco0;
initial begin
  if ($test$plusargs("MVP_FORCE_PLL")) begin   
    force_pll = 1;
    
    //Check for VCO0 to spit out a clock
    this_inst = $psprintf("%m");
    //$display("%s", this_inst);
    for(integer i = 0; i < this_inst.len(); i++) begin
      check_str = this_inst.substr(i , this_inst.len()-1);
      //$display("checking: %s", check_str);
      if(check_str == ".IVCO0.VCO") begin
        //$display("found VCO");
        is_vco0 = 1;
        break;
      end
    end
  end 
   
end


wire      power_good = vdda & ~vss;
wire      en_int     = power_good && en;
real		  clk_per;
reg				clk0_int = 0; 
reg       clk90_int = 0;

real freq;
real vgate2;
always @(*) begin
  if(force_pll) begin
    if(~is_vco0) begin
      case(course)
          0 : freq = 1e9/2.114872;
          1 : freq = 1e9/1.570058;
          2 : freq = 1e9/1.271428;
          3 : freq = 1e9/1.079676;
          4 : freq = 1e9/0.956076;
          5 : freq = 1e9/0.855788;
          6 : freq = 1e9/0.780740;
          7 : freq = 1e9/0.725522;
          8 : freq = 1e9/0.677114;
          9 : freq = 1e9/0.638662;
          10: freq = 1e9/0.602576;
          11: freq = 1e9/0.574692;
          12: freq = 1e9/0.547646;
          13: freq = 1e9/0.525228;
          14: freq = 1e9/0.506288;
          15: freq = 1e9/0.489672;
          16: freq = 1e9/0.472084;
          17: freq = 1e9/0.462600;
          18: freq = 1e9/0.445360;
          19: freq = 1e9/0.425650;
          20: freq = 1e9/0.424886;
          21: freq = 1e9/0.405894;
          22: freq = 1e9/0.405028;
          23: freq = 1e9/0.386752;
          24: freq = 1e9/0.382644;
          25: freq = 1e9/0.376504;
          26: freq = 1e9/0.374686;
          27: freq = 1e9/0.358910;
          28: freq = 1e9/0.351652;
          29: freq = 1e9/0.346420;
          30: freq = 1e9/0.343980;
          31: freq = 1e9/0.336408;
          32: freq = 1e9/0.331616;
          33: freq = 1e9/0.326148;
          34: freq = 1e9/0.321642;
          35: freq = 1e9/0.319502;
          36: freq = 1e9/0.313674;
          37: freq = 1e9/0.310204;
          38: freq = 1e9/0.308150;
          39: freq = 1e9/0.306250;
          40: freq = 1e9/0.296846;
          41: freq = 1e9/0.301702;
          42: freq = 1e9/0.298428;
          43: freq = 1e9/0.290104;
          44: freq = 1e9/0.288418;
          45: freq = 1e9/0.285426;
          46: freq = 1e9/0.284248;
          47: freq = 1e9/0.280768;
          48: freq = 1e9/0.279188;
          49: freq = 1e9/0.276940;
          50: freq = 1e9/0.270820;
          51: freq = 1e9/0.267658;
          52: freq = 1e9/0.272136;
          53: freq = 1e9/0.268418;
          54: freq = 1e9/0.261666;
          55: freq = 1e9/0.260674;
          56: freq = 1e9/0.257744;
          57: freq = 1e9/0.255828;
          58: freq = 1e9/0.259426;
          59: freq = 1e9/0.257484;
          60: freq = 1e9/0.256046;
          61: freq = 1e9/0.253686;
          62: freq = 1e9/0.247646;
          63: freq = 1e9/0.250000;
          default : freq = freerun;
        endcase
        freq = ((0.009*fine) + 0.76) * freq;
      end else begin
        freq = 768e6;
      end
  end else begin
    if((vgate >= 0.8) && (vgate <= 1.2) && en_int) begin
      vgate2 = vgate**2;
      case(course)

        0 : freq =  (vgate2 * 7.21E+07         + vgate * 1.71E+09  +  -1.12E+09  ) + ( vgate2 *-1.16E+12  + vgate *  7.64E+11  + 6.46E+12)*vring;
        1 : freq =  (vgate2 * 7.29E+07         + vgate * 2.40E+09  +  -1.58E+09  ) + ( vgate2 * 3.29E+11  + vgate * -2.74E+12  + 8.03E+12)*vring;
        2 : freq =  (vgate2 * 5.29E+07         + vgate * 3.05E+09  +  -2.00E+09  ) + ( vgate2 * 8.14E+11  + vgate * -3.96E+12  + 8.43E+12)*vring;
        3 : freq =  (vgate2 * 1.86E+07         + vgate * 3.67E+09  +  -2.39E+09  ) + ( vgate2 * 1.19E+12  + vgate * -4.89E+12  + 8.72E+12)*vring;
        4 : freq =  (vgate2 * -2.29E+07        + vgate * 4.26E+09  +  -2.77E+09  ) + ( vgate2 * 1.51E+12  + vgate * -5.70E+12  + 8.98E+12)*vring;
        5 : freq =  (vgate2 * -7.14E+07        + vgate * 4.83E+09  +  -3.12E+09  ) + ( vgate2 * 1.79E+12  + vgate * -6.37E+12  + 9.18E+12)*vring;
        6 : freq =  (vgate2 * -1.14E+08        + vgate * 5.36E+09  +  -3.45E+09  ) + ( vgate2 * 2.11E+12  + vgate * -7.12E+12  + 9.43E+12)*vring;
        7 : freq =  (vgate2 * -1.67E+08        + vgate * 5.87E+09  +  -3.77E+09  ) + ( vgate2 * 2.28E+12  + vgate * -7.53E+12  + 9.54E+12)*vring;
        8 : freq =  (vgate2 * -2.19E+08        + vgate * 6.36E+09  +  -4.07E+09  ) + ( vgate2 * 2.49E+12  + vgate * -8.03E+12  + 9.68E+12)*vring;
        9 : freq =  (vgate2 * -2.74E+08        + vgate * 6.84E+09  +  -4.37E+09  ) + ( vgate2 * 2.69E+12  + vgate * -8.48E+12  + 9.82E+12)*vring;
        10: freq =	(vgate2 * -3.43E+08        + vgate * 7.33E+09  +  -4.66E+09  ) + ( vgate2 * 2.86E+12  + vgate * -8.89E+12  + 9.94E+12)*vring;
        11: freq =	(vgate2 * -4.00E+08        + vgate * 7.77E+09  +  -4.93E+09  ) + ( vgate2 * 3.02E+12  + vgate * -9.24E+12  + 1.00E+13)*vring;
        12: freq =	(vgate2 * -4.50E+08        + vgate * 8.19E+09  +  -5.18E+09  ) + ( vgate2 * 3.14E+12  + vgate * -9.52E+12  + 1.01E+13)*vring;
        13: freq =	(vgate2 * -5.21E+08        + vgate * 8.63E+09  +  -5.44E+09  ) + ( vgate2 * 3.29E+12  + vgate * -9.84E+12  + 1.02E+13)*vring;
        14: freq =	(vgate2 * -5.71E+08        + vgate * 9.02E+09  +  -5.68E+09  ) + ( vgate2 * 3.39E+12  + vgate * -1.01E+13  + 1.02E+13)*vring;
        15: freq =	(vgate2 * -6.57E+08        + vgate * 9.46E+09  +  -5.94E+09  ) + ( vgate2 * 3.51E+12  + vgate * -1.03E+13  + 1.03E+13)*vring;
        16: freq =	(vgate2 * -7.21E+08        + vgate * 9.86E+09  +  -6.17E+09  ) + ( vgate2 * 3.60E+12  + vgate * -1.05E+13  + 1.04E+13)*vring;
        17: freq =	(vgate2 * -7.79E+08        + vgate * 1.02E+10  +  -6.39E+09  ) + ( vgate2 * 3.69E+12  + vgate * -1.08E+13  + 1.04E+13)*vring;
        18: freq =	(vgate2 * -8.43E+08        + vgate * 1.06E+10  +  -6.61E+09  ) + ( vgate2 * 3.77E+12  + vgate * -1.09E+13  + 1.04E+13)*vring;
        19: freq =	(vgate2 * -9.00E+08        + vgate * 1.10E+10  +  -6.81E+09  ) + ( vgate2 * 3.86E+12  + vgate * -1.11E+13  + 1.05E+13)*vring;
        20: freq =	(vgate2 * -9.71E+08        + vgate * 1.13E+10  +  -7.03E+09  ) + ( vgate2 * 3.95E+12  + vgate * -1.13E+13  + 1.05E+13)*vring;
        21: freq =	(vgate2 * -1.03E+09        + vgate * 1.17E+10  +  -7.22E+09  ) + ( vgate2 * 4.01E+12  + vgate * -1.14E+13  + 1.05E+13)*vring;
        22: freq =	(vgate2 * -1.11E+09        + vgate * 1.20E+10  +  -7.43E+09  ) + ( vgate2 * 4.06E+12  + vgate * -1.15E+13  + 1.05E+13)*vring;
        23: freq =	(vgate2 * -1.16E+09        + vgate * 1.24E+10  +  -7.62E+09  ) + ( vgate2 * 4.11E+12  + vgate * -1.17E+13  + 1.06E+13)*vring;
        24: freq =	(vgate2 * -1.23E+09        + vgate * 1.27E+10  +  -7.81E+09  ) + ( vgate2 * 4.19E+12  + vgate * -1.18E+13  + 1.06E+13)*vring;
        25: freq =	(vgate2 * -1.29E+09        + vgate * 1.30E+10  +  -7.99E+09  ) + ( vgate2 * 4.24E+12  + vgate * -1.19E+13  + 1.06E+13)*vring;
        26: freq =	(vgate2 * -1.37E+09        + vgate * 1.33E+10  +  -8.19E+09  ) + ( vgate2 * 4.29E+12  + vgate * -1.20E+13  + 1.06E+13)*vring;
        27: freq =	(vgate2 * -1.44E+09        + vgate * 1.37E+10  +  -8.36E+09  ) + ( vgate2 * 4.36E+12  + vgate * -1.22E+13  + 1.07E+13)*vring;
        28: freq =	(vgate2 * -1.49E+09        + vgate * 1.40E+10  +  -8.53E+09  ) + ( vgate2 * 4.39E+12  + vgate * -1.22E+13  + 1.07E+13)*vring;
        29: freq =	(vgate2 * -1.56E+09        + vgate * 1.43E+10  +  -8.70E+09  ) + ( vgate2 * 4.43E+12  + vgate * -1.23E+13  + 1.07E+13)*vring;
        30: freq =	(vgate2 * -1.64E+09        + vgate * 1.46E+10  +  -8.89E+09  ) + ( vgate2 * 4.49E+12  + vgate * -1.25E+13  + 1.07E+13)*vring;
        31: freq =	(vgate2 * -1.70E+09        + vgate * 1.49E+10  +  -9.04E+09  ) + ( vgate2 * 4.50E+12  + vgate * -1.25E+13  + 1.07E+13)*vring;
        32: freq =	(vgate2 * -1.77E+09        + vgate * 1.52E+10  +  -9.21E+09  ) + ( vgate2 * 4.54E+12  + vgate * -1.26E+13  + 1.07E+13)*vring;
        33: freq =	(vgate2 * -1.84E+09        + vgate * 1.55E+10  +  -9.37E+09  ) + ( vgate2 * 4.60E+12  + vgate * -1.27E+13  + 1.07E+13)*vring;
        34: freq =	(vgate2 * -1.91E+09        + vgate * 1.58E+10  +  -9.54E+09  ) + ( vgate2 * 4.63E+12  + vgate * -1.27E+13  + 1.07E+13)*vring;
        35: freq =	(vgate2 * -1.95E+09        + vgate * 1.60E+10  +  -9.67E+09  ) + ( vgate2 * 4.65E+12  + vgate * -1.28E+13  + 1.07E+13)*vring;
        36: freq =	(vgate2 * -2.02E+09        + vgate * 1.63E+10  +  -9.82E+09  ) + ( vgate2 * 4.69E+12  + vgate * -1.29E+13  + 1.07E+13)*vring;
        37: freq =	(vgate2 * -2.10E+09        + vgate * 1.66E+10  +  -9.99E+09  ) + ( vgate2 * 4.71E+12  + vgate * -1.29E+13  + 1.07E+13)*vring;
        38: freq =	(vgate2 * -2.16E+09        + vgate * 1.68E+10  +  -1.01E+10  ) + ( vgate2 * 4.74E+12  + vgate * -1.30E+13  + 1.07E+13)*vring;
        39: freq =	(vgate2 * -2.23E+09        + vgate * 1.71E+10  +  -1.03E+10  ) + ( vgate2 * 4.77E+12  + vgate * -1.30E+13  + 1.07E+13)*vring;
        40: freq =	(vgate2 * -2.29E+09        + vgate * 1.74E+10  +  -1.04E+10  ) + ( vgate2 * 4.79E+12  + vgate * -1.31E+13  + 1.07E+13)*vring;
        41: freq =	(vgate2 * -2.36E+09        + vgate * 1.76E+10  +  -1.06E+10  ) + ( vgate2 * 4.82E+12  + vgate * -1.31E+13  + 1.07E+13)*vring;
        42: freq =	(vgate2 * -2.41E+09        + vgate * 1.78E+10  +  -1.07E+10  ) + ( vgate2 * 4.83E+12  + vgate * -1.31E+13  + 1.07E+13)*vring;
        43: freq =	(vgate2 * -2.48E+09        + vgate * 1.81E+10  +  -1.08E+10  ) + ( vgate2 * 4.86E+12  + vgate * -1.32E+13  + 1.07E+13)*vring;
        44: freq =	(vgate2 * -2.55E+09        + vgate * 1.84E+10  +  -1.10E+10  ) + ( vgate2 * 4.89E+12  + vgate * -1.33E+13  + 1.07E+13)*vring;
        45: freq =	(vgate2 * -2.60E+09        + vgate * 1.86E+10  +  -1.11E+10  ) + ( vgate2 * 4.91E+12  + vgate * -1.33E+13  + 1.07E+13)*vring;
        46: freq =	(vgate2 * -2.68E+09        + vgate * 1.88E+10  +  -1.12E+10  ) + ( vgate2 * 4.91E+12  + vgate * -1.33E+13  + 1.07E+13)*vring;
        47: freq =	(vgate2 * -2.72E+09        + vgate * 1.90E+10  +  -1.13E+10  ) + ( vgate2 * 4.93E+12  + vgate * -1.33E+13  + 1.07E+13)*vring;
        48: freq =	(vgate2 * -2.79E+09        + vgate * 1.93E+10  +  -1.15E+10  ) + ( vgate2 * 4.97E+12  + vgate * -1.34E+13  + 1.07E+13)*vring;
        49: freq =	(vgate2 * -2.85E+09        + vgate * 1.95E+10  +  -1.16E+10  ) + ( vgate2 * 5.01E+12  + vgate * -1.35E+13  + 1.07E+13)*vring;
        50: freq =	(vgate2 * -2.94E+09        + vgate * 1.98E+10  +  -1.17E+10  ) + ( vgate2 * 5.01E+12  + vgate * -1.35E+13  + 1.07E+13)*vring;
        51: freq =	(vgate2 * -2.98E+09        + vgate * 2.00E+10  +  -1.18E+10  ) + ( vgate2 * 5.05E+12  + vgate * -1.36E+13  + 1.07E+13)*vring;
        52: freq =	(vgate2 * -3.06E+09        + vgate * 2.02E+10  +  -1.20E+10  ) + ( vgate2 * 5.05E+12  + vgate * -1.36E+13  + 1.07E+13)*vring;
        53: freq =	(vgate2 * -3.09E+09        + vgate * 2.04E+10  +  -1.21E+10  ) + ( vgate2 * 5.06E+12  + vgate * -1.36E+13  + 1.07E+13)*vring;
        54: freq =	(vgate2 * -3.16E+09        + vgate * 2.07E+10  +  -1.22E+10  ) + ( vgate2 * 5.08E+12  + vgate * -1.36E+13  + 1.07E+13)*vring;
        55: freq =	(vgate2 * -3.24E+09        + vgate * 2.09E+10  +  -1.23E+10  ) + ( vgate2 * 5.10E+12  + vgate * -1.37E+13  + 1.07E+13)*vring;
        56: freq =	(vgate2 * -3.28E+09        + vgate * 2.11E+10  +  -1.24E+10  ) + ( vgate2 * 5.12E+12  + vgate * -1.37E+13  + 1.07E+13)*vring;
        57: freq =	(vgate2 * -3.34E+09        + vgate * 2.13E+10  +  -1.25E+10  ) + ( vgate2 * 5.12E+12  + vgate * -1.37E+13  + 1.06E+13)*vring;
        58: freq =	(vgate2 * -3.41E+09        + vgate * 2.15E+10  +  -1.27E+10  ) + ( vgate2 * 5.14E+12  + vgate * -1.37E+13  + 1.06E+13)*vring;
        59: freq =	(vgate2 * -3.47E+09        + vgate * 2.17E+10  +  -1.28E+10  ) + ( vgate2 * 5.14E+12  + vgate * -1.37E+13  + 1.06E+13)*vring;
        60: freq =	(vgate2 * -3.54E+09        + vgate * 2.19E+10  +  -1.29E+10  ) + ( vgate2 * 5.17E+12  + vgate * -1.38E+13  + 1.06E+13)*vring;
        61: freq =	(vgate2 * -3.59E+09        + vgate * 2.21E+10  +  -1.30E+10  ) + ( vgate2 * 5.19E+12  + vgate * -1.38E+13  + 1.06E+13)*vring;
        62: freq =	(vgate2 * -3.66E+09        + vgate * 2.24E+10  +  -1.31E+10  ) + ( vgate2 * 5.21E+12  + vgate * -1.38E+13  + 1.06E+13)*vring;
        63: freq =	(vgate2 * -3.71E+09        + vgate * 2.25E+10  +  -1.32E+10  ) + ( vgate2 * 5.22E+12  + vgate * -1.39E+13  + 1.06E+13)*vring;

        default : freq = freerun;
      endcase
      //fine adjustment
      freq = ((0.009*fine) + 0.76) * freq;
    end else begin
      freq = freerun;
    end
  end

  //Formula above can go negative, so put in a small check to protect against
  //negative delays and div0
  if(freq < freerun) begin
    freq = freerun;
  end
  
  clk_per = (1e9 / freq);
end


always begin
  #(clk_per/2)    clk0_int = ~clk0_int;
end

always @(clk0_int) begin
  #(clk_per/4)    clk90_int = clk0_int;
end

assign clk0 	= en_int ? clk0_int : 1'b0;
assign clk180	= ~clk0;
assign clk90	= en_int ? clk90_int : 1'b0;
assign clk270	= ~clk90;
  
endmodule

// HDL file - gf12lp_rpll_lib, rpll_14g_dbl, functional.

//Verilog HDL for "wmx_rpll_lib", "rpll_14g_dbl" "functional"

`timescale 1ns/1ps
module wphy_rpll_mvp_4g_rpll_14g_dbl ( vdbl, vdda, vss, clksel, divclk, en, refclk );

  input refclk;
  input clksel;
  output reg vdbl;
  inout vdda;
  input divclk;
  input en;
  inout vss;
  parameter real VDBL_DELAY = 1000 ;	//1us delay from the time refclk/divclk edge is seen
  
  /*
  * clksel = 0 -- refclk
  * clksel = 1 -- divclk
  *
  * One of these clocks needs to be running for this to work. Hold the vdbl until
  * and edge of the selected clock is seen
  */
  
  wire en_int;
  wire sel_clk_int;
  
  
  assign en_int			= en & vdda & ~vss;
  assign sel_clk_int		= clksel ? divclk : refclk;
  
  always @(*) begin
  	if(en_int) begin
    	@(posedge sel_clk_int);
      #(VDBL_DELAY) vdbl = 1'b1;
    end else begin
    	vdbl = 1'b0;
    end
  end
  

endmodule


// HDL file - wavshared_gf12lp_dig_lib, MUXT2_D2_GL16_RVT, systemVerilog.

//systemVerilog HDL for "wavshared_tsmc12ffc_lib", "MUXT2_D2_GL16_RVT" "systemVerilog"


module wphy_rpll_mvp_4g_MUXT2_D2_GL16_RVT( yb, a, b, s, sb
`ifdef WLOGIC_MODEL_NO_PG
`else
, vss, vdd 
`endif //WLOGIC_MODEL_NO_PG
); 

  input a; 
  input sb;
  input s;
  output yb;
  input b;
`ifdef WLOGIC_MODEL_NO_PG
`else
  inout vdd;
  inout vss;
`endif //WLOGIC_MODEL_NO_PG

  wire yb;

`ifdef WLOGIC_MODEL_NO_PG
`else

`ifdef WLOGIC_PWR_CHECK
  wire   power_ok;
  assign power_ok = ~vss & vdd;
  
  assign yb = (power_ok) ? 1'bz : 1'bx;

`endif //WLOGIC_PWR_CHECK

`endif //WLOGIC_MODEL_NO_PG

  assign yb = (s && ~sb) ? ~b:~a;



endmodule

// HDL file - wavshared_gf12lp_dig_lib, FF_D1_GL16_RVT, systemVerilog.

//systemVerilog HDL for "wavshared_tsmc12ffc_lib", "FF_D1_GL16_RVT" "systemVerilog"

module wphy_rpll_mvp_4g_FF_D1_GL16_RVT( q, clk, clkb, d
`ifdef WLOGIC_MODEL_NO_TIE
`else
,tielo, tiehi
`endif //WLOGIC_MODEL_NO_TIE
`ifdef WLOGIC_MODEL_NO_PG
`else
, vss, vdd 
`endif //WLOGIC_MODEL_NO_PG
); 

  input clk;
  output q;
  input d;
  input clkb;
`ifdef WLOGIC_MODEL_NO_TIE
`else
  input tiehi;
  input tielo;
`endif //WLOGIC_MODEL_NO_TIE
`ifdef WLOGIC_MODEL_NO_PG
`else
  inout vdd;
  inout vss;
`endif //WLOGIC_MODEL_NO_PG

  reg q_int;

`ifdef WLOGIC_MODEL_NO_TIE
`else

`ifdef WLOGIC_TIE_CHECK
  wire   signals_ok;
  assign signals_ok = tiehi & ~tielo;

  initial  begin
       q_int = (signals_ok) ? 1'bz : 1'bx;
  end
  always @(*) begin
       q_int = (signals_ok) ? 1'bz : 1'bx;
  end
`endif // WLOGIC_TIE_CHECK

`endif //WLOGIC_MODEL_NO_TIE

`ifdef WLOGIC_MODEL_NO_PG
`else

`ifdef WLOGIC_PWR_CHECK
  wire   power_ok;
  assign power_ok = ~vss & vdd;
  
  initial  begin
       q_int = (power_ok) ? 1'bz : 1'bx;
  end
  always @(*) begin
       q_int = (power_ok) ? 1'bz : 1'bx;
  end
`endif //WLOGIC_PWR_CHECK

`endif //WLOGIC_MODEL_NO_PG


  wire q;
  assign q= q_int;

  initial begin
    q_int = $random;
  end

always @ (posedge clk) q_int<= (d === 1'bx) ? $random : d;

endmodule


// HDL file - gf12lp_rpll_lib, mvp_vco_400MHz_wcdac, systemVerilog.

//systemVerilog HDL for "gf12lp_rpll_lib", "mvp_vco_400MHz_wcdac" "systemVerilog"

`timescale 1ns/1fs
module wphy_rpll_mvp_4g_mvp_vco_400MHz_wcdac ( clk, vdda, vring, vss, course, en, fine, vgate
);

  input real vring;
  input real vgate;
  inout vdda;
  input  [5:0] course;
  input en;
  output clk;
  input  [5:0] fine;
  inout vss;

parameter real	  	freerun		= 10e6;
// V - vgate
// IP - vring(proportional)
//F= (A1*V^2+B1*V+C1) + (A2*V^2+B2*V+C2)*IP

bit     force_pll;
string  this_inst;
int     last_char;
string  check_str;
bit     is_vco0;
initial begin
  if ($test$plusargs("MVP_FORCE_PLL")) begin   
    force_pll = 1;
    
    //Check for VCO0 to spit out a clock
    this_inst = $psprintf("%m");
    //$display("%s", this_inst);
    for(integer i = 0; i < this_inst.len(); i++) begin
      check_str = this_inst.substr(i , this_inst.len()-1);
      //$display("checking: %s", check_str);
      if(check_str == ".IVCO0.VCO") begin
        //$display("found VCO");
        is_vco0 = 1;
        break;
      end
    end
  end 
   
end


wire      power_good = vdda & ~vss;
wire      en_int     = power_good && en;
real		  clk_per;
reg				clk0_int = 0; 

real freq;
real vgate2;
always @(*) begin
  if(force_pll) begin
    if(~is_vco0) begin
      case(course)
          0 : freq = 1e9/2.114872;
          1 : freq = 1e9/1.570058;
          2 : freq = 1e9/1.271428;
          3 : freq = 1e9/1.079676;
          4 : freq = 1e9/0.956076;
          5 : freq = 1e9/0.855788;
          6 : freq = 1e9/0.780740;
          7 : freq = 1e9/0.725522;
          8 : freq = 1e9/0.677114;
          9 : freq = 1e9/0.638662;
          10: freq = 1e9/0.602576;
          11: freq = 1e9/0.574692;
          12: freq = 1e9/0.547646;
          13: freq = 1e9/0.525228;
          14: freq = 1e9/0.506288;
          15: freq = 1e9/0.489672;
          16: freq = 1e9/0.472084;
          17: freq = 1e9/0.462600;
          18: freq = 1e9/0.445360;
          19: freq = 1e9/0.425650;
          20: freq = 1e9/0.424886;
          21: freq = 1e9/0.405894;
          22: freq = 1e9/0.405028;
          23: freq = 1e9/0.386752;
          24: freq = 1e9/0.382644;
          25: freq = 1e9/0.376504;
          26: freq = 1e9/0.374686;
          27: freq = 1e9/0.358910;
          28: freq = 1e9/0.351652;
          29: freq = 1e9/0.346420;
          30: freq = 1e9/0.343980;
          31: freq = 1e9/0.336408;
          32: freq = 1e9/0.331616;
          33: freq = 1e9/0.326148;
          34: freq = 1e9/0.321642;
          35: freq = 1e9/0.319502;
          36: freq = 1e9/0.313674;
          37: freq = 1e9/0.310204;
          38: freq = 1e9/0.308150;
          39: freq = 1e9/0.306250;
          40: freq = 1e9/0.296846;
          41: freq = 1e9/0.301702;
          42: freq = 1e9/0.298428;
          43: freq = 1e9/0.290104;
          44: freq = 1e9/0.288418;
          45: freq = 1e9/0.285426;
          46: freq = 1e9/0.284248;
          47: freq = 1e9/0.280768;
          48: freq = 1e9/0.279188;
          49: freq = 1e9/0.276940;
          50: freq = 1e9/0.270820;
          51: freq = 1e9/0.267658;
          52: freq = 1e9/0.272136;
          53: freq = 1e9/0.268418;
          54: freq = 1e9/0.261666;
          55: freq = 1e9/0.260674;
          56: freq = 1e9/0.257744;
          57: freq = 1e9/0.255828;
          58: freq = 1e9/0.259426;
          59: freq = 1e9/0.257484;
          60: freq = 1e9/0.256046;
          61: freq = 1e9/0.253686;
          62: freq = 1e9/0.247646;
          63: freq = 1e9/0.250000;
          default : freq = freerun;
        endcase
		freq = freq / 3.0;
		freq = ((0.009*fine) + 0.76) * freq;
      end else begin
        freq = 384e6;
      end
  end else begin
    if((vgate >= 0.8) && (vgate <= 1.2) && en_int) begin
      vgate2 = vgate**2;
      case(course)

        0 : freq =  (vgate2 * 7.21E+07         + vgate * 1.71E+09  +  -1.12E+09  ) + ( vgate2 *-1.16E+12  + vgate *  7.64E+11  + 6.46E+12)*vring;
        1 : freq =  (vgate2 * 7.29E+07         + vgate * 2.40E+09  +  -1.58E+09  ) + ( vgate2 * 3.29E+11  + vgate * -2.74E+12  + 8.03E+12)*vring;
        2 : freq =  (vgate2 * 5.29E+07         + vgate * 3.05E+09  +  -2.00E+09  ) + ( vgate2 * 8.14E+11  + vgate * -3.96E+12  + 8.43E+12)*vring;
        3 : freq =  (vgate2 * 1.86E+07         + vgate * 3.67E+09  +  -2.39E+09  ) + ( vgate2 * 1.19E+12  + vgate * -4.89E+12  + 8.72E+12)*vring;
        4 : freq =  (vgate2 * -2.29E+07        + vgate * 4.26E+09  +  -2.77E+09  ) + ( vgate2 * 1.51E+12  + vgate * -5.70E+12  + 8.98E+12)*vring;
        5 : freq =  (vgate2 * -7.14E+07        + vgate * 4.83E+09  +  -3.12E+09  ) + ( vgate2 * 1.79E+12  + vgate * -6.37E+12  + 9.18E+12)*vring;
        6 : freq =  (vgate2 * -1.14E+08        + vgate * 5.36E+09  +  -3.45E+09  ) + ( vgate2 * 2.11E+12  + vgate * -7.12E+12  + 9.43E+12)*vring;
        7 : freq =  (vgate2 * -1.67E+08        + vgate * 5.87E+09  +  -3.77E+09  ) + ( vgate2 * 2.28E+12  + vgate * -7.53E+12  + 9.54E+12)*vring;
        8 : freq =  (vgate2 * -2.19E+08        + vgate * 6.36E+09  +  -4.07E+09  ) + ( vgate2 * 2.49E+12  + vgate * -8.03E+12  + 9.68E+12)*vring;
        9 : freq =  (vgate2 * -2.74E+08        + vgate * 6.84E+09  +  -4.37E+09  ) + ( vgate2 * 2.69E+12  + vgate * -8.48E+12  + 9.82E+12)*vring;
        10: freq =	(vgate2 * -3.43E+08        + vgate * 7.33E+09  +  -4.66E+09  ) + ( vgate2 * 2.86E+12  + vgate * -8.89E+12  + 9.94E+12)*vring;
        11: freq =	(vgate2 * -4.00E+08        + vgate * 7.77E+09  +  -4.93E+09  ) + ( vgate2 * 3.02E+12  + vgate * -9.24E+12  + 1.00E+13)*vring;
        12: freq =	(vgate2 * -4.50E+08        + vgate * 8.19E+09  +  -5.18E+09  ) + ( vgate2 * 3.14E+12  + vgate * -9.52E+12  + 1.01E+13)*vring;
        13: freq =	(vgate2 * -5.21E+08        + vgate * 8.63E+09  +  -5.44E+09  ) + ( vgate2 * 3.29E+12  + vgate * -9.84E+12  + 1.02E+13)*vring;
        14: freq =	(vgate2 * -5.71E+08        + vgate * 9.02E+09  +  -5.68E+09  ) + ( vgate2 * 3.39E+12  + vgate * -1.01E+13  + 1.02E+13)*vring;
        15: freq =	(vgate2 * -6.57E+08        + vgate * 9.46E+09  +  -5.94E+09  ) + ( vgate2 * 3.51E+12  + vgate * -1.03E+13  + 1.03E+13)*vring;
        16: freq =	(vgate2 * -7.21E+08        + vgate * 9.86E+09  +  -6.17E+09  ) + ( vgate2 * 3.60E+12  + vgate * -1.05E+13  + 1.04E+13)*vring;
        17: freq =	(vgate2 * -7.79E+08        + vgate * 1.02E+10  +  -6.39E+09  ) + ( vgate2 * 3.69E+12  + vgate * -1.08E+13  + 1.04E+13)*vring;
        18: freq =	(vgate2 * -8.43E+08        + vgate * 1.06E+10  +  -6.61E+09  ) + ( vgate2 * 3.77E+12  + vgate * -1.09E+13  + 1.04E+13)*vring;
        19: freq =	(vgate2 * -9.00E+08        + vgate * 1.10E+10  +  -6.81E+09  ) + ( vgate2 * 3.86E+12  + vgate * -1.11E+13  + 1.05E+13)*vring;
        20: freq =	(vgate2 * -9.71E+08        + vgate * 1.13E+10  +  -7.03E+09  ) + ( vgate2 * 3.95E+12  + vgate * -1.13E+13  + 1.05E+13)*vring;
        21: freq =	(vgate2 * -1.03E+09        + vgate * 1.17E+10  +  -7.22E+09  ) + ( vgate2 * 4.01E+12  + vgate * -1.14E+13  + 1.05E+13)*vring;
        22: freq =	(vgate2 * -1.11E+09        + vgate * 1.20E+10  +  -7.43E+09  ) + ( vgate2 * 4.06E+12  + vgate * -1.15E+13  + 1.05E+13)*vring;
        23: freq =	(vgate2 * -1.16E+09        + vgate * 1.24E+10  +  -7.62E+09  ) + ( vgate2 * 4.11E+12  + vgate * -1.17E+13  + 1.06E+13)*vring;
        24: freq =	(vgate2 * -1.23E+09        + vgate * 1.27E+10  +  -7.81E+09  ) + ( vgate2 * 4.19E+12  + vgate * -1.18E+13  + 1.06E+13)*vring;
        25: freq =	(vgate2 * -1.29E+09        + vgate * 1.30E+10  +  -7.99E+09  ) + ( vgate2 * 4.24E+12  + vgate * -1.19E+13  + 1.06E+13)*vring;
        26: freq =	(vgate2 * -1.37E+09        + vgate * 1.33E+10  +  -8.19E+09  ) + ( vgate2 * 4.29E+12  + vgate * -1.20E+13  + 1.06E+13)*vring;
        27: freq =	(vgate2 * -1.44E+09        + vgate * 1.37E+10  +  -8.36E+09  ) + ( vgate2 * 4.36E+12  + vgate * -1.22E+13  + 1.07E+13)*vring;
        28: freq =	(vgate2 * -1.49E+09        + vgate * 1.40E+10  +  -8.53E+09  ) + ( vgate2 * 4.39E+12  + vgate * -1.22E+13  + 1.07E+13)*vring;
        29: freq =	(vgate2 * -1.56E+09        + vgate * 1.43E+10  +  -8.70E+09  ) + ( vgate2 * 4.43E+12  + vgate * -1.23E+13  + 1.07E+13)*vring;
        30: freq =	(vgate2 * -1.64E+09        + vgate * 1.46E+10  +  -8.89E+09  ) + ( vgate2 * 4.49E+12  + vgate * -1.25E+13  + 1.07E+13)*vring;
        31: freq =	(vgate2 * -1.70E+09        + vgate * 1.49E+10  +  -9.04E+09  ) + ( vgate2 * 4.50E+12  + vgate * -1.25E+13  + 1.07E+13)*vring;
        32: freq =	(vgate2 * -1.77E+09        + vgate * 1.52E+10  +  -9.21E+09  ) + ( vgate2 * 4.54E+12  + vgate * -1.26E+13  + 1.07E+13)*vring;
        33: freq =	(vgate2 * -1.84E+09        + vgate * 1.55E+10  +  -9.37E+09  ) + ( vgate2 * 4.60E+12  + vgate * -1.27E+13  + 1.07E+13)*vring;
        34: freq =	(vgate2 * -1.91E+09        + vgate * 1.58E+10  +  -9.54E+09  ) + ( vgate2 * 4.63E+12  + vgate * -1.27E+13  + 1.07E+13)*vring;
        35: freq =	(vgate2 * -1.95E+09        + vgate * 1.60E+10  +  -9.67E+09  ) + ( vgate2 * 4.65E+12  + vgate * -1.28E+13  + 1.07E+13)*vring;
        36: freq =	(vgate2 * -2.02E+09        + vgate * 1.63E+10  +  -9.82E+09  ) + ( vgate2 * 4.69E+12  + vgate * -1.29E+13  + 1.07E+13)*vring;
        37: freq =	(vgate2 * -2.10E+09        + vgate * 1.66E+10  +  -9.99E+09  ) + ( vgate2 * 4.71E+12  + vgate * -1.29E+13  + 1.07E+13)*vring;
        38: freq =	(vgate2 * -2.16E+09        + vgate * 1.68E+10  +  -1.01E+10  ) + ( vgate2 * 4.74E+12  + vgate * -1.30E+13  + 1.07E+13)*vring;
        39: freq =	(vgate2 * -2.23E+09        + vgate * 1.71E+10  +  -1.03E+10  ) + ( vgate2 * 4.77E+12  + vgate * -1.30E+13  + 1.07E+13)*vring;
        40: freq =	(vgate2 * -2.29E+09        + vgate * 1.74E+10  +  -1.04E+10  ) + ( vgate2 * 4.79E+12  + vgate * -1.31E+13  + 1.07E+13)*vring;
        41: freq =	(vgate2 * -2.36E+09        + vgate * 1.76E+10  +  -1.06E+10  ) + ( vgate2 * 4.82E+12  + vgate * -1.31E+13  + 1.07E+13)*vring;
        42: freq =	(vgate2 * -2.41E+09        + vgate * 1.78E+10  +  -1.07E+10  ) + ( vgate2 * 4.83E+12  + vgate * -1.31E+13  + 1.07E+13)*vring;
        43: freq =	(vgate2 * -2.48E+09        + vgate * 1.81E+10  +  -1.08E+10  ) + ( vgate2 * 4.86E+12  + vgate * -1.32E+13  + 1.07E+13)*vring;
        44: freq =	(vgate2 * -2.55E+09        + vgate * 1.84E+10  +  -1.10E+10  ) + ( vgate2 * 4.89E+12  + vgate * -1.33E+13  + 1.07E+13)*vring;
        45: freq =	(vgate2 * -2.60E+09        + vgate * 1.86E+10  +  -1.11E+10  ) + ( vgate2 * 4.91E+12  + vgate * -1.33E+13  + 1.07E+13)*vring;
        46: freq =	(vgate2 * -2.68E+09        + vgate * 1.88E+10  +  -1.12E+10  ) + ( vgate2 * 4.91E+12  + vgate * -1.33E+13  + 1.07E+13)*vring;
        47: freq =	(vgate2 * -2.72E+09        + vgate * 1.90E+10  +  -1.13E+10  ) + ( vgate2 * 4.93E+12  + vgate * -1.33E+13  + 1.07E+13)*vring;
        48: freq =	(vgate2 * -2.79E+09        + vgate * 1.93E+10  +  -1.15E+10  ) + ( vgate2 * 4.97E+12  + vgate * -1.34E+13  + 1.07E+13)*vring;
        49: freq =	(vgate2 * -2.85E+09        + vgate * 1.95E+10  +  -1.16E+10  ) + ( vgate2 * 5.01E+12  + vgate * -1.35E+13  + 1.07E+13)*vring;
        50: freq =	(vgate2 * -2.94E+09        + vgate * 1.98E+10  +  -1.17E+10  ) + ( vgate2 * 5.01E+12  + vgate * -1.35E+13  + 1.07E+13)*vring;
        51: freq =	(vgate2 * -2.98E+09        + vgate * 2.00E+10  +  -1.18E+10  ) + ( vgate2 * 5.05E+12  + vgate * -1.36E+13  + 1.07E+13)*vring;
        52: freq =	(vgate2 * -3.06E+09        + vgate * 2.02E+10  +  -1.20E+10  ) + ( vgate2 * 5.05E+12  + vgate * -1.36E+13  + 1.07E+13)*vring;
        53: freq =	(vgate2 * -3.09E+09        + vgate * 2.04E+10  +  -1.21E+10  ) + ( vgate2 * 5.06E+12  + vgate * -1.36E+13  + 1.07E+13)*vring;
        54: freq =	(vgate2 * -3.16E+09        + vgate * 2.07E+10  +  -1.22E+10  ) + ( vgate2 * 5.08E+12  + vgate * -1.36E+13  + 1.07E+13)*vring;
        55: freq =	(vgate2 * -3.24E+09        + vgate * 2.09E+10  +  -1.23E+10  ) + ( vgate2 * 5.10E+12  + vgate * -1.37E+13  + 1.07E+13)*vring;
        56: freq =	(vgate2 * -3.28E+09        + vgate * 2.11E+10  +  -1.24E+10  ) + ( vgate2 * 5.12E+12  + vgate * -1.37E+13  + 1.07E+13)*vring;
        57: freq =	(vgate2 * -3.34E+09        + vgate * 2.13E+10  +  -1.25E+10  ) + ( vgate2 * 5.12E+12  + vgate * -1.37E+13  + 1.06E+13)*vring;
        58: freq =	(vgate2 * -3.41E+09        + vgate * 2.15E+10  +  -1.27E+10  ) + ( vgate2 * 5.14E+12  + vgate * -1.37E+13  + 1.06E+13)*vring;
        59: freq =	(vgate2 * -3.47E+09        + vgate * 2.17E+10  +  -1.28E+10  ) + ( vgate2 * 5.14E+12  + vgate * -1.37E+13  + 1.06E+13)*vring;
        60: freq =	(vgate2 * -3.54E+09        + vgate * 2.19E+10  +  -1.29E+10  ) + ( vgate2 * 5.17E+12  + vgate * -1.38E+13  + 1.06E+13)*vring;
        61: freq =	(vgate2 * -3.59E+09        + vgate * 2.21E+10  +  -1.30E+10  ) + ( vgate2 * 5.19E+12  + vgate * -1.38E+13  + 1.06E+13)*vring;
        62: freq =	(vgate2 * -3.66E+09        + vgate * 2.24E+10  +  -1.31E+10  ) + ( vgate2 * 5.21E+12  + vgate * -1.38E+13  + 1.06E+13)*vring;
        63: freq =	(vgate2 * -3.71E+09        + vgate * 2.25E+10  +  -1.32E+10  ) + ( vgate2 * 5.22E+12  + vgate * -1.39E+13  + 1.06E+13)*vring;

        default : freq = freerun;
      endcase
      //fine adjustment
      freq = freq / 3.0;
      freq = ((0.009*fine) + 0.76) * freq;
    end else begin
      freq = freerun;
    end
  end

  //Formula above can go negative, so put in a small check to protect against
  //negative delays and div0
  if(freq < freerun) begin
    freq = freerun;
  end
  
  clk_per = (1e9 / freq);
end


always begin
  #(clk_per/2)    clk0_int = ~clk0_int;
end



assign clk 	= en_int ? clk0_int : 1'b0;
  
endmodule


// HDL file - wavshared_gf12lp_dig_lib, INV_D2_GL16_RVT, systemVerilog.

//systemVerilog HDL for "wavshared_tsmc12ffc_lib", "INV_D2_GL16_RVT" "systemVerilog"


module wphy_rpll_mvp_4g_INV_D2_GL16_RVT ( in, out
`ifdef WLOGIC_MODEL_NO_PG
`else
, vdd, vss
`endif //WLOGIC_MODEL_NO_PG
);

  input in;
  output out;
`ifdef WLOGIC_MODEL_NO_PG
`else
  inout vdd;
  inout vss;
`endif //WLOGIC_MODEL_NO_PG

`ifdef WLOGIC_MODEL_NO_PG
`else

`ifdef WLOGIC_PWR_CHECK
  wire   power_ok;
  assign power_ok = ~vss & vdd;
  
  assign out = (power_ok) ? 1'bz : 1'bx;

`endif //WLOGIC_PWR_CHECK

`endif //WLOGIC_MODEL_NO_PG

   assign out = ~in;

endmodule
// End HDL models

// Library - gf12lp_rpll_lib, Cell - mvp_vco_400MHz_top, View -
//schematic
// LAST TIME SAVED: Oct 27 10:14:55 2020
// NETLIST TIME: Jan  5 13:28:17 2021
`timescale 1ns / 1ns 

module wphy_rpll_mvp_4g_mvp_vco_400MHz_top ( 
output wire logic   clk, 
inout wire logic   vdda, 
inout wire logic   vss, 
input wire logic  [5:0] course, 
input wire logic   en, 
input wire logic  [5:0] fine, 
input wire logic   refclk, 
input var real  vgate , 
input var real  vring  );


wire logic rclkb ;

wire logic rclk ;

// Buses in the design

wire logic [5:0]  net015;

wire logic [5:0]  net014;

wire logic [5:0]  fine_ctrl;



wphy_rpll_mvp_4g_INV_D2_GL16_RVT INV1[5:0] ( .out(net014[5:0]), .vdd(vdda), .vss(vss),
     .in(net015[5:0]));
wphy_rpll_mvp_4g_INV_D2_GL16_RVT INV3[1:0] ( .out(rclk), .vdd(vdda), .vss(vss),
     .in(rclkb));
wphy_rpll_mvp_4g_INV_D2_GL16_RVT INV2[1:0] ( .out(rclkb), .vdd(vdda), .vss(vss),
     .in(refclk));
wphy_rpll_mvp_4g_INV_D2_GL16_RVT INV4[5:0] ( .out(fine_ctrl[5:0]), .vdd(vdda),
     .vss(vss), .in(net014[5:0]));
wphy_rpll_mvp_4g_mvp_vco_400MHz_wcdac VCO ( .clk(clk), .course(course[5:0]),
     .vring(vring), .fine(fine_ctrl[5:0]), .vgate(vgate), .en(en),
     .vdda(vdda), .vss(vss));
wphy_rpll_mvp_4g_FF_D1_GL16_RVT FF0[5:0] ( .q(net015[5:0]), .vdd(vdda), .vss(vss),
     .clk(rclk), .clkb(rclkb), .d(fine[5:0]), .tiehi(vdda),
     .tielo(vss));

endmodule
// Library - gf12lp_rpll_lib, Cell - mvp_vco_4GHz_top, View - schematic
// LAST TIME SAVED: Oct 19 17:23:38 2020
// NETLIST TIME: Jan  5 13:28:17 2021
`timescale 1ns / 1ns 

module wphy_rpll_mvp_4g_mvp_vco_4GHz_top ( 
output wire logic   clk0, 
output wire logic   clk90, 
output wire logic   clk180, 
output wire logic   clk270, 
inout wire logic   vdda, 
inout wire logic   vss, 
input wire logic  [5:0] course, 
input wire logic   en, 
input wire logic  [5:0] fine, 
input wire logic   refclk, 
input var real  vgate , 
input var real  vring  );


wire logic clkb ;

wire logic clk ;

// Buses in the design

wire logic [5:0]  net015;

wire logic [5:0]  net014;

wire logic [5:0]  fine_ctrl;



wphy_rpll_mvp_4g_mvp_vco_4GHz_wcdac VCO ( .course(course[5:0]), .vring(vring),
     .fine(fine_ctrl[5:0]), .vgate(vgate), .en(en), .vdda(vdda),
     .vss(vss), .clk270(clk270), .clk180(clk180), .clk90(clk90),
     .clk0(clk0));
wphy_rpll_mvp_4g_INV_D2_GL16_RVT INV1[5:0] ( .out(net014[5:0]), .vdd(vdda), .vss(vss),
     .in(net015[5:0]));
wphy_rpll_mvp_4g_INV_D2_GL16_RVT INV3[1:0] ( .out(clk), .vdd(vdda), .vss(vss),
     .in(clkb));
wphy_rpll_mvp_4g_INV_D2_GL16_RVT INV2[1:0] ( .out(clkb), .vdd(vdda), .vss(vss),
     .in(refclk));
wphy_rpll_mvp_4g_INV_D2_GL16_RVT INV4[5:0] ( .out(fine_ctrl[5:0]), .vdd(vdda),
     .vss(vss), .in(net014[5:0]));
wphy_rpll_mvp_4g_FF_D1_GL16_RVT FF0[5:0] ( .q(net015[5:0]), .vdd(vdda), .vss(vss),
     .clk(clk), .clkb(clkb), .d(fine[5:0]), .tiehi(vdda), .tielo(vss));

endmodule
// Library - gf12lp_rpll_lib, Cell - wphy_rpll_postdiv_se, View -
//schematic
// LAST TIME SAVED: Oct 27 16:24:05 2020
// NETLIST TIME: Jan  5 13:28:17 2021
`timescale 1ns / 1ns 

module wphy_rpll_mvp_4g_wphy_rpll_postdiv_se ( 
output wire logic   div2clk, 
output wire logic   outclk, 
inout wire logic   vdda, 
inout wire logic   vss, 
input wire logic   byp_clk, 
input wire logic   byp_clk_sel, 
input wire logic   vcoclk );


wire logic mx0 ;

wire logic clkintp ;

wire logic byp_clk_selb ;

wire logic net015 ;

wire logic byp_clkb ;

wire logic net016 ;

wire logic clkintn ;

wire logic byp_clk_sela ;



/*REMOVED VIA SCRIPT -- pcapacitor  C0 ( .MINUS(vss), .PLUS(net015));*/
wphy_rpll_mvp_4g_MUXT2_D2_GL16_RVT MUX4 ( .vss(vss), .sb(byp_clk_selb),
     .s(byp_clk_sela), .b(byp_clkb), .a(clkintn), .yb(mx0),
     .vdd(vdda));
wphy_rpll_mvp_4g_INV_D2_GL16_RVT INV3 ( .in(vcoclk), .vss(vss), .out(clkintp),
     .vdd(vdda));
wphy_rpll_mvp_4g_INV_D2_GL16_RVT INV2 ( .in(clkintp), .vss(vss), .out(clkintn),
     .vdd(vdda));
wphy_rpll_mvp_4g_INV_D2_GL16_RVT INV34 ( .in(net015), .vss(vss), .out(net016),
     .vdd(vdda));
wphy_rpll_mvp_4g_INV_D2_GL16_RVT INV33 ( .in(net015), .vss(vss), .out(div2clk),
     .vdd(vdda));
wphy_rpll_mvp_4g_INV_D2_GL16_RVT INV28 ( .in(byp_clk), .vss(vss), .out(byp_clkb),
     .vdd(vdda));
wphy_rpll_mvp_4g_INV_D2_GL16_RVT INV30 ( .in(byp_clk_selb), .vss(vss),
     .out(byp_clk_sela), .vdd(vdda));
wphy_rpll_mvp_4g_INV_D2_GL16_RVT INV17[2:0] ( .out(outclk), .vdd(vdda), .vss(vss),
     .in(mx0));
wphy_rpll_mvp_4g_INV_D2_GL16_RVT INV29 ( .in(byp_clk_sel), .vss(vss),
     .out(byp_clk_selb), .vdd(vdda));
wphy_rpll_mvp_4g_FF_D1_GL16_RVT LA1 ( .tielo(vss), .tiehi(vdda), .vss(vss), .vdd(vdda),
     .d(net016), .clkb(clkintn), .clk(clkintp), .q(net015));

endmodule
// Library - gf12lp_rpll_lib, Cell - rpll_14g_chp, View - schematic
// LAST TIME SAVED: Oct 20 12:04:28 2020
// NETLIST TIME: Jan  5 13:28:17 2021
`timescale 1ns / 1ns 

module wphy_rpll_mvp_4g_rpll_14g_chp ( 
output var real  idn_int , 
output var real  idn_prop , 
output var real  idnb_int , 
output var real  idnb_prop , 
output var real  iup_int , 
output var real  iup_prop , 
output var real  iupb_int , 
output var real  iupb_prop , 
inout wire logic   vdda, 
inout wire logic   vss, 
input wire logic   dn, 
input wire logic   dnb, 
input wire logic  [4:0] int_ctrl, 
input wire logic   mode, 
input wire logic   nbias, 
input wire logic   up, 
input wire logic   upb );


wire logic bcrnt_en ;

wire logic net059 ;

// Buses in the design

wire  [4:0]  int_;

wire logic [4:0]  net2;



wphy_rpll_mvp_4g_rpll_14g_chp_diff PROP_DN ( .ictrl({vdda, vdda, vdda, vdda, vdda}),
     .vdda(vdda), .out(idn_prop), .outb(idnb_prop),
     .bcrnt_en(bcrnt_en), .in(dn), .inb(dnb), .nbias(nbias),
     .vss(vss));
wphy_rpll_mvp_4g_rpll_14g_chp_diff INT_DN ( .ictrl(int_[4:0]), .vdda(vdda),
     .out(idn_int), .outb(idnb_int), .bcrnt_en(bcrnt_en), .in(dn),
     .inb(dnb), .nbias(nbias), .vss(vss));
wphy_rpll_mvp_4g_rpll_14g_chp_diff PROP_UP ( .ictrl({vdda, vdda, vdda, vdda, vdda}),
     .vdda(vdda), .out(iup_prop), .outb(iupb_prop),
     .bcrnt_en(bcrnt_en), .in(up), .inb(upb), .nbias(nbias),
     .vss(vss));
wphy_rpll_mvp_4g_rpll_14g_chp_diff INT_UP ( .ictrl(int_[4:0]), .vdda(vdda),
     .out(iup_int), .outb(iupb_int), .bcrnt_en(bcrnt_en), .in(up),
     .inb(upb), .nbias(nbias), .vss(vss));
wphy_rpll_mvp_4g_INV_D2_GL16_RVT INV7[4:0] ( .out(net2[4:0]), .vdd(vdda), .vss(vss),
     .in(int_ctrl[4:0]));
wphy_rpll_mvp_4g_INV_D2_GL16_RVT INV0 ( .vdd(vdda), .in(mode), .vss(vss), .out(net059));
wphy_rpll_mvp_4g_INV_D2_GL16_RVT INV1 ( .vdd(vdda), .in(net059), .vss(vss),
     .out(bcrnt_en));
wphy_rpll_mvp_4g_INV_D2_GL16_RVT INV2[4:0] ( .out(int_[4:0]), .vdd(vdda), .vss(vss),
     .in(net2[4:0]));

endmodule
// Library - gf12lp_rpll_lib, Cell - mvp_rpll_filter, View - schematic
// LAST TIME SAVED: Oct 26 13:51:31 2020
// NETLIST TIME: Jan  5 13:28:17 2021
`timescale 1ns / 1ns 

module wphy_rpll_mvp_4g_mvp_rpll_filter ( 
output var real  iprop , 
output var real  vint , 
inout wire logic   vdbl, 
inout wire logic   vdda, 
inout wire logic   vss, 
input wire logic  [1:0] c_ctrl, 
input wire logic   en, 
input var real  idn_int , 
input var real  idn_prop , 
input var real  idnb_int , 
input var real  idnb_prop , 
input var real  iup_int , 
input var real  iup_prop , 
input var real  iupb_int , 
input var real  iupb_prop , 
input wire logic  [4:0] prop_ctrl, 
input wire logic  [1:0] r_ctrl );


wire logic ena ;

wire logic enb ;

var real iout_up ;

var real iout_dn ;



wphy_rpll_mvp_4g_rpll_14g_chp_prop_dac IFIL_PROP ( .ctrl(prop_ctrl[4:0]),
     .c_ctrl(c_ctrl[1:0]), .r_ctrl(r_ctrl[1:0]), .idn_prop(idn_prop),
     .idnb_prop(idnb_prop), .iup_prop(iup_prop), .iupb_prop(iupb_prop),
     .vdda(vdda), .iout_prop(iprop), .vss(vss));
wphy_rpll_mvp_4g_rpll_14g_filter_int IFIL_INT ( .iout_dn(iout_dn), .iout_up(iout_up),
     .idn_int(idn_int), .idnb_int(idnb_int), .iup_int(iup_int),
     .iupb_int(iupb_int), .vdbl(vdbl), .vss(vss), .vdda(vdda));
wphy_rpll_mvp_4g_rpll_filter_cap_20pF ICAP ( .vcap(vint), .ena(ena), .idn(iout_dn),
     .iup(iout_up), .vss(vss), .vdda(vdda));
wphy_rpll_mvp_4g_INV_D2_GL16_RVT INV3 ( .vdd(vdda), .in(enb), .vss(vss), .out(ena));
wphy_rpll_mvp_4g_INV_D2_GL16_RVT INV2 ( .vdd(vdda), .in(en), .vss(vss), .out(enb));

endmodule
// Library - gf12lp_rpll_lib, Cell - rpll_14g_fbdiv_logic_unit, View -
//schematic
// LAST TIME SAVED: Oct 22 12:16:51 2020
// NETLIST TIME: Jan  5 13:28:17 2021
`timescale 1ns / 1ns 

module wphy_rpll_mvp_4g_rpll_14g_fbdiv_logic_unit ( 
output wire logic   Q, 
output wire logic   next, 
inout wire logic   vdd, 
inout wire logic   vss, 
input wire logic   T, 
input wire logic   clk, 
input wire logic   clkb, 
input wire logic   load, 
input wire logic   loadval );


wire logic Tb ;

wire logic rst ;

wire logic prst ;

wire logic net015 ;

wire logic prstb ;

wire logic rstb ;

wire logic ffin ;

wire logic ffout2 ;

wire logic ffout ;



wphy_rpll_mvp_4g_NOR2_D1_GL16_LVT NOR0 ( .tielo(vss), .tiehi(vdd), .vdd(vdd), .y(next),
     .vss(vss), .b(Tb), .a(ffout));
wphy_rpll_mvp_4g_INV_D2_GL16_LVT INV6 ( .vdd(vdd), .in(loadval), .vss(vss),
     .out(net015));
wphy_rpll_mvp_4g_INV_D2_GL16_LVT INV8 ( .vdd(vdd), .in(ffout2), .vss(vss), .out(Q));
wphy_rpll_mvp_4g_INV_D2_GL16_LVT INV2 ( .vdd(vdd), .in(T), .vss(vss), .out(Tb));
wphy_rpll_mvp_4g_INV_D2_GL16_LVT INV9 ( .vdd(vdd), .in(ffout), .vss(vss), .out(ffout2));
wphy_rpll_mvp_4g_INV_D2_GL16_LVT INV5 ( .vdd(vdd), .in(rstb), .vss(vss), .out(rst));
wphy_rpll_mvp_4g_INV_D2_GL16_LVT INV4 ( .vdd(vdd), .in(prstb), .vss(vss), .out(prst));
wphy_rpll_mvp_4g_MUXT2_D2_GL16_LVT MUX0 ( .vdd(vdd), .vss(vss), .sb(Q), .s(ffout2),
     .b(Tb), .a(T), .yb(ffin));
wphy_rpll_mvp_4g_FFSETRES_D1_GL16_LVT FF1 ( .tielo(vss), .tiehi(vdd), .prstb(prstb),
     .prst(prst), .rst(rst), .rstb(rstb), .vss(vss), .vdd(vdd),
     .d(ffin), .clkb(clkb), .clk(clk), .q(ffout));
/*REMOVED VIA SCRIPT -- wphy_rpll_mvp_4g_DUM_D1_GL16_LVT DUM0[0:16] ( .vdd(vdd), .vss(vss), .tiehi(vdd),
     .tielo(vss));*/
wphy_rpll_mvp_4g_NAND2_D1_GL16_LVT NAND7 ( .tielo(vss), .tiehi(vdd), .vdd(vdd),
     .y(rstb), .vss(vss), .b(load), .a(net015));
wphy_rpll_mvp_4g_NAND2_D1_GL16_LVT AND0 ( .tielo(vss), .tiehi(vdd), .vdd(vdd),
     .y(prstb), .vss(vss), .b(load), .a(loadval));

endmodule
// Library - wavshared_gf12lp_dig_lib, Cell - SE2DIHS_D2_GL16_LVT, View
//- schematic
// LAST TIME SAVED: Nov 10 12:03:13 2020
// NETLIST TIME: Jan  5 13:28:18 2021
`timescale 1ns / 1ns 

module wphy_rpll_mvp_4g_SE2DIHS_D2_GL16_LVT ( 
output wire logic   outn, 
output wire logic   outp, 
inout wire logic   vdd, 
inout wire logic   vss, 
input wire logic   in, 
input wire logic   tiehi, 
input wire logic   tielo );


wire logic p1 ;

wire logic n1 ;

wire logic inb ;



wphy_rpll_mvp_4g_PD_D1_GL16_LVT PD1 ( .vss(vss), .enb(tielo), .y(n1));
wphy_rpll_mvp_4g_PD_D1_GL16_LVT PD0 ( .vss(vss), .enb(tielo), .y(inb));
wphy_rpll_mvp_4g_INV_D2_GL16_LVT INV4[1:0] ( .out(outn), .vdd(vdd), .vss(vss), .in(p1));
wphy_rpll_mvp_4g_INV_D2_GL16_LVT INV6 ( .in(inb), .vss(vss), .out(p1), .vdd(vdd));
wphy_rpll_mvp_4g_INV_D2_GL16_LVT INV8 ( .in(in), .vss(vss), .out(inb), .vdd(vdd));
wphy_rpll_mvp_4g_INV_D2_GL16_LVT INV7 ( .in(in), .vss(vss), .out(inb), .vdd(vdd));
wphy_rpll_mvp_4g_INV_D2_GL16_LVT INV5[1:0] ( .out(outp), .vdd(vdd), .vss(vss), .in(n1));
wphy_rpll_mvp_4g_XG_D1_GL16_LVT XGATE0[4:0] ( .y(n1), .vdd(vdd), .vss(vss), .a(inb),
     .en(vdd), .enb(vss));
wphy_rpll_mvp_4g_INV_D1_GL16_LVT_Mmod_nomodel INV10 ( .tiehi(tiehi), .tielo(tielo),
     .in(outp), .vss(vss), .out(outn), .vdd(vdd));
wphy_rpll_mvp_4g_INV_D1_GL16_LVT_Mmod_nomodel INV3 ( .tiehi(tiehi), .tielo(tielo),
     .in(n1), .vss(vss), .out(p1), .vdd(vdd));
wphy_rpll_mvp_4g_INV_D1_GL16_LVT_Mmod_nomodel INV2 ( .tiehi(tiehi), .tielo(tielo),
     .in(p1), .vss(vss), .out(n1), .vdd(vdd));
wphy_rpll_mvp_4g_INV_D1_GL16_LVT_Mmod_nomodel INV9 ( .tiehi(tiehi), .tielo(tielo),
     .in(outn), .vss(vss), .out(outp), .vdd(vdd));
wphy_rpll_mvp_4g_PU_D1_GL16_LVT PU1 ( .vdd(vdd), .en(tiehi), .y(n1));
wphy_rpll_mvp_4g_PU_D1_GL16_LVT PU0 ( .vdd(vdd), .en(tiehi), .y(inb));

endmodule
// Library - gf12lp_rpll_lib, Cell - rpll_14g_fbdiv, View - schematic
// LAST TIME SAVED: Oct  9 14:57:33 2020
// NETLIST TIME: Jan  5 13:28:18 2021
`timescale 1ns / 1ns 

module wphy_rpll_mvp_4g_rpll_14g_fbdiv ( 
output wire logic   clkdiv_out, 
inout wire logic   vdda, 
inout wire logic   vss, 
input wire logic   clkin, 
input wire logic  [8:0] div, 
input wire logic   reset );


wire logic load ;

wire logic outn ;

wire logic outp ;

wire logic Q3 ;

wire logic Q8 ;

wire logic Q7 ;

wire logic netb ;

wire logic clkb ;

wire logic Q6 ;

wire logic Q5 ;

wire logic clk ;

wire logic Q2 ;

wire logic Q4 ;

wire logic Q1 ;

wire logic resetb ;

wire logic reset_buf ;

wire logic net0154 ;

wire net0151 ;

wire logic net0152 ;

wire logic net0156 ;

wire logic net0136 ;

wire logic net0148 ;

wire logic net0135 ;

wire net0147 ;

wire logic net043 ;

wire logic net0118 ;

wire logic net0140 ;

wire logic net0142 ;

wire logic net0137 ;

wire logic net0124 ;

wire logic net0150 ;

wire logic net0123 ;

wire logic net0120 ;

wire logic net0149 ;

wire logic net0144 ;

wire logic net0127 ;

wire logic net0117 ;

wire logic net0121 ;

wire logic net0119 ;

wire logic net0130 ;

wire logic net0141 ;

wire logic net0146 ;

wire logic net0122 ;

wire logic net0126 ;

wire logic net0112 ;

wire logic net0138 ;

wire logic net049 ;

wire logic net0128 ;

wire logic net0139 ;

wire logic net0111 ;

wire net0155 ;

wire logic net0160 ;

wire logic net0159 ;



/*REMOVED VIA SCRIPT -- wphy_rpll_mvp_4g_DUM_D1_GL16_LVT DUM0[0:167] ( .vdd(vdda), .vss(vss), .tiehi(vdda),
     .tielo(vss));*/
wphy_rpll_mvp_4g_rpll_14g_fbdiv_logic_unit DIV_UNIT0 ( .vdd(vdda), .T(vdda), .Q(Q1),
     .next(net0140), .clk(clk), .clkb(clkb), .load(load),
     .loadval(div[1]), .vss(vss));
wphy_rpll_mvp_4g_rpll_14g_fbdiv_logic_unit DIV_UNIT3 ( .vdd(vdda), .T(net0155), .Q(Q4),
     .next(net0150), .clk(clk), .clkb(clkb), .load(load),
     .loadval(div[4]), .vss(vss));
wphy_rpll_mvp_4g_rpll_14g_fbdiv_logic_unit DIV_UNIT4 ( .vdd(vdda), .T(net0150), .Q(Q5),
     .next(net0142), .clk(clk), .clkb(clkb), .load(load),
     .loadval(div[5]), .vss(vss));
wphy_rpll_mvp_4g_rpll_14g_fbdiv_logic_unit DIV_UNIT5 ( .vdd(vdda), .T(net0142), .Q(Q6),
     .next(net0160), .clk(clk), .clkb(clkb), .load(load),
     .loadval(div[6]), .vss(vss));
wphy_rpll_mvp_4g_rpll_14g_fbdiv_logic_unit DIV_UNIT1 ( .vdd(vdda), .T(net0140), .Q(Q2),
     .next(net0139), .clk(clk), .clkb(clkb), .load(load),
     .loadval(div[2]), .vss(vss));
wphy_rpll_mvp_4g_rpll_14g_fbdiv_logic_unit DIV_UNIT6 ( .vdd(vdda), .T(net0151), .Q(Q7),
     .next(net0141), .clk(clk), .clkb(clkb), .load(load),
     .loadval(div[7]), .vss(vss));
wphy_rpll_mvp_4g_rpll_14g_fbdiv_logic_unit DIV_UNIT7 ( .vdd(vdda), .T(net0141), .Q(Q8),
     .next(net0138), .clk(clk), .clkb(clkb), .load(load),
     .loadval(div[8]), .vss(vss));
wphy_rpll_mvp_4g_rpll_14g_fbdiv_logic_unit DIV_UNIT2 ( .vdd(vdda), .T(net0139), .Q(Q3),
     .next(net0156), .clk(clk), .clkb(clkb), .load(load),
     .loadval(div[3]), .vss(vss));
wphy_rpll_mvp_4g_NAND3_D1_GL16_LVT NAND3 ( .tielo(vss), .tiehi(vdda), .vdd(vdda),
     .y(net0146), .vss(vss), .c(net0127), .b(resetb), .a(net0128));
wphy_rpll_mvp_4g_SE2DIHS_D2_GL16_LVT SE2DIFF0 ( .tiehi(vdda), .tielo(vss), .vdd(vdda),
     .vss(vss), .outp(outp), .outn(outn), .in(clkin));
wphy_rpll_mvp_4g_FFRES_D1_GL16_LVT FF3 ( .tiehi(vdda), .tielo(vss), .rst(reset_buf),
     .vss(vss), .vdd(vdda), .rstb(resetb), .d(net0154), .clkb(clkb),
     .clk(clk), .q(net0147));
wphy_rpll_mvp_4g_FFRES_D1_GL16_LVT FF0 ( .tiehi(vdda), .tielo(vss), .rst(load),
     .vss(vss), .vdd(vdda), .rstb(net0159), .d(net0160), .clkb(clkb),
     .clk(clk), .q(net0151));
wphy_rpll_mvp_4g_FFRES_D1_GL16_LVT FF1 ( .tiehi(vdda), .tielo(vss), .rst(load),
     .vss(vss), .vdd(vdda), .rstb(net0124), .d(net0156), .clkb(clkb),
     .clk(clk), .q(net0155));
wphy_rpll_mvp_4g_NAND2_D1_GL16_LVT NAND7 ( .tielo(vss), .tiehi(vdda), .vdd(vdda),
     .y(net0122), .vss(vss), .b(net0118), .a(net0119));
wphy_rpll_mvp_4g_NAND2_D1_GL16_LVT NAND1 ( .tielo(vss), .tiehi(vdda), .vdd(vdda),
     .y(net0123), .vss(vss), .b(net0120), .a(net0121));
wphy_rpll_mvp_4g_NAND2_D1_GL16_LVT NAND5 ( .tielo(vss), .tiehi(vdda), .vdd(vdda),
     .y(net0127), .vss(vss), .b(net0112), .a(net043));
wphy_rpll_mvp_4g_NAND2_D1_GL16_LVT NAND0 ( .tielo(vss), .tiehi(vdda), .vdd(vdda),
     .y(net0128), .vss(vss), .b(net0126), .a(net0111));
wphy_rpll_mvp_4g_NAND2_D1_GL16_LVT NAND2 ( .tielo(vss), .tiehi(vdda), .vdd(vdda),
     .y(net0137), .vss(vss), .b(load), .a(net0135));
wphy_rpll_mvp_4g_NAND2_D1_GL16_LVT NAND4 ( .tielo(vss), .tiehi(vdda), .vdd(vdda),
     .y(net0154), .vss(vss), .b(net0136), .a(net0137));
wphy_rpll_mvp_4g_NAND2_D1_GL16_LVT NAND6 ( .tielo(vss), .tiehi(vdda), .vdd(vdda),
     .y(net0136), .vss(vss), .b(netb), .a(clkdiv_out));
wphy_rpll_mvp_4g_NAND2_D1_GL16_LVT NAND8 ( .tielo(vss), .tiehi(vdda), .vdd(vdda),
     .y(net0144), .vss(vss), .b(net0130), .a(clkdiv_out));
wphy_rpll_mvp_4g_FF_D1_GL16_LVT FF6 ( .tiehi(vdda), .tielo(vss), .vss(vss), .vdd(vdda),
     .d(div[0]), .clkb(net0148), .clk(clkdiv_out), .q(net0130));
wphy_rpll_mvp_4g_FF_D1_GL16_LVT FF5 ( .tiehi(vdda), .tielo(vss), .vss(vss), .vdd(vdda),
     .d(net0111), .clkb(clkb), .clk(clk), .q(net043));
wphy_rpll_mvp_4g_FF_D1_GL16_LVT FF2 ( .tiehi(vdda), .tielo(vss), .vss(vss), .vdd(vdda),
     .d(net0146), .clkb(clkb), .clk(clk), .q(net049));
wphy_rpll_mvp_4g_FF_D1_GL16_LVT FF4 ( .tiehi(vdda), .tielo(vss), .vss(vss), .vdd(vdda),
     .d(net0152), .clkb(clkb), .clk(clk), .q(net0111));
wphy_rpll_mvp_4g_INV_D2_GL16_LVT INV32 ( .in(load), .vss(vss), .out(net0159),
     .vdd(vdda));
wphy_rpll_mvp_4g_INV_D2_GL16_LVT INV0 ( .in(load), .vss(vss), .out(net0124),
     .vdd(vdda));
wphy_rpll_mvp_4g_INV_D2_GL16_LVT INV10 ( .in(Q1), .vss(vss), .out(net0117), .vdd(vdda));
wphy_rpll_mvp_4g_INV_D2_GL16_LVT INV8 ( .in(Q2), .vss(vss), .out(net0149), .vdd(vdda));
wphy_rpll_mvp_4g_INV_D2_GL16_LVT INV12[6:0] ( .out(clk), .vdd(vdda), .vss(vss),
     .in(outn));
wphy_rpll_mvp_4g_INV_D2_GL16_LVT INV2 ( .in(reset), .vss(vss), .out(resetb),
     .vdd(vdda));
wphy_rpll_mvp_4g_INV_D2_GL16_LVT INV15 ( .in(clkdiv_out), .vss(vss), .out(net0148),
     .vdd(vdda));
wphy_rpll_mvp_4g_INV_D2_GL16_LVT INV14 ( .in(net0144), .vss(vss), .out(net0112),
     .vdd(vdda));
wphy_rpll_mvp_4g_INV_D2_GL16_LVT INV6 ( .in(net0147), .vss(vss), .out(net0135),
     .vdd(vdda));
wphy_rpll_mvp_4g_INV_D2_GL16_LVT INV5[4:0] ( .out(load), .vdd(vdda), .vss(vss),
     .in(netb));
wphy_rpll_mvp_4g_INV_D2_GL16_LVT INV7[3:0] ( .out(clkdiv_out), .vdd(vdda), .vss(vss),
     .in(net0135));
wphy_rpll_mvp_4g_INV_D2_GL16_LVT INV9 ( .in(net0112), .vss(vss), .out(net0126),
     .vdd(vdda));
wphy_rpll_mvp_4g_INV_D2_GL16_LVT INV4[1:0] ( .out(netb), .vdd(vdda), .vss(vss),
     .in(net049));
wphy_rpll_mvp_4g_INV_D2_GL16_LVT INV3 ( .in(resetb), .vss(vss), .out(reset_buf),
     .vdd(vdda));
wphy_rpll_mvp_4g_INV_D2_GL16_LVT INV33[6:0] ( .out(clkb), .vdd(vdda), .vss(vss),
     .in(outp));
wphy_rpll_mvp_4g_NOR2_D1_GL16_LVT NOR10 ( .tielo(vss), .tiehi(vdda), .y(net0152),
     .vss(vss), .vdd(vdda), .b(net0122), .a(net0123));
wphy_rpll_mvp_4g_NOR2_D1_GL16_LVT NOR3 ( .tielo(vss), .tiehi(vdda), .y(net0119),
     .vss(vss), .vdd(vdda), .b(Q3), .a(Q4));
wphy_rpll_mvp_4g_NOR2_D1_GL16_LVT NOR4 ( .tielo(vss), .tiehi(vdda), .y(net0118),
     .vss(vss), .vdd(vdda), .b(net0117), .a(net0149));
wphy_rpll_mvp_4g_NOR2_D1_GL16_LVT NOR0 ( .tielo(vss), .tiehi(vdda), .y(net0121),
     .vss(vss), .vdd(vdda), .b(Q7), .a(Q8));
wphy_rpll_mvp_4g_NOR2_D1_GL16_LVT NOR1 ( .tielo(vss), .tiehi(vdda), .y(net0120),
     .vss(vss), .vdd(vdda), .b(Q5), .a(Q6));

endmodule
// Library - gf12lp_rpll_lib, Cell - rpll_pfd, View - schematic
// LAST TIME SAVED: Oct  9 14:57:34 2020
// NETLIST TIME: Jan  5 13:28:18 2021
`timescale 1ns / 1ns 

module wphy_rpll_mvp_4g_rpll_pfd ( 
output wire logic   dn, 
output wire logic   dnb, 
output wire logic   up, 
output wire logic   upb, 
inout wire logic   vdda, 
inout wire logic   vss, 
input wire logic   fbclk, 
input wire logic  [1:0] mode, 
input wire logic   refclk, 
input wire logic   reset );


wire logic rst ;

wire net012 ;

wire logic rsta ;

wire net7 ;

wire logic s0b ;

wire logic s1b ;

wire logic s0 ;

wire logic s1 ;

wire logic fbclk_buf ;

wire logic fbclk_b ;

wire logic refclk_buf ;

wire logic refclk_b ;

wire logic net013 ;

wire logic net014 ;

wire logic rstb ;

// Buses in the design

wire logic [0:16]  rstdly;



wphy_rpll_mvp_4g_NAND2_D1_GL16_LVT NAND0 ( .tielo(vss), .tiehi(vdda), .vdd(vdda),
     .y(rsta), .vss(vss), .b(up), .a(dn));
wphy_rpll_mvp_4g_INV_D2_GL16_LVT INV5 ( .vdd(vdda), .in(rstb), .vss(vss), .out(rst));
wphy_rpll_mvp_4g_INV_D2_GL16_LVT INV4 ( .vdd(vdda), .in(net013), .vss(vss),
     .out(fbclk_buf));
wphy_rpll_mvp_4g_INV_D2_GL16_LVT INV3 ( .vdd(vdda), .in(fbclk_buf), .vss(vss),
     .out(fbclk_b));
wphy_rpll_mvp_4g_INV_D2_GL16_LVT INV2 ( .vdd(vdda), .in(refclk_buf), .vss(vss),
     .out(refclk_b));
wphy_rpll_mvp_4g_INV_D2_GL16_LVT INV1 ( .vdd(vdda), .in(net014), .vss(vss),
     .out(refclk_buf));
wphy_rpll_mvp_4g_INV_D2_GL16_LVT INV8[1:0] ( .out({s0, s1}), .vdd(vdda), .vss(vss),
     .in({s0b, s1b}));
wphy_rpll_mvp_4g_INV_D2_GL16_LVT INV7[1:0] ( .out({s0b, s1b}), .vdd(vdda), .vss(vss),
     .in(mode[1:0]));
wphy_rpll_mvp_4g_SE2DIHS_D2_GL16_LVT SE2DIFF0 ( .tiehi(vdda), .tielo(vss), .vdd(vdda),
     .vss(vss), .outp(dn), .outn(dnb), .in(net7));
wphy_rpll_mvp_4g_SE2DIHS_D2_GL16_LVT SE2DIFF1 ( .tiehi(vdda), .tielo(vss), .vdd(vdda),
     .vss(vss), .outp(up), .outn(upb), .in(net012));
wphy_rpll_mvp_4g_FFRES_D1_GL16_LVT IFF0 ( .tiehi(vdda), .tielo(vss), .rst(rst),
     .rstb(rstb), .vdd(vdda), .d(vdda), .q(net7), .clk(fbclk_buf),
     .clkb(fbclk_b), .vss(vss));
wphy_rpll_mvp_4g_FFRES_D1_GL16_LVT FF0 ( .tiehi(vdda), .tielo(vss), .rst(rst),
     .vss(vss), .vdd(vdda), .rstb(rstb), .d(vdda), .clkb(refclk_b),
     .clk(refclk_buf), .q(net012));
wphy_rpll_mvp_4g_INV_D1_GL16_LVT_Mmod_delay INV0[0:16] ( .out(rstdly[0:16]), .vdd(vdda),
     .vss(vss), .in({rsta, rstdly[0], rstdly[1], rstdly[2], rstdly[3],
     rstdly[4], rstdly[5], rstdly[6], rstdly[7], rstdly[8], rstdly[9],
     rstdly[10], rstdly[11], rstdly[12], rstdly[13], rstdly[14],
     rstdly[15]}), .tiehi(vdda), .tielo(vss));
wphy_rpll_mvp_4g_NOR2_D1_GL16_LVT NOR1 ( .tielo(vss), .tiehi(vdda), .vdd(vdda),
     .y(rstb), .vss(vss), .b(reset), .a(rstdly[16]));
/*REMOVED VIA SCRIPT -- wphy_rpll_mvp_4g_DUM_D1_GL16_LVT DUM0[0:87] ( .vdd(vdda), .vss(vss), .tiehi(vdda),
     .tielo(vss));*/
wphy_rpll_mvp_4g_MUXT2_D2_GL16_LVT MUX0 ( .vdd(vdda), .vss(vss), .sb(s0b), .s(s0),
     .b(refclk), .a(fbclk), .yb(net013));
wphy_rpll_mvp_4g_MUXT2_D2_GL16_LVT MUX1 ( .vdd(vdda), .vss(vss), .sb(s1b), .s(s1),
     .b(fbclk), .a(refclk), .yb(net014));

endmodule
// Library - wavshared_gf12lp_dig_lib, Cell - SE2DIHS_D2_GL16_RVT, View
//- schematic
// LAST TIME SAVED: Dec 29 08:37:38 2020
// NETLIST TIME: Jan  5 13:28:18 2021
`timescale 1ns / 1ns 

module wphy_rpll_mvp_4g_SE2DIHS_D2_GL16_RVT ( 
output wire logic   outn, 
output wire logic   outp, 
inout wire logic   vdd, 
inout wire logic   vss, 
input wire logic   in, 
input wire logic   tiehi, 
input wire logic   tielo );


wire logic p1 ;

wire logic n1 ;

wire logic inb ;



/*REMOVED VIA SCRIPT -- wphy_rpll_mvp_4g_DUM_D1_GL16_RVT DUM0[1:0] ( .vdd(vdd), .vss(vss), .tiehi(tiehi),
     .tielo(tielo));*/
wphy_rpll_mvp_4g_INV_D2_GL16_RVT INV4[1:0] ( .out(outn), .vdd(vdd), .vss(vss), .in(p1));
wphy_rpll_mvp_4g_INV_D2_GL16_RVT INV6 ( .in(inb), .vss(vss), .out(p1), .vdd(vdd));
wphy_rpll_mvp_4g_INV_D2_GL16_RVT INV8 ( .in(in), .vss(vss), .out(inb), .vdd(vdd));
wphy_rpll_mvp_4g_INV_D2_GL16_RVT INV7 ( .in(in), .vss(vss), .out(inb), .vdd(vdd));
wphy_rpll_mvp_4g_INV_D2_GL16_RVT INV5[1:0] ( .out(outp), .vdd(vdd), .vss(vss), .in(n1));
wphy_rpll_mvp_4g_PU_D1_GL16_RVT PU0 ( .vdd(vdd), .en(tiehi), .y(inb));
wphy_rpll_mvp_4g_PU_D1_GL16_RVT PU1 ( .vdd(vdd), .en(tiehi), .y(n1));
wphy_rpll_mvp_4g_XG_D1_GL16_RVT XGATE0[4:0] ( .y(n1), .vdd(vdd), .vss(vss), .a(inb),
     .en(tiehi), .enb(tielo));
wphy_rpll_mvp_4g_INV_D1_GL16_RVT_Mmod_nomodel INV10 ( .tiehi(tiehi), .tielo(tielo),
     .in(outp), .vss(vss), .out(outn), .vdd(vdd));
wphy_rpll_mvp_4g_INV_D1_GL16_RVT_Mmod_nomodel INV3 ( .tiehi(tiehi), .tielo(tielo),
     .in(n1), .vss(vss), .out(p1), .vdd(vdd));
wphy_rpll_mvp_4g_INV_D1_GL16_RVT_Mmod_nomodel INV2 ( .tiehi(tiehi), .tielo(tielo),
     .in(p1), .vss(vss), .out(n1), .vdd(vdd));
wphy_rpll_mvp_4g_INV_D1_GL16_RVT_Mmod_nomodel INV9 ( .tiehi(tiehi), .tielo(tielo),
     .in(outn), .vss(vss), .out(outp), .vdd(vdd));
wphy_rpll_mvp_4g_PD_D1_GL16_RVT PD0 ( .vss(vss), .enb(tielo), .y(inb));
wphy_rpll_mvp_4g_PD_D1_GL16_RVT PD1 ( .vss(vss), .enb(tielo), .y(n1));

endmodule
// Library - gf12lp_rpll_lib, Cell - wphy_rpll_div2_iq_v3, View -
//schematic
// LAST TIME SAVED: Oct 19 16:24:30 2020
// NETLIST TIME: Jan  5 13:28:18 2021
`timescale 1ns / 1ns 

module wphy_rpll_mvp_4g_wphy_rpll_div2_iq_v3 ( 
output wire logic   o_clk0, 
output wire logic   o_clk90, 
inout wire logic   vdd, 
inout wire logic   vss, 
input wire logic   ena, 
input wire logic   i_clk );


wire logic clkn ;

wire logic clkp ;

wire logic net07 ;

wire logic net015 ;

wire logic net011 ;



wphy_rpll_mvp_4g_INV_D2_GL16_RVT INV1 ( .in(net07), .vss(vss), .out(o_clk0), .vdd(vdd));
wphy_rpll_mvp_4g_INV_D2_GL16_RVT INV0 ( .in(net015), .vss(vss), .out(o_clk90),
     .vdd(vdd));
wphy_rpll_mvp_4g_INV_D2_GL16_RVT INV6 ( .in(clkn), .vss(vss), .out(clkp), .vdd(vdd));
wphy_rpll_mvp_4g_LAT_D1_GL16_RVT LA0 ( .tielo(vss), .tiehi(vdd), .vss(vss), .vdd(vdd),
     .d(net07), .clkb(clkp), .clk(clkn), .q(net015));
wphy_rpll_mvp_4g_LAT_D1_GL16_RVT LA1 ( .tielo(vss), .tiehi(vdd), .vss(vss), .vdd(vdd),
     .d(net011), .clkb(clkn), .clk(clkp), .q(net07));
wphy_rpll_mvp_4g_NAND2_D1_GL16_RVT NAND1 ( .tielo(vss), .tiehi(vdd), .vdd(vdd),
     .y(net011), .vss(vss), .b(net015), .a(ena));
wphy_rpll_mvp_4g_NAND2_D1_GL16_RVT NAND0 ( .tielo(vss), .tiehi(vdd), .vdd(vdd),
     .y(clkn), .vss(vss), .b(i_clk), .a(ena));
/*REMOVED VIA SCRIPT -- pcapacitor  C0 ( .MINUS(vss), .PLUS(net07));*/

endmodule
// Library - gf12lp_rpll_lib, Cell - wphy_rpll_postdiv, View -
//schematic
// LAST TIME SAVED: Oct 19 16:24:40 2020
// NETLIST TIME: Jan  5 13:28:18 2021
`timescale 1ns / 1ns 

module wphy_rpll_mvp_4g_wphy_rpll_postdiv ( 
output wire logic   div2clk, 
output wire logic   div16clk, 
output wire logic   outclk0, 
output wire logic   outclk90, 
output wire logic   outclk180, 
output wire logic   outclk270, 
inout wire logic   vdda, 
inout wire logic   vss, 
input wire logic   byp_clk, 
input wire logic   byp_clk_sel, 
input wire logic   div16_ena, 
input wire logic  [1:0] post_div, 
input wire logic   vcoclk0, 
input wire logic   vcoclk90, 
input wire logic   vcoclk180, 
input wire logic   vcoclk270 );


wire logic net039 ;

wire logic net033 ;

wire logic iclk2 ;

wire logic iclk8 ;

wire logic iclk4 ;

wire logic qclk8 ;

wire logic a111 ;

wire logic qclk4 ;

wire logic qclk2 ;

wire logic qclk2b ;

wire logic iclkdivint ;

wire logic ibclkdivint ;

wire logic qclkdivint ;

wire logic qbclkdivint ;

wire logic div4_sel ;

wire logic div8_sel ;

wire logic div4_8_en ;

wire logic byp_clk_q ;

wire logic div2_selb ;

wire logic iclk2b ;

wire logic idiv4_8 ;

wire logic net034 ;

wire logic div4_8_sel ;

wire logic qdiv4_8 ;

wire logic idiv2_4_8 ;

wire logic qdiv2_4_8 ;

wire logic post_div_sel ;

wire logic mx0 ;

wire logic div1_sel ;

wire logic mx180 ;

wire logic clk0b ;

wire logic mx270 ;

wire logic mx90 ;

wire logic div16_en ;

wire logic div2_sel ;

wire logic div16_enb ;

wire logic byp_clk_i ;

wire logic b111 ;

wire logic byp_clk_ix ;

wire logic byp_clk_qx ;

wire logic byp_clk_selb ;

wire logic byp_clk_sela ;

wire logic byp_clk_int ;

// Buses in the design

wire logic [1:0]  post_divb;



wphy_rpll_mvp_4g_NAND2_D1_GL16_RVT I8 ( .tielo(vss), .tiehi(vdda), .y(div4_8_en),
     .b(div16_enb), .a(post_divb[1]), .vdd(vdda), .vss(vss));
/*REMOVED VIA SCRIPT -- wphy_rpll_mvp_4g_DUMLOAD_D1_GL16_RVT I7[0:1] ( .vdd(vdda), .vss(vss), .inn(vcoclk180),
     .inp(vcoclk180));*/
/*REMOVED VIA SCRIPT -- wphy_rpll_mvp_4g_DUMLOAD_D1_GL16_RVT I6[0:1] ( .vdd(vdda), .vss(vss), .inn(vcoclk90),
     .inp(vcoclk90));*/
/*REMOVED VIA SCRIPT -- wphy_rpll_mvp_4g_DUMLOAD_D1_GL16_RVT I5[0:1] ( .vdd(vdda), .vss(vss), .inn(vcoclk270),
     .inp(vcoclk270));*/
wphy_rpll_mvp_4g_INV_D2_GL16_RVT INV40 ( .in(div2_sel), .vss(vss), .out(div2_selb),
     .vdd(vdda));
wphy_rpll_mvp_4g_INV_D2_GL16_RVT INV39 ( .in(post_divb[1]), .vss(vss), .out(div4_8_sel),
     .vdd(vdda));
wphy_rpll_mvp_4g_INV_D2_GL16_RVT INV38 ( .in(net033), .vss(vss), .out(byp_clk_q),
     .vdd(vdda));
wphy_rpll_mvp_4g_INV_D2_GL16_RVT INV37 ( .in(net034), .vss(vss), .out(byp_clk_i),
     .vdd(vdda));
wphy_rpll_mvp_4g_INV_D2_GL16_RVT INV31 ( .in(vcoclk0), .vss(vss), .out(clk0b),
     .vdd(vdda));
wphy_rpll_mvp_4g_INV_D2_GL16_RVT INV30 ( .in(byp_clk_selb), .vss(vss),
     .out(byp_clk_sela), .vdd(vdda));
wphy_rpll_mvp_4g_INV_D2_GL16_RVT INV33 ( .in(div16_ena), .vss(vss), .out(div16_enb),
     .vdd(vdda));
wphy_rpll_mvp_4g_INV_D2_GL16_RVT INV17[2:0] ( .out(outclk0), .vdd(vdda), .vss(vss),
     .in(mx0));
wphy_rpll_mvp_4g_INV_D2_GL16_RVT INV20[2:0] ( .out(outclk270), .vdd(vdda), .vss(vss),
     .in(mx270));
wphy_rpll_mvp_4g_INV_D2_GL16_RVT INV19[2:0] ( .out(outclk180), .vdd(vdda), .vss(vss),
     .in(mx180));
wphy_rpll_mvp_4g_INV_D2_GL16_RVT INV18[2:0] ( .out(outclk90), .vdd(vdda), .vss(vss),
     .in(mx90));
wphy_rpll_mvp_4g_INV_D2_GL16_RVT INV36 ( .in(byp_clk), .vss(vss), .out(byp_clk_int),
     .vdd(vdda));
wphy_rpll_mvp_4g_INV_D2_GL16_RVT INV11[1:0] ( .out(div2clk), .vdd(vdda), .vss(vss),
     .in(iclk2b));
wphy_rpll_mvp_4g_INV_D2_GL16_RVT INV7[1:0] ( .out(post_divb[1:0]), .vdd(vdda),
     .vss(vss), .in(post_div[1:0]));
wphy_rpll_mvp_4g_INV_D2_GL16_RVT INV9 ( .vdd(vdda), .in(div1_sel), .vss(vss),
     .out(post_div_sel));
wphy_rpll_mvp_4g_INV_D2_GL16_RVT INV29 ( .in(byp_clk_sel), .vss(vss),
     .out(byp_clk_selb), .vdd(vdda));
wphy_rpll_mvp_4g_INV_D2_GL16_RVT INV34 ( .in(div16_enb), .vss(vss), .out(div16_en),
     .vdd(vdda));
wphy_rpll_mvp_4g_INV_D2_GL16_RVT INV4 ( .vdd(vdda), .in(qclk2), .vss(vss),
     .out(qclk2b));
wphy_rpll_mvp_4g_INV_D2_GL16_RVT INV35[1:0] ( .out(iclk2b), .vdd(vdda), .vss(vss),
     .in(iclk2));
wphy_rpll_mvp_4g_NOR2_D1_GL16_RVT NOR3 ( .tielo(vss), .tiehi(vdda), .vdd(vdda),
     .y(div8_sel), .vss(vss), .b(post_divb[1]), .a(post_divb[0]));
wphy_rpll_mvp_4g_NOR2_D1_GL16_RVT NOR1 ( .tielo(vss), .tiehi(vdda), .vdd(vdda),
     .y(div2_sel), .vss(vss), .b(post_div[1]), .a(post_divb[0]));
wphy_rpll_mvp_4g_NOR2_D1_GL16_RVT NOR0 ( .tielo(vss), .tiehi(vdda), .vdd(vdda),
     .y(div1_sel), .vss(vss), .b(post_div[1]), .a(post_div[0]));
wphy_rpll_mvp_4g_NOR2_D1_GL16_RVT NOR2 ( .tielo(vss), .tiehi(vdda), .vdd(vdda),
     .y(div4_sel), .vss(vss), .b(post_divb[1]), .a(post_div[0]));
wphy_rpll_mvp_4g_MUXT2_D2_GL16_RVT MUX13 ( .vss(vss), .sb(div2_sel), .s(div2_selb),
     .b(byp_clk_int), .a(byp_clk_ix), .yb(net034), .vdd(vdda));
wphy_rpll_mvp_4g_MUXT2_D2_GL16_RVT MUX12 ( .vss(vss), .sb(div2_sel), .s(div2_selb),
     .b(byp_clk_int), .a(byp_clk_qx), .yb(net033), .vdd(vdda));
wphy_rpll_mvp_4g_MUXT2_D2_GL16_RVT MUX11 ( .vss(vss), .sb(byp_clk_selb),
     .s(byp_clk_sela), .b(byp_clk_i), .a(idiv2_4_8), .yb(b111),
     .vdd(vdda));
wphy_rpll_mvp_4g_MUXT2_D2_GL16_RVT MUX10 ( .vss(vss), .sb(byp_clk_selb),
     .s(byp_clk_sela), .b(byp_clk_q), .a(qdiv2_4_8), .yb(a111),
     .vdd(vdda));
wphy_rpll_mvp_4g_MUXT2_D2_GL16_RVT MUX7[1:0] ( .yb(mx270), .vdd(vdda), .vss(vss),
     .a(qbclkdivint), .b(vcoclk270), .s(div1_sel), .sb(post_div_sel));
wphy_rpll_mvp_4g_MUXT2_D2_GL16_RVT MUX6[1:0] ( .yb(mx90), .vdd(vdda), .vss(vss),
     .a(qclkdivint), .b(vcoclk90), .s(div1_sel), .sb(post_div_sel));
wphy_rpll_mvp_4g_MUXT2_D2_GL16_RVT MUX5[1:0] ( .yb(mx180), .vdd(vdda), .vss(vss),
     .a(ibclkdivint), .b(vcoclk180), .s(div1_sel), .sb(post_div_sel));
wphy_rpll_mvp_4g_MUXT2_D2_GL16_RVT MUX4[1:0] ( .yb(mx0), .vdd(vdda), .vss(vss),
     .a(iclkdivint), .b(vcoclk0), .s(div1_sel), .sb(post_div_sel));
wphy_rpll_mvp_4g_MUXT2_D2_GL16_RVT MUX3 ( .vdd(vdda), .vss(vss), .sb(div2_sel),
     .s(div4_8_sel), .b(qdiv4_8), .a(qclk2b), .yb(qdiv2_4_8));
wphy_rpll_mvp_4g_MUXT2_D2_GL16_RVT MUX2 ( .vdd(vdda), .vss(vss), .sb(div4_sel),
     .s(div8_sel), .b(qclk8), .a(qclk4), .yb(qdiv4_8));
wphy_rpll_mvp_4g_MUXT2_D2_GL16_RVT MUX1 ( .vdd(vdda), .vss(vss), .sb(div2_sel),
     .s(div4_8_sel), .b(idiv4_8), .a(iclk2b), .yb(idiv2_4_8));
wphy_rpll_mvp_4g_MUXT2_D2_GL16_RVT MUX0 ( .vdd(vdda), .vss(vss), .sb(div4_sel),
     .s(div8_sel), .b(iclk8), .a(iclk4), .yb(idiv4_8));
wphy_rpll_mvp_4g_SE2DIHS_D2_GL16_RVT SE2DIFF1 ( .tiehi(vdda), .tielo(vss), .vdd(vdda),
     .vss(vss), .outp(qbclkdivint), .outn(qclkdivint), .in(a111));
wphy_rpll_mvp_4g_SE2DIHS_D2_GL16_RVT SE2DIFF0 ( .tiehi(vdda), .tielo(vss), .vdd(vdda),
     .vss(vss), .outp(ibclkdivint), .outn(iclkdivint), .in(b111));
wphy_rpll_mvp_4g_PU_D1_GL16_RVT PU6[1:0] ( .vdd(vdda), .en(post_div_sel),
     .y(idiv2_4_8));
wphy_rpll_mvp_4g_PU_D1_GL16_RVT PU4[1:0] ( .vdd(vdda), .en(div4_8_sel), .y(qdiv4_8));
wphy_rpll_mvp_4g_PU_D1_GL16_RVT PU5[1:0] ( .vdd(vdda), .en(post_div_sel),
     .y(qdiv2_4_8));
wphy_rpll_mvp_4g_PU_D1_GL16_RVT PU0[1:0] ( .vdd(vdda), .en(div4_8_sel), .y(idiv4_8));
wphy_rpll_mvp_4g_wphy_rpll_div2_iq_v3 DIV2IQ3 ( .ena(byp_clk_sela), .vdd(vdda),
     .o_clk0(byp_clk_ix), .i_clk(byp_clk_int), .o_clk90(byp_clk_qx),
     .vss(vss));
wphy_rpll_mvp_4g_wphy_rpll_div2_iq_v3 DIV2IQ4 ( .ena(div16_en), .vdd(vdda),
     .o_clk0(div16clk), .i_clk(iclk8), .o_clk90(net039), .vss(vss));
wphy_rpll_mvp_4g_wphy_rpll_div2_iq_v3 DIV2IQ2 ( .ena(div4_8_en), .vdd(vdda),
     .o_clk0(iclk8), .i_clk(iclk4), .o_clk90(qclk8), .vss(vss));
wphy_rpll_mvp_4g_wphy_rpll_div2_iq_v3 DIV2IQ0 ( .ena(vdda), .vdd(vdda), .o_clk0(iclk2),
     .i_clk(clk0b), .o_clk90(qclk2), .vss(vss));
wphy_rpll_mvp_4g_wphy_rpll_div2_iq_v3 DIV2IQ1 ( .ena(div4_8_en), .vdd(vdda),
     .o_clk0(iclk4), .i_clk(iclk2), .o_clk90(qclk4), .vss(vss));

endmodule
// Library - gf12lp_rpll_lib, Cell - mvp_pll_mux4, View - schematic
// LAST TIME SAVED: Oct 13 06:39:45 2020
// NETLIST TIME: Jan  5 13:28:18 2021
`timescale 1ns / 1ns 

module wphy_rpll_mvp_4g_mvp_pll_mux4 ( 
output wire logic   out, 
inout wire logic   vdd, 
inout wire logic   vss, 
input wire logic   in0, 
input wire logic   in1, 
input wire logic   in2, 
input wire logic   in3, 
input wire logic  [1:0] sel );


wire logic sel2 ;

wire logic sel0b ;

wire logic sel0 ;

wire logic sel1b ;

wire logic sel1 ;

wire logic sel2b ;

wire logic sel3 ;

wire logic sel3b ;

// Buses in the design

wire logic [1:0]  selb;



wphy_rpll_mvp_4g_NAND2_D1_GL16_LVT NAND3 ( .tielo(vss), .tiehi(vdd), .vdd(vdd),
     .y(sel3b), .vss(vss), .b(sel[1]), .a(sel[0]));
wphy_rpll_mvp_4g_NAND2_D1_GL16_LVT NAND2 ( .tielo(vss), .tiehi(vdd), .vdd(vdd),
     .y(sel2b), .vss(vss), .b(sel[1]), .a(selb[0]));
wphy_rpll_mvp_4g_NAND2_D1_GL16_LVT NAND1 ( .tielo(vss), .tiehi(vdd), .vdd(vdd),
     .y(sel1b), .vss(vss), .b(selb[1]), .a(sel[0]));
wphy_rpll_mvp_4g_NAND2_D1_GL16_LVT NAND0 ( .tielo(vss), .tiehi(vdd), .vdd(vdd),
     .y(sel0b), .vss(vss), .b(selb[1]), .a(selb[0]));
wphy_rpll_mvp_4g_INV_D1_GL16_LVT I4 ( .tielo(vss), .tiehi(vdd), .in(sel3b), .vss(vss),
     .out(sel3), .vdd(vdd));
wphy_rpll_mvp_4g_INV_D1_GL16_LVT I3 ( .tielo(vss), .tiehi(vdd), .in(sel2b), .vss(vss),
     .out(sel2), .vdd(vdd));
wphy_rpll_mvp_4g_INV_D1_GL16_LVT I2 ( .tielo(vss), .tiehi(vdd), .in(sel1b), .vss(vss),
     .out(sel1), .vdd(vdd));
wphy_rpll_mvp_4g_INV_D1_GL16_LVT I0[1:0] ( .out(selb[1:0]), .vdd(vdd), .vss(vss),
     .in(sel[1:0]), .tiehi(vdd), .tielo(vss));
wphy_rpll_mvp_4g_INV_D1_GL16_LVT I1 ( .tielo(vss), .tiehi(vdd), .in(sel0b), .vss(vss),
     .out(sel0), .vdd(vdd));
wphy_rpll_mvp_4g_XG_D1_GL16_LVT XGATE4 ( .y(out), .a(in3), .en(sel3), .enb(sel3b),
     .vdd(vdd), .vss(vss));
wphy_rpll_mvp_4g_XG_D1_GL16_LVT XGATE3 ( .y(out), .a(in0), .en(sel0), .enb(sel0b),
     .vdd(vdd), .vss(vss));
wphy_rpll_mvp_4g_XG_D1_GL16_LVT XGATE2 ( .y(out), .a(in2), .en(sel2), .enb(sel2b),
     .vdd(vdd), .vss(vss));
wphy_rpll_mvp_4g_XG_D1_GL16_LVT XGATE0 ( .y(out), .a(in1), .en(sel1), .enb(sel1b),
     .vdd(vdd), .vss(vss));

endmodule
// Library - gf12lp_rpll_lib, Cell - wphy_rpll_mvp_4g, View - schematic
// LAST TIME SAVED: Jan  4 12:57:03 2021
// NETLIST TIME: Jan  5 13:28:18 2021
`timescale 1ns / 1ns 

`endif //SYNTHESIS 
module wphy_rpll_mvp_4g ( 
output wire logic   fbclk, 
output wire logic   refclk_out, 
output wire logic   vco0_clk, 
output wire logic   vco0_div2_clk, 
output wire logic   vco1_clk0, 
output wire logic   vco1_clk90, 
output wire logic   vco1_clk180, 
output wire logic   vco1_clk270, 
output wire logic   vco1_div2_clk, 
output wire logic   vco1_div16_clk, 
output wire logic   vco2_clk0, 
output wire logic   vco2_clk90, 
output wire logic   vco2_clk180, 
output wire logic   vco2_clk270, 
output wire logic   vco2_div2_clk, 
output wire logic   vco2_div16_clk, 
`ifdef WLOGIC_NO_PG
`else
inout wire logic   vdda, 
inout wire logic   vss, 
`endif //WLOGIC_NO_PG
input  [3:0] bias_lvl, 
input wire logic   cp_int_mode, 
input wire logic   div16_ena, 
input wire logic   ena, 
input wire logic  [8:0] fbdiv_sel, 
input wire logic  [4:0] int_ctrl, 
input wire logic  [1:0] pfd_mode, 
input wire logic  [1:0] prop_c_ctrl, 
input wire logic  [4:0] prop_ctrl, 
input wire logic  [1:0] prop_r_ctrl, 
input wire logic   refclk, 
input wire logic   refclk_alt, 
input wire logic   reset, 
input wire logic   sel_refclk_alt, 
input wire logic  [5:0] vco0_band, 
input wire logic   vco0_byp_clk_sel, 
input wire logic   vco0_ena, 
input wire logic  [5:0] vco0_fine, 
input wire logic  [5:0] vco1_band, 
input wire logic   vco1_byp_clk_sel, 
input wire logic   vco1_ena, 
input wire logic  [5:0] vco1_fine, 
input wire logic  [1:0] vco1_post_div, 
input wire logic  [5:0] vco2_band, 
input wire logic   vco2_byp_clk_sel, 
input wire logic   vco2_ena, 
input wire logic  [5:0] vco2_fine, 
input wire logic  [1:0] vco2_post_div, 
input wire logic  [1:0] vco_sel );


`ifdef WLOGIC_NO_PG
wire vdda;
assign vdda=1'b1;
wire vss;
assign vss=1'b0;
`else
`endif //WLOGIC_NO_PG

`ifdef SYNTHESIS 
`else

wire logic dn ;

wire logic dnb ;

var real dnbprop ;

wire logic vdbl ;

var real upint ;

var real upbint ;

var real dnint ;

var real dnbint ;

var real dnprop ;

var real iprop ;

wire logic refck1 ;

wire logic up ;

wire logic vco1_out_clk90 ;

wire logic vco1_out_clk180 ;

wire logic vco1_out_clk270 ;

wire logic nbias_cp ;

var real vint ;

var real upbprop ;

var real upprop ;

wire logic refclk_int ;

wire logic fbclk_int ;

wire logic refclk_alt_sel ;

wire logic vco0_out_clk0 ;

wire logic net046 ;

var real vco2_vring ;

wire logic vco2_out_clk270 ;

wire logic vco2_out_clk90 ;

wire logic vco2_out_clk180 ;

wire logic vco2_out_clk0 ;

wire logic net061 ;

wire logic refclk_alt_selb ;

wire logic vco1_out_clk0 ;

var real vco1_vring ;

wire logic net042 ;

wire logic upb ;

var real net064 ;

var real vco0_vring ;

// Buses in the design

wire logic [1:0]  vco_selb;

wire logic [1:0]  vco_sela;



wphy_rpll_mvp_4g_mvp_vco_400MHz_top IVCO0 ( .clk(vco0_out_clk0), .refclk(refclk_int),
     .course(vco0_band[5:0]), .fine(vco0_fine[5:0]), .en(vco0_ena),
     .vring(vco0_vring), .vgate(vint), .vdda(vdda), .vss(vss));
wphy_rpll_mvp_4g_MUXT2_D2_GL16_RVT MUX0 ( .vss(vss), .sb(refclk_alt_selb),
     .s(refclk_alt_sel), .b(refclk_alt), .a(refclk), .yb(net042),
     .vdd(vdda));
wphy_rpll_mvp_4g_INV_D2_GL16_RVT INV7[1:0] ( .out(vco_selb[1:0]), .vdd(vdda), .vss(vss),
     .in(vco_sel[1:0]));
wphy_rpll_mvp_4g_INV_D2_GL16_RVT INV8[1:0] ( .out(vco_sela[1:0]), .vdd(vdda), .vss(vss),
     .in(vco_selb[1:0]));
wphy_rpll_mvp_4g_INV_D2_GL16_RVT INV1 ( .in(fbclk_int), .vss(vss), .out(fbclk),
     .vdd(vdda));
wphy_rpll_mvp_4g_INV_D2_GL16_RVT INV9 ( .in(net046), .vss(vss), .out(net061),
     .vdd(vdda));
wphy_rpll_mvp_4g_INV_D2_GL16_RVT INV2 ( .in(sel_refclk_alt), .vss(vss),
     .out(refclk_alt_selb), .vdd(vdda));
wphy_rpll_mvp_4g_INV_D2_GL16_RVT INV4 ( .in(refclk_alt_selb), .vss(vss),
     .out(refclk_alt_sel), .vdd(vdda));
wphy_rpll_mvp_4g_INV_D2_GL16_RVT INV0 ( .in(refclk_int), .vss(vss), .out(refclk_out),
     .vdd(vdda));
wphy_rpll_mvp_4g_rpll_14g_dbl IDBL ( .clksel(vss), .vdbl(vdbl), .divclk(refclk_int),
     .en(ena), .refclk(refclk_int), .vdda(vdda), .vss(vss));
wphy_rpll_mvp_4g_mvp_vco_4GHz_top IVCO2 ( .refclk(refclk_int), .course(vco2_band[5:0]),
     .fine(vco2_fine[5:0]), .vring(vco2_vring), .clk0(vco2_out_clk0),
     .clk90(vco2_out_clk90), .clk180(vco2_out_clk180),
     .clk270(vco2_out_clk270), .en(vco2_ena), .vgate(vint),
     .vdda(vdda), .vss(vss));
wphy_rpll_mvp_4g_mvp_vco_4GHz_top IVCO1 ( .refclk(refclk_int), .course(vco1_band[5:0]),
     .fine(vco1_fine[5:0]), .vring(vco1_vring), .clk0(vco1_out_clk0),
     .clk90(vco1_out_clk90), .clk180(vco1_out_clk180),
     .clk270(vco1_out_clk270), .en(vco1_ena), .vgate(vint),
     .vdda(vdda), .vss(vss));
wphy_rpll_mvp_4g_mvp_pll_demux4 VRING_DEMUX ( .in(iprop), .sel(vco_sela[1:0]),
     .out0(vco0_vring), .out1(vco1_vring), .out2(vco2_vring),
     .out3(net064), .vss(vss), .vdd(vdda));
wphy_rpll_mvp_4g_INV_D4_GL16_RVT INV3[1:0] ( .out(refclk_int), .vdd(vdda), .vss(vss),
     .in(refck1));
wphy_rpll_mvp_4g_INV_D4_GL16_RVT INV5 ( .in(net042), .vss(vss), .out(refck1),
     .vdd(vdda));
wphy_rpll_mvp_4g_wphy_rpll_postdiv_se IPOSTDIV0 ( .outclk(vco0_clk),
     .div2clk(vco0_div2_clk), .byp_clk_sel(vco0_byp_clk_sel),
     .vdda(vdda), .vcoclk(vco0_out_clk0), .byp_clk(refclk_int),
     .vss(vss));
wphy_rpll_mvp_4g_rpll_14g_chp CP ( .int_ctrl(int_ctrl[4:0]), .iupb_prop(upbprop),
     .vdda(vdda), .mode(cp_int_mode), .idn_prop(dnprop),
     .idnb_prop(dnbprop), .iup_prop(upprop), .vss(vss),
     .idn_int(dnint), .idnb_int(dnbint), .nbias(nbias_cp),
     .iup_int(upint), .iupb_int(upbint), .dn(dn), .dnb(dnb), .up(up),
     .upb(upb));
wphy_rpll_mvp_4g_rpll_bias IBIAS ( .bias_lvl(bias_lvl[3:0]), .vdda(vdda),
     .nbias_cp(nbias_cp), .en(ena), .vss(vss));
wphy_rpll_mvp_4g_mvp_rpll_filter IFILTER ( .prop_ctrl(prop_ctrl[4:0]), .vint(vint),
     .iprop(iprop), .en(ena), .c_ctrl(prop_c_ctrl[1:0]), .vdda(vdda),
     .idn_prop(dnprop), .idnb_prop(dnbprop), .r_ctrl(prop_r_ctrl[1:0]),
     .vdbl(vdbl), .vss(vss), .iupb_prop(upbprop), .iupb_int(upbint),
     .iup_int(upint), .idnb_int(dnbint), .iup_prop(upprop),
     .idn_int(dnint));
wphy_rpll_mvp_4g_rpll_14g_fbdiv IFBDIV ( .clkdiv_out(fbclk_int), .div(fbdiv_sel[8:0]),
     .reset(reset), .clkin(net061), .vdda(vdda), .vss(vss));
wphy_rpll_mvp_4g_rpll_pfd IPFD ( .reset(reset), .dn(dn), .dnb(dnb), .up(up), .upb(upb),
     .fbclk(fbclk_int), .mode(pfd_mode[1:0]), .refclk(refclk_int),
     .vdda(vdda), .vss(vss));
wphy_rpll_mvp_4g_wphy_rpll_postdiv IPOSTDIV2 ( .div16clk(vco2_div16_clk),
     .div16_ena(div16_ena), .div2clk(vco2_div2_clk),
     .byp_clk_sel(vco2_byp_clk_sel), .vdda(vdda), .outclk0(vco2_clk0),
     .outclk90(vco2_clk90), .outclk180(vco2_clk180),
     .outclk270(vco2_clk270), .post_div(vco2_post_div[1:0]),
     .byp_clk(refclk_int), .vcoclk0(vco2_out_clk0),
     .vcoclk90(vco2_out_clk90), .vcoclk180(vco2_out_clk180),
     .vcoclk270(vco2_out_clk270), .vss(vss));
wphy_rpll_mvp_4g_wphy_rpll_postdiv IPOSTDIV1 ( .div16clk(vco1_div16_clk),
     .div16_ena(div16_ena), .div2clk(vco1_div2_clk),
     .byp_clk_sel(vco1_byp_clk_sel), .vdda(vdda), .outclk0(vco1_clk0),
     .outclk90(vco1_clk90), .outclk180(vco1_clk180),
     .outclk270(vco1_clk270), .post_div(vco1_post_div[1:0]),
     .byp_clk(refclk_int), .vcoclk0(vco1_out_clk0),
     .vcoclk90(vco1_out_clk90), .vcoclk180(vco1_out_clk180),
     .vcoclk270(vco1_out_clk270), .vss(vss));
wphy_rpll_mvp_4g_mvp_pll_mux4 FBCLK_MUX ( .sel(vco_sela[1:0]), .out(net046),
     .in0(vco0_clk), .in1(vco1_out_clk0), .in2(vco2_out_clk0),
     .in3(vss), .vss(vss), .vdd(vdda));

`endif //SYNTHESIS 
endmodule
`ifdef SYNTHESIS
`else

/* This alias module is for use internal to the netlister only.
 Please
      do not use the same name for modules or
 assume the existence of 
     this module. */

module wphy_rpll_mvp_4g_cds_alias( cds_alias_sig, cds_alias_sig);

parameter width = 1;

     input [width:1] cds_alias_sig;

endmodule
`endif //SYNTHESIS
