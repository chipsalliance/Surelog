`timescale 1 ns / 100 ps
`suppress_faults
`enable_portfaults
module GND(Y);
    
    output Y;
    supply0 Y;
               
    specify

         specparam   LibName     = "act2";
         specparam   OutputLoad$Y = 0;

    endspecify


endmodule
`disable_portfaults
`nosuppress_faults

`suppress_faults
`enable_portfaults
`timescale 1 ns / 100 ps
module OUTBUF(D, PAD);
    
    input D;
    output PAD;
    
    buf  BF1  (PAD, D);
    
    specify

         specparam   LibName     = "act2";
         specparam   InputLoad$D = 0; 
         specparam   OutputLoad$PAD = 0;
         specparam   MacroType = "io";




        (D => PAD) = (1.0:1.0:1.0, 1.0:1.0:1.0);

    endspecify

endmodule
`endcelldefine
`disable_portfaults
`nosuppress_faults

`suppress_faults
`enable_portfaults
`timescale 1 ns / 100 ps
module VCC(Y);
    
    output Y;
    supply1 Y;
               
    specify

         specparam   LibName     = "act2";
         specparam   OutputLoad$Y = 0;

    endspecify


endmodule
`endcelldefine
`disable_portfaults
`nosuppress_faults

`suppress_faults
`enable_portfaults

primitive U_MUX_2 (Q, A, B, SL);
    output Q;
    input A, B, SL;

// FUNCTION :  TWO TO ONE MULTIPLEXER

    table
    //  A   B   SL  :   Q
        0   0   ?   :   0 ;
        1   1   ?   :   1 ;

        0   ?   0   :   0 ;
        1   ?   0   :   1 ;

        ?   0   1   :   0 ;
        ?   1   1   :   1 ;

    endtable
endprimitive    
`disable_portfaults
`nosuppress_faults

`suppress_faults
`enable_portfaults
`timescale 1 ns / 100 ps
module xCM8(D0, D1, D2, D3, S00, S01, S10, S11, Y);
    
    input D0, D1, D2, D3, S00, S01, S10, S11;
    output Y;
    
       
    and      and1 (Y1, S00, S01); 
    or       or1  (Y2, S10, S11);
    U_MUX_2  mux1 (T1, D0, D1, Y1);
    U_MUX_2  mux2 (T2, D2, D3, Y1);
    U_MUX_2  mux3 (Y, T1, T2, Y2);


    specify

         specparam   LibName     = "act2";
         specparam   InputLoad$D0 = 1; 
         specparam   InputLoad$D1 = 1; 
         specparam   InputLoad$D2 = 1; 
         specparam   InputLoad$D3 = 2; 
         specparam   InputLoad$S00 = 1; 
         specparam   InputLoad$S01 = 1; 
         specparam   InputLoad$S10 = 1; 
         specparam   InputLoad$S11 = 2; 
         specparam   OutputLoad$Y = 0;

         specparam   MacroType = "slm";



         ( D0 => Y ) = ( 1.0:1.0:1.0, 1.0:1.0:1.0 );
         ( D1 => Y ) = ( 1.0:1.0:1.0, 1.0:1.0:1.0 );
         ( D2 => Y ) = ( 1.0:1.0:1.0, 1.0:1.0:1.0 );
         ( D3 => Y ) = ( 1.0:1.0:1.0, 1.0:1.0:1.0 );

         ( S00 => Y ) = ( 1.0:1.0:1.0, 1.0:1.0:1.0 );
         ( S01 => Y ) = ( 1.0:1.0:1.0, 1.0:1.0:1.0 );
         ( S10 => Y ) = ( 1.0:1.0:1.0, 1.0:1.0:1.0 );
         ( S11 => Y ) = ( 1.0:1.0:1.0, 1.0:1.0:1.0 );

    endspecify


endmodule
`endcelldefine
`disable_portfaults
`nosuppress_faults

`suppress_faults
`enable_portfaults
`timescale 1 ns / 100 ps
module INBUF(PAD, Y);
    
    input PAD;
    output Y;
    
    buf  BF1  (Y, PAD);
    
    specify

         specparam   LibName     = "act2";
         specparam   InputLoad$PAD = 0; 
         specparam   OutputLoad$Y = 0;
         specparam   MacroType = "io";




        (PAD => Y) = (1.0:1.0:1.0, 1.0:1.0:1.0);

    endspecify

endmodule
`endcelldefine
`disable_portfaults
`nosuppress_faults

`suppress_faults
`enable_portfaults
`celldefine
`delay_mode_path
`timescale 1 ns / 100 ps
module DFM7A ( D0, D1, D2, D3, S0, S10, S11, CLK, CLR, Q);
    
    input    D0, D1, D2, D3, S0, S10, S11, CLR, CLK;
    output   Q;
    
    reg NOTIFY_REG;
    
    
        or 	OR1_inst ( S1, S10, S11);
	U_MUX_4 inst2 ( D_EFF, D0, D1, D2, D3, S0, S1);

	UFPRB  	inst3 (Q, D_EFF, CLK, CLR, NOTIFY_REG);
      
      or     OR1   (ORs10s11, S10, S11);
      not    NT1   (S0_, S0);
      not    NT2   (ORs10s11_, ORs10s11);
      and    AN1   (EN_D0, CLR, S0_, ORs10s11_);
      and    AN2   (EN_D1, CLR, S0, ORs10s11_);
      and    AN3   (EN_D2, CLR, S0_, ORs10s11);
      and    AN4   (EN_D3, CLR, S0, ORs10s11);
      not    NT3   (S10_, S10);
      not    NT4   (S11_, S11);
      xor    XN1   (X1, D0, D2);
      xor    XN2   (X2, D1, D3);
      xor    XN3   (X3, D0, D1);
      xor    XN4   (X4, D2, D3);
      and    AN5   (EN1_S0, X3, ORs10s11_, CLR);
      and    AN6   (EN2_S0, X4, ORs10s11, CLR);
      and    AN7   (EN1_S10, X1, S0_, S11_, CLR);
      and    AN8   (EN2_S10, X2, S0, S11_, CLR);
      and    AN9   (EN1_S11, X1, S0_, S10_, CLR);
      and    AN10  (EN2_S11, X2, S0, S10_, CLR);
      or     OR2   (EN_S0, EN1_S0, EN2_S0);
      or     OR3   (EN_S10, EN1_S10, EN2_S10);
      or     OR4   (EN_S11, EN1_S11, EN2_S11);

    specify

         specparam   LibName     = "act2";
         specparam   InputLoad$D0 = 1; 
         specparam   InputLoad$D1 = 1; 
         specparam   InputLoad$D2 = 1; 
         specparam   InputLoad$D3 = 1; 
         specparam   InputLoad$S0 = 1; 
         specparam   InputLoad$S10 = 1; 
         specparam   InputLoad$S11 = 1; 
         specparam   InputLoad$CLR = 1; 
         specparam   InputLoad$CLK = 1; 
         specparam   OutputLoad$Q = 0;

         specparam   EdgeType       = "pos";
         specparam   MacroType      = "seq";
         specparam   SeqType        = "flipflop";
         specparam   FlipFlopType   = "seq";     


      
          if (!S0 && !(S10 || S11) &&  CLR)
            (posedge CLK =>  (Q +: D0))  = (1.0:1.0:1.0, 1.0:1.0:1.0);  
          if (S0 && !(S10 || S11) &&  CLR)
            (posedge CLK =>  (Q +: D1))  = (1.0:1.0:1.0, 1.0:1.0:1.0);  
          if (!S0 && (S10 || S11) &&  CLR)
            (posedge CLK =>  (Q +: D2))  = (1.0:1.0:1.0, 1.0:1.0:1.0);  
          if (S0 && (S10 || S11) &&  CLR)
            (posedge CLK =>  (Q +: D3))  = (1.0:1.0:1.0, 1.0:1.0:1.0);  
            
          (negedge CLR => (Q +: 1'b0))   = (1.0:1.0:1.0, 1.0:1.0:1.0);  

      
      $setup(D0, posedge CLK &&& EN_D0, 0.0, NOTIFY_REG);
      $hold(posedge CLK, D0 &&& EN_D0, 0.0, NOTIFY_REG);
      $setup(D1, posedge CLK &&& EN_D1, 0.0, NOTIFY_REG);
      $hold(posedge CLK, D1 &&& EN_D1, 0.0, NOTIFY_REG);
      $setup(D2, posedge CLK &&& EN_D2, 0.0, NOTIFY_REG);
      $hold(posedge CLK, D2 &&& EN_D2, 0.0, NOTIFY_REG);
      $setup(D3, posedge CLK &&& EN_D3, 0.0, NOTIFY_REG);
      $hold(posedge CLK, D3 &&& EN_D3, 0.0, NOTIFY_REG);
  
      $setup(S0, posedge CLK &&& EN_S0, 0.0, NOTIFY_REG);
      $hold(posedge CLK, S0 &&& EN_S0, 0.0, NOTIFY_REG);
      $setup(S10, posedge CLK &&& EN_S10, 0.0, NOTIFY_REG);
      $hold(posedge CLK, S10 &&& EN_S10, 0.0, NOTIFY_REG);
      $setup(S11, posedge CLK &&& EN_S11, 0.0, NOTIFY_REG);
      $hold(posedge CLK, S11 &&& EN_S11, 0.0, NOTIFY_REG);

      $hold(posedge CLK, posedge CLR, 0.0, NOTIFY_REG);
 
      $width(negedge CLR, 0.0, 0, NOTIFY_REG);
      $width(posedge CLK &&& CLR, 0.0, 0, NOTIFY_REG);
      $width(negedge CLK &&& CLR, 0.0, 0, NOTIFY_REG);
      
      $recovery(posedge CLR, posedge CLK, 0.0, NOTIFY_REG);

    endspecify


endmodule
`endcelldefine
`disable_portfaults
`nosuppress_faults

`suppress_faults
`enable_portfaults
`celldefine
`delay_mode_path
primitive U_MUX_4 (Y, D0, D1, D2, D3, S0, S1);

    input D0, D1, D2, D3, S0, S1;
    output Y;
   
// FUNCTION :  FOUR TO ONE MULTIPLEXER WITH 2 SELECT CONTROLS

    table

//   D0  D1  D2 D3  S0  S1 : Y
                       
     0   ?   ?  ?    0  0  : 0 ; 
     1   ?   ?  ?    0  0  : 1 ; 
                                 
     ?   0   ?  ?    1  0  : 0 ; 
     ?   1   ?  ?    1  0  : 1 ; 
                                 
     ?   ?   0  ?    0  1  : 0 ; 
     ?   ?   1  ?    0  1  : 1 ; 
                                 
     ?   ?   ?  0    1  1  : 0 ; 
     ?   ?   ?  1    1  1  : 1 ; 
                                 
                                 
     0   0   0   0   ?  ?  : 0 ; 
                       
     1   1   1   1   ?  ?  : 1 ; 

     0   0   ?   ?   ?  0  : 0 ;    
     1   1   ?   ?   ?  0  : 1 ; 

     ?   ?   0   0   ?  1  : 0 ; 
     ?   ?   1   1   ?  1  : 1 ; 

     0   ?   0   ?   0  ?  : 0 ; 
     1   ?   1   ?   0  ?  : 1 ; 

     ?   0   ?   0   1  ?  : 0 ; 
     ?   1   ?   1   1  ?  : 1 ; 
                 
     endtable
endprimitive
`disable_portfaults
`nosuppress_faults

`suppress_faults
`enable_portfaults
primitive UFPRB (Q, D, CP, RB, NOTIFIER_REG); 

    output Q;  
    input  NOTIFIER_REG,
           D, CP, RB;
    reg    Q; 
    
// FUNCTION : POSITIVE EDGE TRIGGERED D FLIP-FLOP WITH ACTIVE LOW
//            ASYNCHRONOUS CLEAR ( Q OUTPUT UDP ).


    table
 
    //  D   CP      RB     NOTIFIER_REG  :   Qt  :   Qt+1

        1   (01)    1         ?          :   ?   :   1;  // clocked data
        0   (01)    1         ?          :   ?   :   0;

        0   (01)    x         ?          :   ?   :   0;  // pessimism
        0    ?      x         ?          :   0   :   0;  // pessimism

        1    0      x         ?          :   0   :   0;  // pessimism
        1    x    (?x)        ?          :   0   :   0;  // pessimism
        1    1    (?x)        ?          :   0   :   0;  // pessimism

        x    0      x         ?          :   0   :   0;  // pessimism
        x    x    (?x)        ?          :   0   :   0;  // pessimism
        x    1    (?x)        ?          :   0   :   0;  // pessimism

        1   (x1)    1         ?          :   1   :   1;  // reducing pessimism
        0   (x1)    1         ?          :   0   :   0;                          
        1   (0x)    1         ?          :   1   :   1;  
        0   (0x)    1         ?          :   0   :   0;  


        ?   ?       0         ?          :   ?   :   0;  // asynchronous clear

        ?   (?0)    ?         ?          :   ?   :   -;  // ignore falling clock
        ?   (1x)    ?         ?          :   ?   :   -;  // ignore falling clock
        *    ?      ?         ?          :   ?   :   -;  // ignore the edges on data

        ?    ?    (?1)        ?          :   ?   :   -;  // ignore the edges on clear 

        ?    ?      ?         *          :   ?   :   x;
 
    endtable
endprimitive
`disable_portfaults
`nosuppress_faults

// Schematic name: CM8
`timescale 1ns /100ps
module CM8(D, S, Y);
input [3:0]D;
input [3:0]S;
output Y;
wire [3:0]D;
wire [3:0]S;
wire T1;
wire T2;
wire Y;
wire Y1;
wire Y2;
and21 Iand1 (.A(S[0]), .B(S[1]), .Y(Y1));
U_MUX_2 imux1 (T1, D[0], D[1], Y1);
U_MUX_2 imux2 (T2, D[2], D[3], Y1);
U_MUX_2 imux3 (Y, T1, T2, Y2);
or21 Ior1 (.A(S[2]), .B(S[3]), .Y(Y2));
specify
         specparam   LibName     = "act2";
         specparam   InputLoad$D0 = 1; 
         specparam   InputLoad$D1 = 1; 
         specparam   InputLoad$D2 = 1; 
         specparam   InputLoad$D3 = 2; 
         specparam   InputLoad$S00 = 1; 
         specparam   InputLoad$S01 = 1; 
         specparam   InputLoad$S10 = 1; 
         specparam   InputLoad$S11 = 2; 
         specparam   OutputLoad$Y = 0;
         specparam   MacroType = "slm";
         ( D[0] => Y ) = ( 1.0:1.0:1.0, 1.0:1.0:1.0 );
         ( D[1] => Y ) = ( 1.0:1.0:1.0, 1.0:1.0:1.0 );
         ( D[2] => Y ) = ( 1.0:1.0:1.0, 1.0:1.0:1.0 );
         ( D[3] => Y ) = ( 1.0:1.0:1.0, 1.0:1.0:1.0 );
         ( S[0] => Y ) = ( 1.0:1.0:1.0, 1.0:1.0:1.0 );
         ( S[1] => Y ) = ( 1.0:1.0:1.0, 1.0:1.0:1.0 );
         ( S[2] => Y ) = ( 1.0:1.0:1.0, 1.0:1.0:1.0 );
         ( S[3] => Y ) = ( 1.0:1.0:1.0, 1.0:1.0:1.0 );
    endspecify
endmodule // CM8
