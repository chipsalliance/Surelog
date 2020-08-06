module top();

const logic [RomSize-1:0][63:0] mem = {
       64'h00000000_7b200073,
       64'h7b302573_7b202473
     };
   
 const logic [7:0] sbox_enc [256] = '{
      8'h63, 
      8'h7C
  };

  localparam int RhoOffset [5][5]  = '{
       //y  0    1    2    3    4     x
       '{   0,  36},
       '{   1, 300}
     };

   
endmodule
