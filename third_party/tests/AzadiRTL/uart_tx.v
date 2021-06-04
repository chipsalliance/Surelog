module uart_tx (
   input       clk_i,
   input       rst_ni,
   input       tx_en,
   input [7:0] i_TX_Byte, 
   input [15:0]CLKS_PER_BIT,
   //output      o_TX_Active,
   output reg  o_TX_Serial,
   output      o_TX_Done
   );
 
  localparam IDLE         = 3'b000;
  localparam TX_START_BIT = 3'b001;
  localparam TX_DATA_BITS = 3'b010;
  localparam TX_STOP_BIT  = 3'b011;
  localparam CLEANUP      = 3'b100;
  
  reg [2:0] r_SM_Main     ;
  reg [15:0] r_Clock_Count ;
  reg [2:0] r_Bit_Index   ;
  reg [7:0] r_TX_Data     ;
  reg       r_TX_Done     ;
//  reg       r_TX_Active   ;
    
  always @(posedge clk_i)
  begin
    if(~rst_ni) begin
        r_SM_Main     = 0;
        r_Clock_Count = 0;
        r_Bit_Index   = 0;
        r_TX_Data     = 0;
        r_TX_Done     = 0;
       // r_TX_Active   = 0;
    end else begin
    case (r_SM_Main)
      IDLE :
        begin
          o_TX_Serial   <= 1'b1;         // Drive Line High for Idle
          r_TX_Done     <= 1'b0;
          r_Clock_Count <= 0;
          r_Bit_Index   <= 0;
          
          if (tx_en == 1'b1)
          begin
           // r_TX_Active <= 1'b1;
            r_TX_Data   <= i_TX_Byte;
            r_SM_Main   <= TX_START_BIT;
          end
          else
            r_SM_Main <= IDLE;
        end // case: IDLE
      
      
      // Send out Start Bit. Start bit = 0
      TX_START_BIT :
        begin
          o_TX_Serial <= 1'b0;
          
          // Wait CLKS_PER_BIT-1 clock cycles for start bit to finish
          if (r_Clock_Count < CLKS_PER_BIT-1)
          begin
            r_Clock_Count <= r_Clock_Count + 1;
            r_SM_Main     <= TX_START_BIT;
          end
          else
          begin
            r_Clock_Count <= 0;
            r_SM_Main     <= TX_DATA_BITS;
          end
        end // case: TX_START_BIT
      
      
      // Wait CLKS_PER_BIT-1 clock cycles for data bits to finish         
      TX_DATA_BITS :
        begin
          o_TX_Serial <= r_TX_Data[r_Bit_Index];
          
          if (r_Clock_Count < CLKS_PER_BIT-1)
          begin
            r_Clock_Count <= r_Clock_Count + 1;
            r_SM_Main     <= TX_DATA_BITS;
          end
          else
          begin
            r_Clock_Count <= 0;
            
            // Check if we have sent out all bits
            if (r_Bit_Index < 7)
            begin
              r_Bit_Index <= r_Bit_Index + 1;
              r_SM_Main   <= TX_DATA_BITS;
            end
            else
            begin
              r_Bit_Index <= 0;
              r_SM_Main   <= TX_STOP_BIT;
            end
          end 
        end // case: TX_DATA_BITS
      
      
      // Send out Stop bit.  Stop bit = 1
      TX_STOP_BIT :
        begin
          o_TX_Serial <= 1'b1;
          
          // Wait CLKS_PER_BIT-1 clock cycles for Stop bit to finish
          if (r_Clock_Count < CLKS_PER_BIT-1)
          begin
            r_Clock_Count <= r_Clock_Count + 1;
            r_SM_Main     <= TX_STOP_BIT;
          end
          else
          begin
            r_TX_Done     <= 1'b1;
            r_Clock_Count <= 0;
            r_SM_Main     <= CLEANUP;
           // r_TX_Active   <= 1'b0;
          end 
        end // case: TX_STOP_BIT
      
      
      // Stay here 1 clock
      CLEANUP :
        begin
          r_TX_Done <= 1'b1;
          r_SM_Main <= IDLE;
        end
      
      
      default :
        r_SM_Main <= IDLE;
      
    endcase
    end 
  end
  
  //assign o_TX_Active = r_TX_Active;
  assign o_TX_Done   = r_TX_Done;
  
endmodule
 
