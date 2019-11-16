module hb_exp
#(parameter
 HRQW=32,
 HRSW=32,
 RSTRT=0,
 REND=7,
 ADDRW = 3,
 NTGT=REND-RSTRT+1,

 ADDR_COMP = 0,
 BASE_ADDR_VEC = 0,
 ADDR_MASK_VEC = 0,
 DFF_SAMPLES   = 1

)(

input  clk,
input  areset_n,
input             init_exp_rq,
input [ADDRW-1:0] init_exp_addr,
input [HRQW-1:0]  init_exp_data,
input  [NTGT-1:0] tgt_exp_ack,
input  [NTGT-1:0] tgt_exp_err,
input  [NTGT*HRSW-1:0] tgt_exp_data
);
wire [NTGT-1:0] exp_tgt_rq_samp_int    ;
wire [NTGT-1:0] tgt_sel;
generate
  if(ADDR_COMP==0) begin: GEN_IND_TREE
    assign tgt_sel = addr_dec(init_hb_addr_ff);
  end
  else begin: GEN_REG_TREE
    assign tgt_sel = addr_dec_comp(init_hb_addr_ff,BASE_ADDR_VEC,ADDR_MASK_VEC);
  end
endgenerate

assign exp_tgt_rq_samp_int = {NTGT{init_exp_rq_ff}} & tgt_sel;


////////////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////////////
// Functions

function  [NTGT-1:0] addr_dec(input [ADDRW-1:0] f_addr);
integer i_tgt;
reg [NTGT-1:0] tgt_tmp;
begin
  tgt_tmp={NTGT{1'b0}};
  for(i_tgt=RSTRT;i_tgt<=REND;i_tgt=i_tgt+1) begin
    if(f_addr==i_tgt) begin
      tgt_tmp[i_tgt]=1'b1;
    end
  end
  addr_dec=tgt_tmp;
end
endfunction


function  [NTGT-1:0] addr_dec_comp(input [ADDRW-1:0] f_addr,input [NTGT*ADDRW-1:0] base_addr_in,input [NTGT*ADDRW-1:0] mask_in);
integer i_tgt;
reg [NTGT-1:0] tgt_tmp;
reg [ADDRW-1:0] base_addr_arr [NTGT-1:0];
reg [ADDRW-1:0] addr_mask_arr [NTGT-1:0];
reg [ADDRW-1:0] end_addr_arr [NTGT-1:0];

begin
  for(i_tgt=RSTRT;i_tgt<=REND;i_tgt=i_tgt+1) begin
    base_addr_arr[i_tgt]=base_addr_in[i_tgt*ADDRW +: ADDRW];
    addr_mask_arr[i_tgt]=mask_in[i_tgt*ADDRW +: ADDRW];
    end_addr_arr[i_tgt]=base_addr_arr[i_tgt] + addr_mask_arr[i_tgt];
  end
  tgt_tmp={NTGT{1'b0}};
  for(i_tgt=RSTRT;i_tgt<=REND;i_tgt=i_tgt+1) begin
    if((f_addr>=base_addr_arr[i_tgt])&&(f_addr<=end_addr_arr[i_tgt])) begin
      tgt_tmp[i_tgt]=1'b1;
    end
  end
  addr_dec_comp=tgt_tmp;
end
endfunction


endmodule
