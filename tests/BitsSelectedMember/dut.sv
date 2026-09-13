// $bits of a SELECTED / hierarchical primary must size the selected member,
// not the first identifier's typespec: `$bits(app_i[app_id].strb)` is 8 (the
// strb member), not 73 (the whole element struct) — OpenTitan kmac_app's
// strb->byte-mask loop bound.
package p;
  typedef struct packed { logic valid; logic [63:0] data; logic [7:0] strb; } req_t;
  localparam int Shares = 2;
  typedef struct packed { logic valid; logic [Shares-1:0][255:0] key; } hw_key_req_t;
endpackage
module dut(input p::req_t app_i [3], input logic [1:0] app_id, input p::hw_key_req_t keymgr_key_i,
           output logic [63:0] mask_o,
           output int w_dyn, output int w_const, output int w_field, output int w_part, output int w_elem);
  // element of a 2-D packed member: one 256-bit share, not 1 bit (kmac_app KeyMgrKeyW)
  localparam int KeyMgrKeyW = $bits(keymgr_key_i.key[0]);
  assign w_elem = KeyMgrKeyW;
  p::req_t s;
  assign s = app_i[1];
  assign w_dyn   = $bits(app_i[app_id].strb);
  assign w_const = $bits(app_i[1].strb);
  assign w_field = $bits(s.data);
  assign w_part  = $bits(s.data[7:4]);
  always_comb begin
    mask_o = '0;
    for (int i = 0; i < $bits(app_i[app_id].strb); i++)
      mask_o[8*i +: 8] = {8{app_i[app_id].strb[i]}};
  end
endmodule
