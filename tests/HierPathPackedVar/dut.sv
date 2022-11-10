package std_cache_pkg;
   typedef struct packed {
    logic                req;
    ariane_axi::ad_req_t reqtype;
    ariane_pkg::amo_t    amo;
    logic [3:0]          id;
    logic [63:0]         addr;
    logic [63:0]         wdata;
    logic                we;
    logic [7:0]          be;
    logic [1:0]          size;
} bypass_req_t;

endpackage

module axi_adapter_arbiter #(
    parameter NR_PORTS = 4,
    parameter type req_t = std_cache_pkg::bypass_req_t)
    (input  req_t [NR_PORTS-1:0] req_i);
    reg state_d;
    always_comb begin
       if (req_i[i].req == 1'b1) begin                    
          state_d = SERVING;   
      end
    end
endmodule
