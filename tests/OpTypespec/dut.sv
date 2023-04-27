module ibex_csr #(
parameter bit [Width-1:0] ResetValue = '0
)
();

endmodule

module dut();
typedef struct packed {
  logic          lock;
  logic          read;
} pmp_cfg_t;

localparam pmp_cfg_t pmp_cfg_rst[1] = '{
  '{lock: 1'b0, read: 1'b0}
};

  ibex_csr #(
    .ResetValue(pmp_cfg_rst[0])
  ) u_pmp_cfg_csr ();
endmodule
