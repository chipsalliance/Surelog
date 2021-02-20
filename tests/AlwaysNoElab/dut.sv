module dut #(
  parameter int NrDevices = 1
  )();

  localparam int unsigned NumBitsDeviceSel = NrDevices > 1 ? $clog2(NrDevices) : 1;
  logic [NumBitsDeviceSel-1:0] device_sel_req;
  int device = 2;
  always_comb begin
    device_sel_req = NumBitsDeviceSel'(device);
  end

endmodule // dut

