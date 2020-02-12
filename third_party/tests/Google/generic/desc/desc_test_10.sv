/*
:name: desc_test_10
:description: Test
:type: preprocessing
:should_fail: 0
:tags: 5.6.4
*/
`ifdef FPGA
`ifndef DEBUGGER
interface myinterface;
endinterface
`endif
`endif
