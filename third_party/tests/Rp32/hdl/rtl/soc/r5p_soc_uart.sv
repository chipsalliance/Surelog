////////////////////////////////////////////////////////////////////////////////
// R5P: UART controller
////////////////////////////////////////////////////////////////////////////////
// Copyright 2022 Iztok Jeras
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
///////////////////////////////////////////////////////////////////////////////

module r5p_soc_gpio #(
  int unsigned GW = 32,   // GPIO width
  bit     CFG_MIN = 1'b0  // minimalistic implementation
)(
  // GPIO signals
  output logic [GW-1:0] gpio_o,
  output logic [GW-1:0] gpio_e,
  input  logic [GW-1:0] gpio_i,
  // bus interface
  r5p_bus_if.sub bus
);

module uart #(
  // UART parameters
  parameter int BYTESIZE = 8,              // transfer size in bits
  parameter     PARITY   = "NONE",         // parity type "EVEN", "ODD", "NONE"
  parameter int STOPSIZE = 1,              // number of stop bits
  parameter int N_BIT    = 2,              // clock cycles per bit
  parameter int N_LOG    = $clog2(N_BIT),  // size of boudrate generator counter
  // Avalon parameters
  parameter int AAW = 1,     // address width
  parameter int ADW = 32,    // data width
  parameter int ABW = ADW/8  // byte enable width
)(
  // system signals
  input  logic           clk,  // clock
  input  logic           rst,  // reset (asynchronous)
  // Avalon MM interface
  input  logic           avalon_read,
  input  logic           avalon_write,
  input  logic [ADW-1:0] avalon_writedata,
  output logic [ADW-1:0] avalon_readdata,
  output logic           avalon_waitrequest,
  output logic           avalon_interrupt,
  // UART
  input  logic           uart_rxd,  // receive
  output logic           uart_txd   // transmit
);

// UART transfer length
localparam UTL = BYTESIZE + (PARITY!="NONE") + STOPSIZE;

// parity option
localparam PRT = (PARITY!="EVEN");

// Avalon signals
logic avalon_trn_w;
logic avalon_trn_r;

// baudrate signals
logic    [N_LOG-1:0] txd_bdr, rxd_bdr;
logic                txd_ena, rxd_ena;

// UART signals
logic                txd_run, rxd_run;  // transfer run status
logic          [3:0] txd_cnt, rxd_cnt;  // transfer length counter
logic [BYTESIZE-1:0] txd_dat, rxd_dat;  // data shift register
logic                txd_prt, rxd_prt;  // parity register

logic                rxd_start, rxd_end;
 
// receiver status
logic                status_rdy;  // receive data ready
logic                status_err;  // receive data error
logic                status_prt;  // receive data parity error
logic [BYTESIZE-1:0] status_dat;  // receive data register

//////////////////////////////////////////////////////////////////////////////
// Avalon logic
//////////////////////////////////////////////////////////////////////////////

// Avalon transfer status
assign avalon_waitrequest = txd_run & ~avalon_read;
assign avalon_trn_w = avalon_write & ~avalon_waitrequest;
assign avalon_trn_r = avalon_read  & ~avalon_waitrequest;

// Avalon read data
generate if (PARITY!="NONE") begin
assign avalon_readdata = {status_rdy, status_err, status_prt, {ADW-BYTESIZE-3{1'b0}}, status_dat};
end else begin
assign avalon_readdata = {status_rdy, status_err, {ADW-BYTESIZE-2{1'b0}}, status_dat};
end endgenerate
// Avalon interrupt
assign avalon_interrupt = status_rdy | status_err;

//////////////////////////////////////////////////////////////////////////////
// UART transmitter
//////////////////////////////////////////////////////////////////////////////

// baudrate generator from clock (it counts down to 0 generating a baud pulse)
always @ (posedge clk, posedge rst)
if (rst) txd_bdr <= N_BIT-1;
else     txd_bdr <= ~|txd_bdr ? N_BIT-1 : txd_bdr - txd_run;

// enable signal for shifting logic
always @ (posedge clk, posedge rst)
if (rst)  txd_ena <= 1'b0;
else      txd_ena <= (txd_bdr == 'd1);

// bit counter
always @ (posedge clk, posedge rst)
if (rst)             txd_cnt <= 0;
else begin
  if (avalon_trn_w)  txd_cnt <= UTL;
  else if (txd_ena)  txd_cnt <= txd_cnt - 1;
end

// shift status
always @ (posedge clk, posedge rst)
if (rst)             txd_run <= 1'b0;
else begin
  if (avalon_trn_w)  txd_run <= 1'b1;
  else if (txd_ena)  txd_run <= txd_cnt != 4'd0;
end

// data shift register
always @ (posedge clk)
  if (avalon_trn_w)  txd_dat <= avalon_writedata[BYTESIZE-1:0];
  else if (txd_ena)  txd_dat <= {1'b1, txd_dat[BYTESIZE-1:1]};

generate if (PARITY!="NONE") begin

// parity register
always @ (posedge clk)
  if (avalon_trn_w)  txd_prt <= PRT;
  else if (txd_ena)  txd_prt <= txd_prt ^ txd_dat[0];

// output register
always @ (posedge clk, posedge rst)
if (rst)             uart_txd <= 1'b1;
else begin
  if (avalon_trn_w)  uart_txd <= 1'b0;
  else if (txd_ena)  uart_txd <= (txd_cnt==STOPSIZE+1) ? txd_prt : txd_dat[0];
end

end else begin

// output register
always @ (posedge clk, posedge rst)
if (rst)             uart_txd <= 1'b1;
else begin
  if (avalon_trn_w)  uart_txd <= 1'b0;
  else if (txd_ena)  uart_txd <= txd_dat[0];
end

end endgenerate

//////////////////////////////////////////////////////////////////////////////
// UART receiver
//////////////////////////////////////////////////////////////////////////////

reg uart_rxd_dly;

// delay uart_rxd and detect a start negative edge
always @ (posedge clk)
uart_rxd_dly <= uart_rxd;

assign rxd_start = uart_rxd_dly & ~uart_rxd & ~rxd_run;

// baudrate generator from clock (it counts down to 0 generating a baud pulse)
always @ (posedge clk, posedge rst)
if (rst)          rxd_bdr <= N_BIT-1;
else begin
  if (rxd_start)  rxd_bdr <= ((N_BIT-1)>>1)-1;
  else            rxd_bdr <= ~|rxd_bdr ? N_BIT-1 : rxd_bdr - rxd_run;
end

// enable signal for shifting logic
always @ (posedge clk, posedge rst)
if (rst)  rxd_ena <= 1'b0;
else      rxd_ena <= (rxd_bdr == 'd1);

// bit counter
always @ (posedge clk, posedge rst)
if (rst)             rxd_cnt <= 0;
else begin
  if (rxd_start)     rxd_cnt <= UTL;
  else if (rxd_ena)  rxd_cnt <= rxd_cnt - 1;
end

// shift status
always @ (posedge clk, posedge rst)
if (rst)             rxd_run <= 1'b0;
else begin
  if (rxd_start)     rxd_run <= 1'b1;
  else if (rxd_ena)  rxd_run <= rxd_cnt != 4'd0;
end

assign rxd_end = ~|rxd_cnt & rxd_ena;

// data shift register
always @ (posedge clk)
  if ((PARITY!="NONE") ? ~(txd_cnt==STOPSIZE) & rxd_ena : rxd_ena)
    rxd_dat <= {uart_rxd, rxd_dat[BYTESIZE-1:1]};

// avalon read data and parity error
always @ (posedge clk)
  if (rxd_end)  status_dat <= rxd_dat;

generate if (PARITY!="NONE") begin

// parity register
always @ (posedge clk)
  if (rxd_start)     rxd_prt <= PRT;
  else if (rxd_ena)  rxd_prt <= rxd_prt ^ uart_rxd;

// avalon read data and parity error
always @ (posedge clk)
  if (rxd_end)  status_prt <= rxd_prt;

end endgenerate

// fifo interrupt status
always @ (posedge clk, posedge rst)
if (rst)                 status_rdy <= 1'b0;
else begin
  if (rxd_end)           status_rdy <= 1'b1;
  else if (avalon_trn_r) status_rdy <= 1'b0;
end

// fifo overflow error
always @ (posedge clk, posedge rst)
if (rst)                 status_err <= 1'b0;
else begin
  if (avalon_trn_r)      status_err <= 1'b0;
  else if (rxd_end)      status_err <= status_rdy;
end

endmodule: uart

