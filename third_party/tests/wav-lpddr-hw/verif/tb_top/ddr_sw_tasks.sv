/*********************************************************************************
Copyright (c) 2021 Wavious LLC

This program is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

This program is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with this program.  If not, see <http://www.gnu.org/licenses/>.

*********************************************************************************/
task phy2host_receive_msg;
   logic val;
   output logic [31:0] id;
   output logic [31:0] data;
   begin
      // wait till any message arrives
      do begin
         `CSR_RDF1(DDR_MCUINTF_OFFSET, WAV_MCUINTF_MCU2HOST_MSG_REQ, REQ, val);
	wait_hclk (20);
      end while (val != 1'b1 );

      // read message
      `CSR_RDF1(DDR_MCUINTF_OFFSET, WAV_MCUINTF_MCU2HOST_MSG_ID, ID, id);
      `CSR_RDF1(DDR_MCUINTF_OFFSET, WAV_MCUINTF_MCU2HOST_MSG_DATA, DATA, data);

      // clear request
       `CSR_WRF1(DDR_MCUINTF_OFFSET, WAV_MCUINTF_MCU2HOST_MSG_REQ, REQ, 1);

      // send ack
      `CSR_WRF1(DDR_MCUINTF_OFFSET, WAV_MCUINTF_MCU2HOST_MSG_ACK, ACK, 1);

   end
endtask

task host2phy_send_msg;
   input logic [31:0] id;
   input logic [31:0] data;
   logic val;
   begin
      // send message
      `CSR_WRF1(DDR_MCUINTF_OFFSET, WAV_MCUINTF_HOST2MCU_MSG_DATA, DATA, data);
      `CSR_WRF1(DDR_MCUINTF_OFFSET, WAV_MCUINTF_HOST2MCU_MSG_ID, ID, id);
      `CSR_WRF1(DDR_MCUINTF_OFFSET, WAV_MCUINTF_HOST2MCU_MSG_REQ, REQ, 1);

      // wait for ack
      do begin
         `CSR_RDF1(DDR_MCUINTF_OFFSET, WAV_MCUINTF_HOST2MCU_MSG_ACK, ACK, val);
         wait_hclk (20);
      end while (val != 1'b1 );

      // clear ack
      `CSR_WRF1(DDR_MCUINTF_OFFSET, WAV_MCUINTF_HOST2MCU_MSG_ACK, ACK, 1);
   end
endtask

task host2phy_stopsim;
   input logic [15:0] msg;
   logic [31:0] data;
   begin
      data[31:16] = msg;
      data[15:0]  = 16'h1;
      host2phy_send_msg( .id(0), .data(data));
   end
endtask

task host2phy_sw_freqswitch;
   input logic [3:0] msg;
   logic [31:0] data;
   begin
      data[31:0] = msg;
      host2phy_send_msg( .id(1), .data(data));
   end
endtask

task host2phy_hw_freqswitch;
   input logic [3:0] msg;
   logic [31:0] data;
   begin
      data[31:0] = msg;
      host2phy_send_msg( .id(2), .data(data));
   end
endtask
