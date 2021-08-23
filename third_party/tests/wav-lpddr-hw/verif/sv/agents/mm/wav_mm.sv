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
`timescale 1ps/1ps

module wav_mm (
    CK_T_A,
    CK_C_A,
    CK_T_B,
    CK_C_B,
    CKE_A,
    CKE_B,
    CS_A,
    CS_B,
    CA_A,
    CA_B,
    ODT_CA_A,
    ODT_CA_B,
    DQ_A,
    DQ_B,
    DQS_T_A,
    DQS_C_A,
    DQS_T_B,
    DQS_C_B,
    DMI_A,
    DMI_B,
    RESET_N
);

input CK_T_A;
input CK_C_A;
input CK_T_B;
input CK_C_B;
input CKE_A;
input CKE_B;
input CS_A;
input CS_B;
input [5:0] CA_A;
input [5:0] CA_B;
input ODT_CA_A;
input ODT_CA_B;
inout [15:0] DQ_A;
inout [15:0] DQ_B;
inout [1:0] DQS_T_A;
inout [1:0] DQS_C_A;
inout [1:0] DQS_T_B;
inout [1:0] DQS_C_B;
inout [1:0] DMI_A;
inout [1:0] DMI_B;
input RESET_N;

reg [15:0] dq_a_sig = 'hz;
assign DQ_A = dq_a_sig;

reg [15:0] dq_b_sig = 'hz;
assign DQ_B = dq_b_sig;

reg [1:0] dqs_t_a_sig = 'hz;
assign DQS_T_A = dqs_t_a_sig;

reg [1:0] dqs_c_a_sig = 'hz;
assign DQS_C_A = dqs_c_a_sig;

reg [1:0] dqs_t_b_sig = 'hz;
assign DQS_T_B = dqs_t_b_sig;

reg [1:0] dqs_c_b_sig = 'hz;
assign DQS_C_B = dqs_c_b_sig;

reg [1:0] dmi_a_sig = 'hz;
assign DMI_A = dmi_a_sig;

reg [1:0] dmi_b_sig = 'hz;
assign DMI_B = dmi_b_sig;

reg [7:0] txdata = 0;
reg [7:0] rxdata = 0;

int vcoFreq1 = 806;
int delay = 269;
int rl = 22;

initial
begin
    if($value$plusargs("vcoFreq1=%0d",vcoFreq1))
    begin
        if(vcoFreq1 == 230)
        begin
            delay = 1500;
            rl = 7;
        end
        if(vcoFreq1 == 2112)
        begin
            delay = 86;
            rl = 40;
        end
    end

    @(posedge RESET_N);
    fork
    begin
        if ($test$plusargs("MM_FF"))
        begin
            drive_11_ff;
        end
        else
        begin
            if(vcoFreq1 == 2112)
                drive_12_inc;
                else
                    drive_11_inc;

                end
            end
        begin
            rcv_data;
        end
    join
end

task drive_11_inc;
    txdata = 0;
    forever begin
        if ((CA_A == 2) && (CS_A == 1)) begin
            // Pre-ample
            repeat(rl)  @(negedge CK_C_A);
            #delay;
            dqs_c_a_sig = 3;
            dqs_t_a_sig = ~dqs_c_a_sig;
            repeat(2)  @(negedge CK_C_A);
            #delay;
            dqs_c_a_sig = ~dqs_c_a_sig;
            dqs_t_a_sig = ~dqs_c_a_sig;
            // Data
            for (int i=0; i < 8; i++) begin
                dq_a_sig = {(txdata+1),(txdata)};
                @(posedge CK_C_A);
                #delay;
                dqs_c_a_sig = ~dqs_c_a_sig;
                dqs_t_a_sig = ~dqs_c_a_sig;
                txdata = txdata + 2;
                dq_a_sig = {(txdata+1),(txdata)};
                @(negedge CK_C_A);
                #delay;
                dqs_c_a_sig = ~dqs_c_a_sig;
                dqs_t_a_sig = ~dqs_c_a_sig;
                txdata = txdata + 2;
            end
            // Post-ample
            @(posedge CK_C_A);
            #delay;
            dq_a_sig = 'hz;
            dqs_c_a_sig = 'hz;
            dqs_t_a_sig = 'hz;
            txdata = 0;
        end
        @(posedge CK_C_A);
    end
endtask

task drive_12_inc;
    txdata = 0;
    forever begin
        if ((CA_A == 2) && (CS_A == 1)) begin
            // Pre-ample
            repeat(rl)  @(negedge CK_C_A);
            #delay;
            dqs_c_a_sig = 3;
            dqs_t_a_sig = ~dqs_c_a_sig;
            @(negedge CK_C_A);
            #delay;
            dqs_c_a_sig = ~dqs_c_a_sig;
            dqs_t_a_sig = ~dqs_c_a_sig;
            @(posedge CK_C_A);
            #delay;
            dqs_c_a_sig = ~dqs_c_a_sig;
            dqs_t_a_sig = ~dqs_c_a_sig;
            @(negedge CK_C_A);
            #delay;
            dqs_c_a_sig = ~dqs_c_a_sig;
            dqs_t_a_sig = ~dqs_c_a_sig;
            // Data
            for (int i=0; i < 8; i++) begin
                dq_a_sig = {(txdata+1),(txdata)};
                @(posedge CK_C_A);
                #delay;
                dqs_c_a_sig = ~dqs_c_a_sig;
                dqs_t_a_sig = ~dqs_c_a_sig;
                txdata = txdata + 2;
                dq_a_sig = {(txdata+1),(txdata)};
                @(negedge CK_C_A);
                #delay;
                dqs_c_a_sig = ~dqs_c_a_sig;
                dqs_t_a_sig = ~dqs_c_a_sig;
                txdata = txdata + 2;
            end
            // Post-ample
            dq_a_sig = 'hz;
            dqs_c_a_sig = 'hz;
            dqs_t_a_sig = 'hz;
            txdata = 0;
        end
        @(posedge CK_C_A);
    end
endtask

task drive_11_ff;
    txdata = 8'hFF;
    forever begin
        if ((CA_A == 2) && (CS_A == 1)) begin
            // Pre-ample
            repeat(rl)  @(negedge CK_C_A);
            #delay;
            dqs_c_a_sig = 3;
            dqs_t_a_sig = ~dqs_c_a_sig;
            repeat(2)  @(negedge CK_C_A);
            #delay;
            dqs_c_a_sig = ~dqs_c_a_sig;
            dqs_t_a_sig = ~dqs_c_a_sig;
            // Data
            for (int i=0; i < 8; i++) begin
                dq_a_sig = {txdata,txdata};
                @(posedge CK_C_A);
                #delay;
                dqs_c_a_sig = ~dqs_c_a_sig;
                dqs_t_a_sig = ~dqs_c_a_sig;
                dq_a_sig = {txdata,txdata};
                @(negedge CK_C_A);
                #delay;
                dqs_c_a_sig = ~dqs_c_a_sig;
                dqs_t_a_sig = ~dqs_c_a_sig;
            end
            // Post-ample
            @(posedge CK_C_A);
            #delay;
            dq_a_sig = 'hz;
            dqs_c_a_sig = 'hz;
            dqs_t_a_sig = 'hz;
        end
        @(posedge CK_C_A);
    end
endtask

task rcv_data;
    forever begin
        if ((CA_A == 4) && (CS_A == 1)) begin
            // Pre-ample
            wait(DQS_C_A == 0);
            wait(DQS_C_A == 3);
            wait(DQS_C_A == 0);
            wait(DQS_C_A == 3);
            // Data
            for (int i=0; i < 8; i++) begin
                if (DQ_A !== {(rxdata+1),(rxdata)}) $display(" Error rcv_data: %h", DQ_A);
                rxdata = rxdata + 2;
                @(posedge CK_C_A);
                if (DQ_A == {(rxdata+1),(rxdata)}) $display( "Error rcv_data: %h", DQ_A);
                rxdata = rxdata + 2;
                @(negedge CK_C_A);
            end
            rxdata = 0;
        end
        @(posedge CK_C_A);
    end
endtask

endmodule
