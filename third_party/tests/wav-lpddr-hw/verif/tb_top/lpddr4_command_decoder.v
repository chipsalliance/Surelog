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
module lpddr4_command_decoder (input ck_t ,
    input ca0 , ca1, ca2 ,ca3 , ca4 ,ca5,rst_n,
input cs);

reg [5:0] command ; //for case statements
reg [7:0] command_mod ; //for case statements

reg [5:0] command_name ;
reg [5:0] command_type ;

reg [5:0] command_name_2 ; //for cas2 information in write , mask write ,read ,mrr ,mpc
reg [5:0] command_type_2 ;

wire      int_cs;

assign int_cs = cs & rst_n;

initial begin
    command        = 0;
    command_name   = 0;
    command_type   = 0;

    command_name_2 = 0;
    command_type_2 = 0;
    @(posedge rst_n);
    forever begin
        while (cs != 1'b1)
            @(posedge ck_t) ;
        if(cs == 1)
        begin
            command = {ca0,ca1,ca2,ca3,ca4,ca5};
            command_name  = {ca5,ca4,ca3,ca2,ca1,ca0} ;
            @(posedge ck_t) ;
            command_type  = {ca5,ca4,ca3,ca2,ca1,ca0} ;

            if(command[5:1] ==  5'b00100 || 5'b00110 || 5'b01000 || 5'b01110 ) //write,mask write ,read ,mrr
            begin
                @(posedge ck_t);
                command_name_2 = {ca5,ca4,ca3,ca2,ca1,ca0} ; //cas2 information on rising edge r1
                @(posedge ck_t);
                command_type_2 = {ca5,ca4,ca3,ca2,ca1,ca0} ; //cas2 information on rising edge r2
            end
            else if(command[5:1] == 5'b00000  ) //mpc command
            begin
                if(command_name[5] == 1'b1) //op[6] == 1
                begin
                    if(command_type == 6'b000111 || 6'b000001 || 6'b000011 ) // wr_fifo & rd_ffio  & rd dq calibration
                    begin
                        @(posedge ck_t);
                        command_name_2 = {ca5,ca4,ca3,ca2,ca1,ca0} ; //cas2 information on r1
                        @(posedge ck_t);
                        command_type_2 = {ca5,ca4,ca3,ca2,ca1,ca0} ; //cas2 information on r2
                    end
                end
            end
            else if(command[5:1] ==  5'b01100 ) //mode register write
            begin
                @(posedge ck_t);
                command_name_2 = {ca5,ca4,ca3,ca2,ca1,ca0} ; //mrw_2 information on rising edge r1
                @(posedge ck_t);
                command_type_2 = {ca5,ca4,ca3,ca2,ca1,ca0} ; //mrw_2 information on rising edge r2
            end
            else if(command_name[5:4] ==  2'b10 ) //activate command
            begin
                @(posedge ck_t);
                command_name_2 = {ca5,ca4,ca3,ca2,ca1,ca0} ; //act_2 information on rising edge r1
                @(posedge ck_t);
                command_type_2 = {ca5,ca4,ca3,ca2,ca1,ca0} ; //act_2_2 information on rising edge r2
            end

        end

        casez(command[5:1])
            5'b00000 : begin
                $display("--------------------------------------------------------------------");
                $display("At time:%t,            LPDDR4 MPC COMMAND                           ",$time());
                casez({command_name[5],command_type[5:0]})
                    7'b0?????? : $display("At time:%t,NO OPERATION",$time());
                    7'b1000001 : $display("At time:%t,RD FIFO SUPPORTS ONLY BL 16 OPERATION",$time());
                    7'b1000011 : $display("At time:%t,RD DQ CALIBRATION",$time());
                    7'b1000101 : $display("At time:%t,RFU",$time());
                    7'b1000111 : $display("At time:%t,WR FIFO SUPPORTS ONLY BL 16 OPERATION",$time());
                    7'b1001001 : $display("At time:%t,RFU",$time());
                    7'b1001011 : $display("At time:%t,START DQS OSC",$time());
                    7'b1001101 : $display("At time:%t,STOP  DQS OSC",$time());
                    7'b1001111 : $display("At time:%t,ZQ CAL START",$time());
                    7'b1010001 : $display("At time:%t,ZQ CAL LATCH",$time());
                    default    : $display("RESERVED");
                endcase
                $display("At time:%t,CAS2 COMMAND WITH COLUMN ADDRESS FROM C[8:2] : %h  ",$time(),{command_name_2[5],command_type_2});
                $display("--------------------------------------------------------------------");
            end
            5'b00001 : begin // precharge command
                $display("--------------------------------------------------------------------");
                $display("At time:%t, LPDDR4 PRECHARGE COMMAND                              ", $time());
                if(command_name[5] == 1 )
                    $display(" ALL BANKS ARE SELECTED");
                else
                begin
                    case(command_type[2:0])
                        0 : $display("BANK0  SELECTED");
                        1 : $display("BANK1  SELECTED");
                        2 : $display("BANK2  SELECTED");
                        3 : $display("BANK3  SELECTED");
                        4 : $display("BANK4  SELECTED");
                        5 : $display("BANK5  SELECTED");
                        6 : $display("BANK6  SELECTED");
                        7 : $display("BANK7  SELECTED");
                    endcase
                end
                $display("--------------------------------------------------------------------");
            end
            5'b00010 : begin // refresh command
                $display("--------------------------------------------------------------------");
                $display("At time:%t,      LPDDR4 REFRESH COMMAND                              ", $time());
                if(command_name[5] == 1 )
                    $display("ALL BANKS ARE SELECTED");
                else
                begin
                    case(command_type[2:0])
                        0 : $display("BANK0  SELECTED");
                        1 : $display("BANK1  SELECTED");
                        2 : $display("BANK2  SELECTED");
                        3 : $display("BANK3  SELECTED");
                        4 : $display("BANK4  SELECTED");
                        5 : $display("BANK5  SELECTED");
                        6 : $display("BANK6  SELECTED");
                        7 : $display("BANK7  SELECTED");
                    endcase
                end
                $display("--------------------------------------------------------------------");
            end
            5'b00011 : begin
                $display("--------------------------------------------------------------------");
                $display("lpddr4  : SRE COMMAND"); // self refresh entry
                $display("--------------------------------------------------------------------");
            end
            5'b00100 : begin
                $display("--------------------------------------------------------------------");
                if(command_type[5] == 0)
                    $display("             LPDDR4 : WRITE COMMAND WITH AUTOPRECHARGE              ");
                else
                begin
                    $display("          LPDDR4 : WRITE COMMAND WITHOUT AUTOPRECHARGE            ");
                end
                case(command_type[2:0])
                    0 : $display("BANK0  ACTIVATED");
                    1 : $display("BANK1  ACTIVATED");
                    2 : $display("BANK2  ACTIVATED");
                    3 : $display("BANK3  ACTIVATED");
                    4 : $display("BANK4  ACTIVATED");
                    5 : $display("BANK5  ACTIVATED");
                    6 : $display("BANK6  ACTIVATED");
                    7 : $display("BANK7  ACTIVATED");
                endcase
                $display("CAS2 COMMAND WITH COLUMN ADDRESS FROM C[9:2] : %h  ",{command_type[4],command_name_2[5],command_type_2});
                $display("--------------------------------------------------------------------");
            end
            5'b00101 : begin
                $display("--------------------------------------------------------------------");
                $display( "lpddr4  : SRX COMMAND"); //  self refresh exit
                $display("--------------------------------------------------------------------");
            end
            5'b00110 : begin
                $display("--------------------------------------------------------------------");
                if(command_type[5] == 0)
                    $display("       LPDDR4 :MASK WRITE COMMAND WITH AUTOPRECHARGE      ");
                else
                begin
                    $display("      LPDDR4 :MASK WRITE COMMAND WITHOUT AUTOPRECHARGE          ");
                end
                case(command_type[2:0])
                    0 : $display("BANK0  ACTIVATED");
                    1 : $display("BANK1  ACTIVATED");
                    2 : $display("BANK2  ACTIVATED");
                    3 : $display("BANK3  ACTIVATED");
                    4 : $display("BANK4  ACTIVATED");
                    5 : $display("BANK5  ACTIVATED");
                    6 : $display("BANK6  ACTIVATED");
                    7 : $display("BANK7  ACTIVATED");
                endcase
                $display("CAS2 COMMAND WITH COLUMN ADDRESS FROM C[9:2] : %h  ",{command_type[4],command_name_2[5],command_type_2});
                $display("--------------------------------------------------------------------");
            end
            5'b01000 : begin
                $display("--------------------------------------------------------------------");
                if(command_type[5] == 0)
                    $display("       LPDDR4 :READ COMMAND WITH AUTOPRECHARGE      ");
                else
                begin
                    $display("      LPDDR4 :READ COMMAND WITHOUT AUTOPRECHARGE          ");
                end
                case(command_type[2:0])
                    0 : $display("BANK0  ACTIVATED");
                    1 : $display("BANK1  ACTIVATED");
                    2 : $display("BANK2  ACTIVATED");
                    3 : $display("BANK3  ACTIVATED");
                    4 : $display("BANK4  ACTIVATED");
                    5 : $display("BANK5  ACTIVATED");
                    6 : $display("BANK6  ACTIVATED");
                    7 : $display("BANK7  ACTIVATED");
                endcase
                $display("CAS2 COMMAND WITH COLUMN ADDRESS FROM C[9:2] : %h  ",{command_type[4],command_name_2[5],command_type_2});
                $display("--------------------------------------------------------------------");
            end
            5'b00111,5'b01011,5'b01011,5'b01111 : begin
                $display("--------------------------------------------------------------------");
                $display("lpddr4  : RFU COMMAND"); // rfu command
                $display("--------------------------------------------------------------------");
            end
            5'b01100 : begin
                $display("--------------------------------------------------------------------");
                $display("                LPDDR4  MRW_1 COMMAND                               ");
                $display("         MODE REGISTER ADDRESS : %h ",command_type);
                $display("                LPDDR4  MRW_2 COMMAND            ");
                $display("         MODE REGISTER DATA : %h ",{command_name[5],command_name_2[5],command_type_2});
                command_mod = {command_name[5],command_name_2[5],command_type_2};
                case (command_type)
                    6'b000000: begin
                        $display("        MR0 config: %s ",(command_mod[0]   == 1'b1)  ? "Only modified Refresh mode supported" :
                        "Both Legacy and modified refresh mode supported");
                        $display("        MR0 config: %s ",(command_mod[4:3] == 2'b00) ? "RZQ Self test not supported " :
                            (command_mod[4:3] == 2'b01) ? "ZQ pin may connect to VSS or float" :
                            (command_mod[4:3] == 2'b10) ? "ZQ pin may may short to VDDQ"       :
                        "ZQ pin self test Completed");
                        $display("        MR0 config: %s ",(command_mod[7]   == 1'b0)  ? "CA for this rank is not terminated" :
                        "CA for this rank is terminated");
                    end
                    6'b000001: begin
                        $display("        MR1 config: %s ",(command_mod[1:0]  == 2'b00)  ? "burst length of 16 supported for both write and read" :
                            (command_mod[1:0]  == 2'b01)  ? "burst length of 32 supported for both write and read" :
                            (command_mod[1:0]  == 2'b10)  ? "On the fly burst length of 16 or 32 supported for both write and read" :
                        "This case is RESERVED");

                        $display("        MR1 config: %s ",(command_mod[ 2 ]  == 1'b1 )  ? "Write Pre-amble  = 2*tck " :
                        "This case is RESERVED");
                        $display("        MR1 config: %s ",(command_mod[ 3 ]  == 1'b0 )  ? "Static read pre-amble    " :
                        "Toggle read pre-amble");
                        $display("        MR1 config: Write recovery for Auto precharge commands= %d ",(4*command_mod[6:4] + 6));
                        $display("        MR1 config: Read post-amble length = %s ",(command_mod[ 7 ]  == 1'b0 )  ? "0.5*TCK " : "1.5*TCK");
                    end
                    6'b000010: begin
                        $display("        MR2 config: Read latency= %d cycles ", 6 + (4 *command_mod[2:0]));
                        $display("        MR2 config: Write latency= %d cycles ", 6 + (4 *command_mod[5:3]));
                        $display("        MR2 config: Write latency set used : set%s",command_mod[6] ? "B" : "A");
                        $display("        MR2 config: Write levelling %s",command_mod[7] ? "enabled" : "disabled");
                    end

                endcase
                $display("--------------------------------------------------------------------");
            end
            5'b01110 : begin
                $display("--------------------------------------------------------------------");
                $display("                LPDDR4  MRR1 COMMAND                               ");
                $display("         MODE REGISTER ADDRESS : %h ",command_type);
                $display("CAS2 COMMAND WITH COLUMN ADDRESS FROM C[8:2] : %h  ",{command_name_2[5],command_type_2});
                $display("--------------------------------------------------------------------");
            end
            5'b10??? : begin
                $display("--------------------------------------------------------------------");
                $display("                LPDDR4  ACTIVATE COMMAND                          ");
                case(command_type[2:0])
                    0 : $display("BANK0  ACTIVATED");
                    1 : $display("BANK1  ACTIVATED");
                    2 : $display("BANK2  ACTIVATED");
                    3 : $display("BANK3  ACTIVATED");
                    4 : $display("BANK4  ACTIVATED");
                    5 : $display("BANK5  ACTIVATED");
                    6 : $display("BANK6  ACTIVATED");
                    7 : $display("BANK7  ACTIVATED");
                endcase
                $display("SELECTED ROW IN PARTICULAR BANK : %h ",command_name[5:2],{command_type[5:4],command_name_2[5:2],command_type_2[5:0]});
                $display("--------------------------------------------------------------------");
            end
        endcase
    end
end

endmodule
