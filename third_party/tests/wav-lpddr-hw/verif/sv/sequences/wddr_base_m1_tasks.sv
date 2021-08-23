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
task automatic set_rx_gb_m1;
    input byte_sel_t    byte_sel;
    input dgb_t         rgb_mode;
    input fgb_t         fgb_mode;
    input logic         wck_mode;
    begin
        if((byte_sel == DQ0) || (byte_sel == DQ_ALL) || (byte_sel == ALL)) begin
            `CSR_WRF3(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_RX_M1_CFG,RGB_MODE,FGB_MODE,WCK_MODE,rgb_mode,fgb_mode,wck_mode);
            `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_RX_M1_CFG,RGB_MODE,FGB_MODE,rgb_mode,fgb_mode);
            `CSR_WRF3(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_RX_M1_CFG,RGB_MODE,FGB_MODE,WCK_MODE,rgb_mode,fgb_mode,wck_mode);
            `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_RX_M1_CFG,RGB_MODE,FGB_MODE,rgb_mode,fgb_mode);
        end
        if((byte_sel == DQ1) || (byte_sel == DQ_ALL) || (byte_sel == ALL)) begin
            `CSR_WRF3(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_RX_M1_CFG,RGB_MODE,FGB_MODE,WCK_MODE,rgb_mode,fgb_mode,wck_mode);
            `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_RX_M1_CFG,RGB_MODE,FGB_MODE,rgb_mode,fgb_mode);
            `CSR_WRF3(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_RX_M1_CFG,RGB_MODE,FGB_MODE,WCK_MODE,rgb_mode,fgb_mode,wck_mode);
            `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_RX_M1_CFG,RGB_MODE,FGB_MODE,rgb_mode,fgb_mode);
        end
        if((byte_sel == CA) || (byte_sel == ALL)) begin
            `CSR_WRF3(DDR_CH0_CA_OFFSET,DDR_CA_DQS_RX_M1_CFG,RGB_MODE,FGB_MODE,WCK_MODE,rgb_mode,fgb_mode,wck_mode);
            `CSR_WRF2(DDR_CH0_CA_OFFSET,DDR_CA_DQ_RX_M1_CFG,RGB_MODE,FGB_MODE,rgb_mode,fgb_mode);
            `CSR_WRF3(DDR_CH1_CA_OFFSET,DDR_CA_DQS_RX_M1_CFG,RGB_MODE,FGB_MODE,WCK_MODE,rgb_mode,fgb_mode,wck_mode);
            `CSR_WRF2(DDR_CH1_CA_OFFSET,DDR_CA_DQ_RX_M1_CFG,RGB_MODE,FGB_MODE,rgb_mode,fgb_mode);
        end
    end
endtask

task automatic set_tx_gb_m1;
    input byte_sel_t   byte_sel;
    input dgb_t        tgb_mode;
    input wgb_t        wgb_mode;
    begin
        if((byte_sel == DQ0) || (byte_sel == DQ_ALL) || (byte_sel == ALL)) begin
            `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_M1_CFG,TGB_MODE,WGB_MODE, tgb_mode, wgb_mode);
            `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_M1_CFG,TGB_MODE,WGB_MODE, tgb_mode, wgb_mode);
        end
        if((byte_sel == DQ1) || (byte_sel == DQ_ALL) || (byte_sel == ALL)) begin
            `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_M1_CFG,TGB_MODE,WGB_MODE, tgb_mode, wgb_mode);
            `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_M1_CFG,TGB_MODE,WGB_MODE, tgb_mode, wgb_mode);
        end
        if((byte_sel == CA)  || (byte_sel == ALL)) begin
            `CSR_WRF2(DDR_CH0_CA_OFFSET,DDR_CA_DQS_TX_M1_CFG,TGB_MODE,WGB_MODE, tgb_mode, wgb_mode);
            `CSR_WRF2(DDR_CH1_CA_OFFSET,DDR_CA_DQS_TX_M1_CFG,TGB_MODE,WGB_MODE, tgb_mode, wgb_mode);
        end
    end
endtask

task automatic set_dqs_egress_mode_m1;
    input byte_sel_t   byte_sel;
    input integer       dqs;
    input logic   [6:0] mode;
    logic   [5:0] ana_mode;
    logic   [6:0] dig_mode;
    begin

        //DIG_EGRESS_SDR          0   //ANA_EGRESS_DDR_2TO1     1
        //DIG_EGRESS_DDR_2TO1     1   //ANA_EGRESS_QDR_2TO1     2
        //DIG_EGRESS_BSCAN        6   //ANA_EGRESS_BYPASS       0

        //DIG_EGRESS_QDR_2TO1     2   //ANA_EGRESS_ODR_2TO1     3
        //DIG_EGRESS_ODR_2TO1     3   //ANA_EGRESS_QDR_4TO1     4
        //DIG_EGRESS_QDR_4TO1     4   //ANA_EGRESS_ODR_4TO1     5
        //DIG_EGRESS_ODR_4TO1     5

        case(mode)
            //SDR
            7'h1 : begin
                dig_mode = 7'h1;
                ana_mode = 6'h1;
            end
            //DDR2TO1
            7'h2 : begin
                dig_mode = 7'h1;
                ana_mode = 6'h2;
            end
            //QDR2TO1
            7'h4 : begin
                dig_mode = 7'h2;
                ana_mode = 6'h4;
            end
            //ODR2TO1
            7'h8 : begin
                dig_mode = 7'h4;
                ana_mode = 6'h8;
            end
            //QDR4TO1
            7'h10 : begin
                dig_mode = 7'h1;
                ana_mode = 6'h10;
            end
            //ODR4TO1
            7'h20 : begin
                dig_mode = 7'h2;
                ana_mode = 6'h20;
            end
            //BSCAN
            7'h40 : begin
                dig_mode = 7'h40;
                ana_mode = 6'h1;
            end
            //SDR
            default: begin
                dig_mode = 7'h1;
                ana_mode = 6'h1;
            end
        endcase

        if((byte_sel == DQ0 ) || (byte_sel == DQ_ALL) || (byte_sel == ALL)) begin
            case(dqs)
                {8'd0} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_EGRESS_ANA_M1_CFG_0, ana_mode);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_EGRESS_DIG_M1_CFG_0, dig_mode);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_EGRESS_ANA_M1_CFG_0, ana_mode);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_EGRESS_DIG_M1_CFG_0, dig_mode);
                end
                {8'd1} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_EGRESS_ANA_M1_CFG_1, ana_mode);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_EGRESS_DIG_M1_CFG_1, dig_mode);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_EGRESS_ANA_M1_CFG_1, ana_mode);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_EGRESS_DIG_M1_CFG_1, dig_mode);
                end
                {8'd2} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_EGRESS_ANA_M1_CFG_2, ana_mode);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_EGRESS_DIG_M1_CFG_2, dig_mode);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_EGRESS_ANA_M1_CFG_2, ana_mode);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_EGRESS_DIG_M1_CFG_2, dig_mode);
                end
                {8'd3} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_EGRESS_ANA_M1_CFG_3, ana_mode);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_EGRESS_DIG_M1_CFG_3, dig_mode);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_EGRESS_ANA_M1_CFG_3, ana_mode);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_EGRESS_DIG_M1_CFG_3, dig_mode);
                end
                {8'd4} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_EGRESS_ANA_M1_CFG_4, ana_mode);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_EGRESS_DIG_M1_CFG_4, dig_mode);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_EGRESS_ANA_M1_CFG_4, ana_mode);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_EGRESS_DIG_M1_CFG_4, dig_mode);
                end
                {8'd5} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_EGRESS_ANA_M1_CFG_5, ana_mode);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_EGRESS_DIG_M1_CFG_5, dig_mode);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_EGRESS_ANA_M1_CFG_5, ana_mode);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_EGRESS_DIG_M1_CFG_5, dig_mode);
                end
                {8'd6} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_EGRESS_ANA_M1_CFG_6, ana_mode);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_EGRESS_DIG_M1_CFG_6, dig_mode);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_EGRESS_ANA_M1_CFG_6, ana_mode);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_EGRESS_DIG_M1_CFG_6, dig_mode);
                end
                {8'd7} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_EGRESS_ANA_M1_CFG_7, ana_mode);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_EGRESS_DIG_M1_CFG_7, dig_mode);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_EGRESS_ANA_M1_CFG_7, ana_mode);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_EGRESS_DIG_M1_CFG_7, dig_mode);
                end
                {8'd8} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_EGRESS_ANA_M1_CFG_8, ana_mode);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_EGRESS_DIG_M1_CFG_8, dig_mode);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_EGRESS_ANA_M1_CFG_8, ana_mode);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_EGRESS_DIG_M1_CFG_8, dig_mode);
                end
                default : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_EGRESS_ANA_M1_CFG_0, ana_mode);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_EGRESS_DIG_M1_CFG_0, dig_mode);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_EGRESS_ANA_M1_CFG_1, ana_mode);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_EGRESS_DIG_M1_CFG_1, dig_mode);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_EGRESS_ANA_M1_CFG_2, ana_mode);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_EGRESS_DIG_M1_CFG_2, dig_mode);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_EGRESS_ANA_M1_CFG_3, ana_mode);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_EGRESS_DIG_M1_CFG_3, dig_mode);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_EGRESS_ANA_M1_CFG_4, ana_mode);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_EGRESS_DIG_M1_CFG_4, dig_mode);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_EGRESS_ANA_M1_CFG_5, ana_mode);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_EGRESS_DIG_M1_CFG_5, dig_mode);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_EGRESS_ANA_M1_CFG_6, ana_mode);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_EGRESS_DIG_M1_CFG_6, dig_mode);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_EGRESS_ANA_M1_CFG_7, ana_mode);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_EGRESS_DIG_M1_CFG_7, dig_mode);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_EGRESS_ANA_M1_CFG_8, ana_mode);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_EGRESS_DIG_M1_CFG_8, dig_mode);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_EGRESS_ANA_M1_CFG_0, ana_mode);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_EGRESS_DIG_M1_CFG_0, dig_mode);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_EGRESS_ANA_M1_CFG_1, ana_mode);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_EGRESS_DIG_M1_CFG_1, dig_mode);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_EGRESS_ANA_M1_CFG_2, ana_mode);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_EGRESS_DIG_M1_CFG_2, dig_mode);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_EGRESS_ANA_M1_CFG_3, ana_mode);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_EGRESS_DIG_M1_CFG_3, dig_mode);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_EGRESS_ANA_M1_CFG_4, ana_mode);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_EGRESS_DIG_M1_CFG_4, dig_mode);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_EGRESS_ANA_M1_CFG_5, ana_mode);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_EGRESS_DIG_M1_CFG_5, dig_mode);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_EGRESS_ANA_M1_CFG_6, ana_mode);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_EGRESS_DIG_M1_CFG_6, dig_mode);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_EGRESS_ANA_M1_CFG_7, ana_mode);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_EGRESS_DIG_M1_CFG_7, dig_mode);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_EGRESS_ANA_M1_CFG_8, ana_mode);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_EGRESS_DIG_M1_CFG_8, dig_mode);
                end
            endcase
        end
        if((byte_sel == DQ1 ) || (byte_sel == DQ_ALL) || (byte_sel == ALL)) begin
            case(dqs)
                {8'd0} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_EGRESS_ANA_M1_CFG_0, ana_mode);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_EGRESS_DIG_M1_CFG_0, dig_mode);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_EGRESS_ANA_M1_CFG_0, ana_mode);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_EGRESS_DIG_M1_CFG_0, dig_mode);
                end
                {8'd1} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_EGRESS_ANA_M1_CFG_1, ana_mode);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_EGRESS_DIG_M1_CFG_1, dig_mode);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_EGRESS_ANA_M1_CFG_1, ana_mode);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_EGRESS_DIG_M1_CFG_1, dig_mode);
                end
                {8'd2} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_EGRESS_ANA_M1_CFG_2, ana_mode);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_EGRESS_DIG_M1_CFG_2, dig_mode);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_EGRESS_ANA_M1_CFG_2, ana_mode);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_EGRESS_DIG_M1_CFG_2, dig_mode);
                end
                {8'd3} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_EGRESS_ANA_M1_CFG_3, ana_mode);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_EGRESS_DIG_M1_CFG_3, dig_mode);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_EGRESS_ANA_M1_CFG_3, ana_mode);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_EGRESS_DIG_M1_CFG_3, dig_mode);
                end
                {8'd4} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_EGRESS_ANA_M1_CFG_4, ana_mode);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_EGRESS_DIG_M1_CFG_4, dig_mode);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_EGRESS_ANA_M1_CFG_4, ana_mode);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_EGRESS_DIG_M1_CFG_4, dig_mode);
                end
                {8'd5} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_EGRESS_ANA_M1_CFG_5, ana_mode);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_EGRESS_DIG_M1_CFG_5, dig_mode);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_EGRESS_ANA_M1_CFG_5, ana_mode);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_EGRESS_DIG_M1_CFG_5, dig_mode);
                end
                {8'd6} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_EGRESS_ANA_M1_CFG_6, ana_mode);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_EGRESS_DIG_M1_CFG_6, dig_mode);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_EGRESS_ANA_M1_CFG_6, ana_mode);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_EGRESS_DIG_M1_CFG_6, dig_mode);
                end
                {8'd7} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_EGRESS_ANA_M1_CFG_7, ana_mode);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_EGRESS_DIG_M1_CFG_7, dig_mode);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_EGRESS_ANA_M1_CFG_7, ana_mode);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_EGRESS_DIG_M1_CFG_7, dig_mode);
                end
                {8'd8} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_EGRESS_ANA_M1_CFG_8, ana_mode);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_EGRESS_DIG_M1_CFG_8, dig_mode);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_EGRESS_ANA_M1_CFG_8, ana_mode);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_EGRESS_DIG_M1_CFG_8, dig_mode);
                end
                default : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_EGRESS_ANA_M1_CFG_0, ana_mode);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_EGRESS_DIG_M1_CFG_0, dig_mode);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_EGRESS_ANA_M1_CFG_1, ana_mode);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_EGRESS_DIG_M1_CFG_1, dig_mode);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_EGRESS_ANA_M1_CFG_2, ana_mode);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_EGRESS_DIG_M1_CFG_2, dig_mode);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_EGRESS_ANA_M1_CFG_3, ana_mode);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_EGRESS_DIG_M1_CFG_3, dig_mode);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_EGRESS_ANA_M1_CFG_4, ana_mode);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_EGRESS_DIG_M1_CFG_4, dig_mode);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_EGRESS_ANA_M1_CFG_5, ana_mode);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_EGRESS_DIG_M1_CFG_5, dig_mode);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_EGRESS_ANA_M1_CFG_6, ana_mode);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_EGRESS_DIG_M1_CFG_6, dig_mode);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_EGRESS_ANA_M1_CFG_7, ana_mode);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_EGRESS_DIG_M1_CFG_7, dig_mode);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_EGRESS_ANA_M1_CFG_8, ana_mode);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_EGRESS_DIG_M1_CFG_8, dig_mode);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_EGRESS_ANA_M1_CFG_0, ana_mode);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_EGRESS_DIG_M1_CFG_0, dig_mode);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_EGRESS_ANA_M1_CFG_1, ana_mode);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_EGRESS_DIG_M1_CFG_1, dig_mode);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_EGRESS_ANA_M1_CFG_2, ana_mode);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_EGRESS_DIG_M1_CFG_2, dig_mode);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_EGRESS_ANA_M1_CFG_3, ana_mode);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_EGRESS_DIG_M1_CFG_3, dig_mode);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_EGRESS_ANA_M1_CFG_4, ana_mode);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_EGRESS_DIG_M1_CFG_4, dig_mode);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_EGRESS_ANA_M1_CFG_5, ana_mode);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_EGRESS_DIG_M1_CFG_5, dig_mode);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_EGRESS_ANA_M1_CFG_6, ana_mode);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_EGRESS_DIG_M1_CFG_6, dig_mode);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_EGRESS_ANA_M1_CFG_7, ana_mode);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_EGRESS_DIG_M1_CFG_7, dig_mode);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_EGRESS_ANA_M1_CFG_8, ana_mode);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_EGRESS_DIG_M1_CFG_8, dig_mode);
                end
            endcase
        end
        if((byte_sel == CA) || (byte_sel == ALL)) begin
            case(dqs)
                {8'd0} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQS_TX_EGRESS_ANA_M1_CFG_0, ana_mode);
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQS_TX_EGRESS_DIG_M1_CFG_0, dig_mode);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQS_TX_EGRESS_ANA_M1_CFG_0, ana_mode);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQS_TX_EGRESS_DIG_M1_CFG_0, dig_mode);
                end
                default : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQS_TX_EGRESS_ANA_M1_CFG_0, ana_mode);
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQS_TX_EGRESS_DIG_M1_CFG_0, dig_mode);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQS_TX_EGRESS_ANA_M1_CFG_0, ana_mode);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQS_TX_EGRESS_DIG_M1_CFG_0, dig_mode);
                end
            endcase
        end
    end
endtask

task automatic set_dq_egress_mode_m1;
    input byte_sel_t    byte_sel;
    input integer       dq;
    input logic   [6:0] mode;
    logic   [5:0] ana_mode;
    logic   [6:0] dig_mode;
    begin

        //DIG_EGRESS_SDR          0
        //DIG_EGRESS_DDR_2TO1     1
        //DIG_EGRESS_QDR_2TO1     2
        //DIG_EGRESS_ODR_2TO1     3
        //DIG_EGRESS_QDR_4TO1     4
        //DIG_EGRESS_ODR_4TO1     5
        //DIG_EGRESS_BSCAN        6
        //ANA_EGRESS_BYPASS       0
        //ANA_EGRESS_DDR_2TO1     1
        //ANA_EGRESS_QDR_2TO1     2
        //ANA_EGRESS_ODR_2TO1     3
        //ANA_EGRESS_QDR_4TO1     4
        //ANA_EGRESS_ODR_4TO1     5

        case(mode)
            //SDR
            7'h1 : begin
                dig_mode = 7'h1;
                ana_mode = 6'h1;
            end
            //DDR2TO1
            7'h2 : begin
                dig_mode = 7'h1;
                ana_mode = 6'h2;
            end
            //QDR2TO1
            7'h4 : begin
                dig_mode = 7'h2;
                ana_mode = 6'h4;
            end
            //ODR2TO1
            7'h8 : begin
                dig_mode = 7'h4;
                ana_mode = 6'h8;
            end
            //QDR4TO1
            7'h10 : begin
                dig_mode = 7'h1;
                ana_mode = 6'h10;
            end
            //ODR4TO1
            7'h20 : begin
                dig_mode = 7'h2;
                ana_mode = 6'h20;
            end
            //BSCAN
            7'h40 : begin
                dig_mode = 7'h40;
                ana_mode = 6'h1;
            end
            //SDR
            default: begin
                dig_mode = 7'h1;
                ana_mode = 6'h1;
            end
        endcase

        if((byte_sel == DQ0 ) || (byte_sel == DQ_ALL) || (byte_sel == ALL)) begin
            case(dq)
                {8'd0} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_EGRESS_ANA_M1_CFG_0, ana_mode);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_EGRESS_DIG_M1_CFG_0, dig_mode);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_EGRESS_ANA_M1_CFG_0, ana_mode);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_EGRESS_DIG_M1_CFG_0, dig_mode);
                end
                {8'd1} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_EGRESS_ANA_M1_CFG_1, ana_mode);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_EGRESS_DIG_M1_CFG_1, dig_mode);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_EGRESS_ANA_M1_CFG_1, ana_mode);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_EGRESS_DIG_M1_CFG_1, dig_mode);
                end
                {8'd2} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_EGRESS_ANA_M1_CFG_2, ana_mode);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_EGRESS_DIG_M1_CFG_2, dig_mode);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_EGRESS_ANA_M1_CFG_2, ana_mode);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_EGRESS_DIG_M1_CFG_2, dig_mode);
                end
                {8'd3} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_EGRESS_ANA_M1_CFG_3, ana_mode);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_EGRESS_DIG_M1_CFG_3, dig_mode);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_EGRESS_ANA_M1_CFG_3, ana_mode);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_EGRESS_DIG_M1_CFG_3, dig_mode);
                end
                {8'd4} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_EGRESS_ANA_M1_CFG_4, ana_mode);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_EGRESS_DIG_M1_CFG_4, dig_mode);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_EGRESS_ANA_M1_CFG_4, ana_mode);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_EGRESS_DIG_M1_CFG_4, dig_mode);
                end
                {8'd5} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_EGRESS_ANA_M1_CFG_5, ana_mode);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_EGRESS_DIG_M1_CFG_5, dig_mode);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_EGRESS_ANA_M1_CFG_5, ana_mode);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_EGRESS_DIG_M1_CFG_5, dig_mode);
                end
                {8'd6} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_EGRESS_ANA_M1_CFG_6, ana_mode);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_EGRESS_DIG_M1_CFG_6, dig_mode);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_EGRESS_ANA_M1_CFG_6, ana_mode);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_EGRESS_DIG_M1_CFG_6, dig_mode);
                end
                {8'd7} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_EGRESS_ANA_M1_CFG_7, ana_mode);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_EGRESS_DIG_M1_CFG_7, dig_mode);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_EGRESS_ANA_M1_CFG_7, ana_mode);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_EGRESS_DIG_M1_CFG_7, dig_mode);
                end
                {8'd8} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_EGRESS_ANA_M1_CFG_8, ana_mode);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_EGRESS_DIG_M1_CFG_8, dig_mode);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_EGRESS_ANA_M1_CFG_8, ana_mode);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_EGRESS_DIG_M1_CFG_8, dig_mode);
                end
                default : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_EGRESS_ANA_M1_CFG_0, ana_mode);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_EGRESS_DIG_M1_CFG_0, dig_mode);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_EGRESS_ANA_M1_CFG_1, ana_mode);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_EGRESS_DIG_M1_CFG_1, dig_mode);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_EGRESS_ANA_M1_CFG_2, ana_mode);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_EGRESS_DIG_M1_CFG_2, dig_mode);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_EGRESS_ANA_M1_CFG_3, ana_mode);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_EGRESS_DIG_M1_CFG_3, dig_mode);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_EGRESS_ANA_M1_CFG_4, ana_mode);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_EGRESS_DIG_M1_CFG_4, dig_mode);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_EGRESS_ANA_M1_CFG_5, ana_mode);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_EGRESS_DIG_M1_CFG_5, dig_mode);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_EGRESS_ANA_M1_CFG_6, ana_mode);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_EGRESS_DIG_M1_CFG_6, dig_mode);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_EGRESS_ANA_M1_CFG_7, ana_mode);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_EGRESS_DIG_M1_CFG_7, dig_mode);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_EGRESS_ANA_M1_CFG_8, ana_mode);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_EGRESS_DIG_M1_CFG_8, dig_mode);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_EGRESS_ANA_M1_CFG_0, ana_mode);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_EGRESS_DIG_M1_CFG_0, dig_mode);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_EGRESS_ANA_M1_CFG_1, ana_mode);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_EGRESS_DIG_M1_CFG_1, dig_mode);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_EGRESS_ANA_M1_CFG_2, ana_mode);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_EGRESS_DIG_M1_CFG_2, dig_mode);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_EGRESS_ANA_M1_CFG_3, ana_mode);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_EGRESS_DIG_M1_CFG_3, dig_mode);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_EGRESS_ANA_M1_CFG_4, ana_mode);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_EGRESS_DIG_M1_CFG_4, dig_mode);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_EGRESS_ANA_M1_CFG_5, ana_mode);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_EGRESS_DIG_M1_CFG_5, dig_mode);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_EGRESS_ANA_M1_CFG_6, ana_mode);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_EGRESS_DIG_M1_CFG_6, dig_mode);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_EGRESS_ANA_M1_CFG_7, ana_mode);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_EGRESS_DIG_M1_CFG_7, dig_mode);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_EGRESS_ANA_M1_CFG_8, ana_mode);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_EGRESS_DIG_M1_CFG_8, dig_mode);
                end
            endcase
        end
        if((byte_sel == DQ1 ) || (byte_sel == DQ_ALL) || (byte_sel == ALL)) begin
            case(dq)
                {8'd0} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_EGRESS_ANA_M1_CFG_0, ana_mode);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_EGRESS_DIG_M1_CFG_0, dig_mode);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_EGRESS_ANA_M1_CFG_0, ana_mode);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_EGRESS_DIG_M1_CFG_0, dig_mode);
                end
                {8'd1} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_EGRESS_ANA_M1_CFG_1, ana_mode);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_EGRESS_DIG_M1_CFG_1, dig_mode);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_EGRESS_ANA_M1_CFG_1, ana_mode);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_EGRESS_DIG_M1_CFG_1, dig_mode);
                end
                {8'd2} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_EGRESS_ANA_M1_CFG_2, ana_mode);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_EGRESS_DIG_M1_CFG_2, dig_mode);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_EGRESS_ANA_M1_CFG_2, ana_mode);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_EGRESS_DIG_M1_CFG_2, dig_mode);
                end
                {8'd3} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_EGRESS_ANA_M1_CFG_3, ana_mode);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_EGRESS_DIG_M1_CFG_3, dig_mode);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_EGRESS_ANA_M1_CFG_3, ana_mode);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_EGRESS_DIG_M1_CFG_3, dig_mode);
                end
                {8'd4} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_EGRESS_ANA_M1_CFG_4, ana_mode);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_EGRESS_DIG_M1_CFG_4, dig_mode);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_EGRESS_ANA_M1_CFG_4, ana_mode);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_EGRESS_DIG_M1_CFG_4, dig_mode);
                end
                {8'd5} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_EGRESS_ANA_M1_CFG_5, ana_mode);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_EGRESS_DIG_M1_CFG_5, dig_mode);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_EGRESS_ANA_M1_CFG_5, ana_mode);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_EGRESS_DIG_M1_CFG_5, dig_mode);
                end
                {8'd6} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_EGRESS_ANA_M1_CFG_6, ana_mode);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_EGRESS_DIG_M1_CFG_6, dig_mode);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_EGRESS_ANA_M1_CFG_6, ana_mode);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_EGRESS_DIG_M1_CFG_6, dig_mode);
                end
                {8'd7} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_EGRESS_ANA_M1_CFG_7, ana_mode);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_EGRESS_DIG_M1_CFG_7, dig_mode);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_EGRESS_ANA_M1_CFG_7, ana_mode);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_EGRESS_DIG_M1_CFG_7, dig_mode);
                end
                {8'd8} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_EGRESS_ANA_M1_CFG_8, ana_mode);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_EGRESS_DIG_M1_CFG_8, dig_mode);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_EGRESS_ANA_M1_CFG_8, ana_mode);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_EGRESS_DIG_M1_CFG_8, dig_mode);
                end
                default : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_EGRESS_ANA_M1_CFG_0, ana_mode);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_EGRESS_DIG_M1_CFG_0, dig_mode);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_EGRESS_ANA_M1_CFG_1, ana_mode);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_EGRESS_DIG_M1_CFG_1, dig_mode);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_EGRESS_ANA_M1_CFG_2, ana_mode);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_EGRESS_DIG_M1_CFG_2, dig_mode);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_EGRESS_ANA_M1_CFG_3, ana_mode);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_EGRESS_DIG_M1_CFG_3, dig_mode);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_EGRESS_ANA_M1_CFG_4, ana_mode);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_EGRESS_DIG_M1_CFG_4, dig_mode);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_EGRESS_ANA_M1_CFG_5, ana_mode);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_EGRESS_DIG_M1_CFG_5, dig_mode);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_EGRESS_ANA_M1_CFG_6, ana_mode);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_EGRESS_DIG_M1_CFG_6, dig_mode);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_EGRESS_ANA_M1_CFG_7, ana_mode);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_EGRESS_DIG_M1_CFG_7, dig_mode);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_EGRESS_ANA_M1_CFG_8, ana_mode);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_EGRESS_DIG_M1_CFG_8, dig_mode);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_EGRESS_ANA_M1_CFG_0, ana_mode);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_EGRESS_DIG_M1_CFG_0, dig_mode);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_EGRESS_ANA_M1_CFG_1, ana_mode);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_EGRESS_DIG_M1_CFG_1, dig_mode);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_EGRESS_ANA_M1_CFG_2, ana_mode);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_EGRESS_DIG_M1_CFG_2, dig_mode);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_EGRESS_ANA_M1_CFG_3, ana_mode);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_EGRESS_DIG_M1_CFG_3, dig_mode);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_EGRESS_ANA_M1_CFG_4, ana_mode);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_EGRESS_DIG_M1_CFG_4, dig_mode);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_EGRESS_ANA_M1_CFG_5, ana_mode);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_EGRESS_DIG_M1_CFG_5, dig_mode);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_EGRESS_ANA_M1_CFG_6, ana_mode);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_EGRESS_DIG_M1_CFG_6, dig_mode);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_EGRESS_ANA_M1_CFG_7, ana_mode);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_EGRESS_DIG_M1_CFG_7, dig_mode);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_EGRESS_ANA_M1_CFG_8, ana_mode);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_EGRESS_DIG_M1_CFG_8, dig_mode);
                end
            endcase
        end
        if((byte_sel == CA) || (byte_sel == ALL)) begin
            case(dq)
                {8'd0} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_EGRESS_ANA_M1_CFG_0, ana_mode);
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_EGRESS_DIG_M1_CFG_0, dig_mode);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_EGRESS_ANA_M1_CFG_0, ana_mode);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_EGRESS_DIG_M1_CFG_0, dig_mode);
                end
                {8'd1} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_EGRESS_ANA_M1_CFG_1, ana_mode);
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_EGRESS_DIG_M1_CFG_1, dig_mode);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_EGRESS_ANA_M1_CFG_1, ana_mode);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_EGRESS_DIG_M1_CFG_1, dig_mode);
                end
                {8'd2} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_EGRESS_ANA_M1_CFG_2, ana_mode);
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_EGRESS_DIG_M1_CFG_2, dig_mode);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_EGRESS_ANA_M1_CFG_2, ana_mode);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_EGRESS_DIG_M1_CFG_2, dig_mode);
                end
                {8'd3} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_EGRESS_ANA_M1_CFG_3, ana_mode);
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_EGRESS_DIG_M1_CFG_3, dig_mode);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_EGRESS_ANA_M1_CFG_3, ana_mode);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_EGRESS_DIG_M1_CFG_3, dig_mode);
                end
                {8'd4} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_EGRESS_ANA_M1_CFG_4, ana_mode);
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_EGRESS_DIG_M1_CFG_4, dig_mode);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_EGRESS_ANA_M1_CFG_4, ana_mode);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_EGRESS_DIG_M1_CFG_4, dig_mode);
                end
                {8'd5} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_EGRESS_ANA_M1_CFG_5, ana_mode);
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_EGRESS_DIG_M1_CFG_5, dig_mode);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_EGRESS_ANA_M1_CFG_5, ana_mode);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_EGRESS_DIG_M1_CFG_5, dig_mode);
                end
                {8'd6} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_EGRESS_ANA_M1_CFG_6, ana_mode);
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_EGRESS_DIG_M1_CFG_6, dig_mode);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_EGRESS_ANA_M1_CFG_6, ana_mode);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_EGRESS_DIG_M1_CFG_6, dig_mode);
                end
                {8'd7} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_EGRESS_ANA_M1_CFG_7, ana_mode);
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_EGRESS_DIG_M1_CFG_7, dig_mode);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_EGRESS_ANA_M1_CFG_7, ana_mode);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_EGRESS_DIG_M1_CFG_7, dig_mode);
                end
                {8'd8} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_EGRESS_ANA_M1_CFG_8, ana_mode);
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_EGRESS_DIG_M1_CFG_8, dig_mode);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_EGRESS_ANA_M1_CFG_8, ana_mode);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_EGRESS_DIG_M1_CFG_8, dig_mode);
                end
                {8'd9} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_EGRESS_ANA_M1_CFG_9, ana_mode);
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_EGRESS_DIG_M1_CFG_9, dig_mode);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_EGRESS_ANA_M1_CFG_9, ana_mode);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_EGRESS_DIG_M1_CFG_9, dig_mode);
                end
                {8'd10} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_EGRESS_ANA_M1_CFG_10, ana_mode);
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_EGRESS_DIG_M1_CFG_10, dig_mode);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_EGRESS_ANA_M1_CFG_10, ana_mode);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_EGRESS_DIG_M1_CFG_10, dig_mode);
                end
                default : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_EGRESS_ANA_M1_CFG_0, ana_mode);
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_EGRESS_DIG_M1_CFG_0, dig_mode);
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_EGRESS_ANA_M1_CFG_1, ana_mode);
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_EGRESS_DIG_M1_CFG_1, dig_mode);
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_EGRESS_ANA_M1_CFG_2, ana_mode);
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_EGRESS_DIG_M1_CFG_2, dig_mode);
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_EGRESS_ANA_M1_CFG_3, ana_mode);
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_EGRESS_DIG_M1_CFG_3, dig_mode);
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_EGRESS_ANA_M1_CFG_4, ana_mode);
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_EGRESS_DIG_M1_CFG_4, dig_mode);
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_EGRESS_ANA_M1_CFG_5, ana_mode);
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_EGRESS_DIG_M1_CFG_5, dig_mode);
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_EGRESS_ANA_M1_CFG_6, ana_mode);
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_EGRESS_DIG_M1_CFG_6, dig_mode);
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_EGRESS_ANA_M1_CFG_7, ana_mode);
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_EGRESS_DIG_M1_CFG_7, dig_mode);
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_EGRESS_ANA_M1_CFG_8, ana_mode);
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_EGRESS_DIG_M1_CFG_8, dig_mode);
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_EGRESS_ANA_M1_CFG_9, ana_mode);
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_EGRESS_DIG_M1_CFG_9, dig_mode);
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_EGRESS_ANA_M1_CFG_10, ana_mode);
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_EGRESS_DIG_M1_CFG_10, dig_mode);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_EGRESS_ANA_M1_CFG_0, ana_mode);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_EGRESS_DIG_M1_CFG_0, dig_mode);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_EGRESS_ANA_M1_CFG_1, ana_mode);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_EGRESS_DIG_M1_CFG_1, dig_mode);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_EGRESS_ANA_M1_CFG_2, ana_mode);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_EGRESS_DIG_M1_CFG_2, dig_mode);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_EGRESS_ANA_M1_CFG_3, ana_mode);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_EGRESS_DIG_M1_CFG_3, dig_mode);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_EGRESS_ANA_M1_CFG_4, ana_mode);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_EGRESS_DIG_M1_CFG_4, dig_mode);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_EGRESS_ANA_M1_CFG_5, ana_mode);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_EGRESS_DIG_M1_CFG_5, dig_mode);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_EGRESS_ANA_M1_CFG_6, ana_mode);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_EGRESS_DIG_M1_CFG_6, dig_mode);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_EGRESS_ANA_M1_CFG_7, ana_mode);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_EGRESS_DIG_M1_CFG_7, dig_mode);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_EGRESS_ANA_M1_CFG_8, ana_mode);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_EGRESS_DIG_M1_CFG_8, dig_mode);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_EGRESS_ANA_M1_CFG_9, ana_mode);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_EGRESS_DIG_M1_CFG_9, dig_mode);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_EGRESS_ANA_M1_CFG_10, ana_mode);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_EGRESS_DIG_M1_CFG_10, dig_mode);
                end
            endcase
        end
    end
endtask

//task automatic set_wr_dbi;
//   input logic en;
//   input logic mode;
//   input logic pipe_en;
//   begin
//      `CSR_WRF3(DDR_CH::`u::_DQ0_OFFSET,DDR_DQ_DQ_DBI_CFG,TX_EN,TX_ONES,TX_PIPE_EN,en,mode,pipe_en);
//   end
//endtask
//
//task automatic set_rd_dbi;
//   input logic en;
//   input logic mode;
//   input logic pipe_en;
//   begin
//      `CSR_WRF3(DDR_CH::`u::_DQ0_OFFSET,DDR_DQ_DQ_DBI_CFG,RX_EN,RX_ONES,RX_PIPE_EN,en,mode,pipe_en);
//   end
//endtask

task automatic set_dq_dqs_drvr_cfg_m1;
    input byte_sel_t  byte_sel;
    input integer  dqs_freq_MHz ;
    input integer  lb_mode ;
    input integer  wck_mode ;
    input integer  se_mode ;
    input integer  termination ;
    logic [2:0] tx_impd;
    logic [2:0] rx_impd;
    logic [2:0] ovrd;
    logic ovrd_val_t;
    logic ovrd_val_c;
    logic [2:0] dq_ovrd;
    logic dq_ovrd_val;
    begin

        if(lb_mode == 1 ) begin
            tx_impd      = 3'h6;
            rx_impd      = 3'h6;
        end else if (dqs_freq_MHz >= 2136) begin
            tx_impd      = 3'h5;
            rx_impd      = 3'h5;
        end else if (dqs_freq_MHz >= 1075) begin
            tx_impd      = 3'h3;
            rx_impd      = 3'h3;
        end else begin
            tx_impd      = 3'h1;
            rx_impd      = (termination != 0) ? 3'h1 : 3'h0 ;
        end

        if(lb_mode == 1 ) begin
            ovrd_val_t  = 1'h0;
            ovrd_val_c  = 1'h0;
            ovrd        = 3'h3;
            dq_ovrd_val    = 1'h0;
            dq_ovrd        = 3'h3;
        end else if (termination == 0) begin
            ovrd_val_t  = 1'h0;
            ovrd_val_c  = 1'h1;
            ovrd        = 3'h1 ;
            dq_ovrd_val    = 1'h0;
            dq_ovrd        = 3'h0;
        end else if (termination == 1) begin
            ovrd_val_t  = 1'h0;
            ovrd_val_c  = 1'h0;
            ovrd        = tx_impd ;
            dq_ovrd_val    = 1'h0;
            dq_ovrd        = tx_impd;
        end

        case({byte_sel})
            {DQ0}: begin
                `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_IO_CMN_M1_R0_CFG, LPBK_EN, SE_MODE, lb_mode, se_mode);
                `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_IO_CMN_M1_R1_CFG, LPBK_EN, SE_MODE, lb_mode, se_mode);
                if (wck_mode == 1) begin
                    `CSR_WRF3(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_IO_M1_CFG_0, OVRD_SEL, OVRD_VAL_C, OVRD_VAL_T, ovrd, ovrd_val_c, ovrd_val_t);
                    `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_IO_M1_CFG_0, TX_IMPD, RX_IMPD, tx_impd, rx_impd );
                end else begin
                    `CSR_WRF3(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_IO_M1_CFG_1, OVRD_SEL, OVRD_VAL_C, OVRD_VAL_T, ovrd, ovrd_val_c, ovrd_val_t);
                    `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_IO_M1_CFG_1, TX_IMPD, RX_IMPD, tx_impd, rx_impd );
                end
                `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M1_CFG_0 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
                // FIXME: DQ bus HIz
                // `CSR_WRF2(DDR_CH::`u::_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M1_CFG_`i ,  TX_IMPD, RX_IMPD, tx_impd, rx_impd );
                `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M1_CFG_1 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
                // FIXME: DQ bus HIz
                // `CSR_WRF2(DDR_CH::`u::_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M1_CFG_`i ,  TX_IMPD, RX_IMPD, tx_impd, rx_impd );
                `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M1_CFG_2 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
                // FIXME: DQ bus HIz
                // `CSR_WRF2(DDR_CH::`u::_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M1_CFG_`i ,  TX_IMPD, RX_IMPD, tx_impd, rx_impd );
                `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M1_CFG_3 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
                // FIXME: DQ bus HIz
                // `CSR_WRF2(DDR_CH::`u::_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M1_CFG_`i ,  TX_IMPD, RX_IMPD, tx_impd, rx_impd );
                `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M1_CFG_4 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
                // FIXME: DQ bus HIz
                // `CSR_WRF2(DDR_CH::`u::_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M1_CFG_`i ,  TX_IMPD, RX_IMPD, tx_impd, rx_impd );
                `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M1_CFG_5 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
                // FIXME: DQ bus HIz
                // `CSR_WRF2(DDR_CH::`u::_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M1_CFG_`i ,  TX_IMPD, RX_IMPD, tx_impd, rx_impd );
                `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M1_CFG_6 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
                // FIXME: DQ bus HIz
                // `CSR_WRF2(DDR_CH::`u::_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M1_CFG_`i ,  TX_IMPD, RX_IMPD, tx_impd, rx_impd );
                `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M1_CFG_7 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
                // FIXME: DQ bus HIz
                // `CSR_WRF2(DDR_CH::`u::_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M1_CFG_`i ,  TX_IMPD, RX_IMPD, tx_impd, rx_impd );
                `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M1_CFG_8 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
                // FIXME: DQ bus HIz
                // `CSR_WRF2(DDR_CH::`u::_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M1_CFG_`i ,  TX_IMPD, RX_IMPD, tx_impd, rx_impd );
                `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_IO_CMN_M1_R0_CFG, LPBK_EN, SE_MODE, lb_mode, se_mode);
                `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_IO_CMN_M1_R1_CFG, LPBK_EN, SE_MODE, lb_mode, se_mode);
                if (wck_mode == 1) begin
                    `CSR_WRF3(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_IO_M1_CFG_0, OVRD_SEL, OVRD_VAL_C, OVRD_VAL_T, ovrd, ovrd_val_c, ovrd_val_t);
                    `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_IO_M1_CFG_0, TX_IMPD, RX_IMPD, tx_impd, rx_impd );
                end else begin
                    `CSR_WRF3(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_IO_M1_CFG_1, OVRD_SEL, OVRD_VAL_C, OVRD_VAL_T, ovrd, ovrd_val_c, ovrd_val_t);
                    `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_IO_M1_CFG_1, TX_IMPD, RX_IMPD, tx_impd, rx_impd );
                end
                `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M1_CFG_0 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
                // FIXME: DQ bus HIz
                // `CSR_WRF2(DDR_CH::`u::_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M1_CFG_`i ,  TX_IMPD, RX_IMPD, tx_impd, rx_impd );
                `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M1_CFG_1 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
                // FIXME: DQ bus HIz
                // `CSR_WRF2(DDR_CH::`u::_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M1_CFG_`i ,  TX_IMPD, RX_IMPD, tx_impd, rx_impd );
                `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M1_CFG_2 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
                // FIXME: DQ bus HIz
                // `CSR_WRF2(DDR_CH::`u::_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M1_CFG_`i ,  TX_IMPD, RX_IMPD, tx_impd, rx_impd );
                `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M1_CFG_3 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
                // FIXME: DQ bus HIz
                // `CSR_WRF2(DDR_CH::`u::_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M1_CFG_`i ,  TX_IMPD, RX_IMPD, tx_impd, rx_impd );
                `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M1_CFG_4 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
                // FIXME: DQ bus HIz
                // `CSR_WRF2(DDR_CH::`u::_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M1_CFG_`i ,  TX_IMPD, RX_IMPD, tx_impd, rx_impd );
                `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M1_CFG_5 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
                // FIXME: DQ bus HIz
                // `CSR_WRF2(DDR_CH::`u::_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M1_CFG_`i ,  TX_IMPD, RX_IMPD, tx_impd, rx_impd );
                `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M1_CFG_6 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
                // FIXME: DQ bus HIz
                // `CSR_WRF2(DDR_CH::`u::_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M1_CFG_`i ,  TX_IMPD, RX_IMPD, tx_impd, rx_impd );
                `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M1_CFG_7 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
                // FIXME: DQ bus HIz
                // `CSR_WRF2(DDR_CH::`u::_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M1_CFG_`i ,  TX_IMPD, RX_IMPD, tx_impd, rx_impd );
                `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M1_CFG_8 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
                // FIXME: DQ bus HIz
                // `CSR_WRF2(DDR_CH::`u::_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M1_CFG_`i ,  TX_IMPD, RX_IMPD, tx_impd, rx_impd );
            end
            {DQ1}: begin
                `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_IO_CMN_M1_R0_CFG, LPBK_EN, SE_MODE, lb_mode, se_mode);
                `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_IO_CMN_M1_R1_CFG, LPBK_EN, SE_MODE, lb_mode, se_mode);
                if (wck_mode == 1) begin
                    `CSR_WRF3(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_IO_M1_CFG_0, OVRD_SEL, OVRD_VAL_C, OVRD_VAL_T, ovrd, ovrd_val_c, ovrd_val_t);
                    `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_IO_M1_CFG_0, TX_IMPD, RX_IMPD, tx_impd, rx_impd );
                end else begin
                    `CSR_WRF3(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_IO_M1_CFG_1, OVRD_SEL, OVRD_VAL_C, OVRD_VAL_T, ovrd, ovrd_val_c, ovrd_val_t);
                    `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_IO_M1_CFG_1, TX_IMPD, RX_IMPD, tx_impd, rx_impd );
                end
                `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M1_CFG_0 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
                //`CSR_WRF2(DDR_CH::`u::_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M1_CFG_`i ,  TX_IMPD, RX_IMPD, tx_impd, rx_impd );
                `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M1_CFG_1 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
                //`CSR_WRF2(DDR_CH::`u::_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M1_CFG_`i ,  TX_IMPD, RX_IMPD, tx_impd, rx_impd );
                `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M1_CFG_2 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
                //`CSR_WRF2(DDR_CH::`u::_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M1_CFG_`i ,  TX_IMPD, RX_IMPD, tx_impd, rx_impd );
                `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M1_CFG_3 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
                //`CSR_WRF2(DDR_CH::`u::_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M1_CFG_`i ,  TX_IMPD, RX_IMPD, tx_impd, rx_impd );
                `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M1_CFG_4 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
                //`CSR_WRF2(DDR_CH::`u::_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M1_CFG_`i ,  TX_IMPD, RX_IMPD, tx_impd, rx_impd );
                `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M1_CFG_5 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
                //`CSR_WRF2(DDR_CH::`u::_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M1_CFG_`i ,  TX_IMPD, RX_IMPD, tx_impd, rx_impd );
                `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M1_CFG_6 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
                //`CSR_WRF2(DDR_CH::`u::_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M1_CFG_`i ,  TX_IMPD, RX_IMPD, tx_impd, rx_impd );
                `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M1_CFG_7 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
                //`CSR_WRF2(DDR_CH::`u::_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M1_CFG_`i ,  TX_IMPD, RX_IMPD, tx_impd, rx_impd );
                `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M1_CFG_8 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
                //`CSR_WRF2(DDR_CH::`u::_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M1_CFG_`i ,  TX_IMPD, RX_IMPD, tx_impd, rx_impd );
                `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_IO_CMN_M1_R0_CFG, LPBK_EN, SE_MODE, lb_mode, se_mode);
                `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_IO_CMN_M1_R1_CFG, LPBK_EN, SE_MODE, lb_mode, se_mode);
                if (wck_mode == 1) begin
                    `CSR_WRF3(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_IO_M1_CFG_0, OVRD_SEL, OVRD_VAL_C, OVRD_VAL_T, ovrd, ovrd_val_c, ovrd_val_t);
                    `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_IO_M1_CFG_0, TX_IMPD, RX_IMPD, tx_impd, rx_impd );
                end else begin
                    `CSR_WRF3(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_IO_M1_CFG_1, OVRD_SEL, OVRD_VAL_C, OVRD_VAL_T, ovrd, ovrd_val_c, ovrd_val_t);
                    `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_IO_M1_CFG_1, TX_IMPD, RX_IMPD, tx_impd, rx_impd );
                end
                `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M1_CFG_0 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
                //`CSR_WRF2(DDR_CH::`u::_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M1_CFG_`i ,  TX_IMPD, RX_IMPD, tx_impd, rx_impd );
                `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M1_CFG_1 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
                //`CSR_WRF2(DDR_CH::`u::_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M1_CFG_`i ,  TX_IMPD, RX_IMPD, tx_impd, rx_impd );
                `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M1_CFG_2 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
                //`CSR_WRF2(DDR_CH::`u::_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M1_CFG_`i ,  TX_IMPD, RX_IMPD, tx_impd, rx_impd );
                `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M1_CFG_3 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
                //`CSR_WRF2(DDR_CH::`u::_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M1_CFG_`i ,  TX_IMPD, RX_IMPD, tx_impd, rx_impd );
                `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M1_CFG_4 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
                //`CSR_WRF2(DDR_CH::`u::_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M1_CFG_`i ,  TX_IMPD, RX_IMPD, tx_impd, rx_impd );
                `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M1_CFG_5 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
                //`CSR_WRF2(DDR_CH::`u::_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M1_CFG_`i ,  TX_IMPD, RX_IMPD, tx_impd, rx_impd );
                `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M1_CFG_6 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
                //`CSR_WRF2(DDR_CH::`u::_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M1_CFG_`i ,  TX_IMPD, RX_IMPD, tx_impd, rx_impd );
                `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M1_CFG_7 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
                //`CSR_WRF2(DDR_CH::`u::_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M1_CFG_`i ,  TX_IMPD, RX_IMPD, tx_impd, rx_impd );
                `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M1_CFG_8 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
                //`CSR_WRF2(DDR_CH::`u::_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M1_CFG_`i ,  TX_IMPD, RX_IMPD, tx_impd, rx_impd );
            end
            {DQ_ALL}: begin
                `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_IO_CMN_M1_R0_CFG, LPBK_EN, SE_MODE, lb_mode, se_mode);
                `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_IO_CMN_M1_R1_CFG, LPBK_EN, SE_MODE, lb_mode, se_mode);
                if (wck_mode == 1) begin
                    `CSR_WRF3(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_IO_M1_CFG_0, OVRD_SEL, OVRD_VAL_C, OVRD_VAL_T, ovrd, ovrd_val_c, ovrd_val_t);
                    `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_IO_M1_CFG_0, TX_IMPD, RX_IMPD, tx_impd, rx_impd );
                end else begin
                    `CSR_WRF3(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_IO_M1_CFG_1, OVRD_SEL, OVRD_VAL_C, OVRD_VAL_T, ovrd, ovrd_val_c, ovrd_val_t);
                    `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_IO_M1_CFG_1, TX_IMPD, RX_IMPD, tx_impd, rx_impd );
                end
                `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_IO_CMN_M1_R0_CFG, LPBK_EN, SE_MODE, lb_mode, se_mode);
                `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_IO_CMN_M1_R1_CFG, LPBK_EN, SE_MODE, lb_mode, se_mode);
                if (wck_mode == 1) begin
                    `CSR_WRF3(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_IO_M1_CFG_0, OVRD_SEL, OVRD_VAL_C, OVRD_VAL_T, ovrd, ovrd_val_c, ovrd_val_t);
                    `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_IO_M1_CFG_0, TX_IMPD, RX_IMPD, tx_impd, rx_impd );
                end else begin
                    `CSR_WRF3(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_IO_M1_CFG_1, OVRD_SEL, OVRD_VAL_C, OVRD_VAL_T, ovrd, ovrd_val_c, ovrd_val_t);
                    `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_IO_M1_CFG_1, TX_IMPD, RX_IMPD, tx_impd, rx_impd );
                end
                `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M1_CFG_0 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
                //`CSR_WRF2(DDR_CH::`u::_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M1_CFG_`i ,  TX_IMPD, RX_IMPD, tx_impd, rx_impd );
                `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M1_CFG_0 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
                //`CSR_WRF2(DDR_CH::`u::_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M1_CFG_`i ,  TX_IMPD, RX_IMPD, tx_impd, rx_impd );
                `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M1_CFG_1 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
                //`CSR_WRF2(DDR_CH::`u::_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M1_CFG_`i ,  TX_IMPD, RX_IMPD, tx_impd, rx_impd );
                `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M1_CFG_1 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
                //`CSR_WRF2(DDR_CH::`u::_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M1_CFG_`i ,  TX_IMPD, RX_IMPD, tx_impd, rx_impd );
                `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M1_CFG_2 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
                //`CSR_WRF2(DDR_CH::`u::_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M1_CFG_`i ,  TX_IMPD, RX_IMPD, tx_impd, rx_impd );
                `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M1_CFG_2 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
                //`CSR_WRF2(DDR_CH::`u::_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M1_CFG_`i ,  TX_IMPD, RX_IMPD, tx_impd, rx_impd );
                `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M1_CFG_3 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
                //`CSR_WRF2(DDR_CH::`u::_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M1_CFG_`i ,  TX_IMPD, RX_IMPD, tx_impd, rx_impd );
                `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M1_CFG_3 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
                //`CSR_WRF2(DDR_CH::`u::_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M1_CFG_`i ,  TX_IMPD, RX_IMPD, tx_impd, rx_impd );
                `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M1_CFG_4 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
                //`CSR_WRF2(DDR_CH::`u::_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M1_CFG_`i ,  TX_IMPD, RX_IMPD, tx_impd, rx_impd );
                `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M1_CFG_4 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
                //`CSR_WRF2(DDR_CH::`u::_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M1_CFG_`i ,  TX_IMPD, RX_IMPD, tx_impd, rx_impd );
                `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M1_CFG_5 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
                //`CSR_WRF2(DDR_CH::`u::_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M1_CFG_`i ,  TX_IMPD, RX_IMPD, tx_impd, rx_impd );
                `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M1_CFG_5 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
                //`CSR_WRF2(DDR_CH::`u::_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M1_CFG_`i ,  TX_IMPD, RX_IMPD, tx_impd, rx_impd );
                `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M1_CFG_6 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
                //`CSR_WRF2(DDR_CH::`u::_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M1_CFG_`i ,  TX_IMPD, RX_IMPD, tx_impd, rx_impd );
                `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M1_CFG_6 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
                //`CSR_WRF2(DDR_CH::`u::_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M1_CFG_`i ,  TX_IMPD, RX_IMPD, tx_impd, rx_impd );
                `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M1_CFG_7 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
                //`CSR_WRF2(DDR_CH::`u::_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M1_CFG_`i ,  TX_IMPD, RX_IMPD, tx_impd, rx_impd );
                `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M1_CFG_7 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
                //`CSR_WRF2(DDR_CH::`u::_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M1_CFG_`i ,  TX_IMPD, RX_IMPD, tx_impd, rx_impd );
                `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M1_CFG_8 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
                //`CSR_WRF2(DDR_CH::`u::_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M1_CFG_`i ,  TX_IMPD, RX_IMPD, tx_impd, rx_impd );
                `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M1_CFG_8 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
                //`CSR_WRF2(DDR_CH::`u::_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M1_CFG_`i ,  TX_IMPD, RX_IMPD, tx_impd, rx_impd );
                `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_IO_CMN_M1_R0_CFG, LPBK_EN, SE_MODE, lb_mode, se_mode);
                `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_IO_CMN_M1_R1_CFG, LPBK_EN, SE_MODE, lb_mode, se_mode);
                if (wck_mode == 1) begin
                    `CSR_WRF3(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_IO_M1_CFG_0, OVRD_SEL, OVRD_VAL_C, OVRD_VAL_T, ovrd, ovrd_val_c, ovrd_val_t);
                    `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_IO_M1_CFG_0, TX_IMPD, RX_IMPD, tx_impd, rx_impd );
                end else begin
                    `CSR_WRF3(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_IO_M1_CFG_1, OVRD_SEL, OVRD_VAL_C, OVRD_VAL_T, ovrd, ovrd_val_c, ovrd_val_t);
                    `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_IO_M1_CFG_1, TX_IMPD, RX_IMPD, tx_impd, rx_impd );
                end
                `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_IO_CMN_M1_R0_CFG, LPBK_EN, SE_MODE, lb_mode, se_mode);
                `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_IO_CMN_M1_R1_CFG, LPBK_EN, SE_MODE, lb_mode, se_mode);
                if (wck_mode == 1) begin
                    `CSR_WRF3(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_IO_M1_CFG_0, OVRD_SEL, OVRD_VAL_C, OVRD_VAL_T, ovrd, ovrd_val_c, ovrd_val_t);
                    `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_IO_M1_CFG_0, TX_IMPD, RX_IMPD, tx_impd, rx_impd );
                end else begin
                    `CSR_WRF3(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_IO_M1_CFG_1, OVRD_SEL, OVRD_VAL_C, OVRD_VAL_T, ovrd, ovrd_val_c, ovrd_val_t);
                    `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_IO_M1_CFG_1, TX_IMPD, RX_IMPD, tx_impd, rx_impd );
                end
                `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M1_CFG_0 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
                //`CSR_WRF2(DDR_CH::`u::_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M1_CFG_`i ,  TX_IMPD, RX_IMPD, tx_impd, rx_impd );
                `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M1_CFG_0 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
                //`CSR_WRF2(DDR_CH::`u::_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M1_CFG_`i ,  TX_IMPD, RX_IMPD, tx_impd, rx_impd );
                `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M1_CFG_1 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
                //`CSR_WRF2(DDR_CH::`u::_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M1_CFG_`i ,  TX_IMPD, RX_IMPD, tx_impd, rx_impd );
                `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M1_CFG_1 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
                //`CSR_WRF2(DDR_CH::`u::_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M1_CFG_`i ,  TX_IMPD, RX_IMPD, tx_impd, rx_impd );
                `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M1_CFG_2 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
                //`CSR_WRF2(DDR_CH::`u::_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M1_CFG_`i ,  TX_IMPD, RX_IMPD, tx_impd, rx_impd );
                `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M1_CFG_2 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
                //`CSR_WRF2(DDR_CH::`u::_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M1_CFG_`i ,  TX_IMPD, RX_IMPD, tx_impd, rx_impd );
                `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M1_CFG_3 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
                //`CSR_WRF2(DDR_CH::`u::_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M1_CFG_`i ,  TX_IMPD, RX_IMPD, tx_impd, rx_impd );
                `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M1_CFG_3 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
                //`CSR_WRF2(DDR_CH::`u::_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M1_CFG_`i ,  TX_IMPD, RX_IMPD, tx_impd, rx_impd );
                `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M1_CFG_4 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
                //`CSR_WRF2(DDR_CH::`u::_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M1_CFG_`i ,  TX_IMPD, RX_IMPD, tx_impd, rx_impd );
                `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M1_CFG_4 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
                //`CSR_WRF2(DDR_CH::`u::_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M1_CFG_`i ,  TX_IMPD, RX_IMPD, tx_impd, rx_impd );
                `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M1_CFG_5 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
                //`CSR_WRF2(DDR_CH::`u::_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M1_CFG_`i ,  TX_IMPD, RX_IMPD, tx_impd, rx_impd );
                `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M1_CFG_5 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
                //`CSR_WRF2(DDR_CH::`u::_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M1_CFG_`i ,  TX_IMPD, RX_IMPD, tx_impd, rx_impd );
                `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M1_CFG_6 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
                //`CSR_WRF2(DDR_CH::`u::_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M1_CFG_`i ,  TX_IMPD, RX_IMPD, tx_impd, rx_impd );
                `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M1_CFG_6 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
                //`CSR_WRF2(DDR_CH::`u::_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M1_CFG_`i ,  TX_IMPD, RX_IMPD, tx_impd, rx_impd );
                `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M1_CFG_7 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
                //`CSR_WRF2(DDR_CH::`u::_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M1_CFG_`i ,  TX_IMPD, RX_IMPD, tx_impd, rx_impd );
                `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M1_CFG_7 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
                //`CSR_WRF2(DDR_CH::`u::_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M1_CFG_`i ,  TX_IMPD, RX_IMPD, tx_impd, rx_impd );
                `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M1_CFG_8 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
                //`CSR_WRF2(DDR_CH::`u::_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M1_CFG_`i ,  TX_IMPD, RX_IMPD, tx_impd, rx_impd );
                `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M1_CFG_8 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
                //`CSR_WRF2(DDR_CH::`u::_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M1_CFG_`i ,  TX_IMPD, RX_IMPD, tx_impd, rx_impd );
            end
        endcase

    end
endtask

task automatic set_dq_dqs_rcvr_cfg_m1;
    input byte_sel_t  byte_sel;
    input rank_sel_t  rank_sel;
    input integer  dqs_freq_MHz ;
    input integer  dly_ps ;
    logic [2:0] fb_en;
    logic se_mode;
    logic dcpath_en;
    integer dly;
    begin

        if (dqs_freq_MHz <=1075) begin
            se_mode   = 1'b0;
            dcpath_en = 1'b0;
            dly       = (((dly_ps < 150) ? 150 : dly_ps) - 150)*100/85;
            fb_en     = 3'b010;
        end
        else begin
            se_mode   = 1'b0;
            dcpath_en = 1'b0;
            dly       = (((dly_ps < 20) ? 20 : dly_ps) - 20)*100/85;
            fb_en     = 3'b110;
        end
        case({rank_sel,byte_sel})
            {RANK0,DQ0}: begin
                `CSR_WRF3(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_RX_IO_CMN_M1_R0_CFG, FB_EN, DCPATH_EN, SE_MODE, fb_en, dcpath_en, se_mode);
                `CSR_WRF3(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_RX_IO_CMN_M1_R0_CFG, FB_EN, DCPATH_EN, SE_MODE, fb_en, dcpath_en, se_mode);
            end
            {RANK1,DQ0}: begin
                `CSR_WRF3(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_RX_IO_CMN_M1_R1_CFG, FB_EN, DCPATH_EN, SE_MODE, fb_en, dcpath_en, se_mode);
                `CSR_WRF3(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_RX_IO_CMN_M1_R1_CFG, FB_EN, DCPATH_EN, SE_MODE, fb_en, dcpath_en, se_mode);
            end
            {RANK_ALL,DQ0}: begin
                `CSR_WRF3(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_RX_IO_CMN_M1_R0_CFG, FB_EN, DCPATH_EN, SE_MODE, fb_en, dcpath_en, se_mode);
                `CSR_WRF3(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_RX_IO_CMN_M1_R1_CFG, FB_EN, DCPATH_EN, SE_MODE, fb_en, dcpath_en, se_mode);
                `CSR_WRF3(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_RX_IO_CMN_M1_R0_CFG, FB_EN, DCPATH_EN, SE_MODE, fb_en, dcpath_en, se_mode);
                `CSR_WRF3(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_RX_IO_CMN_M1_R1_CFG, FB_EN, DCPATH_EN, SE_MODE, fb_en, dcpath_en, se_mode);
            end
            {RANK0,DQ1}: begin
                `CSR_WRF3(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_RX_IO_CMN_M1_R0_CFG, FB_EN, DCPATH_EN, SE_MODE, fb_en, dcpath_en, se_mode);
                `CSR_WRF3(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_RX_IO_CMN_M1_R0_CFG, FB_EN, DCPATH_EN, SE_MODE, fb_en, dcpath_en, se_mode);
            end
            {RANK1,DQ1}: begin
                `CSR_WRF3(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_RX_IO_CMN_M1_R1_CFG, FB_EN, DCPATH_EN, SE_MODE, fb_en, dcpath_en, se_mode);
                `CSR_WRF3(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_RX_IO_CMN_M1_R1_CFG, FB_EN, DCPATH_EN, SE_MODE, fb_en, dcpath_en, se_mode);
            end
            {RANK_ALL,DQ1}: begin
                `CSR_WRF3(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_RX_IO_CMN_M1_R0_CFG, FB_EN, DCPATH_EN, SE_MODE, fb_en, dcpath_en, se_mode);
                `CSR_WRF3(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_RX_IO_CMN_M1_R1_CFG, FB_EN, DCPATH_EN, SE_MODE, fb_en, dcpath_en, se_mode);
                `CSR_WRF3(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_RX_IO_CMN_M1_R0_CFG, FB_EN, DCPATH_EN, SE_MODE, fb_en, dcpath_en, se_mode);
                `CSR_WRF3(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_RX_IO_CMN_M1_R1_CFG, FB_EN, DCPATH_EN, SE_MODE, fb_en, dcpath_en, se_mode);
            end
            {RANK0,DQ_ALL}: begin
                `CSR_WRF3(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_RX_IO_CMN_M1_R0_CFG, FB_EN, DCPATH_EN, SE_MODE, fb_en, dcpath_en, se_mode);
                `CSR_WRF3(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_RX_IO_CMN_M1_R0_CFG, FB_EN, DCPATH_EN, SE_MODE, fb_en, dcpath_en, se_mode);
                `CSR_WRF3(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_RX_IO_CMN_M1_R0_CFG, FB_EN, DCPATH_EN, SE_MODE, fb_en, dcpath_en, se_mode);
                `CSR_WRF3(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_RX_IO_CMN_M1_R0_CFG, FB_EN, DCPATH_EN, SE_MODE, fb_en, dcpath_en, se_mode);
            end
            {RANK1,DQ_ALL}: begin
                `CSR_WRF3(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_RX_IO_CMN_M1_R1_CFG, FB_EN, DCPATH_EN, SE_MODE, fb_en, dcpath_en, se_mode);
                `CSR_WRF3(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_RX_IO_CMN_M1_R1_CFG, FB_EN, DCPATH_EN, SE_MODE, fb_en, dcpath_en, se_mode);
                `CSR_WRF3(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_RX_IO_CMN_M1_R1_CFG, FB_EN, DCPATH_EN, SE_MODE, fb_en, dcpath_en, se_mode);
                `CSR_WRF3(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_RX_IO_CMN_M1_R1_CFG, FB_EN, DCPATH_EN, SE_MODE, fb_en, dcpath_en, se_mode);
            end
            {RANK_ALL,DQ_ALL}: begin
                `CSR_WRF3(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_RX_IO_CMN_M1_R0_CFG, FB_EN, DCPATH_EN, SE_MODE, fb_en, dcpath_en, se_mode);
                `CSR_WRF3(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_RX_IO_CMN_M1_R1_CFG, FB_EN, DCPATH_EN, SE_MODE, fb_en, dcpath_en, se_mode);
                `CSR_WRF3(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_RX_IO_CMN_M1_R0_CFG, FB_EN, DCPATH_EN, SE_MODE, fb_en, dcpath_en, se_mode);
                `CSR_WRF3(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_RX_IO_CMN_M1_R1_CFG, FB_EN, DCPATH_EN, SE_MODE, fb_en, dcpath_en, se_mode);
                `CSR_WRF3(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_RX_IO_CMN_M1_R0_CFG, FB_EN, DCPATH_EN, SE_MODE, fb_en, dcpath_en, se_mode);
                `CSR_WRF3(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_RX_IO_CMN_M1_R1_CFG, FB_EN, DCPATH_EN, SE_MODE, fb_en, dcpath_en, se_mode);
                `CSR_WRF3(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_RX_IO_CMN_M1_R0_CFG, FB_EN, DCPATH_EN, SE_MODE, fb_en, dcpath_en, se_mode);
                `CSR_WRF3(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_RX_IO_CMN_M1_R1_CFG, FB_EN, DCPATH_EN, SE_MODE, fb_en, dcpath_en, se_mode);
            end
        endcase
        case({rank_sel,byte_sel})
            {RANK0,DQ0}: begin
                `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_RX_IO_M1_R0_CFG_1,DLY_CTRL_T, DLY_CTRL_C, dly , dly);
                `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_RX_IO_M1_R0_CFG_1,DLY_CTRL_T, DLY_CTRL_C, dly , dly);
            end
            {RANK1,DQ0}: begin
                `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_RX_IO_M1_R1_CFG_1,DLY_CTRL_T, DLY_CTRL_C, dly, dly);
                `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_RX_IO_M1_R1_CFG_1,DLY_CTRL_T, DLY_CTRL_C, dly, dly);
            end
            {RANK_ALL,DQ0}: begin
                `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_RX_IO_M1_R0_CFG_1,DLY_CTRL_T, DLY_CTRL_C, dly, dly);
                `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_RX_IO_M1_R1_CFG_1,DLY_CTRL_T, DLY_CTRL_C, dly, dly);
                `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_RX_IO_M1_R0_CFG_1,DLY_CTRL_T, DLY_CTRL_C, dly, dly);
                `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_RX_IO_M1_R1_CFG_1,DLY_CTRL_T, DLY_CTRL_C, dly, dly);
            end
            {RANK0,DQ1}: begin
                `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_RX_IO_M1_R0_CFG_1,DLY_CTRL_T, DLY_CTRL_C, dly, dly);
                `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_RX_IO_M1_R0_CFG_1,DLY_CTRL_T, DLY_CTRL_C, dly, dly);
            end
            {RANK1,DQ1}: begin
                `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_RX_IO_M1_R1_CFG_1,DLY_CTRL_T, DLY_CTRL_C, dly, dly);
                `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_RX_IO_M1_R1_CFG_1,DLY_CTRL_T, DLY_CTRL_C, dly, dly);
            end
            {RANK_ALL,DQ1}: begin
                `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_RX_IO_M1_R0_CFG_1,DLY_CTRL_T, DLY_CTRL_C, dly, dly);
                `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_RX_IO_M1_R1_CFG_1,DLY_CTRL_T, DLY_CTRL_C, dly, dly);
                `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_RX_IO_M1_R0_CFG_1,DLY_CTRL_T, DLY_CTRL_C, dly, dly);
                `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_RX_IO_M1_R1_CFG_1,DLY_CTRL_T, DLY_CTRL_C, dly, dly);
            end
            {RANK0,DQ_ALL}: begin
                `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_RX_IO_M1_R0_CFG_1,DLY_CTRL_T, DLY_CTRL_C, dly, dly);
                `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_RX_IO_M1_R0_CFG_1,DLY_CTRL_T, DLY_CTRL_C, dly, dly);
                `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_RX_IO_M1_R0_CFG_1,DLY_CTRL_T, DLY_CTRL_C, dly, dly);
                `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_RX_IO_M1_R0_CFG_1,DLY_CTRL_T, DLY_CTRL_C, dly, dly);
            end
            {RANK1,DQ_ALL}: begin
                `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_RX_IO_M1_R1_CFG_1,DLY_CTRL_T, DLY_CTRL_C, dly, dly);
                `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_RX_IO_M1_R1_CFG_1,DLY_CTRL_T, DLY_CTRL_C, dly, dly);
                `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_RX_IO_M1_R1_CFG_1,DLY_CTRL_T, DLY_CTRL_C, dly, dly);
                `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_RX_IO_M1_R1_CFG_1,DLY_CTRL_T, DLY_CTRL_C, dly, dly);
            end
            {RANK_ALL,DQ_ALL}: begin
                `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_RX_IO_M1_R0_CFG_1,DLY_CTRL_T, DLY_CTRL_C, dly, dly);
                `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_RX_IO_M1_R1_CFG_1,DLY_CTRL_T, DLY_CTRL_C, dly, dly);
                `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_RX_IO_M1_R0_CFG_1,DLY_CTRL_T, DLY_CTRL_C, dly, dly);
                `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_RX_IO_M1_R1_CFG_1,DLY_CTRL_T, DLY_CTRL_C, dly, dly);
                `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_RX_IO_M1_R0_CFG_1,DLY_CTRL_T, DLY_CTRL_C, dly, dly);
                `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_RX_IO_M1_R1_CFG_1,DLY_CTRL_T, DLY_CTRL_C, dly, dly);
                `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_RX_IO_M1_R0_CFG_1,DLY_CTRL_T, DLY_CTRL_C, dly, dly);
                `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_RX_IO_M1_R1_CFG_1,DLY_CTRL_T, DLY_CTRL_C, dly, dly);
            end
        endcase
    end
endtask

task automatic set_rdqs_dly_m1;
    input byte_sel_t  byte_sel;
    input rank_sel_t  rank_sel;
    input logic [7:0] r0_tdly;
    input logic [7:0] r0_cdly;
    input logic [7:0] r1_tdly;
    input logic [7:0] r1_cdly;
    begin
        case({rank_sel,byte_sel})
            {RANK0,DQ0}: begin
                `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_RX_IO_M1_R0_CFG_1,DLY_CTRL_T, DLY_CTRL_C, r0_tdly, r0_cdly);
                `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_RX_IO_M1_R0_CFG_1,DLY_CTRL_T, DLY_CTRL_C, r0_tdly, r0_cdly);
            end
            {RANK1,DQ0}: begin
                `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_RX_IO_M1_R1_CFG_1,DLY_CTRL_T, DLY_CTRL_C, r1_tdly, r1_cdly);
                `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_RX_IO_M1_R1_CFG_1,DLY_CTRL_T, DLY_CTRL_C, r1_tdly, r1_cdly);
            end
            {RANK_ALL,DQ0}: begin
                `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_RX_IO_M1_R0_CFG_1,DLY_CTRL_T, DLY_CTRL_C, r0_tdly, r0_cdly);
                `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_RX_IO_M1_R1_CFG_1,DLY_CTRL_T, DLY_CTRL_C, r1_tdly, r1_cdly);
                `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_RX_IO_M1_R0_CFG_1,DLY_CTRL_T, DLY_CTRL_C, r0_tdly, r0_cdly);
                `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_RX_IO_M1_R1_CFG_1,DLY_CTRL_T, DLY_CTRL_C, r1_tdly, r1_cdly);
            end
            {RANK0,DQ1}: begin
                `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_RX_IO_M1_R0_CFG_1,DLY_CTRL_T, DLY_CTRL_C, r0_tdly, r0_cdly);
                `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_RX_IO_M1_R0_CFG_1,DLY_CTRL_T, DLY_CTRL_C, r0_tdly, r0_cdly);
            end
            {RANK1,DQ1}: begin
                `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_RX_IO_M1_R1_CFG_1,DLY_CTRL_T, DLY_CTRL_C, r1_tdly, r1_cdly);
                `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_RX_IO_M1_R1_CFG_1,DLY_CTRL_T, DLY_CTRL_C, r1_tdly, r1_cdly);
            end
            {RANK_ALL,DQ1}: begin
                `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_RX_IO_M1_R0_CFG_1,DLY_CTRL_T, DLY_CTRL_C, r0_tdly, r0_cdly);
                `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_RX_IO_M1_R1_CFG_1,DLY_CTRL_T, DLY_CTRL_C, r1_tdly, r1_cdly);
                `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_RX_IO_M1_R0_CFG_1,DLY_CTRL_T, DLY_CTRL_C, r0_tdly, r0_cdly);
                `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_RX_IO_M1_R1_CFG_1,DLY_CTRL_T, DLY_CTRL_C, r1_tdly, r1_cdly);
            end
            {RANK0,DQ_ALL}: begin
                `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_RX_IO_M1_R0_CFG_1,DLY_CTRL_T, DLY_CTRL_C, r0_tdly, r0_cdly);
                `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_RX_IO_M1_R0_CFG_1,DLY_CTRL_T, DLY_CTRL_C, r0_tdly, r0_cdly);
                `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_RX_IO_M1_R0_CFG_1,DLY_CTRL_T, DLY_CTRL_C, r0_tdly, r0_cdly);
                `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_RX_IO_M1_R0_CFG_1,DLY_CTRL_T, DLY_CTRL_C, r0_tdly, r0_cdly);
            end
            {RANK1,DQ_ALL}: begin
                `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_RX_IO_M1_R1_CFG_1,DLY_CTRL_T, DLY_CTRL_C, r1_tdly, r1_cdly);
                `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_RX_IO_M1_R1_CFG_1,DLY_CTRL_T, DLY_CTRL_C, r1_tdly, r1_cdly);
                `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_RX_IO_M1_R1_CFG_1,DLY_CTRL_T, DLY_CTRL_C, r1_tdly, r1_cdly);
                `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_RX_IO_M1_R1_CFG_1,DLY_CTRL_T, DLY_CTRL_C, r1_tdly, r1_cdly);
            end
            {RANK_ALL,DQ_ALL}: begin
                `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_RX_IO_M1_R0_CFG_1,DLY_CTRL_T, DLY_CTRL_C, r0_tdly, r0_cdly);
                `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_RX_IO_M1_R1_CFG_1,DLY_CTRL_T, DLY_CTRL_C, r1_tdly, r1_cdly);
                `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_RX_IO_M1_R0_CFG_1,DLY_CTRL_T, DLY_CTRL_C, r0_tdly, r0_cdly);
                `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_RX_IO_M1_R1_CFG_1,DLY_CTRL_T, DLY_CTRL_C, r1_tdly, r1_cdly);
                `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_RX_IO_M1_R0_CFG_1,DLY_CTRL_T, DLY_CTRL_C, r0_tdly, r0_cdly);
                `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_RX_IO_M1_R1_CFG_1,DLY_CTRL_T, DLY_CTRL_C, r1_tdly, r1_cdly);
                `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_RX_IO_M1_R0_CFG_1,DLY_CTRL_T, DLY_CTRL_C, r0_tdly, r0_cdly);
                `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_RX_IO_M1_R1_CFG_1,DLY_CTRL_T, DLY_CTRL_C, r1_tdly, r1_cdly);
            end

        endcase
    end
endtask

task automatic set_rdsdr_lpde_dly_m1;
    input byte_sel_t  byte_sel;
    input rank_sel_t  rank_sel;
    input logic[1:0] gear;
    input logic [7:0] r0_dly;
    input logic [7:0] r1_dly;
    begin
        if((byte_sel == DQ0) || (byte_sel == DQ_ALL) || (byte_sel == ALL)) begin
            case(rank_sel)
                RANK0 : begin
                    `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_RX_SDR_LPDE_M1_R0_CFG,CTRL_BIN,GEAR,r0_dly,gear);
                    `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_RX_SDR_LPDE_M1_R0_CFG,CTRL_BIN,GEAR,r0_dly,gear);
                end
                RANK1 : begin
                    `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_RX_SDR_LPDE_M1_R1_CFG,CTRL_BIN,GEAR,r1_dly,gear);
                    `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_RX_SDR_LPDE_M1_R1_CFG,CTRL_BIN,GEAR,r1_dly,gear);
                end
                RANK_ALL : begin
                    `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_RX_SDR_LPDE_M1_R0_CFG,CTRL_BIN,GEAR,r0_dly,gear);
                    `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_RX_SDR_LPDE_M1_R1_CFG,CTRL_BIN,GEAR,r1_dly,gear);
                    `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_RX_SDR_LPDE_M1_R0_CFG,CTRL_BIN,GEAR,r0_dly,gear);
                    `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_RX_SDR_LPDE_M1_R1_CFG,CTRL_BIN,GEAR,r1_dly,gear);
                end
            endcase
        end
        if((byte_sel == DQ1) || (byte_sel == DQ_ALL) || (byte_sel == ALL)) begin
            case(rank_sel)
                RANK0 : begin
                    `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_RX_SDR_LPDE_M1_R0_CFG,CTRL_BIN,GEAR,r0_dly,gear);
                    `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_RX_SDR_LPDE_M1_R0_CFG,CTRL_BIN,GEAR,r0_dly,gear);
                end
                RANK1 : begin
                    `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_RX_SDR_LPDE_M1_R1_CFG,CTRL_BIN,GEAR,r1_dly,gear);
                    `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_RX_SDR_LPDE_M1_R1_CFG,CTRL_BIN,GEAR,r1_dly,gear);
                end
                RANK_ALL : begin
                    `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_RX_SDR_LPDE_M1_R0_CFG,CTRL_BIN,GEAR,r0_dly,gear);
                    `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_RX_SDR_LPDE_M1_R1_CFG,CTRL_BIN,GEAR,r1_dly,gear);
                    `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_RX_SDR_LPDE_M1_R0_CFG,CTRL_BIN,GEAR,r0_dly,gear);
                    `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_RX_SDR_LPDE_M1_R1_CFG,CTRL_BIN,GEAR,r1_dly,gear);
                end
            endcase
        end
        if((byte_sel == CA) || (byte_sel == ALL)) begin
            case(rank_sel)
                RANK0 : begin
                    `CSR_WRF2(DDR_CH0_CA_OFFSET,DDR_CA_DQS_RX_SDR_LPDE_M1_R0_CFG,CTRL_BIN,GEAR,r0_dly,gear);
                    `CSR_WRF2(DDR_CH1_CA_OFFSET,DDR_CA_DQS_RX_SDR_LPDE_M1_R0_CFG,CTRL_BIN,GEAR,r0_dly,gear);
                end
                RANK1 : begin
                    `CSR_WRF2(DDR_CH0_CA_OFFSET,DDR_CA_DQS_RX_SDR_LPDE_M1_R1_CFG,CTRL_BIN,GEAR,r1_dly,gear);
                    `CSR_WRF2(DDR_CH1_CA_OFFSET,DDR_CA_DQS_RX_SDR_LPDE_M1_R1_CFG,CTRL_BIN,GEAR,r1_dly,gear);
                end
                RANK_ALL : begin
                    `CSR_WRF2(DDR_CH0_CA_OFFSET,DDR_CA_DQS_RX_SDR_LPDE_M1_R0_CFG,CTRL_BIN,GEAR,r0_dly,gear);
                    `CSR_WRF2(DDR_CH0_CA_OFFSET,DDR_CA_DQS_RX_SDR_LPDE_M1_R1_CFG,CTRL_BIN,GEAR,r1_dly,gear);
                    `CSR_WRF2(DDR_CH1_CA_OFFSET,DDR_CA_DQS_RX_SDR_LPDE_M1_R0_CFG,CTRL_BIN,GEAR,r0_dly,gear);
                    `CSR_WRF2(DDR_CH1_CA_OFFSET,DDR_CA_DQS_RX_SDR_LPDE_M1_R1_CFG,CTRL_BIN,GEAR,r1_dly,gear);
                end
            endcase
        end
    end
endtask

task automatic set_wrdq_lpde_dly_m1;
    input byte_sel_t  byte_sel;
    input rank_sel_t  rank_sel;
    input integer     dq;
    input logic [1:0] gear;
    input logic [7:0] r0_dly;
    input logic [7:0] r1_dly;
    begin
        if((byte_sel == DQ0) || (byte_sel == DQ_ALL) || (byte_sel == ALL)) begin
            case({rank_sel,dq})
                {RANK0,8'd0} : begin
                    `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_LPDE_M1_R0_CFG_0,CTRL_BIN,GEAR,r0_dly,gear);
                    `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_LPDE_M1_R0_CFG_0,CTRL_BIN,GEAR,r0_dly,gear);
                end
                {RANK0,8'd1} : begin
                    `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_LPDE_M1_R0_CFG_1,CTRL_BIN,GEAR,r0_dly,gear);
                    `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_LPDE_M1_R0_CFG_1,CTRL_BIN,GEAR,r0_dly,gear);
                end
                {RANK0,8'd2} : begin
                    `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_LPDE_M1_R0_CFG_2,CTRL_BIN,GEAR,r0_dly,gear);
                    `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_LPDE_M1_R0_CFG_2,CTRL_BIN,GEAR,r0_dly,gear);
                end
                {RANK0,8'd3} : begin
                    `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_LPDE_M1_R0_CFG_3,CTRL_BIN,GEAR,r0_dly,gear);
                    `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_LPDE_M1_R0_CFG_3,CTRL_BIN,GEAR,r0_dly,gear);
                end
                {RANK0,8'd4} : begin
                    `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_LPDE_M1_R0_CFG_4,CTRL_BIN,GEAR,r0_dly,gear);
                    `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_LPDE_M1_R0_CFG_4,CTRL_BIN,GEAR,r0_dly,gear);
                end
                {RANK0,8'd5} : begin
                    `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_LPDE_M1_R0_CFG_5,CTRL_BIN,GEAR,r0_dly,gear);
                    `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_LPDE_M1_R0_CFG_5,CTRL_BIN,GEAR,r0_dly,gear);
                end
                {RANK0,8'd6} : begin
                    `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_LPDE_M1_R0_CFG_6,CTRL_BIN,GEAR,r0_dly,gear);
                    `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_LPDE_M1_R0_CFG_5,CTRL_BIN,GEAR,r0_dly,gear);
                end
                {RANK0,8'd6} : begin
                    `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_LPDE_M1_R0_CFG_6,CTRL_BIN,GEAR,r0_dly,gear);
                    `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_LPDE_M1_R0_CFG_6,CTRL_BIN,GEAR,r0_dly,gear);
                end
                {RANK0,8'd7} : begin
                    `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_LPDE_M1_R0_CFG_7,CTRL_BIN,GEAR,r0_dly,gear);
                    `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_LPDE_M1_R0_CFG_7,CTRL_BIN,GEAR,r0_dly,gear);
                end
                {RANK0,8'd8} : begin
                    `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_LPDE_M1_R0_CFG_8,CTRL_BIN,GEAR,r0_dly,gear);
                    `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_LPDE_M1_R0_CFG_8,CTRL_BIN,GEAR,r0_dly,gear);
                end
                {RANK1,8'd0} : begin
                    `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_LPDE_M1_R1_CFG_0,CTRL_BIN,GEAR,r1_dly,gear);
                    `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_LPDE_M1_R1_CFG_0,CTRL_BIN,GEAR,r1_dly,gear);
                end
                {RANK1,8'd1} : begin
                    `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_LPDE_M1_R1_CFG_1,CTRL_BIN,GEAR,r1_dly,gear);
                    `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_LPDE_M1_R1_CFG_1,CTRL_BIN,GEAR,r1_dly,gear);
                end
                {RANK1,8'd2} : begin
                    `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_LPDE_M1_R1_CFG_2,CTRL_BIN,GEAR,r1_dly,gear);
                    `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_LPDE_M1_R1_CFG_2,CTRL_BIN,GEAR,r1_dly,gear);
                end
                {RANK1,8'd3} : begin
                    `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_LPDE_M1_R1_CFG_3,CTRL_BIN,GEAR,r1_dly,gear);
                    `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_LPDE_M1_R1_CFG_3,CTRL_BIN,GEAR,r1_dly,gear);
                end
                {RANK1,8'd4} : begin
                    `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_LPDE_M1_R1_CFG_4,CTRL_BIN,GEAR,r1_dly,gear);
                    `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_LPDE_M1_R1_CFG_4,CTRL_BIN,GEAR,r1_dly,gear);
                end
                {RANK1,8'd5} : begin
                    `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_LPDE_M1_R1_CFG_5,CTRL_BIN,GEAR,r1_dly,gear);
                    `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_LPDE_M1_R1_CFG_5,CTRL_BIN,GEAR,r1_dly,gear);
                end
                {RANK1,8'd6} : begin
                    `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_LPDE_M1_R1_CFG_6,CTRL_BIN,GEAR,r1_dly,gear);
                    `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_LPDE_M1_R1_CFG_6,CTRL_BIN,GEAR,r1_dly,gear);
                end
                {RANK1,8'd7} : begin
                    `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_LPDE_M1_R1_CFG_7,CTRL_BIN,GEAR,r1_dly,gear);
                    `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_LPDE_M1_R1_CFG_7,CTRL_BIN,GEAR,r1_dly,gear);
                end
                {RANK1,8'd8} : begin
                    `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_LPDE_M1_R1_CFG_8,CTRL_BIN,GEAR,r1_dly,gear);
                    `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_LPDE_M1_R1_CFG_8,CTRL_BIN,GEAR,r1_dly,gear);
                end
                default : begin
                    `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_LPDE_M1_R0_CFG_0,CTRL_BIN,GEAR,r0_dly,gear);
                    `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_LPDE_M1_R0_CFG_1,CTRL_BIN,GEAR,r0_dly,gear);
                    `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_LPDE_M1_R0_CFG_2,CTRL_BIN,GEAR,r0_dly,gear);
                    `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_LPDE_M1_R0_CFG_3,CTRL_BIN,GEAR,r0_dly,gear);
                    `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_LPDE_M1_R0_CFG_4,CTRL_BIN,GEAR,r0_dly,gear);
                    `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_LPDE_M1_R0_CFG_5,CTRL_BIN,GEAR,r0_dly,gear);
                    `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_LPDE_M1_R0_CFG_6,CTRL_BIN,GEAR,r0_dly,gear);
                    `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_LPDE_M1_R0_CFG_7,CTRL_BIN,GEAR,r0_dly,gear);
                    `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_LPDE_M1_R0_CFG_8,CTRL_BIN,GEAR,r0_dly,gear);
                    `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_LPDE_M1_R0_CFG_0,CTRL_BIN,GEAR,r0_dly,gear);
                    `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_LPDE_M1_R0_CFG_1,CTRL_BIN,GEAR,r0_dly,gear);
                    `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_LPDE_M1_R0_CFG_2,CTRL_BIN,GEAR,r0_dly,gear);
                    `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_LPDE_M1_R0_CFG_3,CTRL_BIN,GEAR,r0_dly,gear);
                    `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_LPDE_M1_R0_CFG_4,CTRL_BIN,GEAR,r0_dly,gear);
                    `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_LPDE_M1_R0_CFG_5,CTRL_BIN,GEAR,r0_dly,gear);
                    `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_LPDE_M1_R0_CFG_6,CTRL_BIN,GEAR,r0_dly,gear);
                    `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_LPDE_M1_R0_CFG_7,CTRL_BIN,GEAR,r0_dly,gear);
                    `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_LPDE_M1_R0_CFG_8,CTRL_BIN,GEAR,r0_dly,gear);
                    `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_LPDE_M1_R1_CFG_0,CTRL_BIN,GEAR,r1_dly,gear);
                    `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_LPDE_M1_R1_CFG_1,CTRL_BIN,GEAR,r1_dly,gear);
                    `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_LPDE_M1_R1_CFG_2,CTRL_BIN,GEAR,r1_dly,gear);
                    `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_LPDE_M1_R1_CFG_3,CTRL_BIN,GEAR,r1_dly,gear);
                    `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_LPDE_M1_R1_CFG_4,CTRL_BIN,GEAR,r1_dly,gear);
                    `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_LPDE_M1_R1_CFG_5,CTRL_BIN,GEAR,r1_dly,gear);
                    `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_LPDE_M1_R1_CFG_6,CTRL_BIN,GEAR,r1_dly,gear);
                    `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_LPDE_M1_R1_CFG_7,CTRL_BIN,GEAR,r1_dly,gear);
                    `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_LPDE_M1_R1_CFG_8,CTRL_BIN,GEAR,r1_dly,gear);
                    `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_LPDE_M1_R1_CFG_0,CTRL_BIN,GEAR,r1_dly,gear);
                    `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_LPDE_M1_R1_CFG_1,CTRL_BIN,GEAR,r1_dly,gear);
                    `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_LPDE_M1_R1_CFG_2,CTRL_BIN,GEAR,r1_dly,gear);
                    `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_LPDE_M1_R1_CFG_3,CTRL_BIN,GEAR,r1_dly,gear);
                    `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_LPDE_M1_R1_CFG_4,CTRL_BIN,GEAR,r1_dly,gear);
                    `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_LPDE_M1_R1_CFG_5,CTRL_BIN,GEAR,r1_dly,gear);
                    `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_LPDE_M1_R1_CFG_6,CTRL_BIN,GEAR,r1_dly,gear);
                    `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_LPDE_M1_R1_CFG_7,CTRL_BIN,GEAR,r1_dly,gear);
                    `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_LPDE_M1_R1_CFG_8,CTRL_BIN,GEAR,r1_dly,gear);
                end
            endcase
        end
        if((byte_sel == DQ1) || (byte_sel == DQ_ALL) || (byte_sel == ALL)) begin
            case({rank_sel,dq})
                {RANK0,8'd0} : begin
                    `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_LPDE_M1_R0_CFG_0,CTRL_BIN,GEAR,r0_dly,gear);
                    `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_LPDE_M1_R0_CFG_0,CTRL_BIN,GEAR,r0_dly,gear);
                end
                {RANK0,8'd1} : begin
                    `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_LPDE_M1_R0_CFG_1,CTRL_BIN,GEAR,r0_dly,gear);
                    `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_LPDE_M1_R0_CFG_1,CTRL_BIN,GEAR,r0_dly,gear);
                end
                {RANK0,8'd2} : begin
                    `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_LPDE_M1_R0_CFG_2,CTRL_BIN,GEAR,r0_dly,gear);
                    `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_LPDE_M1_R0_CFG_2,CTRL_BIN,GEAR,r0_dly,gear);
                end
                {RANK0,8'd3} : begin
                    `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_LPDE_M1_R0_CFG_3,CTRL_BIN,GEAR,r0_dly,gear);
                    `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_LPDE_M1_R0_CFG_3,CTRL_BIN,GEAR,r0_dly,gear);
                end
                {RANK0,8'd4} : begin
                    `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_LPDE_M1_R0_CFG_4,CTRL_BIN,GEAR,r0_dly,gear);
                    `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_LPDE_M1_R0_CFG_4,CTRL_BIN,GEAR,r0_dly,gear);
                end
                {RANK0,8'd5} : begin
                    `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_LPDE_M1_R0_CFG_5,CTRL_BIN,GEAR,r0_dly,gear);
                    `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_LPDE_M1_R0_CFG_5,CTRL_BIN,GEAR,r0_dly,gear);
                end
                {RANK0,8'd6} : begin
                    `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_LPDE_M1_R0_CFG_6,CTRL_BIN,GEAR,r0_dly,gear);
                    `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_LPDE_M1_R0_CFG_6,CTRL_BIN,GEAR,r0_dly,gear);
                end
                {RANK0,8'd7} : begin
                    `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_LPDE_M1_R0_CFG_7,CTRL_BIN,GEAR,r0_dly,gear);
                    `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_LPDE_M1_R0_CFG_7,CTRL_BIN,GEAR,r0_dly,gear);
                end
                {RANK0,8'd8} : begin
                    `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_LPDE_M1_R0_CFG_8,CTRL_BIN,GEAR,r0_dly,gear);
                    `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_LPDE_M1_R0_CFG_8,CTRL_BIN,GEAR,r0_dly,gear);
                end
                {RANK1,8'd0} : begin
                    `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_LPDE_M1_R1_CFG_0,CTRL_BIN,GEAR,r1_dly,gear);
                    `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_LPDE_M1_R1_CFG_0,CTRL_BIN,GEAR,r1_dly,gear);
                end
                {RANK1,8'd1} : begin
                    `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_LPDE_M1_R1_CFG_1,CTRL_BIN,GEAR,r1_dly,gear);
                    `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_LPDE_M1_R1_CFG_1,CTRL_BIN,GEAR,r1_dly,gear);
                end
                {RANK1,8'd2} : begin
                    `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_LPDE_M1_R1_CFG_2,CTRL_BIN,GEAR,r1_dly,gear);
                    `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_LPDE_M1_R1_CFG_2,CTRL_BIN,GEAR,r1_dly,gear);
                end
                {RANK1,8'd3} : begin
                    `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_LPDE_M1_R1_CFG_3,CTRL_BIN,GEAR,r1_dly,gear);
                    `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_LPDE_M1_R1_CFG_3,CTRL_BIN,GEAR,r1_dly,gear);
                end
                {RANK1,8'd4} : begin
                    `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_LPDE_M1_R1_CFG_4,CTRL_BIN,GEAR,r1_dly,gear);
                    `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_LPDE_M1_R1_CFG_4,CTRL_BIN,GEAR,r1_dly,gear);
                end
                {RANK1,8'd5} : begin
                    `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_LPDE_M1_R1_CFG_5,CTRL_BIN,GEAR,r1_dly,gear);
                    `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_LPDE_M1_R1_CFG_5,CTRL_BIN,GEAR,r1_dly,gear);
                end
                {RANK1,8'd6} : begin
                    `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_LPDE_M1_R1_CFG_6,CTRL_BIN,GEAR,r1_dly,gear);
                    `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_LPDE_M1_R1_CFG_6,CTRL_BIN,GEAR,r1_dly,gear);
                end
                {RANK1,8'd7} : begin
                    `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_LPDE_M1_R1_CFG_7,CTRL_BIN,GEAR,r1_dly,gear);
                    `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_LPDE_M1_R1_CFG_7,CTRL_BIN,GEAR,r1_dly,gear);
                end
                {RANK1,8'd8} : begin
                    `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_LPDE_M1_R1_CFG_8,CTRL_BIN,GEAR,r1_dly,gear);
                    `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_LPDE_M1_R1_CFG_8,CTRL_BIN,GEAR,r1_dly,gear);
                end
                default : begin
                    `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_LPDE_M1_R0_CFG_0,CTRL_BIN,GEAR,r0_dly,gear);
                    `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_LPDE_M1_R0_CFG_1,CTRL_BIN,GEAR,r0_dly,gear);
                    `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_LPDE_M1_R0_CFG_2,CTRL_BIN,GEAR,r0_dly,gear);
                    `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_LPDE_M1_R0_CFG_3,CTRL_BIN,GEAR,r0_dly,gear);
                    `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_LPDE_M1_R0_CFG_4,CTRL_BIN,GEAR,r0_dly,gear);
                    `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_LPDE_M1_R0_CFG_5,CTRL_BIN,GEAR,r0_dly,gear);
                    `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_LPDE_M1_R0_CFG_6,CTRL_BIN,GEAR,r0_dly,gear);
                    `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_LPDE_M1_R0_CFG_7,CTRL_BIN,GEAR,r0_dly,gear);
                    `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_LPDE_M1_R0_CFG_8,CTRL_BIN,GEAR,r0_dly,gear);
                    `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_LPDE_M1_R0_CFG_0,CTRL_BIN,GEAR,r0_dly,gear);
                    `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_LPDE_M1_R0_CFG_1,CTRL_BIN,GEAR,r0_dly,gear);
                    `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_LPDE_M1_R0_CFG_2,CTRL_BIN,GEAR,r0_dly,gear);
                    `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_LPDE_M1_R0_CFG_3,CTRL_BIN,GEAR,r0_dly,gear);
                    `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_LPDE_M1_R0_CFG_4,CTRL_BIN,GEAR,r0_dly,gear);
                    `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_LPDE_M1_R0_CFG_5,CTRL_BIN,GEAR,r0_dly,gear);
                    `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_LPDE_M1_R0_CFG_6,CTRL_BIN,GEAR,r0_dly,gear);
                    `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_LPDE_M1_R0_CFG_7,CTRL_BIN,GEAR,r0_dly,gear);
                    `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_LPDE_M1_R0_CFG_8,CTRL_BIN,GEAR,r0_dly,gear);
                    `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_LPDE_M1_R1_CFG_0,CTRL_BIN,GEAR,r1_dly,gear);
                    `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_LPDE_M1_R1_CFG_1,CTRL_BIN,GEAR,r1_dly,gear);
                    `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_LPDE_M1_R1_CFG_2,CTRL_BIN,GEAR,r1_dly,gear);
                    `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_LPDE_M1_R1_CFG_3,CTRL_BIN,GEAR,r1_dly,gear);
                    `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_LPDE_M1_R1_CFG_4,CTRL_BIN,GEAR,r1_dly,gear);
                    `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_LPDE_M1_R1_CFG_5,CTRL_BIN,GEAR,r1_dly,gear);
                    `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_LPDE_M1_R1_CFG_6,CTRL_BIN,GEAR,r1_dly,gear);
                    `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_LPDE_M1_R1_CFG_7,CTRL_BIN,GEAR,r1_dly,gear);
                    `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_LPDE_M1_R1_CFG_8,CTRL_BIN,GEAR,r1_dly,gear);
                    `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_LPDE_M1_R1_CFG_0,CTRL_BIN,GEAR,r1_dly,gear);
                    `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_LPDE_M1_R1_CFG_1,CTRL_BIN,GEAR,r1_dly,gear);
                    `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_LPDE_M1_R1_CFG_2,CTRL_BIN,GEAR,r1_dly,gear);
                    `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_LPDE_M1_R1_CFG_3,CTRL_BIN,GEAR,r1_dly,gear);
                    `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_LPDE_M1_R1_CFG_4,CTRL_BIN,GEAR,r1_dly,gear);
                    `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_LPDE_M1_R1_CFG_5,CTRL_BIN,GEAR,r1_dly,gear);
                    `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_LPDE_M1_R1_CFG_6,CTRL_BIN,GEAR,r1_dly,gear);
                    `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_LPDE_M1_R1_CFG_7,CTRL_BIN,GEAR,r1_dly,gear);
                    `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_LPDE_M1_R1_CFG_8,CTRL_BIN,GEAR,r1_dly,gear);
                end
            endcase
        end
        if((byte_sel == CA) || (byte_sel == ALL)) begin
            case({rank_sel,dq})
                {RANK0,8'd0} : begin
                    `CSR_WRF2(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_LPDE_M1_R0_CFG_0,CTRL_BIN,GEAR,r0_dly,gear);
                    `CSR_WRF2(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_LPDE_M1_R0_CFG_0,CTRL_BIN,GEAR,r0_dly,gear);
                end
                {RANK0,8'd1} : begin
                    `CSR_WRF2(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_LPDE_M1_R0_CFG_1,CTRL_BIN,GEAR,r0_dly,gear);
                    `CSR_WRF2(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_LPDE_M1_R0_CFG_1,CTRL_BIN,GEAR,r0_dly,gear);
                end
                {RANK0,8'd2} : begin
                    `CSR_WRF2(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_LPDE_M1_R0_CFG_2,CTRL_BIN,GEAR,r0_dly,gear);
                    `CSR_WRF2(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_LPDE_M1_R0_CFG_2,CTRL_BIN,GEAR,r0_dly,gear);
                end
                {RANK0,8'd3} : begin
                    `CSR_WRF2(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_LPDE_M1_R0_CFG_3,CTRL_BIN,GEAR,r0_dly,gear);
                    `CSR_WRF2(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_LPDE_M1_R0_CFG_3,CTRL_BIN,GEAR,r0_dly,gear);
                end
                {RANK0,8'd4} : begin
                    `CSR_WRF2(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_LPDE_M1_R0_CFG_4,CTRL_BIN,GEAR,r0_dly,gear);
                    `CSR_WRF2(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_LPDE_M1_R0_CFG_4,CTRL_BIN,GEAR,r0_dly,gear);
                end
                {RANK0,8'd5} : begin
                    `CSR_WRF2(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_LPDE_M1_R0_CFG_5,CTRL_BIN,GEAR,r0_dly,gear);
                    `CSR_WRF2(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_LPDE_M1_R0_CFG_5,CTRL_BIN,GEAR,r0_dly,gear);
                end
                {RANK0,8'd6} : begin
                    `CSR_WRF2(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_LPDE_M1_R0_CFG_6,CTRL_BIN,GEAR,r0_dly,gear);
                    `CSR_WRF2(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_LPDE_M1_R0_CFG_6,CTRL_BIN,GEAR,r0_dly,gear);
                end
                {RANK0,8'd7} : begin
                    `CSR_WRF2(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_LPDE_M1_R0_CFG_7,CTRL_BIN,GEAR,r0_dly,gear);
                    `CSR_WRF2(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_LPDE_M1_R0_CFG_7,CTRL_BIN,GEAR,r0_dly,gear);
                end
                {RANK0,8'd8} : begin
                    `CSR_WRF2(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_LPDE_M1_R0_CFG_8,CTRL_BIN,GEAR,r0_dly,gear);
                    `CSR_WRF2(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_LPDE_M1_R0_CFG_8,CTRL_BIN,GEAR,r0_dly,gear);
                end
                {RANK0,8'd9} : begin
                    `CSR_WRF2(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_LPDE_M1_R0_CFG_9,CTRL_BIN,GEAR,r0_dly,gear);
                    `CSR_WRF2(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_LPDE_M1_R0_CFG_9,CTRL_BIN,GEAR,r0_dly,gear);
                end
                {RANK0,8'd10} : begin
                    `CSR_WRF2(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_LPDE_M1_R0_CFG_10,CTRL_BIN,GEAR,r0_dly,gear);
                    `CSR_WRF2(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_LPDE_M1_R0_CFG_10,CTRL_BIN,GEAR,r0_dly,gear);
                end
                {RANK1,8'd0} : begin
                    `CSR_WRF2(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_LPDE_M1_R1_CFG_0,CTRL_BIN,GEAR,r1_dly,gear);
                    `CSR_WRF2(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_LPDE_M1_R1_CFG_0,CTRL_BIN,GEAR,r1_dly,gear);
                end
                {RANK1,8'd1} : begin
                    `CSR_WRF2(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_LPDE_M1_R1_CFG_1,CTRL_BIN,GEAR,r1_dly,gear);
                    `CSR_WRF2(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_LPDE_M1_R1_CFG_1,CTRL_BIN,GEAR,r1_dly,gear);
                end
                {RANK1,8'd2} : begin
                    `CSR_WRF2(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_LPDE_M1_R1_CFG_2,CTRL_BIN,GEAR,r1_dly,gear);
                    `CSR_WRF2(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_LPDE_M1_R1_CFG_2,CTRL_BIN,GEAR,r1_dly,gear);
                end
                {RANK1,8'd3} : begin
                    `CSR_WRF2(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_LPDE_M1_R1_CFG_3,CTRL_BIN,GEAR,r1_dly,gear);
                    `CSR_WRF2(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_LPDE_M1_R1_CFG_3,CTRL_BIN,GEAR,r1_dly,gear);
                end
                {RANK1,8'd4} : begin
                    `CSR_WRF2(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_LPDE_M1_R1_CFG_4,CTRL_BIN,GEAR,r1_dly,gear);
                    `CSR_WRF2(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_LPDE_M1_R1_CFG_4,CTRL_BIN,GEAR,r1_dly,gear);
                end
                {RANK1,8'd5} : begin
                    `CSR_WRF2(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_LPDE_M1_R1_CFG_5,CTRL_BIN,GEAR,r1_dly,gear);
                    `CSR_WRF2(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_LPDE_M1_R1_CFG_5,CTRL_BIN,GEAR,r1_dly,gear);
                end
                {RANK1,8'd6} : begin
                    `CSR_WRF2(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_LPDE_M1_R1_CFG_6,CTRL_BIN,GEAR,r1_dly,gear);
                    `CSR_WRF2(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_LPDE_M1_R1_CFG_6,CTRL_BIN,GEAR,r1_dly,gear);
                end
                {RANK1,8'd7} : begin
                    `CSR_WRF2(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_LPDE_M1_R1_CFG_7,CTRL_BIN,GEAR,r1_dly,gear);
                    `CSR_WRF2(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_LPDE_M1_R1_CFG_7,CTRL_BIN,GEAR,r1_dly,gear);
                end
                {RANK1,8'd8} : begin
                    `CSR_WRF2(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_LPDE_M1_R1_CFG_8,CTRL_BIN,GEAR,r1_dly,gear);
                    `CSR_WRF2(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_LPDE_M1_R1_CFG_8,CTRL_BIN,GEAR,r1_dly,gear);
                end
                {RANK1,8'd9} : begin
                    `CSR_WRF2(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_LPDE_M1_R1_CFG_9,CTRL_BIN,GEAR,r1_dly,gear);
                    `CSR_WRF2(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_LPDE_M1_R1_CFG_9,CTRL_BIN,GEAR,r1_dly,gear);
                end
                {RANK1,8'd10} : begin
                    `CSR_WRF2(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_LPDE_M1_R1_CFG_10,CTRL_BIN,GEAR,r1_dly,gear);
                    `CSR_WRF2(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_LPDE_M1_R1_CFG_10,CTRL_BIN,GEAR,r1_dly,gear);
                end
                default : begin
                    `CSR_WRF2(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_LPDE_M1_R0_CFG_0,CTRL_BIN,GEAR,r0_dly,gear);
                    `CSR_WRF2(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_LPDE_M1_R0_CFG_1,CTRL_BIN,GEAR,r0_dly,gear);
                    `CSR_WRF2(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_LPDE_M1_R0_CFG_2,CTRL_BIN,GEAR,r0_dly,gear);
                    `CSR_WRF2(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_LPDE_M1_R0_CFG_3,CTRL_BIN,GEAR,r0_dly,gear);
                    `CSR_WRF2(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_LPDE_M1_R0_CFG_4,CTRL_BIN,GEAR,r0_dly,gear);
                    `CSR_WRF2(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_LPDE_M1_R0_CFG_5,CTRL_BIN,GEAR,r0_dly,gear);
                    `CSR_WRF2(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_LPDE_M1_R0_CFG_6,CTRL_BIN,GEAR,r0_dly,gear);
                    `CSR_WRF2(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_LPDE_M1_R0_CFG_7,CTRL_BIN,GEAR,r0_dly,gear);
                    `CSR_WRF2(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_LPDE_M1_R0_CFG_8,CTRL_BIN,GEAR,r0_dly,gear);
                    `CSR_WRF2(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_LPDE_M1_R0_CFG_9,CTRL_BIN,GEAR,r0_dly,gear);
                    `CSR_WRF2(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_LPDE_M1_R0_CFG_10,CTRL_BIN,GEAR,r0_dly,gear);
                    `CSR_WRF2(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_LPDE_M1_R0_CFG_0,CTRL_BIN,GEAR,r0_dly,gear);
                    `CSR_WRF2(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_LPDE_M1_R0_CFG_1,CTRL_BIN,GEAR,r0_dly,gear);
                    `CSR_WRF2(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_LPDE_M1_R0_CFG_2,CTRL_BIN,GEAR,r0_dly,gear);
                    `CSR_WRF2(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_LPDE_M1_R0_CFG_3,CTRL_BIN,GEAR,r0_dly,gear);
                    `CSR_WRF2(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_LPDE_M1_R0_CFG_4,CTRL_BIN,GEAR,r0_dly,gear);
                    `CSR_WRF2(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_LPDE_M1_R0_CFG_5,CTRL_BIN,GEAR,r0_dly,gear);
                    `CSR_WRF2(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_LPDE_M1_R0_CFG_6,CTRL_BIN,GEAR,r0_dly,gear);
                    `CSR_WRF2(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_LPDE_M1_R0_CFG_7,CTRL_BIN,GEAR,r0_dly,gear);
                    `CSR_WRF2(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_LPDE_M1_R0_CFG_8,CTRL_BIN,GEAR,r0_dly,gear);
                    `CSR_WRF2(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_LPDE_M1_R0_CFG_9,CTRL_BIN,GEAR,r0_dly,gear);
                    `CSR_WRF2(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_LPDE_M1_R0_CFG_10,CTRL_BIN,GEAR,r0_dly,gear);
                    `CSR_WRF2(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_LPDE_M1_R1_CFG_0,CTRL_BIN,GEAR,r1_dly,gear);
                    `CSR_WRF2(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_LPDE_M1_R1_CFG_1,CTRL_BIN,GEAR,r1_dly,gear);
                    `CSR_WRF2(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_LPDE_M1_R1_CFG_2,CTRL_BIN,GEAR,r1_dly,gear);
                    `CSR_WRF2(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_LPDE_M1_R1_CFG_3,CTRL_BIN,GEAR,r1_dly,gear);
                    `CSR_WRF2(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_LPDE_M1_R1_CFG_4,CTRL_BIN,GEAR,r1_dly,gear);
                    `CSR_WRF2(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_LPDE_M1_R1_CFG_5,CTRL_BIN,GEAR,r1_dly,gear);
                    `CSR_WRF2(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_LPDE_M1_R1_CFG_6,CTRL_BIN,GEAR,r1_dly,gear);
                    `CSR_WRF2(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_LPDE_M1_R1_CFG_7,CTRL_BIN,GEAR,r1_dly,gear);
                    `CSR_WRF2(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_LPDE_M1_R1_CFG_8,CTRL_BIN,GEAR,r1_dly,gear);
                    `CSR_WRF2(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_LPDE_M1_R1_CFG_9,CTRL_BIN,GEAR,r1_dly,gear);
                    `CSR_WRF2(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_LPDE_M1_R1_CFG_10,CTRL_BIN,GEAR,r1_dly,gear);
                    `CSR_WRF2(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_LPDE_M1_R1_CFG_0,CTRL_BIN,GEAR,r1_dly,gear);
                    `CSR_WRF2(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_LPDE_M1_R1_CFG_1,CTRL_BIN,GEAR,r1_dly,gear);
                    `CSR_WRF2(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_LPDE_M1_R1_CFG_2,CTRL_BIN,GEAR,r1_dly,gear);
                    `CSR_WRF2(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_LPDE_M1_R1_CFG_3,CTRL_BIN,GEAR,r1_dly,gear);
                    `CSR_WRF2(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_LPDE_M1_R1_CFG_4,CTRL_BIN,GEAR,r1_dly,gear);
                    `CSR_WRF2(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_LPDE_M1_R1_CFG_5,CTRL_BIN,GEAR,r1_dly,gear);
                    `CSR_WRF2(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_LPDE_M1_R1_CFG_6,CTRL_BIN,GEAR,r1_dly,gear);
                    `CSR_WRF2(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_LPDE_M1_R1_CFG_7,CTRL_BIN,GEAR,r1_dly,gear);
                    `CSR_WRF2(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_LPDE_M1_R1_CFG_8,CTRL_BIN,GEAR,r1_dly,gear);
                    `CSR_WRF2(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_LPDE_M1_R1_CFG_9,CTRL_BIN,GEAR,r1_dly,gear);
                    `CSR_WRF2(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_LPDE_M1_R1_CFG_10,CTRL_BIN,GEAR,r1_dly,gear);
                end
            endcase
        end
    end
endtask

task automatic set_wrdqs_lpde_dly_m1;
    input rank_sel_t  rank_sel;
    input byte_sel_t  byte_sel;
    input integer     dqs;
    input logic [1:0] gear;
    input logic [7:0] r0_dly;
    input logic [7:0] r1_dly;
    begin
        if((byte_sel == DQ0) || (byte_sel == DQ_ALL) || (byte_sel == ALL)) begin
            case({rank_sel,dqs})
                {RANK0,8'd0} : begin
                    `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_LPDE_M1_R0_CFG_0,CTRL_BIN,GEAR,r0_dly,gear);
                    `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_LPDE_M1_R0_CFG_0,CTRL_BIN,GEAR,r0_dly,gear);
                end
                {RANK0,8'd1} : begin
                    `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_LPDE_M1_R0_CFG_1,CTRL_BIN,GEAR,r0_dly,gear);
                    `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_LPDE_M1_R0_CFG_1,CTRL_BIN,GEAR,r0_dly,gear);
                end
                {RANK1,8'd0} : begin
                    `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_LPDE_M1_R1_CFG_0,CTRL_BIN,GEAR,r1_dly,gear);
                    `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_LPDE_M1_R1_CFG_0,CTRL_BIN,GEAR,r1_dly,gear);
                end
                {RANK1,8'd1} : begin
                    `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_LPDE_M1_R1_CFG_1,CTRL_BIN,GEAR,r1_dly,gear);
                    `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_LPDE_M1_R1_CFG_1,CTRL_BIN,GEAR,r1_dly,gear);
                end
                default: begin
                    `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_LPDE_M1_R0_CFG_0,CTRL_BIN,GEAR,r0_dly,gear);
                    `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_LPDE_M1_R0_CFG_1,CTRL_BIN,GEAR,r0_dly,gear);
                    `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_LPDE_M1_R1_CFG_0,CTRL_BIN,GEAR,r1_dly,gear);
                    `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_LPDE_M1_R1_CFG_1,CTRL_BIN,GEAR,r1_dly,gear);
                    `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_LPDE_M1_R0_CFG_0,CTRL_BIN,GEAR,r0_dly,gear);
                    `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_LPDE_M1_R0_CFG_1,CTRL_BIN,GEAR,r0_dly,gear);
                    `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_LPDE_M1_R1_CFG_0,CTRL_BIN,GEAR,r1_dly,gear);
                    `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_LPDE_M1_R1_CFG_1,CTRL_BIN,GEAR,r1_dly,gear);
                end
            endcase
        end
        if((byte_sel == DQ1) || (byte_sel == DQ_ALL) || (byte_sel == ALL)) begin
            case({rank_sel,dqs})
                {RANK0,8'd0} : begin
                    `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_LPDE_M1_R0_CFG_0,CTRL_BIN,GEAR,r0_dly,gear);
                    `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_LPDE_M1_R0_CFG_0,CTRL_BIN,GEAR,r0_dly,gear);
                end
                {RANK0,8'd1} : begin
                    `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_LPDE_M1_R0_CFG_1,CTRL_BIN,GEAR,r0_dly,gear);
                    `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_LPDE_M1_R0_CFG_1,CTRL_BIN,GEAR,r0_dly,gear);
                end
                {RANK1,8'd0} : begin
                    `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_LPDE_M1_R1_CFG_0,CTRL_BIN,GEAR,r1_dly,gear);
                    `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_LPDE_M1_R1_CFG_0,CTRL_BIN,GEAR,r1_dly,gear);
                end
                {RANK1,8'd1} : begin
                    `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_LPDE_M1_R1_CFG_1,CTRL_BIN,GEAR,r1_dly,gear);
                    `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_LPDE_M1_R1_CFG_1,CTRL_BIN,GEAR,r1_dly,gear);
                end
                default: begin
                    `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_LPDE_M1_R0_CFG_0,CTRL_BIN,GEAR,r0_dly,gear);
                    `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_LPDE_M1_R0_CFG_1,CTRL_BIN,GEAR,r0_dly,gear);
                    `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_LPDE_M1_R1_CFG_0,CTRL_BIN,GEAR,r1_dly,gear);
                    `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_LPDE_M1_R1_CFG_1,CTRL_BIN,GEAR,r1_dly,gear);
                    `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_LPDE_M1_R0_CFG_0,CTRL_BIN,GEAR,r0_dly,gear);
                    `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_LPDE_M1_R0_CFG_1,CTRL_BIN,GEAR,r0_dly,gear);
                    `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_LPDE_M1_R1_CFG_0,CTRL_BIN,GEAR,r1_dly,gear);
                    `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_LPDE_M1_R1_CFG_1,CTRL_BIN,GEAR,r1_dly,gear);
                end
            endcase
        end
        if((byte_sel == CA) || (byte_sel == ALL)) begin
            case({rank_sel,dqs})
                {RANK0,8'd0} : begin
                    `CSR_WRF2(DDR_CH0_CA_OFFSET,DDR_CA_DQS_TX_LPDE_M1_R0_CFG_0,CTRL_BIN,GEAR,r0_dly,gear);
                    `CSR_WRF2(DDR_CH1_CA_OFFSET,DDR_CA_DQS_TX_LPDE_M1_R0_CFG_0,CTRL_BIN,GEAR,r0_dly,gear);
                end
                {RANK1,8'd0} : begin
                    `CSR_WRF2(DDR_CH0_CA_OFFSET,DDR_CA_DQS_TX_LPDE_M1_R1_CFG_0,CTRL_BIN,GEAR,r1_dly,gear);
                    `CSR_WRF2(DDR_CH1_CA_OFFSET,DDR_CA_DQS_TX_LPDE_M1_R1_CFG_0,CTRL_BIN,GEAR,r1_dly,gear);
                end
                default: begin
                    `CSR_WRF2(DDR_CH0_CA_OFFSET,DDR_CA_DQS_TX_LPDE_M1_R0_CFG_0,CTRL_BIN,GEAR,r0_dly,gear);
                    `CSR_WRF2(DDR_CH1_CA_OFFSET,DDR_CA_DQS_TX_LPDE_M1_R0_CFG_0,CTRL_BIN,GEAR,r0_dly,gear);
                    `CSR_WRF2(DDR_CH0_CA_OFFSET,DDR_CA_DQS_TX_LPDE_M1_R1_CFG_0,CTRL_BIN,GEAR,r1_dly,gear);
                    `CSR_WRF2(DDR_CH1_CA_OFFSET,DDR_CA_DQS_TX_LPDE_M1_R1_CFG_0,CTRL_BIN,GEAR,r1_dly,gear);
                end
            endcase
        end
    end
endtask

task automatic set_tx_io_cmn_cfg_m1;
    input byte_sel_t byte_sel;
    input rank_sel_t rank_sel;
    input logic      lpbk_en;
    begin
        if((byte_sel == DQ0 ) || (byte_sel == DQ_ALL) || (byte_sel == ALL)) begin
            case(rank_sel)
                RANK0 : begin
                    `CSR_WRF1(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_IO_CMN_M1_R0_CFG,LPBK_EN,lpbk_en);
                    `CSR_WRF1(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_IO_CMN_M1_R0_CFG,LPBK_EN,lpbk_en);
                end
                RANK1 : begin
                    `CSR_WRF1(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_IO_CMN_M1_R1_CFG,LPBK_EN,lpbk_en);
                    `CSR_WRF1(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_IO_CMN_M1_R1_CFG,LPBK_EN,lpbk_en);
                end
                RANK_ALL : begin
                    `CSR_WRF1(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_IO_CMN_M1_R0_CFG,LPBK_EN,lpbk_en);
                    `CSR_WRF1(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_IO_CMN_M1_R1_CFG,LPBK_EN,lpbk_en);
                    `CSR_WRF1(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_IO_CMN_M1_R0_CFG,LPBK_EN,lpbk_en);
                    `CSR_WRF1(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_IO_CMN_M1_R1_CFG,LPBK_EN,lpbk_en);
                end
            endcase
        end
        if((byte_sel == DQ1 ) || (byte_sel == DQ_ALL) || (byte_sel == ALL)) begin
            case(rank_sel)
                RANK0 : begin
                    `CSR_WRF1(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_IO_CMN_M1_R0_CFG,LPBK_EN,lpbk_en);
                    `CSR_WRF1(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_IO_CMN_M1_R0_CFG,LPBK_EN,lpbk_en);
                end
                RANK1 : begin
                    `CSR_WRF1(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_IO_CMN_M1_R1_CFG,LPBK_EN,lpbk_en);
                    `CSR_WRF1(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_IO_CMN_M1_R1_CFG,LPBK_EN,lpbk_en);
                end
                RANK_ALL : begin
                    `CSR_WRF1(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_IO_CMN_M1_R0_CFG,LPBK_EN,lpbk_en);
                    `CSR_WRF1(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_IO_CMN_M1_R1_CFG,LPBK_EN,lpbk_en);
                    `CSR_WRF1(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_IO_CMN_M1_R0_CFG,LPBK_EN,lpbk_en);
                    `CSR_WRF1(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_IO_CMN_M1_R1_CFG,LPBK_EN,lpbk_en);
                end
            endcase
        end
        if((byte_sel == CA) || (byte_sel == ALL)) begin
            case(rank_sel)
                RANK0 : begin
                    `CSR_WRF1(DDR_CH0_CA_OFFSET,DDR_CA_DQS_TX_IO_CMN_M1_R0_CFG,LPBK_EN,lpbk_en);
                    `CSR_WRF1(DDR_CH1_CA_OFFSET,DDR_CA_DQS_TX_IO_CMN_M1_R0_CFG,LPBK_EN,lpbk_en);
                end
                RANK1 : begin
                    `CSR_WRF1(DDR_CH0_CA_OFFSET,DDR_CA_DQS_TX_IO_CMN_M1_R1_CFG,LPBK_EN,lpbk_en);
                    `CSR_WRF1(DDR_CH1_CA_OFFSET,DDR_CA_DQS_TX_IO_CMN_M1_R1_CFG,LPBK_EN,lpbk_en);
                end
                RANK_ALL : begin
                    `CSR_WRF1(DDR_CH0_CA_OFFSET,DDR_CA_DQS_TX_IO_CMN_M1_R0_CFG,LPBK_EN,lpbk_en);
                    `CSR_WRF1(DDR_CH0_CA_OFFSET,DDR_CA_DQS_TX_IO_CMN_M1_R1_CFG,LPBK_EN,lpbk_en);
                    `CSR_WRF1(DDR_CH1_CA_OFFSET,DDR_CA_DQS_TX_IO_CMN_M1_R0_CFG,LPBK_EN,lpbk_en);
                    `CSR_WRF1(DDR_CH1_CA_OFFSET,DDR_CA_DQS_TX_IO_CMN_M1_R1_CFG,LPBK_EN,lpbk_en);
                end
            endcase
        end
    end
endtask

task automatic set_tx_dqs_qdr_pi_cfg_m1;
    input byte_sel_t  byte_sel;
    input rank_sel_t  rank_sel;
    input logic       pi_sel;
    input logic       en;
    input logic [3:0] gear;
    input logic [3:0] xcpl;
    input logic [5:0] code;
    begin
        if((byte_sel == DQ0 ) || (byte_sel == DQ_ALL) || (byte_sel == ALL)) begin
            case({pi_sel, rank_sel})
                {1'b0, RANK0} : begin
                    `CSR_WRF3(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_QDR_PI_0_M1_R0_CFG,EN,CODE,GEAR,en,code,gear);
                    `CSR_WRF3(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_QDR_PI_0_M1_R0_CFG,EN,CODE,GEAR,en,code,gear);
                end
                {1'b1, RANK0} : begin
                    `CSR_WRF3(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_QDR_PI_1_M1_R0_CFG,EN,CODE,GEAR,en,code,gear);
                    `CSR_WRF3(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_QDR_PI_1_M1_R0_CFG,EN,CODE,GEAR,en,code,gear);
                end
                {1'b0, RANK1} : begin
                    `CSR_WRF3(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_QDR_PI_0_M1_R1_CFG,EN,CODE,GEAR,en,code,gear);
                    `CSR_WRF3(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_QDR_PI_0_M1_R1_CFG,EN,CODE,GEAR,en,code,gear);
                end
                {1'b1, RANK1} : begin
                    `CSR_WRF3(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_QDR_PI_1_M1_R1_CFG,EN,CODE,GEAR,en,code,gear);
                    `CSR_WRF3(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_QDR_PI_1_M1_R1_CFG,EN,CODE,GEAR,en,code,gear);
                end
                {1'b1, RANK_ALL} : begin
                    `CSR_WRF3(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_QDR_PI_1_M1_R1_CFG,EN,CODE,GEAR,en,code,gear);
                    `CSR_WRF3(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_QDR_PI_1_M1_R0_CFG,EN,CODE,GEAR,en,code,gear);
                    `CSR_WRF3(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_QDR_PI_1_M1_R1_CFG,EN,CODE,GEAR,en,code,gear);
                    `CSR_WRF3(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_QDR_PI_1_M1_R0_CFG,EN,CODE,GEAR,en,code,gear);
                end
                {1'b0, RANK_ALL} : begin
                    `CSR_WRF3(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_QDR_PI_0_M1_R1_CFG,EN,CODE,GEAR,en,code,gear);
                    `CSR_WRF3(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_QDR_PI_0_M1_R0_CFG,EN,CODE,GEAR,en,code,gear);
                    `CSR_WRF3(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_QDR_PI_0_M1_R1_CFG,EN,CODE,GEAR,en,code,gear);
                    `CSR_WRF3(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_QDR_PI_0_M1_R0_CFG,EN,CODE,GEAR,en,code,gear);
                end
            endcase
        end
        if((byte_sel == DQ1 ) || (byte_sel == DQ_ALL) || (byte_sel == ALL)) begin
            case({pi_sel, rank_sel})
                {1'b0, RANK0} : begin
                    `CSR_WRF3(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_QDR_PI_0_M1_R0_CFG,EN,CODE,GEAR,en,code,gear);
                    `CSR_WRF3(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_QDR_PI_0_M1_R0_CFG,EN,CODE,GEAR,en,code,gear);
                end
                {1'b1, RANK0} : begin
                    `CSR_WRF3(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_QDR_PI_1_M1_R0_CFG,EN,CODE,GEAR,en,code,gear);
                    `CSR_WRF3(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_QDR_PI_1_M1_R0_CFG,EN,CODE,GEAR,en,code,gear);
                end
                {1'b0, RANK1} : begin
                    `CSR_WRF3(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_QDR_PI_0_M1_R1_CFG,EN,CODE,GEAR,en,code,gear);
                    `CSR_WRF3(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_QDR_PI_0_M1_R1_CFG,EN,CODE,GEAR,en,code,gear);
                end
                {1'b1, RANK1} : begin
                    `CSR_WRF3(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_QDR_PI_1_M1_R1_CFG,EN,CODE,GEAR,en,code,gear);
                    `CSR_WRF3(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_QDR_PI_1_M1_R1_CFG,EN,CODE,GEAR,en,code,gear);
                end
                {1'b1, RANK_ALL} : begin
                    `CSR_WRF3(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_QDR_PI_1_M1_R1_CFG,EN,CODE,GEAR,en,code,gear);
                    `CSR_WRF3(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_QDR_PI_1_M1_R0_CFG,EN,CODE,GEAR,en,code,gear);
                    `CSR_WRF3(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_QDR_PI_1_M1_R1_CFG,EN,CODE,GEAR,en,code,gear);
                    `CSR_WRF3(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_QDR_PI_1_M1_R0_CFG,EN,CODE,GEAR,en,code,gear);
                end
                {1'b0, RANK_ALL} : begin
                    `CSR_WRF3(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_QDR_PI_0_M1_R1_CFG,EN,CODE,GEAR,en,code,gear);
                    `CSR_WRF3(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_QDR_PI_0_M1_R0_CFG,EN,CODE,GEAR,en,code,gear);
                    `CSR_WRF3(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_QDR_PI_0_M1_R1_CFG,EN,CODE,GEAR,en,code,gear);
                    `CSR_WRF3(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_QDR_PI_0_M1_R0_CFG,EN,CODE,GEAR,en,code,gear);
                end
            endcase
        end
        if((byte_sel == CA) || (byte_sel == ALL)) begin
            case({pi_sel, rank_sel})
                {1'b0, RANK0} : begin
                    `CSR_WRF3(DDR_CH0_CA_OFFSET,DDR_CA_DQS_TX_QDR_PI_0_M1_R0_CFG,EN,CODE,GEAR,en,code,gear);
                    `CSR_WRF3(DDR_CH1_CA_OFFSET,DDR_CA_DQS_TX_QDR_PI_0_M1_R0_CFG,EN,CODE,GEAR,en,code,gear);
                end
                {1'b1, RANK0} : begin
                    `CSR_WRF3(DDR_CH0_CA_OFFSET,DDR_CA_DQS_TX_QDR_PI_1_M1_R0_CFG,EN,CODE,GEAR,en,code,gear);
                    `CSR_WRF3(DDR_CH1_CA_OFFSET,DDR_CA_DQS_TX_QDR_PI_1_M1_R0_CFG,EN,CODE,GEAR,en,code,gear);
                end
                {1'b0, RANK1} : begin
                    `CSR_WRF3(DDR_CH0_CA_OFFSET,DDR_CA_DQS_TX_QDR_PI_0_M1_R1_CFG,EN,CODE,GEAR,en,code,gear);
                    `CSR_WRF3(DDR_CH1_CA_OFFSET,DDR_CA_DQS_TX_QDR_PI_0_M1_R1_CFG,EN,CODE,GEAR,en,code,gear);
                end
                {1'b1, RANK1} : begin
                    `CSR_WRF3(DDR_CH0_CA_OFFSET,DDR_CA_DQS_TX_QDR_PI_1_M1_R1_CFG,EN,CODE,GEAR,en,code,gear);
                    `CSR_WRF3(DDR_CH1_CA_OFFSET,DDR_CA_DQS_TX_QDR_PI_1_M1_R1_CFG,EN,CODE,GEAR,en,code,gear);
                end
                {1'b1, RANK_ALL} : begin
                    `CSR_WRF3(DDR_CH0_CA_OFFSET,DDR_CA_DQS_TX_QDR_PI_1_M1_R1_CFG,EN,CODE,GEAR,en,code,gear);
                    `CSR_WRF3(DDR_CH0_CA_OFFSET,DDR_CA_DQS_TX_QDR_PI_1_M1_R0_CFG,EN,CODE,GEAR,en,code,gear);
                    `CSR_WRF3(DDR_CH1_CA_OFFSET,DDR_CA_DQS_TX_QDR_PI_1_M1_R1_CFG,EN,CODE,GEAR,en,code,gear);
                    `CSR_WRF3(DDR_CH1_CA_OFFSET,DDR_CA_DQS_TX_QDR_PI_1_M1_R0_CFG,EN,CODE,GEAR,en,code,gear);
                end
                {1'b0, RANK_ALL} : begin
                    `CSR_WRF3(DDR_CH0_CA_OFFSET,DDR_CA_DQS_TX_QDR_PI_0_M1_R1_CFG,EN,CODE,GEAR,en,code,gear);
                    `CSR_WRF3(DDR_CH0_CA_OFFSET,DDR_CA_DQS_TX_QDR_PI_0_M1_R0_CFG,EN,CODE,GEAR,en,code,gear);
                    `CSR_WRF3(DDR_CH1_CA_OFFSET,DDR_CA_DQS_TX_QDR_PI_0_M1_R1_CFG,EN,CODE,GEAR,en,code,gear);
                    `CSR_WRF3(DDR_CH1_CA_OFFSET,DDR_CA_DQS_TX_QDR_PI_0_M1_R0_CFG,EN,CODE,GEAR,en,code,gear);
                end
            endcase
        end
    end
endtask

task automatic set_tx_dqs_ddr_pi_cfg_m1;
    input byte_sel_t  byte_sel;
    input rank_sel_t  rank_sel;
    input logic       pi_sel;
    input logic       en;
    input logic [3:0] gear;
    input logic [3:0] xcpl;
    input logic [5:0] code;
    begin
        if((byte_sel == DQ0 ) || (byte_sel == DQ_ALL) || (byte_sel == ALL)) begin
            case({pi_sel, rank_sel})
                {1'b0, RANK0} : begin
                    `CSR_WRF3(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_DDR_PI_0_M1_R0_CFG,EN,CODE,GEAR,en,code,gear);
                    `CSR_WRF3(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_DDR_PI_0_M1_R0_CFG,EN,CODE,GEAR,en,code,gear);
                end
                {1'b1, RANK0} : begin
                    `CSR_WRF3(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_DDR_PI_1_M1_R0_CFG,EN,CODE,GEAR,en,code,gear);
                    `CSR_WRF3(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_DDR_PI_1_M1_R0_CFG,EN,CODE,GEAR,en,code,gear);
                end
                {1'b0, RANK1} : begin
                    `CSR_WRF3(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_DDR_PI_0_M1_R1_CFG,EN,CODE,GEAR,en,code,gear);
                    `CSR_WRF3(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_DDR_PI_0_M1_R1_CFG,EN,CODE,GEAR,en,code,gear);
                end
                {1'b1, RANK1} : begin
                    `CSR_WRF3(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_DDR_PI_1_M1_R1_CFG,EN,CODE,GEAR,en,code,gear);
                    `CSR_WRF3(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_DDR_PI_1_M1_R1_CFG,EN,CODE,GEAR,en,code,gear);
                end
                {1'b1, RANK_ALL} : begin
                    `CSR_WRF3(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_DDR_PI_1_M1_R0_CFG,EN,CODE,GEAR,en,code,gear);
                    `CSR_WRF3(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_DDR_PI_1_M1_R1_CFG,EN,CODE,GEAR,en,code,gear);
                    `CSR_WRF3(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_DDR_PI_1_M1_R0_CFG,EN,CODE,GEAR,en,code,gear);
                    `CSR_WRF3(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_DDR_PI_1_M1_R1_CFG,EN,CODE,GEAR,en,code,gear);
                end
                {1'b0, RANK_ALL} : begin
                    `CSR_WRF3(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_DDR_PI_0_M1_R0_CFG,EN,CODE,GEAR,en,code,gear);
                    `CSR_WRF3(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_DDR_PI_0_M1_R1_CFG,EN,CODE,GEAR,en,code,gear);
                    `CSR_WRF3(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_DDR_PI_0_M1_R0_CFG,EN,CODE,GEAR,en,code,gear);
                    `CSR_WRF3(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_DDR_PI_0_M1_R1_CFG,EN,CODE,GEAR,en,code,gear);
                end
            endcase
        end
        if((byte_sel == DQ1 ) || (byte_sel == DQ_ALL) || (byte_sel == ALL)) begin
            case({pi_sel, rank_sel})
                {1'b0, RANK0} : begin
                    `CSR_WRF3(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_DDR_PI_0_M1_R0_CFG,EN,CODE,GEAR,en,code,gear);
                    `CSR_WRF3(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_DDR_PI_0_M1_R0_CFG,EN,CODE,GEAR,en,code,gear);
                end
                {1'b1, RANK0} : begin
                    `CSR_WRF3(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_DDR_PI_1_M1_R0_CFG,EN,CODE,GEAR,en,code,gear);
                    `CSR_WRF3(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_DDR_PI_1_M1_R0_CFG,EN,CODE,GEAR,en,code,gear);
                end
                {1'b0, RANK1} : begin
                    `CSR_WRF3(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_DDR_PI_0_M1_R1_CFG,EN,CODE,GEAR,en,code,gear);
                    `CSR_WRF3(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_DDR_PI_0_M1_R1_CFG,EN,CODE,GEAR,en,code,gear);
                end
                {1'b1, RANK1} : begin
                    `CSR_WRF3(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_DDR_PI_1_M1_R1_CFG,EN,CODE,GEAR,en,code,gear);
                    `CSR_WRF3(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_DDR_PI_1_M1_R1_CFG,EN,CODE,GEAR,en,code,gear);
                end
                {1'b1, RANK_ALL} : begin
                    `CSR_WRF3(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_DDR_PI_1_M1_R0_CFG,EN,CODE,GEAR,en,code,gear);
                    `CSR_WRF3(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_DDR_PI_1_M1_R1_CFG,EN,CODE,GEAR,en,code,gear);
                    `CSR_WRF3(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_DDR_PI_1_M1_R0_CFG,EN,CODE,GEAR,en,code,gear);
                    `CSR_WRF3(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_DDR_PI_1_M1_R1_CFG,EN,CODE,GEAR,en,code,gear);
                end
                {1'b0, RANK_ALL} : begin
                    `CSR_WRF3(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_DDR_PI_0_M1_R0_CFG,EN,CODE,GEAR,en,code,gear);
                    `CSR_WRF3(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_DDR_PI_0_M1_R1_CFG,EN,CODE,GEAR,en,code,gear);
                    `CSR_WRF3(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_DDR_PI_0_M1_R0_CFG,EN,CODE,GEAR,en,code,gear);
                    `CSR_WRF3(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_DDR_PI_0_M1_R1_CFG,EN,CODE,GEAR,en,code,gear);
                end
            endcase
        end
        if((byte_sel == CA) || (byte_sel == ALL)) begin
            case({pi_sel, rank_sel})
                {1'b0, RANK0} : begin
                    `CSR_WRF3(DDR_CH0_CA_OFFSET,DDR_CA_DQS_TX_DDR_PI_0_M1_R0_CFG,EN,CODE,GEAR,en,code,gear);
                    `CSR_WRF3(DDR_CH1_CA_OFFSET,DDR_CA_DQS_TX_DDR_PI_0_M1_R0_CFG,EN,CODE,GEAR,en,code,gear);
                end
                {1'b1, RANK0} : begin
                    `CSR_WRF3(DDR_CH0_CA_OFFSET,DDR_CA_DQS_TX_DDR_PI_1_M1_R0_CFG,EN,CODE,GEAR,en,code,gear);
                    `CSR_WRF3(DDR_CH1_CA_OFFSET,DDR_CA_DQS_TX_DDR_PI_1_M1_R0_CFG,EN,CODE,GEAR,en,code,gear);
                end
                {1'b0, RANK1} : begin
                    `CSR_WRF3(DDR_CH0_CA_OFFSET,DDR_CA_DQS_TX_DDR_PI_0_M1_R1_CFG,EN,CODE,GEAR,en,code,gear);
                    `CSR_WRF3(DDR_CH1_CA_OFFSET,DDR_CA_DQS_TX_DDR_PI_0_M1_R1_CFG,EN,CODE,GEAR,en,code,gear);
                end
                {1'b1, RANK1} : begin
                    `CSR_WRF3(DDR_CH0_CA_OFFSET,DDR_CA_DQS_TX_DDR_PI_1_M1_R1_CFG,EN,CODE,GEAR,en,code,gear);
                    `CSR_WRF3(DDR_CH1_CA_OFFSET,DDR_CA_DQS_TX_DDR_PI_1_M1_R1_CFG,EN,CODE,GEAR,en,code,gear);
                end
                {1'b1, RANK_ALL} : begin
                    `CSR_WRF3(DDR_CH0_CA_OFFSET,DDR_CA_DQS_TX_DDR_PI_1_M1_R0_CFG,EN,CODE,GEAR,en,code,gear);
                    `CSR_WRF3(DDR_CH0_CA_OFFSET,DDR_CA_DQS_TX_DDR_PI_1_M1_R1_CFG,EN,CODE,GEAR,en,code,gear);
                    `CSR_WRF3(DDR_CH1_CA_OFFSET,DDR_CA_DQS_TX_DDR_PI_1_M1_R0_CFG,EN,CODE,GEAR,en,code,gear);
                    `CSR_WRF3(DDR_CH1_CA_OFFSET,DDR_CA_DQS_TX_DDR_PI_1_M1_R1_CFG,EN,CODE,GEAR,en,code,gear);
                end
                {1'b0, RANK_ALL} : begin
                    `CSR_WRF3(DDR_CH0_CA_OFFSET,DDR_CA_DQS_TX_DDR_PI_0_M1_R0_CFG,EN,CODE,GEAR,en,code,gear);
                    `CSR_WRF3(DDR_CH0_CA_OFFSET,DDR_CA_DQS_TX_DDR_PI_0_M1_R1_CFG,EN,CODE,GEAR,en,code,gear);
                    `CSR_WRF3(DDR_CH1_CA_OFFSET,DDR_CA_DQS_TX_DDR_PI_0_M1_R0_CFG,EN,CODE,GEAR,en,code,gear);
                    `CSR_WRF3(DDR_CH1_CA_OFFSET,DDR_CA_DQS_TX_DDR_PI_0_M1_R1_CFG,EN,CODE,GEAR,en,code,gear);
                end
            endcase
        end
    end
endtask

task automatic set_tx_dqs_sdr_rt_pi_cfg_m1;
    input byte_sel_t  byte_sel;
    input rank_sel_t  rank_sel;
    input logic       en;
    input logic [3:0] gear;
    input logic [3:0] xcpl;
    input logic [5:0] code;
    begin
        if((byte_sel == DQ0 ) || (byte_sel == DQ_ALL) || (byte_sel == ALL)) begin
            case({rank_sel})
                {RANK0} : begin
                    `CSR_WRF3(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_PI_RT_M1_R0_CFG,EN,CODE,GEAR,en,code,gear);
                    `CSR_WRF3(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_PI_RT_M1_R0_CFG,EN,CODE,GEAR,en,code,gear);
                end
                {RANK1} : begin
                    `CSR_WRF3(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_PI_RT_M1_R1_CFG,EN,CODE,GEAR,en,code,gear);
                    `CSR_WRF3(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_PI_RT_M1_R1_CFG,EN,CODE,GEAR,en,code,gear);
                end
                {RANK_ALL} : begin
                    `CSR_WRF3(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_PI_RT_M1_R0_CFG,EN,CODE,GEAR,en,code,gear);
                    `CSR_WRF3(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_PI_RT_M1_R1_CFG,EN,CODE,GEAR,en,code,gear);
                    `CSR_WRF3(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_PI_RT_M1_R0_CFG,EN,CODE,GEAR,en,code,gear);
                    `CSR_WRF3(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_PI_RT_M1_R1_CFG,EN,CODE,GEAR,en,code,gear);
                end
            endcase
        end
        if((byte_sel == DQ1 ) || (byte_sel == DQ_ALL) || (byte_sel == ALL)) begin
            case({rank_sel})
                {RANK0} : begin
                    `CSR_WRF3(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_PI_RT_M1_R0_CFG,EN,CODE,GEAR,en,code,gear);
                    `CSR_WRF3(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_PI_RT_M1_R0_CFG,EN,CODE,GEAR,en,code,gear);
                end
                {RANK1} : begin
                    `CSR_WRF3(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_PI_RT_M1_R1_CFG,EN,CODE,GEAR,en,code,gear);
                    `CSR_WRF3(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_PI_RT_M1_R1_CFG,EN,CODE,GEAR,en,code,gear);
                end
                {RANK_ALL} : begin
                    `CSR_WRF3(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_PI_RT_M1_R0_CFG,EN,CODE,GEAR,en,code,gear);
                    `CSR_WRF3(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_PI_RT_M1_R1_CFG,EN,CODE,GEAR,en,code,gear);
                    `CSR_WRF3(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_PI_RT_M1_R0_CFG,EN,CODE,GEAR,en,code,gear);
                    `CSR_WRF3(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_PI_RT_M1_R1_CFG,EN,CODE,GEAR,en,code,gear);
                end
            endcase
        end
        if((byte_sel == CA) || (byte_sel == ALL)) begin
            case({rank_sel})
                {RANK0} : begin
                    `CSR_WRF3(DDR_CH0_CA_OFFSET,DDR_CA_DQS_TX_PI_RT_M1_R0_CFG,EN,CODE,GEAR,en,code,gear);
                    `CSR_WRF3(DDR_CH1_CA_OFFSET,DDR_CA_DQS_TX_PI_RT_M1_R0_CFG,EN,CODE,GEAR,en,code,gear);
                end
                {RANK1} : begin
                    `CSR_WRF3(DDR_CH0_CA_OFFSET,DDR_CA_DQS_TX_PI_RT_M1_R1_CFG,EN,CODE,GEAR,en,code,gear);
                    `CSR_WRF3(DDR_CH1_CA_OFFSET,DDR_CA_DQS_TX_PI_RT_M1_R1_CFG,EN,CODE,GEAR,en,code,gear);
                end
                {RANK_ALL} : begin
                    `CSR_WRF3(DDR_CH0_CA_OFFSET,DDR_CA_DQS_TX_PI_RT_M1_R0_CFG,EN,CODE,GEAR,en,code,gear);
                    `CSR_WRF3(DDR_CH0_CA_OFFSET,DDR_CA_DQS_TX_PI_RT_M1_R1_CFG,EN,CODE,GEAR,en,code,gear);
                    `CSR_WRF3(DDR_CH1_CA_OFFSET,DDR_CA_DQS_TX_PI_RT_M1_R0_CFG,EN,CODE,GEAR,en,code,gear);
                    `CSR_WRF3(DDR_CH1_CA_OFFSET,DDR_CA_DQS_TX_PI_RT_M1_R1_CFG,EN,CODE,GEAR,en,code,gear);
                end
            endcase
        end
    end
endtask

task automatic set_tx_match_pi_cfg_m1;
    input byte_sel_t  byte_sel;
    input rank_sel_t  rank_sel;
    input logic       en;
    input logic [3:0] gear;
    input logic [3:0] xcpl;
    begin
        if((byte_sel == DQ0 ) || (byte_sel == DQ_ALL) || (byte_sel == ALL)) begin
            case({rank_sel})
                {RANK0} : begin
                    `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_PI_M1_R0_CFG,EN,GEAR,en,gear);
                    `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_DFI_PI_M1_R0_CFG,EN,GEAR,en,gear);
                    `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_PI_M1_R0_CFG,EN,GEAR,en,gear);
                    `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_DFI_PI_M1_R0_CFG,EN,GEAR,en,gear);
                end
                {RANK1} : begin
                    `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_PI_M1_R1_CFG,EN,GEAR,en,gear);
                    `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_DFI_PI_M1_R1_CFG,EN,GEAR,en,gear);
                    `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_PI_M1_R1_CFG,EN,GEAR,en,gear);
                    `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_DFI_PI_M1_R1_CFG,EN,GEAR,en,gear);
                end
                {RANK_ALL} : begin
                    `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_PI_M1_R0_CFG,EN,GEAR,en,gear);
                    `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_PI_M1_R1_CFG,EN,GEAR,en,gear);
                    `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_DFI_PI_M1_R0_CFG,EN,GEAR,en,gear);
                    `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_DFI_PI_M1_R1_CFG,EN,GEAR,en,gear);
                    `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_PI_M1_R0_CFG,EN,GEAR,en,gear);
                    `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_PI_M1_R1_CFG,EN,GEAR,en,gear);
                    `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_DFI_PI_M1_R0_CFG,EN,GEAR,en,gear);
                    `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_DFI_PI_M1_R1_CFG,EN,GEAR,en,gear);
                end
            endcase
        end
        if((byte_sel == DQ1 ) || (byte_sel == DQ_ALL) || (byte_sel == ALL)) begin
            case({rank_sel})
                {RANK0} : begin
                    `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_PI_M1_R0_CFG,EN,GEAR,en,gear);
                    `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_DFI_PI_M1_R0_CFG,EN,GEAR,en,gear);
                    `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_PI_M1_R0_CFG,EN,GEAR,en,gear);
                    `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_DFI_PI_M1_R0_CFG,EN,GEAR,en,gear);
                end
                {RANK1} : begin
                    `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_PI_M1_R1_CFG,EN,GEAR,en,gear);
                    `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_DFI_PI_M1_R1_CFG,EN,GEAR,en,gear);
                    `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_PI_M1_R1_CFG,EN,GEAR,en,gear);
                    `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_DFI_PI_M1_R1_CFG,EN,GEAR,en,gear);
                end
                {RANK_ALL} : begin
                    `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_PI_M1_R0_CFG,EN,GEAR,en,gear);
                    `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_PI_M1_R1_CFG,EN,GEAR,en,gear);
                    `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_DFI_PI_M1_R0_CFG,EN,GEAR,en,gear);
                    `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_DFI_PI_M1_R1_CFG,EN,GEAR,en,gear);
                    `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_PI_M1_R0_CFG,EN,GEAR,en,gear);
                    `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_PI_M1_R1_CFG,EN,GEAR,en,gear);
                    `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_DFI_PI_M1_R0_CFG,EN,GEAR,en,gear);
                    `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_DFI_PI_M1_R1_CFG,EN,GEAR,en,gear);
                end
            endcase
        end
        if((byte_sel == CA) || (byte_sel == ALL)) begin
            case({rank_sel})
                {RANK0} : begin
                    `CSR_WRF2(DDR_CH0_CA_OFFSET,DDR_CA_DQS_TX_SDR_PI_M1_R0_CFG,EN,GEAR,en,gear);
                    `CSR_WRF2(DDR_CH0_CA_OFFSET,DDR_CA_DQS_TX_DFI_PI_M1_R0_CFG,EN,GEAR,en,gear);
                    `CSR_WRF2(DDR_CH1_CA_OFFSET,DDR_CA_DQS_TX_SDR_PI_M1_R0_CFG,EN,GEAR,en,gear);
                    `CSR_WRF2(DDR_CH1_CA_OFFSET,DDR_CA_DQS_TX_DFI_PI_M1_R0_CFG,EN,GEAR,en,gear);
                end
                {RANK1} : begin
                    `CSR_WRF2(DDR_CH0_CA_OFFSET,DDR_CA_DQS_TX_SDR_PI_M1_R1_CFG,EN,GEAR,en,gear);
                    `CSR_WRF2(DDR_CH0_CA_OFFSET,DDR_CA_DQS_TX_DFI_PI_M1_R1_CFG,EN,GEAR,en,gear);
                    `CSR_WRF2(DDR_CH1_CA_OFFSET,DDR_CA_DQS_TX_SDR_PI_M1_R1_CFG,EN,GEAR,en,gear);
                    `CSR_WRF2(DDR_CH1_CA_OFFSET,DDR_CA_DQS_TX_DFI_PI_M1_R1_CFG,EN,GEAR,en,gear);
                end
                {RANK_ALL} : begin
                    `CSR_WRF2(DDR_CH0_CA_OFFSET,DDR_CA_DQS_TX_SDR_PI_M1_R0_CFG,EN,GEAR,en,gear);
                    `CSR_WRF2(DDR_CH0_CA_OFFSET,DDR_CA_DQS_TX_SDR_PI_M1_R1_CFG,EN,GEAR,en,gear);
                    `CSR_WRF2(DDR_CH0_CA_OFFSET,DDR_CA_DQS_TX_DFI_PI_M1_R0_CFG,EN,GEAR,en,gear);
                    `CSR_WRF2(DDR_CH0_CA_OFFSET,DDR_CA_DQS_TX_DFI_PI_M1_R1_CFG,EN,GEAR,en,gear);
                    `CSR_WRF2(DDR_CH1_CA_OFFSET,DDR_CA_DQS_TX_SDR_PI_M1_R0_CFG,EN,GEAR,en,gear);
                    `CSR_WRF2(DDR_CH1_CA_OFFSET,DDR_CA_DQS_TX_SDR_PI_M1_R1_CFG,EN,GEAR,en,gear);
                    `CSR_WRF2(DDR_CH1_CA_OFFSET,DDR_CA_DQS_TX_DFI_PI_M1_R0_CFG,EN,GEAR,en,gear);
                    `CSR_WRF2(DDR_CH1_CA_OFFSET,DDR_CA_DQS_TX_DFI_PI_M1_R1_CFG,EN,GEAR,en,gear);
                end
            endcase
        end
    end
endtask

task automatic set_tx_dq_qdr_pi_cfg_m1;
    input byte_sel_t  byte_sel;
    input rank_sel_t  rank_sel;
    input logic       pi_sel;
    input logic       en;
    input logic [3:0] gear;
    input logic [3:0] xcpl;
    input logic [5:0] code;
    begin
        if((byte_sel == DQ0 ) || (byte_sel == DQ_ALL) || (byte_sel == ALL)) begin
            case({pi_sel, rank_sel})
                {1'b0, RANK0} : begin
                    `CSR_WRF4(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_PI_0_M1_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_PI_0_M1_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                end
                {1'b1, RANK0} : begin
                    `CSR_WRF4(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_PI_1_M1_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_PI_1_M1_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                end
                {1'b0, RANK1} : begin
                    `CSR_WRF4(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_PI_0_M1_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_PI_0_M1_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                end
                {1'b1, RANK1} : begin
                    `CSR_WRF4(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_PI_1_M1_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_PI_1_M1_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                end
                {1'b1, RANK_ALL} : begin
                    `CSR_WRF4(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_PI_1_M1_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_PI_1_M1_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_PI_1_M1_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_PI_1_M1_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                end
                {1'b0, RANK_ALL} : begin
                    `CSR_WRF4(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_PI_0_M1_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_PI_0_M1_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_PI_0_M1_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_PI_0_M1_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                end
            endcase
        end
        if((byte_sel == DQ1 ) || (byte_sel == DQ_ALL) || (byte_sel == ALL)) begin
            case({pi_sel, rank_sel})
                {1'b0, RANK0} : begin
                    `CSR_WRF4(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_PI_0_M1_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_PI_0_M1_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                end
                {1'b1, RANK0} : begin
                    `CSR_WRF4(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_PI_1_M1_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_PI_1_M1_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                end
                {1'b0, RANK1} : begin
                    `CSR_WRF4(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_PI_0_M1_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_PI_0_M1_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                end
                {1'b1, RANK1} : begin
                    `CSR_WRF4(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_PI_1_M1_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_PI_1_M1_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                end
                {1'b1, RANK_ALL} : begin
                    `CSR_WRF4(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_PI_1_M1_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_PI_1_M1_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_PI_1_M1_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_PI_1_M1_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                end
                {1'b0, RANK_ALL} : begin
                    `CSR_WRF4(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_PI_0_M1_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_PI_0_M1_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_PI_0_M1_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_PI_0_M1_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                end
            endcase
        end
        if((byte_sel == CA) || (byte_sel == ALL)) begin
            case({pi_sel, rank_sel})
                {1'b0, RANK0} : begin
                    `CSR_WRF4(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_QDR_PI_0_M1_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_QDR_PI_0_M1_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                end
                {1'b1, RANK0} : begin
                    `CSR_WRF4(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_QDR_PI_1_M1_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_QDR_PI_1_M1_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                end
                {1'b0, RANK1} : begin
                    `CSR_WRF4(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_QDR_PI_0_M1_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_QDR_PI_0_M1_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                end
                {1'b1, RANK1} : begin
                    `CSR_WRF4(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_QDR_PI_1_M1_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_QDR_PI_1_M1_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                end
                {1'b1, RANK_ALL} : begin
                    `CSR_WRF4(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_QDR_PI_1_M1_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_QDR_PI_1_M1_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_QDR_PI_1_M1_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_QDR_PI_1_M1_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                end
                {1'b0, RANK_ALL} : begin
                    `CSR_WRF4(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_QDR_PI_0_M1_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_QDR_PI_0_M1_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_QDR_PI_0_M1_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_QDR_PI_0_M1_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                end
            endcase
        end
    end
endtask

task automatic set_tx_dq_ddr_pi_cfg_m1;
    input byte_sel_t  byte_sel;
    input rank_sel_t  rank_sel;
    input logic       pi_sel;
    input logic       en;
    input logic [3:0] gear;
    input logic [3:0] xcpl;
    input logic [5:0] code;
    begin
        if((byte_sel == DQ0 ) || (byte_sel == DQ_ALL) || (byte_sel == ALL)) begin
            case({pi_sel, rank_sel})
                {1'b0, RANK0} : begin
                    `CSR_WRF4(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_PI_0_M1_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_PI_0_M1_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                end
                {1'b1, RANK0} : begin
                    `CSR_WRF4(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_PI_1_M1_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_PI_1_M1_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                end
                {1'b0, RANK1} : begin
                    `CSR_WRF4(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_PI_0_M1_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_PI_0_M1_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                end
                {1'b1, RANK1} : begin
                    `CSR_WRF4(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_PI_1_M1_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_PI_1_M1_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                end
                {1'b1, RANK_ALL} : begin
                    `CSR_WRF4(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_PI_1_M1_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_PI_1_M1_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_PI_1_M1_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_PI_1_M1_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                end
                {1'b0, RANK_ALL} : begin
                    `CSR_WRF4(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_PI_0_M1_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_PI_0_M1_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_PI_0_M1_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_PI_0_M1_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                end
            endcase
        end
        if((byte_sel == DQ1 ) || (byte_sel == DQ_ALL) || (byte_sel == ALL)) begin
            case({pi_sel, rank_sel})
                {1'b0, RANK0} : begin
                    `CSR_WRF4(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_PI_0_M1_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_PI_0_M1_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                end
                {1'b1, RANK0} : begin
                    `CSR_WRF4(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_PI_1_M1_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_PI_1_M1_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                end
                {1'b0, RANK1} : begin
                    `CSR_WRF4(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_PI_0_M1_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_PI_0_M1_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                end
                {1'b1, RANK1} : begin
                    `CSR_WRF4(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_PI_1_M1_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_PI_1_M1_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                end
                {1'b1, RANK_ALL} : begin
                    `CSR_WRF4(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_PI_1_M1_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_PI_1_M1_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_PI_1_M1_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_PI_1_M1_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                end
                {1'b0, RANK_ALL} : begin
                    `CSR_WRF4(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_PI_0_M1_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_PI_0_M1_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_PI_0_M1_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_PI_0_M1_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                end
            endcase
        end
        if((byte_sel == CA) || (byte_sel == ALL)) begin
            case({pi_sel, rank_sel})
                {1'b0, RANK0} : begin
                    `CSR_WRF4(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_DDR_PI_0_M1_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_DDR_PI_0_M1_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                end
                {1'b1, RANK0} : begin
                    `CSR_WRF4(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_DDR_PI_1_M1_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_DDR_PI_1_M1_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                end
                {1'b0, RANK1} : begin
                    `CSR_WRF4(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_DDR_PI_0_M1_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_DDR_PI_0_M1_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                end
                {1'b1, RANK1} : begin
                    `CSR_WRF4(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_DDR_PI_1_M1_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_DDR_PI_1_M1_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                end
                {1'b1, RANK_ALL} : begin
                    `CSR_WRF4(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_DDR_PI_1_M1_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_DDR_PI_1_M1_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_DDR_PI_1_M1_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_DDR_PI_1_M1_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                end
                {1'b0, RANK_ALL} : begin
                    `CSR_WRF4(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_DDR_PI_0_M1_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_DDR_PI_0_M1_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_DDR_PI_0_M1_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_DDR_PI_0_M1_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                end
            endcase
        end
    end
endtask

task automatic set_tx_dq_sdr_rt_pi_cfg_m1;
    input byte_sel_t  byte_sel;
    input rank_sel_t  rank_sel;
    input logic       en;
    input logic [3:0] gear;
    input logic [3:0] xcpl;
    input logic [5:0] code;
    begin
        if((byte_sel == DQ0 ) || (byte_sel == DQ_ALL) || (byte_sel == ALL)) begin
            case({rank_sel})
                {RANK0} : begin
                    `CSR_WRF4(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_PI_RT_M1_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_PI_RT_M1_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                end
                {RANK1} : begin
                    `CSR_WRF4(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_PI_RT_M1_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_PI_RT_M1_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                end
                {RANK_ALL} : begin
                    `CSR_WRF4(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_PI_RT_M1_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_PI_RT_M1_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_PI_RT_M1_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_PI_RT_M1_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                end
            endcase
        end
        if((byte_sel == DQ1 ) || (byte_sel == DQ_ALL) || (byte_sel == ALL)) begin
            case({rank_sel})
                {RANK0} : begin
                    `CSR_WRF4(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_PI_RT_M1_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_PI_RT_M1_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                end
                {RANK1} : begin
                    `CSR_WRF4(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_PI_RT_M1_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_PI_RT_M1_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                end
                {RANK_ALL} : begin
                    `CSR_WRF4(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_PI_RT_M1_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_PI_RT_M1_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_PI_RT_M1_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_PI_RT_M1_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                end
            endcase
        end
        if((byte_sel == CA) || (byte_sel == ALL)) begin
            case({rank_sel})
                {RANK0} : begin
                    `CSR_WRF4(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_PI_RT_M1_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_PI_RT_M1_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                end
                {RANK1} : begin
                    `CSR_WRF4(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_PI_RT_M1_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_PI_RT_M1_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                end
                {RANK_ALL} : begin
                    `CSR_WRF4(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_PI_RT_M1_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_PI_RT_M1_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_PI_RT_M1_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_PI_RT_M1_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                end
            endcase
        end
    end
endtask

task automatic set_rx_ren_pi_cfg_m1;
    input byte_sel_t  byte_sel;
    input rank_sel_t  rank_sel;
    input logic       en;
    input logic [3:0] gear;
    input logic [3:0] xcpl;
    input logic [5:0] code;
    begin
        if((byte_sel == DQ0) || (byte_sel == DQ_ALL) || (byte_sel == ALL)) begin
            case({rank_sel})
                {RANK0} : begin
                    `CSR_WRF4(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_RX_REN_PI_M1_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_RX_REN_PI_M1_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                end
                {RANK1} : begin
                    `CSR_WRF4(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_RX_REN_PI_M1_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_RX_REN_PI_M1_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                end
                {RANK_ALL} : begin
                    `CSR_WRF4(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_RX_REN_PI_M1_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_RX_REN_PI_M1_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_RX_REN_PI_M1_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_RX_REN_PI_M1_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                end
            endcase
        end
        if((byte_sel == DQ1) || (byte_sel == DQ_ALL) || (byte_sel == ALL)) begin
            case({rank_sel})
                {RANK0} : begin
                    `CSR_WRF4(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_RX_REN_PI_M1_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_RX_REN_PI_M1_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                end
                {RANK1} : begin
                    `CSR_WRF4(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_RX_REN_PI_M1_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_RX_REN_PI_M1_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                end
                {RANK_ALL} : begin
                    `CSR_WRF4(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_RX_REN_PI_M1_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_RX_REN_PI_M1_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_RX_REN_PI_M1_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_RX_REN_PI_M1_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                end
            endcase
        end
        if((byte_sel == CA) || (byte_sel == ALL)) begin
            case({rank_sel})
                {RANK0} : begin
                    `CSR_WRF4(DDR_CH0_CA_OFFSET,DDR_CA_DQS_RX_REN_PI_M1_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_CA_OFFSET,DDR_CA_DQS_RX_REN_PI_M1_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                end
                {RANK1} : begin
                    `CSR_WRF4(DDR_CH0_CA_OFFSET,DDR_CA_DQS_RX_REN_PI_M1_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_CA_OFFSET,DDR_CA_DQS_RX_REN_PI_M1_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                end
                {RANK_ALL} : begin
                    `CSR_WRF4(DDR_CH0_CA_OFFSET,DDR_CA_DQS_RX_REN_PI_M1_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH0_CA_OFFSET,DDR_CA_DQS_RX_REN_PI_M1_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_CA_OFFSET,DDR_CA_DQS_RX_REN_PI_M1_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_CA_OFFSET,DDR_CA_DQS_RX_REN_PI_M1_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                end
            endcase
        end
    end
endtask

task automatic set_rx_rcs_pi_cfg_m1;
    input byte_sel_t  byte_sel;
    input rank_sel_t  rank_sel;
    input logic       en;
    input logic [3:0] gear;
    input logic [3:0] xcpl;
    input logic [5:0] code;
    begin
        if((byte_sel == DQ0) || (byte_sel == DQ_ALL) || (byte_sel == ALL)) begin
            case({rank_sel})
                {RANK0} : begin
                    `CSR_WRF4(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_RX_RCS_PI_M1_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_RX_RCS_PI_M1_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                end
                {RANK1} : begin
                    `CSR_WRF4(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_RX_RCS_PI_M1_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_RX_RCS_PI_M1_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                end
                {RANK_ALL} : begin
                    `CSR_WRF4(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_RX_RCS_PI_M1_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_RX_RCS_PI_M1_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_RX_RCS_PI_M1_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_RX_RCS_PI_M1_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                end
            endcase
        end
        if((byte_sel == DQ1) || (byte_sel == DQ_ALL) || (byte_sel == ALL)) begin
            case({rank_sel})
                {RANK0} : begin
                    `CSR_WRF4(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_RX_RCS_PI_M1_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_RX_RCS_PI_M1_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                end
                {RANK1} : begin
                    `CSR_WRF4(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_RX_RCS_PI_M1_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_RX_RCS_PI_M1_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                end
                {RANK_ALL} : begin
                    `CSR_WRF4(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_RX_RCS_PI_M1_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_RX_RCS_PI_M1_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_RX_RCS_PI_M1_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_RX_RCS_PI_M1_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                end
            endcase
        end
        if((byte_sel == CA) || (byte_sel == ALL)) begin
            case({rank_sel})
                {RANK0} : begin
                    `CSR_WRF4(DDR_CH0_CA_OFFSET,DDR_CA_DQS_RX_RCS_PI_M1_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_CA_OFFSET,DDR_CA_DQS_RX_RCS_PI_M1_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                end
                {RANK1} : begin
                    `CSR_WRF4(DDR_CH0_CA_OFFSET,DDR_CA_DQS_RX_RCS_PI_M1_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_CA_OFFSET,DDR_CA_DQS_RX_RCS_PI_M1_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                end
                {RANK_ALL} : begin
                    `CSR_WRF4(DDR_CH0_CA_OFFSET,DDR_CA_DQS_RX_RCS_PI_M1_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH0_CA_OFFSET,DDR_CA_DQS_RX_RCS_PI_M1_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_CA_OFFSET,DDR_CA_DQS_RX_RCS_PI_M1_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_CA_OFFSET,DDR_CA_DQS_RX_RCS_PI_M1_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                end
            endcase
        end
    end
endtask

task automatic set_rx_rdqs_pi_cfg_m1;
    input byte_sel_t  byte_sel;
    input rank_sel_t  rank_sel;
    input logic       pi_sel;
    input logic       en;
    input logic [3:0] gear;
    input logic [3:0] xcpl;
    input logic [5:0] code;
    begin
        if((byte_sel == DQ0) || (byte_sel == DQ_ALL) || (byte_sel == ALL)) begin
            case({pi_sel, rank_sel})
                {1'b1, RANK0} : begin
                    `CSR_WRF4(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_RX_RDQS_PI_1_M1_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_RX_RDQS_PI_1_M1_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                end
                {1'b0, RANK0} : begin
                    `CSR_WRF4(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_RX_RDQS_PI_0_M1_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_RX_RDQS_PI_0_M1_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                end
                {1'b1, RANK1} : begin
                    `CSR_WRF4(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_RX_RDQS_PI_1_M1_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_RX_RDQS_PI_1_M1_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                end
                {1'b0, RANK1} : begin
                    `CSR_WRF4(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_RX_RDQS_PI_0_M1_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_RX_RDQS_PI_0_M1_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                end
                {1'b1, RANK_ALL} : begin
                    `CSR_WRF4(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_RX_RDQS_PI_1_M1_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_RX_RDQS_PI_1_M1_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_RX_RDQS_PI_1_M1_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_RX_RDQS_PI_1_M1_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                end
                {1'b0, RANK_ALL} : begin
                    `CSR_WRF4(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_RX_RDQS_PI_0_M1_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_RX_RDQS_PI_0_M1_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_RX_RDQS_PI_0_M1_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_RX_RDQS_PI_0_M1_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                end
            endcase
        end
        if((byte_sel == DQ1) || (byte_sel == DQ_ALL) || (byte_sel == ALL)) begin
            case({pi_sel, rank_sel})
                {1'b1, RANK0} : begin
                    `CSR_WRF4(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_RX_RDQS_PI_1_M1_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_RX_RDQS_PI_1_M1_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                end
                {1'b0, RANK0} : begin
                    `CSR_WRF4(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_RX_RDQS_PI_0_M1_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_RX_RDQS_PI_0_M1_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                end
                {1'b1, RANK1} : begin
                    `CSR_WRF4(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_RX_RDQS_PI_1_M1_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_RX_RDQS_PI_1_M1_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                end
                {1'b0, RANK1} : begin
                    `CSR_WRF4(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_RX_RDQS_PI_0_M1_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_RX_RDQS_PI_0_M1_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                end
                {1'b1, RANK_ALL} : begin
                    `CSR_WRF4(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_RX_RDQS_PI_1_M1_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_RX_RDQS_PI_1_M1_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_RX_RDQS_PI_1_M1_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_RX_RDQS_PI_1_M1_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                end
                {1'b0, RANK_ALL} : begin
                    `CSR_WRF4(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_RX_RDQS_PI_0_M1_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_RX_RDQS_PI_0_M1_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_RX_RDQS_PI_0_M1_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_RX_RDQS_PI_0_M1_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                end
            endcase
        end
        if((byte_sel == CA) || (byte_sel == ALL)) begin
            case({pi_sel, rank_sel})
                {1'b1, RANK0} : begin
                    `CSR_WRF4(DDR_CH0_CA_OFFSET,DDR_CA_DQS_RX_RDQS_PI_1_M1_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_CA_OFFSET,DDR_CA_DQS_RX_RDQS_PI_1_M1_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                end
                {1'b0, RANK0} : begin
                    `CSR_WRF4(DDR_CH0_CA_OFFSET,DDR_CA_DQS_RX_RDQS_PI_0_M1_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_CA_OFFSET,DDR_CA_DQS_RX_RDQS_PI_0_M1_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                end
                {1'b1, RANK1} : begin
                    `CSR_WRF4(DDR_CH0_CA_OFFSET,DDR_CA_DQS_RX_RDQS_PI_1_M1_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_CA_OFFSET,DDR_CA_DQS_RX_RDQS_PI_1_M1_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                end
                {1'b0, RANK1} : begin
                    `CSR_WRF4(DDR_CH0_CA_OFFSET,DDR_CA_DQS_RX_RDQS_PI_0_M1_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_CA_OFFSET,DDR_CA_DQS_RX_RDQS_PI_0_M1_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                end
                {1'b1, RANK_ALL} : begin
                    `CSR_WRF4(DDR_CH0_CA_OFFSET,DDR_CA_DQS_RX_RDQS_PI_1_M1_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH0_CA_OFFSET,DDR_CA_DQS_RX_RDQS_PI_1_M1_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_CA_OFFSET,DDR_CA_DQS_RX_RDQS_PI_1_M1_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_CA_OFFSET,DDR_CA_DQS_RX_RDQS_PI_1_M1_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                end
                {1'b0, RANK_ALL} : begin
                    `CSR_WRF4(DDR_CH0_CA_OFFSET,DDR_CA_DQS_RX_RDQS_PI_0_M1_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH0_CA_OFFSET,DDR_CA_DQS_RX_RDQS_PI_0_M1_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_CA_OFFSET,DDR_CA_DQS_RX_RDQS_PI_0_M1_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_CA_OFFSET,DDR_CA_DQS_RX_RDQS_PI_0_M1_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                end
            endcase
        end
    end
endtask

task automatic set_txdq_sdr_fc_dly_m1;
    input byte_sel_t     byte_sel;
    input rank_sel_t     rank_sel;
    input logic    [7:0] dq;
    input logic   [31:0] fc_dly;
    begin
        if((byte_sel == DQ0) || (byte_sel == DQ_ALL) || (byte_sel == ALL)) begin
            case ({rank_sel,dq})
                {RANK0, 8'd0} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R0_CFG_0, fc_dly );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R0_CFG_0, fc_dly );
                end
                {RANK0, 8'd1} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R0_CFG_1, fc_dly );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R0_CFG_1, fc_dly );
                end
                {RANK0, 8'd2} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R0_CFG_2, fc_dly );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R0_CFG_2, fc_dly );
                end
                {RANK0, 8'd3} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R0_CFG_3, fc_dly );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R0_CFG_3, fc_dly );
                end
                {RANK0, 8'd4} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R0_CFG_4, fc_dly );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R0_CFG_4, fc_dly );
                end
                {RANK0, 8'd5} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R0_CFG_5, fc_dly );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R0_CFG_5, fc_dly );
                end
                {RANK0, 8'd6} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R0_CFG_6, fc_dly );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R0_CFG_6, fc_dly );
                end
                {RANK0, 8'd7} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R0_CFG_7, fc_dly );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R0_CFG_7, fc_dly );
                end
                {RANK0, 8'd8} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R0_CFG_8, fc_dly );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R0_CFG_8, fc_dly );
                end
                {RANK1, 8'd0} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R1_CFG_0, fc_dly );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R1_CFG_0, fc_dly );
                end
                {RANK1, 8'd1} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R1_CFG_1, fc_dly );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R1_CFG_1, fc_dly );
                end
                {RANK1, 8'd2} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R1_CFG_2, fc_dly );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R1_CFG_2, fc_dly );
                end
                {RANK1, 8'd3} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R1_CFG_3, fc_dly );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R1_CFG_3, fc_dly );
                end
                {RANK1, 8'd4} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R1_CFG_4, fc_dly );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R1_CFG_4, fc_dly );
                end
                {RANK1, 8'd5} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R1_CFG_5, fc_dly );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R1_CFG_5, fc_dly );
                end
                {RANK1, 8'd6} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R1_CFG_6, fc_dly );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R1_CFG_6, fc_dly );
                end
                {RANK1, 8'd7} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R1_CFG_7, fc_dly );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R1_CFG_7, fc_dly );
                end
                {RANK1, 8'd8} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R1_CFG_8, fc_dly );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R1_CFG_8, fc_dly );
                end
                default: begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R0_CFG_0, fc_dly );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R1_CFG_0, fc_dly );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R0_CFG_0, fc_dly );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R1_CFG_0, fc_dly );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R0_CFG_1, fc_dly );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R1_CFG_1, fc_dly );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R0_CFG_1, fc_dly );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R1_CFG_1, fc_dly );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R0_CFG_2, fc_dly );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R1_CFG_2, fc_dly );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R0_CFG_2, fc_dly );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R1_CFG_2, fc_dly );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R0_CFG_3, fc_dly );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R1_CFG_3, fc_dly );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R0_CFG_3, fc_dly );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R1_CFG_3, fc_dly );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R0_CFG_4, fc_dly );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R1_CFG_4, fc_dly );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R0_CFG_4, fc_dly );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R1_CFG_4, fc_dly );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R0_CFG_5, fc_dly );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R1_CFG_5, fc_dly );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R0_CFG_5, fc_dly );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R1_CFG_5, fc_dly );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R0_CFG_6, fc_dly );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R1_CFG_6, fc_dly );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R0_CFG_6, fc_dly );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R1_CFG_6, fc_dly );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R0_CFG_7, fc_dly );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R1_CFG_7, fc_dly );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R0_CFG_7, fc_dly );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R1_CFG_7, fc_dly );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R0_CFG_8, fc_dly );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R1_CFG_8, fc_dly );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R0_CFG_8, fc_dly );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R1_CFG_8, fc_dly );
                end
            endcase
        end
        if((byte_sel == DQ1) || (byte_sel == DQ_ALL) || (byte_sel == ALL)) begin
            case ({rank_sel,dq})
                {RANK0, 8'd0} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R0_CFG_0, fc_dly );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R0_CFG_0, fc_dly );
                end
                {RANK0, 8'd1} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R0_CFG_1, fc_dly );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R0_CFG_1, fc_dly );
                end
                {RANK0, 8'd2} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R0_CFG_2, fc_dly );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R0_CFG_2, fc_dly );
                end
                {RANK0, 8'd3} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R0_CFG_3, fc_dly );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R0_CFG_3, fc_dly );
                end
                {RANK0, 8'd4} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R0_CFG_4, fc_dly );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R0_CFG_4, fc_dly );
                end
                {RANK0, 8'd5} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R0_CFG_5, fc_dly );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R0_CFG_5, fc_dly );
                end
                {RANK0, 8'd6} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R0_CFG_6, fc_dly );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R0_CFG_6, fc_dly );
                end
                {RANK0, 8'd7} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R0_CFG_7, fc_dly );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R0_CFG_7, fc_dly );
                end
                {RANK0, 8'd8} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R0_CFG_8, fc_dly );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R0_CFG_8, fc_dly );
                end
                {RANK1, 8'd0} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R1_CFG_0, fc_dly );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R1_CFG_0, fc_dly );
                end
                {RANK1, 8'd1} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R1_CFG_1, fc_dly );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R1_CFG_1, fc_dly );
                end
                {RANK1, 8'd2} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R1_CFG_2, fc_dly );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R1_CFG_2, fc_dly );
                end
                {RANK1, 8'd3} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R1_CFG_3, fc_dly );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R1_CFG_3, fc_dly );
                end
                {RANK1, 8'd4} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R1_CFG_4, fc_dly );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R1_CFG_4, fc_dly );
                end
                {RANK1, 8'd5} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R1_CFG_5, fc_dly );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R1_CFG_5, fc_dly );
                end
                {RANK1, 8'd6} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R1_CFG_6, fc_dly );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R1_CFG_6, fc_dly );
                end
                {RANK1, 8'd7} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R1_CFG_7, fc_dly );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R1_CFG_7, fc_dly );
                end
                {RANK1, 8'd8} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R1_CFG_8, fc_dly );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R1_CFG_8, fc_dly );
                end
                default: begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R0_CFG_0, fc_dly );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R1_CFG_0, fc_dly );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R0_CFG_0, fc_dly );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R1_CFG_0, fc_dly );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R0_CFG_1, fc_dly );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R1_CFG_1, fc_dly );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R0_CFG_1, fc_dly );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R1_CFG_1, fc_dly );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R0_CFG_2, fc_dly );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R1_CFG_2, fc_dly );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R0_CFG_2, fc_dly );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R1_CFG_2, fc_dly );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R0_CFG_3, fc_dly );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R1_CFG_3, fc_dly );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R0_CFG_3, fc_dly );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R1_CFG_3, fc_dly );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R0_CFG_4, fc_dly );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R1_CFG_4, fc_dly );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R0_CFG_4, fc_dly );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R1_CFG_4, fc_dly );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R0_CFG_5, fc_dly );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R1_CFG_5, fc_dly );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R0_CFG_5, fc_dly );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R1_CFG_5, fc_dly );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R0_CFG_6, fc_dly );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R1_CFG_6, fc_dly );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R0_CFG_6, fc_dly );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R1_CFG_6, fc_dly );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R0_CFG_7, fc_dly );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R1_CFG_7, fc_dly );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R0_CFG_7, fc_dly );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R1_CFG_7, fc_dly );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R0_CFG_8, fc_dly );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R1_CFG_8, fc_dly );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R0_CFG_8, fc_dly );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M1_R1_CFG_8, fc_dly );
                end
            endcase
        end
        if((byte_sel == CA) || (byte_sel == ALL)) begin
            case ({rank_sel,dq})
                {RANK0, 8'd0} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_FC_DLY_M1_R0_CFG_0, fc_dly );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_FC_DLY_M1_R0_CFG_0, fc_dly );
                end
                {RANK0, 8'd1} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_FC_DLY_M1_R0_CFG_1, fc_dly );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_FC_DLY_M1_R0_CFG_1, fc_dly );
                end
                {RANK0, 8'd2} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_FC_DLY_M1_R0_CFG_2, fc_dly );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_FC_DLY_M1_R0_CFG_2, fc_dly );
                end
                {RANK0, 8'd3} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_FC_DLY_M1_R0_CFG_3, fc_dly );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_FC_DLY_M1_R0_CFG_3, fc_dly );
                end
                {RANK0, 8'd4} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_FC_DLY_M1_R0_CFG_4, fc_dly );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_FC_DLY_M1_R0_CFG_4, fc_dly );
                end
                {RANK0, 8'd5} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_FC_DLY_M1_R0_CFG_5, fc_dly );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_FC_DLY_M1_R0_CFG_5, fc_dly );
                end
                {RANK0, 8'd6} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_FC_DLY_M1_R0_CFG_6, fc_dly );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_FC_DLY_M1_R0_CFG_6, fc_dly );
                end
                {RANK0, 8'd7} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_FC_DLY_M1_R0_CFG_7, fc_dly );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_FC_DLY_M1_R0_CFG_7, fc_dly );
                end
                {RANK0, 8'd8} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_FC_DLY_M1_R0_CFG_8, fc_dly );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_FC_DLY_M1_R0_CFG_8, fc_dly );
                end
                {RANK0, 8'd9} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_FC_DLY_M1_R0_CFG_9, fc_dly );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_FC_DLY_M1_R0_CFG_9, fc_dly );
                end
                {RANK0, 8'd10} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_FC_DLY_M1_R0_CFG_10, fc_dly );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_FC_DLY_M1_R0_CFG_10, fc_dly );
                end
                {RANK1, 8'd0} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_FC_DLY_M1_R1_CFG_0, fc_dly );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_FC_DLY_M1_R1_CFG_0, fc_dly );
                end
                {RANK1, 8'd1} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_FC_DLY_M1_R1_CFG_1, fc_dly );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_FC_DLY_M1_R1_CFG_1, fc_dly );
                end
                {RANK1, 8'd2} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_FC_DLY_M1_R1_CFG_2, fc_dly );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_FC_DLY_M1_R1_CFG_2, fc_dly );
                end
                {RANK1, 8'd3} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_FC_DLY_M1_R1_CFG_3, fc_dly );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_FC_DLY_M1_R1_CFG_3, fc_dly );
                end
                {RANK1, 8'd4} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_FC_DLY_M1_R1_CFG_4, fc_dly );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_FC_DLY_M1_R1_CFG_4, fc_dly );
                end
                {RANK1, 8'd5} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_FC_DLY_M1_R1_CFG_5, fc_dly );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_FC_DLY_M1_R1_CFG_5, fc_dly );
                end
                {RANK1, 8'd6} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_FC_DLY_M1_R1_CFG_6, fc_dly );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_FC_DLY_M1_R1_CFG_6, fc_dly );
                end
                {RANK1, 8'd7} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_FC_DLY_M1_R1_CFG_7, fc_dly );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_FC_DLY_M1_R1_CFG_7, fc_dly );
                end
                {RANK1, 8'd8} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_FC_DLY_M1_R1_CFG_8, fc_dly );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_FC_DLY_M1_R1_CFG_8, fc_dly );
                end
                {RANK1, 8'd9} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_FC_DLY_M1_R1_CFG_9, fc_dly );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_FC_DLY_M1_R1_CFG_9, fc_dly );
                end
                {RANK1, 8'd10} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_FC_DLY_M1_R1_CFG_10, fc_dly );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_FC_DLY_M1_R1_CFG_10, fc_dly );
                end
                default: begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_FC_DLY_M1_R0_CFG_0, fc_dly );
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_FC_DLY_M1_R1_CFG_0, fc_dly );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_FC_DLY_M1_R0_CFG_0, fc_dly );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_FC_DLY_M1_R1_CFG_0, fc_dly );
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_FC_DLY_M1_R0_CFG_1, fc_dly );
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_FC_DLY_M1_R1_CFG_1, fc_dly );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_FC_DLY_M1_R0_CFG_1, fc_dly );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_FC_DLY_M1_R1_CFG_1, fc_dly );
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_FC_DLY_M1_R0_CFG_2, fc_dly );
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_FC_DLY_M1_R1_CFG_2, fc_dly );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_FC_DLY_M1_R0_CFG_2, fc_dly );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_FC_DLY_M1_R1_CFG_2, fc_dly );
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_FC_DLY_M1_R0_CFG_3, fc_dly );
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_FC_DLY_M1_R1_CFG_3, fc_dly );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_FC_DLY_M1_R0_CFG_3, fc_dly );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_FC_DLY_M1_R1_CFG_3, fc_dly );
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_FC_DLY_M1_R0_CFG_4, fc_dly );
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_FC_DLY_M1_R1_CFG_4, fc_dly );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_FC_DLY_M1_R0_CFG_4, fc_dly );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_FC_DLY_M1_R1_CFG_4, fc_dly );
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_FC_DLY_M1_R0_CFG_5, fc_dly );
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_FC_DLY_M1_R1_CFG_5, fc_dly );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_FC_DLY_M1_R0_CFG_5, fc_dly );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_FC_DLY_M1_R1_CFG_5, fc_dly );
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_FC_DLY_M1_R0_CFG_6, fc_dly );
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_FC_DLY_M1_R1_CFG_6, fc_dly );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_FC_DLY_M1_R0_CFG_6, fc_dly );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_FC_DLY_M1_R1_CFG_6, fc_dly );
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_FC_DLY_M1_R0_CFG_7, fc_dly );
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_FC_DLY_M1_R1_CFG_7, fc_dly );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_FC_DLY_M1_R0_CFG_7, fc_dly );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_FC_DLY_M1_R1_CFG_7, fc_dly );
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_FC_DLY_M1_R0_CFG_8, fc_dly );
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_FC_DLY_M1_R1_CFG_8, fc_dly );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_FC_DLY_M1_R0_CFG_8, fc_dly );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_FC_DLY_M1_R1_CFG_8, fc_dly );
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_FC_DLY_M1_R0_CFG_9, fc_dly );
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_FC_DLY_M1_R1_CFG_9, fc_dly );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_FC_DLY_M1_R0_CFG_9, fc_dly );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_FC_DLY_M1_R1_CFG_9, fc_dly );
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_FC_DLY_M1_R0_CFG_10, fc_dly );
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_FC_DLY_M1_R1_CFG_10, fc_dly );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_FC_DLY_M1_R0_CFG_10, fc_dly );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_FC_DLY_M1_R1_CFG_10, fc_dly );
                end
            endcase
        end
    end
endtask

task automatic set_txdq_rt_pipe_en_m1;
    input byte_sel_t     byte_sel;
    input rank_sel_t     rank_sel;
    input logic   [31:0] pipe_en;
    begin
        if((byte_sel == DQ0) || (byte_sel == DQ_ALL) || (byte_sel == ALL)) begin
            case ({rank_sel})
                {RANK0} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_RT_M1_R0_CFG, pipe_en );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_RT_M1_R0_CFG, pipe_en );
                end
                {RANK1} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_RT_M1_R1_CFG, pipe_en );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_RT_M1_R1_CFG, pipe_en );
                end
                default: begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_RT_M1_R0_CFG, pipe_en );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_RT_M1_R1_CFG, pipe_en );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_RT_M1_R0_CFG, pipe_en );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_RT_M1_R1_CFG, pipe_en );
                end
            endcase
        end
        if((byte_sel == DQ1) || (byte_sel == DQ_ALL) || (byte_sel == ALL)) begin
            case ({rank_sel})
                {RANK0} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_RT_M1_R0_CFG, pipe_en );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_RT_M1_R0_CFG, pipe_en );
                end
                {RANK1} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_RT_M1_R1_CFG, pipe_en );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_RT_M1_R1_CFG, pipe_en );
                end
                default: begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_RT_M1_R0_CFG, pipe_en );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_RT_M1_R1_CFG, pipe_en );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_RT_M1_R0_CFG, pipe_en );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_RT_M1_R1_CFG, pipe_en );
                end
            endcase
        end
        if((byte_sel == CA) || (byte_sel == ALL)) begin
            case ({rank_sel})
                {RANK0} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_RT_M1_R0_CFG, pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_RT_M1_R0_CFG, pipe_en);
                end
                {RANK1} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_RT_M1_R1_CFG, pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_RT_M1_R1_CFG, pipe_en);
                end
                default: begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_RT_M1_R0_CFG, pipe_en );
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_RT_M1_R1_CFG, pipe_en );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_RT_M1_R0_CFG, pipe_en );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_RT_M1_R1_CFG, pipe_en );
                end
            endcase
        end
    end
endtask

task automatic set_txdq_sdr_x_sel_m1;
    input byte_sel_t     byte_sel;
    input rank_sel_t     rank_sel;
    input logic    [7:0] dq;
    input logic   [31:0] x_sel;
    begin
        if((byte_sel == DQ0) || (byte_sel == DQ_ALL) || (byte_sel == ALL)) begin
            case ({rank_sel,dq})
                {RANK0, 8'd0} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M1_R0_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M1_R0_CFG_0 , x_sel  );
                end
                {RANK0, 8'd1} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M1_R0_CFG_1 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M1_R0_CFG_1 , x_sel  );
                end
                {RANK0, 8'd2} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M1_R0_CFG_2 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M1_R0_CFG_2 , x_sel  );
                end
                {RANK0, 8'd3} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M1_R0_CFG_3 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M1_R0_CFG_3 , x_sel  );
                end
                {RANK0, 8'd4} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M1_R0_CFG_4 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M1_R0_CFG_4 , x_sel  );
                end
                {RANK0, 8'd5} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M1_R0_CFG_5 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M1_R0_CFG_5 , x_sel  );
                end
                {RANK0, 8'd6} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M1_R0_CFG_6 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M1_R0_CFG_6 , x_sel  );
                end
                {RANK0, 8'd7} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M1_R0_CFG_7 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M1_R0_CFG_7 , x_sel  );
                end
                {RANK0, 8'd8} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M1_R0_CFG_8 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M1_R0_CFG_8 , x_sel  );
                end
                {RANK1, 8'd0} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M1_R1_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M1_R1_CFG_0 , x_sel  );
                end
                {RANK1, 8'd1} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M1_R1_CFG_1 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M1_R1_CFG_1 , x_sel  );
                end
                {RANK1, 8'd2} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M1_R1_CFG_2 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M1_R1_CFG_2 , x_sel  );
                end
                {RANK1, 8'd3} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M1_R1_CFG_3 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M1_R1_CFG_3 , x_sel  );
                end
                {RANK1, 8'd4} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M1_R1_CFG_4 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M1_R1_CFG_4 , x_sel  );
                end
                {RANK1, 8'd5} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M1_R1_CFG_5 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M1_R1_CFG_5 , x_sel  );
                end
                {RANK1, 8'd6} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M1_R1_CFG_6 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M1_R1_CFG_6 , x_sel  );
                end
                {RANK1, 8'd7} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M1_R1_CFG_7 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M1_R1_CFG_7 , x_sel  );
                end
                {RANK1, 8'd8} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M1_R1_CFG_8 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M1_R1_CFG_8 , x_sel  );
                end
                default: begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M1_R0_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M1_R1_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M1_R0_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M1_R1_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M1_R0_CFG_1 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M1_R1_CFG_1 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M1_R0_CFG_1 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M1_R1_CFG_1 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M1_R0_CFG_2 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M1_R1_CFG_2 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M1_R0_CFG_2 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M1_R1_CFG_2 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M1_R0_CFG_3 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M1_R1_CFG_3 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M1_R0_CFG_3 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M1_R1_CFG_3 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M1_R0_CFG_4 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M1_R1_CFG_4 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M1_R0_CFG_4 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M1_R1_CFG_4 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M1_R0_CFG_5 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M1_R1_CFG_5 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M1_R0_CFG_5 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M1_R1_CFG_5 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M1_R0_CFG_6 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M1_R1_CFG_6 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M1_R0_CFG_6 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M1_R1_CFG_6 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M1_R0_CFG_7 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M1_R1_CFG_7 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M1_R0_CFG_7 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M1_R1_CFG_7 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M1_R0_CFG_8 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M1_R1_CFG_8 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M1_R0_CFG_8 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M1_R1_CFG_8 , x_sel  );
                end
            endcase
        end
        if((byte_sel == DQ1) || (byte_sel == DQ_ALL) || (byte_sel == ALL)) begin
            case ({rank_sel,dq})
                {RANK0, 8'd0} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M1_R0_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M1_R0_CFG_0 , x_sel  );
                end
                {RANK0, 8'd1} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M1_R0_CFG_1 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M1_R0_CFG_1 , x_sel  );
                end
                {RANK0, 8'd2} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M1_R0_CFG_2 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M1_R0_CFG_2 , x_sel  );
                end
                {RANK0, 8'd3} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M1_R0_CFG_3 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M1_R0_CFG_3 , x_sel  );
                end
                {RANK0, 8'd4} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M1_R0_CFG_4 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M1_R0_CFG_4 , x_sel  );
                end
                {RANK0, 8'd5} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M1_R0_CFG_5 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M1_R0_CFG_5 , x_sel  );
                end
                {RANK0, 8'd6} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M1_R0_CFG_6 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M1_R0_CFG_6 , x_sel  );
                end
                {RANK0, 8'd7} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M1_R0_CFG_7 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M1_R0_CFG_7 , x_sel  );
                end
                {RANK0, 8'd8} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M1_R0_CFG_8 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M1_R0_CFG_8 , x_sel  );
                end
                {RANK1, 8'd0} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M1_R1_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M1_R1_CFG_0 , x_sel  );
                end
                {RANK1, 8'd1} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M1_R1_CFG_1 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M1_R1_CFG_1 , x_sel  );
                end
                {RANK1, 8'd2} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M1_R1_CFG_2 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M1_R1_CFG_2 , x_sel  );
                end
                {RANK1, 8'd3} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M1_R1_CFG_3 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M1_R1_CFG_3 , x_sel  );
                end
                {RANK1, 8'd4} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M1_R1_CFG_4 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M1_R1_CFG_4 , x_sel  );
                end
                {RANK1, 8'd5} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M1_R1_CFG_5 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M1_R1_CFG_5 , x_sel  );
                end
                {RANK1, 8'd6} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M1_R1_CFG_6 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M1_R1_CFG_6 , x_sel  );
                end
                {RANK1, 8'd7} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M1_R1_CFG_7 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M1_R1_CFG_7 , x_sel  );
                end
                {RANK1, 8'd8} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M1_R1_CFG_8 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M1_R1_CFG_8 , x_sel  );
                end
                default: begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M1_R0_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M1_R1_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M1_R0_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M1_R1_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M1_R0_CFG_1 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M1_R1_CFG_1 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M1_R0_CFG_1 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M1_R1_CFG_1 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M1_R0_CFG_2 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M1_R1_CFG_2 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M1_R0_CFG_2 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M1_R1_CFG_2 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M1_R0_CFG_3 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M1_R1_CFG_3 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M1_R0_CFG_3 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M1_R1_CFG_3 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M1_R0_CFG_4 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M1_R1_CFG_4 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M1_R0_CFG_4 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M1_R1_CFG_4 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M1_R0_CFG_5 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M1_R1_CFG_5 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M1_R0_CFG_5 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M1_R1_CFG_5 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M1_R0_CFG_6 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M1_R1_CFG_6 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M1_R0_CFG_6 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M1_R1_CFG_6 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M1_R0_CFG_7 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M1_R1_CFG_7 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M1_R0_CFG_7 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M1_R1_CFG_7 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M1_R0_CFG_8 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M1_R1_CFG_8 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M1_R0_CFG_8 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M1_R1_CFG_8 , x_sel  );
                end
            endcase
        end
        if((byte_sel == CA) || (byte_sel == ALL)) begin
            case ({rank_sel,dq})
                {RANK0, 8'd0} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_X_SEL_M1_R0_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_X_SEL_M1_R0_CFG_0 , x_sel  );
                end
                {RANK0, 8'd1} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_X_SEL_M1_R0_CFG_1 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_X_SEL_M1_R0_CFG_1 , x_sel  );
                end
                {RANK0, 8'd2} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_X_SEL_M1_R0_CFG_2 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_X_SEL_M1_R0_CFG_2 , x_sel  );
                end
                {RANK0, 8'd3} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_X_SEL_M1_R0_CFG_3 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_X_SEL_M1_R0_CFG_3 , x_sel  );
                end
                {RANK0, 8'd4} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_X_SEL_M1_R0_CFG_4 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_X_SEL_M1_R0_CFG_4 , x_sel  );
                end
                {RANK0, 8'd5} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_X_SEL_M1_R0_CFG_5 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_X_SEL_M1_R0_CFG_5 , x_sel  );
                end
                {RANK0, 8'd6} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_X_SEL_M1_R0_CFG_6 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_X_SEL_M1_R0_CFG_6 , x_sel  );
                end
                {RANK0, 8'd7} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_X_SEL_M1_R0_CFG_7 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_X_SEL_M1_R0_CFG_7 , x_sel  );
                end
                {RANK0, 8'd8} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_X_SEL_M1_R0_CFG_8 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_X_SEL_M1_R0_CFG_8 , x_sel  );
                end
                {RANK0, 8'd9} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_X_SEL_M1_R0_CFG_9 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_X_SEL_M1_R0_CFG_9 , x_sel  );
                end
                {RANK0, 8'd10} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_X_SEL_M1_R0_CFG_10 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_X_SEL_M1_R0_CFG_10 , x_sel  );
                end
                {RANK1, 8'd0} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_X_SEL_M1_R1_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_X_SEL_M1_R1_CFG_0 , x_sel  );
                end
                {RANK1, 8'd1} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_X_SEL_M1_R1_CFG_1 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_X_SEL_M1_R1_CFG_1 , x_sel  );
                end
                {RANK1, 8'd2} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_X_SEL_M1_R1_CFG_2 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_X_SEL_M1_R1_CFG_2 , x_sel  );
                end
                {RANK1, 8'd3} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_X_SEL_M1_R1_CFG_3 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_X_SEL_M1_R1_CFG_3 , x_sel  );
                end
                {RANK1, 8'd4} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_X_SEL_M1_R1_CFG_4 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_X_SEL_M1_R1_CFG_4 , x_sel  );
                end
                {RANK1, 8'd5} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_X_SEL_M1_R1_CFG_5 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_X_SEL_M1_R1_CFG_5 , x_sel  );
                end
                {RANK1, 8'd6} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_X_SEL_M1_R1_CFG_6 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_X_SEL_M1_R1_CFG_6 , x_sel  );
                end
                {RANK1, 8'd7} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_X_SEL_M1_R1_CFG_7 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_X_SEL_M1_R1_CFG_7 , x_sel  );
                end
                {RANK1, 8'd8} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_X_SEL_M1_R1_CFG_8 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_X_SEL_M1_R1_CFG_8 , x_sel  );
                end
                {RANK1, 8'd9} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_X_SEL_M1_R1_CFG_9 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_X_SEL_M1_R1_CFG_9 , x_sel  );
                end
                {RANK1, 8'd10} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_X_SEL_M1_R1_CFG_10 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_X_SEL_M1_R1_CFG_10 , x_sel  );
                end
                default: begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_X_SEL_M1_R0_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_X_SEL_M1_R1_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_X_SEL_M1_R0_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_X_SEL_M1_R1_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_X_SEL_M1_R0_CFG_1 , x_sel  );
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_X_SEL_M1_R1_CFG_1 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_X_SEL_M1_R0_CFG_1 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_X_SEL_M1_R1_CFG_1 , x_sel  );
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_X_SEL_M1_R0_CFG_2 , x_sel  );
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_X_SEL_M1_R1_CFG_2 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_X_SEL_M1_R0_CFG_2 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_X_SEL_M1_R1_CFG_2 , x_sel  );
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_X_SEL_M1_R0_CFG_3 , x_sel  );
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_X_SEL_M1_R1_CFG_3 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_X_SEL_M1_R0_CFG_3 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_X_SEL_M1_R1_CFG_3 , x_sel  );
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_X_SEL_M1_R0_CFG_4 , x_sel  );
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_X_SEL_M1_R1_CFG_4 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_X_SEL_M1_R0_CFG_4 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_X_SEL_M1_R1_CFG_4 , x_sel  );
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_X_SEL_M1_R0_CFG_5 , x_sel  );
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_X_SEL_M1_R1_CFG_5 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_X_SEL_M1_R0_CFG_5 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_X_SEL_M1_R1_CFG_5 , x_sel  );
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_X_SEL_M1_R0_CFG_6 , x_sel  );
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_X_SEL_M1_R1_CFG_6 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_X_SEL_M1_R0_CFG_6 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_X_SEL_M1_R1_CFG_6 , x_sel  );
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_X_SEL_M1_R0_CFG_7 , x_sel  );
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_X_SEL_M1_R1_CFG_7 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_X_SEL_M1_R0_CFG_7 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_X_SEL_M1_R1_CFG_7 , x_sel  );
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_X_SEL_M1_R0_CFG_8 , x_sel  );
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_X_SEL_M1_R1_CFG_8 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_X_SEL_M1_R0_CFG_8 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_X_SEL_M1_R1_CFG_8 , x_sel  );
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_X_SEL_M1_R0_CFG_9 , x_sel  );
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_X_SEL_M1_R1_CFG_9 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_X_SEL_M1_R0_CFG_9 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_X_SEL_M1_R1_CFG_9 , x_sel  );
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_X_SEL_M1_R0_CFG_10 , x_sel  );
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_X_SEL_M1_R1_CFG_10 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_X_SEL_M1_R0_CFG_10 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_X_SEL_M1_R1_CFG_10 , x_sel  );
                end
            endcase
        end
    end
endtask

task automatic set_txdq_sdr_pipe_en_m1 ;
    input byte_sel_t     byte_sel;
    input rank_sel_t     rank_sel;
    input logic    [7:0] dq;
    input logic   [31:0] pipe_en;
    begin
        if((byte_sel == DQ0) || (byte_sel == DQ_ALL) || (byte_sel == ALL)) begin
            case ({rank_sel,dq})
                {RANK0, 8'd0} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_M1_R0_CFG_0       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_M1_R0_CFG_0       , pipe_en);
                end
                {RANK0, 8'd1} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_M1_R0_CFG_1       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_M1_R0_CFG_1       , pipe_en);
                end
                {RANK0, 8'd2} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_M1_R0_CFG_2       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_M1_R0_CFG_2       , pipe_en);
                end
                {RANK0, 8'd3} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_M1_R0_CFG_3       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_M1_R0_CFG_3       , pipe_en);
                end
                {RANK0, 8'd4} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_M1_R0_CFG_4       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_M1_R0_CFG_4       , pipe_en);
                end
                {RANK0, 8'd5} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_M1_R0_CFG_5       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_M1_R0_CFG_5       , pipe_en);
                end
                {RANK0, 8'd6} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_M1_R0_CFG_6       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_M1_R0_CFG_6       , pipe_en);
                end
                {RANK0, 8'd7} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_M1_R0_CFG_7       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_M1_R0_CFG_7       , pipe_en);
                end
                {RANK0, 8'd8} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_M1_R0_CFG_8       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_M1_R0_CFG_8       , pipe_en);
                end
                {RANK1, 8'd0} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_M1_R1_CFG_0       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_M1_R1_CFG_0       , pipe_en);
                end
                {RANK1, 8'd1} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_M1_R1_CFG_1       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_M1_R1_CFG_1       , pipe_en);
                end
                {RANK1, 8'd2} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_M1_R1_CFG_2       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_M1_R1_CFG_2       , pipe_en);
                end
                {RANK1, 8'd3} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_M1_R1_CFG_3       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_M1_R1_CFG_3       , pipe_en);
                end
                {RANK1, 8'd4} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_M1_R1_CFG_4       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_M1_R1_CFG_4       , pipe_en);
                end
                {RANK1, 8'd5} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_M1_R1_CFG_5       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_M1_R1_CFG_5       , pipe_en);
                end
                {RANK1, 8'd6} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_M1_R1_CFG_6       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_M1_R1_CFG_6       , pipe_en);
                end
                {RANK1, 8'd7} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_M1_R1_CFG_7       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_M1_R1_CFG_7       , pipe_en);
                end
                {RANK1, 8'd8} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_M1_R1_CFG_8       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_M1_R1_CFG_8       , pipe_en);
                end
                default: begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_M1_R0_CFG_0       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_M1_R0_CFG_0       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_M1_R0_CFG_1       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_M1_R0_CFG_1       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_M1_R0_CFG_2       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_M1_R0_CFG_2       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_M1_R0_CFG_3       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_M1_R0_CFG_3       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_M1_R0_CFG_4       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_M1_R0_CFG_4       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_M1_R0_CFG_5       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_M1_R0_CFG_5       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_M1_R0_CFG_6       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_M1_R0_CFG_6       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_M1_R0_CFG_7       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_M1_R0_CFG_7       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_M1_R0_CFG_8       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_M1_R0_CFG_8       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_M1_R1_CFG_0       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_M1_R1_CFG_0       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_M1_R1_CFG_1       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_M1_R1_CFG_1       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_M1_R1_CFG_2       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_M1_R1_CFG_2       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_M1_R1_CFG_3       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_M1_R1_CFG_3       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_M1_R1_CFG_4       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_M1_R1_CFG_4       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_M1_R1_CFG_5       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_M1_R1_CFG_5       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_M1_R1_CFG_6       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_M1_R1_CFG_6       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_M1_R1_CFG_7       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_M1_R1_CFG_7       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_M1_R1_CFG_8       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_M1_R1_CFG_8       , pipe_en);
                end
            endcase
        end
        if((byte_sel == DQ1) || (byte_sel == DQ_ALL) || (byte_sel == ALL)) begin
            case ({rank_sel,dq})
                {RANK0, 8'd0} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_M1_R0_CFG_0       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_M1_R0_CFG_0       , pipe_en);
                end
                {RANK0, 8'd1} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_M1_R0_CFG_1       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_M1_R0_CFG_1       , pipe_en);
                end
                {RANK0, 8'd2} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_M1_R0_CFG_2       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_M1_R0_CFG_2       , pipe_en);
                end
                {RANK0, 8'd3} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_M1_R0_CFG_3       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_M1_R0_CFG_3       , pipe_en);
                end
                {RANK0, 8'd4} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_M1_R0_CFG_4       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_M1_R0_CFG_4       , pipe_en);
                end
                {RANK0, 8'd5} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_M1_R0_CFG_5       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_M1_R0_CFG_5       , pipe_en);
                end
                {RANK0, 8'd6} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_M1_R0_CFG_6       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_M1_R0_CFG_6       , pipe_en);
                end
                {RANK0, 8'd7} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_M1_R0_CFG_7       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_M1_R0_CFG_7       , pipe_en);
                end
                {RANK0, 8'd8} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_M1_R0_CFG_8       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_M1_R0_CFG_8       , pipe_en);
                end
                {RANK1, 8'd0} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_M1_R1_CFG_0       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_M1_R1_CFG_0       , pipe_en);
                end
                {RANK1, 8'd1} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_M1_R1_CFG_1       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_M1_R1_CFG_1       , pipe_en);
                end
                {RANK1, 8'd2} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_M1_R1_CFG_2       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_M1_R1_CFG_2       , pipe_en);
                end
                {RANK1, 8'd3} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_M1_R1_CFG_3       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_M1_R1_CFG_3       , pipe_en);
                end
                {RANK1, 8'd4} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_M1_R1_CFG_4       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_M1_R1_CFG_4       , pipe_en);
                end
                {RANK1, 8'd5} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_M1_R1_CFG_5       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_M1_R1_CFG_5       , pipe_en);
                end
                {RANK1, 8'd6} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_M1_R1_CFG_6       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_M1_R1_CFG_6       , pipe_en);
                end
                {RANK1, 8'd7} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_M1_R1_CFG_7       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_M1_R1_CFG_7       , pipe_en);
                end
                {RANK1, 8'd8} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_M1_R1_CFG_8       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_M1_R1_CFG_8       , pipe_en);
                end
                default: begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_M1_R0_CFG_0       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_M1_R0_CFG_0       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_M1_R0_CFG_1       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_M1_R0_CFG_1       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_M1_R0_CFG_2       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_M1_R0_CFG_2       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_M1_R0_CFG_3       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_M1_R0_CFG_3       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_M1_R0_CFG_4       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_M1_R0_CFG_4       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_M1_R0_CFG_5       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_M1_R0_CFG_5       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_M1_R0_CFG_6       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_M1_R0_CFG_6       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_M1_R0_CFG_7       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_M1_R0_CFG_7       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_M1_R0_CFG_8       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_M1_R0_CFG_8       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_M1_R1_CFG_0       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_M1_R1_CFG_0       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_M1_R1_CFG_1       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_M1_R1_CFG_1       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_M1_R1_CFG_2       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_M1_R1_CFG_2       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_M1_R1_CFG_3       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_M1_R1_CFG_3       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_M1_R1_CFG_4       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_M1_R1_CFG_4       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_M1_R1_CFG_5       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_M1_R1_CFG_5       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_M1_R1_CFG_6       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_M1_R1_CFG_6       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_M1_R1_CFG_7       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_M1_R1_CFG_7       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_M1_R1_CFG_8       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_M1_R1_CFG_8       , pipe_en);
                end
            endcase
        end
        if((byte_sel == CA) || (byte_sel == ALL)) begin
            case ({rank_sel,dq})
                {RANK0, 8'd0} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_M1_R0_CFG_0       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_M1_R0_CFG_0       , pipe_en);
                end
                {RANK0, 8'd1} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_M1_R0_CFG_1       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_M1_R0_CFG_1       , pipe_en);
                end
                {RANK0, 8'd2} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_M1_R0_CFG_2       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_M1_R0_CFG_2       , pipe_en);
                end
                {RANK0, 8'd3} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_M1_R0_CFG_3       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_M1_R0_CFG_3       , pipe_en);
                end
                {RANK0, 8'd4} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_M1_R0_CFG_4       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_M1_R0_CFG_4       , pipe_en);
                end
                {RANK0, 8'd5} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_M1_R0_CFG_5       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_M1_R0_CFG_5       , pipe_en);
                end
                {RANK0, 8'd6} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_M1_R0_CFG_6       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_M1_R0_CFG_6       , pipe_en);
                end
                {RANK0, 8'd7} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_M1_R0_CFG_7       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_M1_R0_CFG_7       , pipe_en);
                end
                {RANK0, 8'd8} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_M1_R0_CFG_8       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_M1_R0_CFG_8       , pipe_en);
                end
                {RANK0, 8'd9} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_M1_R0_CFG_9       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_M1_R0_CFG_9       , pipe_en);
                end
                {RANK0, 8'd10} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_M1_R0_CFG_10       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_M1_R0_CFG_10       , pipe_en);
                end
                {RANK1, 8'd0} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_M1_R1_CFG_0       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_M1_R1_CFG_0       , pipe_en);
                end
                {RANK1, 8'd1} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_M1_R1_CFG_1       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_M1_R1_CFG_1       , pipe_en);
                end
                {RANK1, 8'd2} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_M1_R1_CFG_2       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_M1_R1_CFG_2       , pipe_en);
                end
                {RANK1, 8'd3} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_M1_R1_CFG_3       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_M1_R1_CFG_3       , pipe_en);
                end
                {RANK1, 8'd4} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_M1_R1_CFG_4       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_M1_R1_CFG_4       , pipe_en);
                end
                {RANK1, 8'd5} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_M1_R1_CFG_5       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_M1_R1_CFG_5       , pipe_en);
                end
                {RANK1, 8'd6} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_M1_R1_CFG_6       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_M1_R1_CFG_6       , pipe_en);
                end
                {RANK1, 8'd7} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_M1_R1_CFG_7       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_M1_R1_CFG_7       , pipe_en);
                end
                {RANK1, 8'd8} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_M1_R1_CFG_8       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_M1_R1_CFG_8       , pipe_en);
                end
                {RANK1, 8'd9} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_M1_R1_CFG_9       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_M1_R1_CFG_9       , pipe_en);
                end
                {RANK1, 8'd10} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_M1_R1_CFG_10       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_M1_R1_CFG_10       , pipe_en);
                end
                default: begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_M1_R0_CFG_0       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_M1_R0_CFG_0       , pipe_en);
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_M1_R0_CFG_1       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_M1_R0_CFG_1       , pipe_en);
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_M1_R0_CFG_2       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_M1_R0_CFG_2       , pipe_en);
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_M1_R0_CFG_3       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_M1_R0_CFG_3       , pipe_en);
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_M1_R0_CFG_4       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_M1_R0_CFG_4       , pipe_en);
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_M1_R0_CFG_5       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_M1_R0_CFG_5       , pipe_en);
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_M1_R0_CFG_6       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_M1_R0_CFG_6       , pipe_en);
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_M1_R0_CFG_7       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_M1_R0_CFG_7       , pipe_en);
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_M1_R0_CFG_8       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_M1_R0_CFG_8       , pipe_en);
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_M1_R0_CFG_9       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_M1_R0_CFG_9       , pipe_en);
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_M1_R0_CFG_10       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_M1_R0_CFG_10       , pipe_en);
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_M1_R1_CFG_0       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_M1_R1_CFG_0       , pipe_en);
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_M1_R1_CFG_1       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_M1_R1_CFG_1       , pipe_en);
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_M1_R1_CFG_2       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_M1_R1_CFG_2       , pipe_en);
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_M1_R1_CFG_3       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_M1_R1_CFG_3       , pipe_en);
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_M1_R1_CFG_4       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_M1_R1_CFG_4       , pipe_en);
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_M1_R1_CFG_5       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_M1_R1_CFG_5       , pipe_en);
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_M1_R1_CFG_6       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_M1_R1_CFG_6       , pipe_en);
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_M1_R1_CFG_7       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_M1_R1_CFG_7       , pipe_en);
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_M1_R1_CFG_8       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_M1_R1_CFG_8       , pipe_en);
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_M1_R1_CFG_9       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_M1_R1_CFG_9       , pipe_en);
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_M1_R1_CFG_10       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_M1_R1_CFG_10       , pipe_en);
                end
            endcase
        end
    end
endtask

task automatic set_txdq_ddr_x_sel_m1;
    input byte_sel_t     byte_sel;
    input rank_sel_t     rank_sel;
    input logic    [7:0] dq;
    input logic   [31:0] x_sel;
    begin
        if((byte_sel == DQ0) || (byte_sel == DQ_ALL) || (byte_sel == ALL)) begin
            case ({rank_sel,dq})
                {RANK0, 8'd0} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M1_R0_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M1_R0_CFG_0 , x_sel  );
                end
                {RANK0, 8'd1} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M1_R0_CFG_1 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M1_R0_CFG_1 , x_sel  );
                end
                {RANK0, 8'd2} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M1_R0_CFG_2 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M1_R0_CFG_2 , x_sel  );
                end
                {RANK0, 8'd3} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M1_R0_CFG_3 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M1_R0_CFG_3 , x_sel  );
                end
                {RANK0, 8'd4} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M1_R0_CFG_4 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M1_R0_CFG_4 , x_sel  );
                end
                {RANK0, 8'd5} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M1_R0_CFG_5 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M1_R0_CFG_5 , x_sel  );
                end
                {RANK0, 8'd6} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M1_R0_CFG_6 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M1_R0_CFG_6 , x_sel  );
                end
                {RANK0, 8'd7} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M1_R0_CFG_7 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M1_R0_CFG_7 , x_sel  );
                end
                {RANK0, 8'd8} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M1_R0_CFG_8 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M1_R0_CFG_8 , x_sel  );
                end
                {RANK1, 8'd0} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M1_R1_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M1_R1_CFG_0 , x_sel  );
                end
                {RANK1, 8'd1} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M1_R1_CFG_1 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M1_R1_CFG_1 , x_sel  );
                end
                {RANK1, 8'd2} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M1_R1_CFG_2 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M1_R1_CFG_2 , x_sel  );
                end
                {RANK1, 8'd3} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M1_R1_CFG_3 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M1_R1_CFG_3 , x_sel  );
                end
                {RANK1, 8'd4} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M1_R1_CFG_4 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M1_R1_CFG_4 , x_sel  );
                end
                {RANK1, 8'd5} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M1_R1_CFG_5 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M1_R1_CFG_5 , x_sel  );
                end
                {RANK1, 8'd6} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M1_R1_CFG_6 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M1_R1_CFG_6 , x_sel  );
                end
                {RANK1, 8'd7} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M1_R1_CFG_7 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M1_R1_CFG_7 , x_sel  );
                end
                {RANK1, 8'd8} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M1_R1_CFG_8 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M1_R1_CFG_8 , x_sel  );
                end
                default: begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M1_R0_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M1_R1_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M1_R0_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M1_R1_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M1_R0_CFG_1 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M1_R1_CFG_1 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M1_R0_CFG_1 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M1_R1_CFG_1 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M1_R0_CFG_2 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M1_R1_CFG_2 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M1_R0_CFG_2 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M1_R1_CFG_2 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M1_R0_CFG_3 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M1_R1_CFG_3 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M1_R0_CFG_3 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M1_R1_CFG_3 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M1_R0_CFG_4 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M1_R1_CFG_4 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M1_R0_CFG_4 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M1_R1_CFG_4 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M1_R0_CFG_5 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M1_R1_CFG_5 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M1_R0_CFG_5 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M1_R1_CFG_5 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M1_R0_CFG_6 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M1_R1_CFG_6 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M1_R0_CFG_6 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M1_R1_CFG_6 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M1_R0_CFG_7 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M1_R1_CFG_7 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M1_R0_CFG_7 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M1_R1_CFG_7 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M1_R0_CFG_8 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M1_R1_CFG_8 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M1_R0_CFG_8 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M1_R1_CFG_8 , x_sel  );
                end
            endcase
        end
        if((byte_sel == DQ1) || (byte_sel == DQ_ALL) || (byte_sel == ALL)) begin
            case ({rank_sel,dq})
                {RANK0, 8'd0} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M1_R0_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M1_R0_CFG_0 , x_sel  );
                end
                {RANK0, 8'd1} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M1_R0_CFG_1 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M1_R0_CFG_1 , x_sel  );
                end
                {RANK0, 8'd2} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M1_R0_CFG_2 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M1_R0_CFG_2 , x_sel  );
                end
                {RANK0, 8'd3} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M1_R0_CFG_3 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M1_R0_CFG_3 , x_sel  );
                end
                {RANK0, 8'd4} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M1_R0_CFG_4 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M1_R0_CFG_4 , x_sel  );
                end
                {RANK0, 8'd5} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M1_R0_CFG_5 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M1_R0_CFG_5 , x_sel  );
                end
                {RANK0, 8'd6} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M1_R0_CFG_6 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M1_R0_CFG_6 , x_sel  );
                end
                {RANK0, 8'd7} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M1_R0_CFG_7 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M1_R0_CFG_7 , x_sel  );
                end
                {RANK0, 8'd8} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M1_R0_CFG_8 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M1_R0_CFG_8 , x_sel  );
                end
                {RANK1, 8'd0} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M1_R1_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M1_R1_CFG_0 , x_sel  );
                end
                {RANK1, 8'd1} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M1_R1_CFG_1 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M1_R1_CFG_1 , x_sel  );
                end
                {RANK1, 8'd2} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M1_R1_CFG_2 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M1_R1_CFG_2 , x_sel  );
                end
                {RANK1, 8'd3} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M1_R1_CFG_3 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M1_R1_CFG_3 , x_sel  );
                end
                {RANK1, 8'd4} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M1_R1_CFG_4 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M1_R1_CFG_4 , x_sel  );
                end
                {RANK1, 8'd5} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M1_R1_CFG_5 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M1_R1_CFG_5 , x_sel  );
                end
                {RANK1, 8'd6} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M1_R1_CFG_6 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M1_R1_CFG_6 , x_sel  );
                end
                {RANK1, 8'd7} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M1_R1_CFG_7 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M1_R1_CFG_7 , x_sel  );
                end
                {RANK1, 8'd8} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M1_R1_CFG_8 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M1_R1_CFG_8 , x_sel  );
                end
                default: begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M1_R0_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M1_R1_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M1_R0_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M1_R1_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M1_R0_CFG_1 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M1_R1_CFG_1 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M1_R0_CFG_1 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M1_R1_CFG_1 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M1_R0_CFG_2 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M1_R1_CFG_2 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M1_R0_CFG_2 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M1_R1_CFG_2 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M1_R0_CFG_3 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M1_R1_CFG_3 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M1_R0_CFG_3 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M1_R1_CFG_3 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M1_R0_CFG_4 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M1_R1_CFG_4 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M1_R0_CFG_4 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M1_R1_CFG_4 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M1_R0_CFG_5 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M1_R1_CFG_5 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M1_R0_CFG_5 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M1_R1_CFG_5 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M1_R0_CFG_6 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M1_R1_CFG_6 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M1_R0_CFG_6 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M1_R1_CFG_6 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M1_R0_CFG_7 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M1_R1_CFG_7 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M1_R0_CFG_7 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M1_R1_CFG_7 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M1_R0_CFG_8 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M1_R1_CFG_8 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M1_R0_CFG_8 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M1_R1_CFG_8 , x_sel  );
                end
            endcase
        end
        if((byte_sel == CA) || (byte_sel == ALL)) begin
            case ({rank_sel,dq})
                {RANK0, 8'd0} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_DDR_X_SEL_M1_R0_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_DDR_X_SEL_M1_R0_CFG_0 , x_sel  );
                end
                {RANK0, 8'd1} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_DDR_X_SEL_M1_R0_CFG_1 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_DDR_X_SEL_M1_R0_CFG_1 , x_sel  );
                end
                {RANK0, 8'd2} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_DDR_X_SEL_M1_R0_CFG_2 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_DDR_X_SEL_M1_R0_CFG_2 , x_sel  );
                end
                {RANK0, 8'd3} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_DDR_X_SEL_M1_R0_CFG_3 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_DDR_X_SEL_M1_R0_CFG_3 , x_sel  );
                end
                {RANK0, 8'd4} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_DDR_X_SEL_M1_R0_CFG_4 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_DDR_X_SEL_M1_R0_CFG_4 , x_sel  );
                end
                {RANK0, 8'd5} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_DDR_X_SEL_M1_R0_CFG_5 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_DDR_X_SEL_M1_R0_CFG_5 , x_sel  );
                end
                {RANK0, 8'd6} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_DDR_X_SEL_M1_R0_CFG_6 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_DDR_X_SEL_M1_R0_CFG_6 , x_sel  );
                end
                {RANK0, 8'd7} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_DDR_X_SEL_M1_R0_CFG_7 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_DDR_X_SEL_M1_R0_CFG_7 , x_sel  );
                end
                {RANK0, 8'd8} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_DDR_X_SEL_M1_R0_CFG_8 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_DDR_X_SEL_M1_R0_CFG_8 , x_sel  );
                end
                {RANK0, 8'd9} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_DDR_X_SEL_M1_R0_CFG_9 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_DDR_X_SEL_M1_R0_CFG_9 , x_sel  );
                end
                {RANK0, 8'd10} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_DDR_X_SEL_M1_R0_CFG_10 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_DDR_X_SEL_M1_R0_CFG_10 , x_sel  );
                end
                {RANK1, 8'd0} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_DDR_X_SEL_M1_R1_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_DDR_X_SEL_M1_R1_CFG_0 , x_sel  );
                end
                {RANK1, 8'd1} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_DDR_X_SEL_M1_R1_CFG_1 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_DDR_X_SEL_M1_R1_CFG_1 , x_sel  );
                end
                {RANK1, 8'd2} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_DDR_X_SEL_M1_R1_CFG_2 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_DDR_X_SEL_M1_R1_CFG_2 , x_sel  );
                end
                {RANK1, 8'd3} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_DDR_X_SEL_M1_R1_CFG_3 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_DDR_X_SEL_M1_R1_CFG_3 , x_sel  );
                end
                {RANK1, 8'd4} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_DDR_X_SEL_M1_R1_CFG_4 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_DDR_X_SEL_M1_R1_CFG_4 , x_sel  );
                end
                {RANK1, 8'd5} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_DDR_X_SEL_M1_R1_CFG_5 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_DDR_X_SEL_M1_R1_CFG_5 , x_sel  );
                end
                {RANK1, 8'd6} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_DDR_X_SEL_M1_R1_CFG_6 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_DDR_X_SEL_M1_R1_CFG_6 , x_sel  );
                end
                {RANK1, 8'd7} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_DDR_X_SEL_M1_R1_CFG_7 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_DDR_X_SEL_M1_R1_CFG_7 , x_sel  );
                end
                {RANK1, 8'd8} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_DDR_X_SEL_M1_R1_CFG_8 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_DDR_X_SEL_M1_R1_CFG_8 , x_sel  );
                end
                {RANK1, 8'd9} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_DDR_X_SEL_M1_R1_CFG_9 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_DDR_X_SEL_M1_R1_CFG_9 , x_sel  );
                end
                {RANK1, 8'd10} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_DDR_X_SEL_M1_R1_CFG_10 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_DDR_X_SEL_M1_R1_CFG_10 , x_sel  );
                end
                default: begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_DDR_X_SEL_M1_R0_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_DDR_X_SEL_M1_R1_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_DDR_X_SEL_M1_R0_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_DDR_X_SEL_M1_R1_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_DDR_X_SEL_M1_R0_CFG_1 , x_sel  );
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_DDR_X_SEL_M1_R1_CFG_1 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_DDR_X_SEL_M1_R0_CFG_1 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_DDR_X_SEL_M1_R1_CFG_1 , x_sel  );
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_DDR_X_SEL_M1_R0_CFG_2 , x_sel  );
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_DDR_X_SEL_M1_R1_CFG_2 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_DDR_X_SEL_M1_R0_CFG_2 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_DDR_X_SEL_M1_R1_CFG_2 , x_sel  );
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_DDR_X_SEL_M1_R0_CFG_3 , x_sel  );
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_DDR_X_SEL_M1_R1_CFG_3 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_DDR_X_SEL_M1_R0_CFG_3 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_DDR_X_SEL_M1_R1_CFG_3 , x_sel  );
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_DDR_X_SEL_M1_R0_CFG_4 , x_sel  );
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_DDR_X_SEL_M1_R1_CFG_4 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_DDR_X_SEL_M1_R0_CFG_4 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_DDR_X_SEL_M1_R1_CFG_4 , x_sel  );
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_DDR_X_SEL_M1_R0_CFG_5 , x_sel  );
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_DDR_X_SEL_M1_R1_CFG_5 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_DDR_X_SEL_M1_R0_CFG_5 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_DDR_X_SEL_M1_R1_CFG_5 , x_sel  );
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_DDR_X_SEL_M1_R0_CFG_6 , x_sel  );
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_DDR_X_SEL_M1_R1_CFG_6 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_DDR_X_SEL_M1_R0_CFG_6 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_DDR_X_SEL_M1_R1_CFG_6 , x_sel  );
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_DDR_X_SEL_M1_R0_CFG_7 , x_sel  );
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_DDR_X_SEL_M1_R1_CFG_7 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_DDR_X_SEL_M1_R0_CFG_7 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_DDR_X_SEL_M1_R1_CFG_7 , x_sel  );
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_DDR_X_SEL_M1_R0_CFG_8 , x_sel  );
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_DDR_X_SEL_M1_R1_CFG_8 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_DDR_X_SEL_M1_R0_CFG_8 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_DDR_X_SEL_M1_R1_CFG_8 , x_sel  );
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_DDR_X_SEL_M1_R0_CFG_9 , x_sel  );
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_DDR_X_SEL_M1_R1_CFG_9 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_DDR_X_SEL_M1_R0_CFG_9 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_DDR_X_SEL_M1_R1_CFG_9 , x_sel  );
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_DDR_X_SEL_M1_R0_CFG_10 , x_sel  );
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_DDR_X_SEL_M1_R1_CFG_10 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_DDR_X_SEL_M1_R0_CFG_10 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_DDR_X_SEL_M1_R1_CFG_10 , x_sel  );
                end
            endcase
        end
    end
endtask

task automatic set_txdq_ddr_pipe_en_m1 ;
    input byte_sel_t     byte_sel;
    input rank_sel_t     rank_sel;
    input logic    [7:0] dq;
    input logic   [31:0] pipe_en;
    begin
        if((byte_sel == DQ0) || (byte_sel == DQ_ALL) || (byte_sel == ALL)) begin
            case ({rank_sel,dq})
                {RANK0, 8'd0} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_M1_R0_CFG_0       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_M1_R0_CFG_0       , pipe_en);
                end
                {RANK0, 8'd1} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_M1_R0_CFG_1       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_M1_R0_CFG_1       , pipe_en);
                end
                {RANK0, 8'd2} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_M1_R0_CFG_2       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_M1_R0_CFG_2       , pipe_en);
                end
                {RANK0, 8'd3} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_M1_R0_CFG_3       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_M1_R0_CFG_3       , pipe_en);
                end
                {RANK0, 8'd4} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_M1_R0_CFG_4       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_M1_R0_CFG_4       , pipe_en);
                end
                {RANK0, 8'd5} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_M1_R0_CFG_5       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_M1_R0_CFG_5       , pipe_en);
                end
                {RANK0, 8'd6} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_M1_R0_CFG_6       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_M1_R0_CFG_6       , pipe_en);
                end
                {RANK0, 8'd7} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_M1_R0_CFG_7       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_M1_R0_CFG_7       , pipe_en);
                end
                {RANK0, 8'd8} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_M1_R0_CFG_8       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_M1_R0_CFG_8       , pipe_en);
                end
                {RANK1, 8'd0} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_M1_R1_CFG_0       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_M1_R1_CFG_0       , pipe_en);
                end
                {RANK1, 8'd1} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_M1_R1_CFG_1       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_M1_R1_CFG_1       , pipe_en);
                end
                {RANK1, 8'd2} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_M1_R1_CFG_2       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_M1_R1_CFG_2       , pipe_en);
                end
                {RANK1, 8'd3} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_M1_R1_CFG_3       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_M1_R1_CFG_3       , pipe_en);
                end
                {RANK1, 8'd4} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_M1_R1_CFG_4       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_M1_R1_CFG_4       , pipe_en);
                end
                {RANK1, 8'd5} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_M1_R1_CFG_5       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_M1_R1_CFG_5       , pipe_en);
                end
                {RANK1, 8'd6} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_M1_R1_CFG_6       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_M1_R1_CFG_6       , pipe_en);
                end
                {RANK1, 8'd7} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_M1_R1_CFG_7       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_M1_R1_CFG_7       , pipe_en);
                end
                {RANK1, 8'd8} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_M1_R1_CFG_8       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_M1_R1_CFG_8       , pipe_en);
                end
                default: begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_M1_R0_CFG_0       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_M1_R0_CFG_0       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_M1_R0_CFG_1       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_M1_R0_CFG_1       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_M1_R0_CFG_2       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_M1_R0_CFG_2       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_M1_R0_CFG_3       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_M1_R0_CFG_3       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_M1_R0_CFG_4       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_M1_R0_CFG_4       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_M1_R0_CFG_5       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_M1_R0_CFG_5       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_M1_R0_CFG_6       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_M1_R0_CFG_6       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_M1_R0_CFG_7       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_M1_R0_CFG_7       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_M1_R0_CFG_8       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_M1_R0_CFG_8       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_M1_R1_CFG_0       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_M1_R1_CFG_0       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_M1_R1_CFG_1       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_M1_R1_CFG_1       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_M1_R1_CFG_2       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_M1_R1_CFG_2       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_M1_R1_CFG_3       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_M1_R1_CFG_3       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_M1_R1_CFG_4       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_M1_R1_CFG_4       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_M1_R1_CFG_5       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_M1_R1_CFG_5       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_M1_R1_CFG_6       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_M1_R1_CFG_6       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_M1_R1_CFG_7       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_M1_R1_CFG_7       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_M1_R1_CFG_8       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_M1_R1_CFG_8       , pipe_en);
                end
            endcase
        end
        if((byte_sel == DQ1) || (byte_sel == DQ_ALL) || (byte_sel == ALL)) begin
            case ({rank_sel,dq})
                {RANK0, 8'd0} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_M1_R0_CFG_0       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_M1_R0_CFG_0       , pipe_en);
                end
                {RANK0, 8'd1} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_M1_R0_CFG_1       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_M1_R0_CFG_1       , pipe_en);
                end
                {RANK0, 8'd2} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_M1_R0_CFG_2       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_M1_R0_CFG_2       , pipe_en);
                end
                {RANK0, 8'd3} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_M1_R0_CFG_3       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_M1_R0_CFG_3       , pipe_en);
                end
                {RANK0, 8'd4} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_M1_R0_CFG_4       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_M1_R0_CFG_4       , pipe_en);
                end
                {RANK0, 8'd5} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_M1_R0_CFG_5       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_M1_R0_CFG_5       , pipe_en);
                end
                {RANK0, 8'd6} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_M1_R0_CFG_6       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_M1_R0_CFG_6       , pipe_en);
                end
                {RANK0, 8'd7} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_M1_R0_CFG_7       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_M1_R0_CFG_7       , pipe_en);
                end
                {RANK0, 8'd8} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_M1_R0_CFG_8       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_M1_R0_CFG_8       , pipe_en);
                end
                {RANK1, 8'd0} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_M1_R1_CFG_0       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_M1_R1_CFG_0       , pipe_en);
                end
                {RANK1, 8'd1} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_M1_R1_CFG_1       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_M1_R1_CFG_1       , pipe_en);
                end
                {RANK1, 8'd2} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_M1_R1_CFG_2       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_M1_R1_CFG_2       , pipe_en);
                end
                {RANK1, 8'd3} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_M1_R1_CFG_3       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_M1_R1_CFG_3       , pipe_en);
                end
                {RANK1, 8'd4} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_M1_R1_CFG_4       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_M1_R1_CFG_4       , pipe_en);
                end
                {RANK1, 8'd5} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_M1_R1_CFG_5       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_M1_R1_CFG_5       , pipe_en);
                end
                {RANK1, 8'd6} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_M1_R1_CFG_6       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_M1_R1_CFG_6       , pipe_en);
                end
                {RANK1, 8'd7} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_M1_R1_CFG_7       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_M1_R1_CFG_7       , pipe_en);
                end
                {RANK1, 8'd8} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_M1_R1_CFG_8       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_M1_R1_CFG_8       , pipe_en);
                end
                default: begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_M1_R0_CFG_0       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_M1_R0_CFG_0       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_M1_R0_CFG_1       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_M1_R0_CFG_1       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_M1_R0_CFG_2       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_M1_R0_CFG_2       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_M1_R0_CFG_3       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_M1_R0_CFG_3       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_M1_R0_CFG_4       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_M1_R0_CFG_4       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_M1_R0_CFG_5       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_M1_R0_CFG_5       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_M1_R0_CFG_6       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_M1_R0_CFG_6       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_M1_R0_CFG_7       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_M1_R0_CFG_7       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_M1_R0_CFG_8       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_M1_R0_CFG_8       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_M1_R1_CFG_0       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_M1_R1_CFG_0       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_M1_R1_CFG_1       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_M1_R1_CFG_1       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_M1_R1_CFG_2       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_M1_R1_CFG_2       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_M1_R1_CFG_3       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_M1_R1_CFG_3       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_M1_R1_CFG_4       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_M1_R1_CFG_4       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_M1_R1_CFG_5       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_M1_R1_CFG_5       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_M1_R1_CFG_6       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_M1_R1_CFG_6       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_M1_R1_CFG_7       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_M1_R1_CFG_7       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_M1_R1_CFG_8       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_M1_R1_CFG_8       , pipe_en);
                end
            endcase
        end
        if((byte_sel == CA) || (byte_sel == ALL)) begin
            case ({rank_sel,dq})
                {RANK0, 8'd0} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_DDR_M1_R0_CFG_0       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_DDR_M1_R0_CFG_0       , pipe_en);
                end
                {RANK0, 8'd1} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_DDR_M1_R0_CFG_1       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_DDR_M1_R0_CFG_1       , pipe_en);
                end
                {RANK0, 8'd2} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_DDR_M1_R0_CFG_2       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_DDR_M1_R0_CFG_2       , pipe_en);
                end
                {RANK0, 8'd3} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_DDR_M1_R0_CFG_3       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_DDR_M1_R0_CFG_3       , pipe_en);
                end
                {RANK0, 8'd4} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_DDR_M1_R0_CFG_4       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_DDR_M1_R0_CFG_4       , pipe_en);
                end
                {RANK0, 8'd5} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_DDR_M1_R0_CFG_5       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_DDR_M1_R0_CFG_5       , pipe_en);
                end
                {RANK0, 8'd6} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_DDR_M1_R0_CFG_6       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_DDR_M1_R0_CFG_6       , pipe_en);
                end
                {RANK0, 8'd7} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_DDR_M1_R0_CFG_7       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_DDR_M1_R0_CFG_7       , pipe_en);
                end
                {RANK0, 8'd8} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_DDR_M1_R0_CFG_8       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_DDR_M1_R0_CFG_8       , pipe_en);
                end
                {RANK0, 8'd9} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_DDR_M1_R0_CFG_9       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_DDR_M1_R0_CFG_9       , pipe_en);
                end
                {RANK0, 8'd10} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_DDR_M1_R0_CFG_10       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_DDR_M1_R0_CFG_10       , pipe_en);
                end
                {RANK1, 8'd0} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_DDR_M1_R1_CFG_0       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_DDR_M1_R1_CFG_0       , pipe_en);
                end
                {RANK1, 8'd1} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_DDR_M1_R1_CFG_1       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_DDR_M1_R1_CFG_1       , pipe_en);
                end
                {RANK1, 8'd2} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_DDR_M1_R1_CFG_2       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_DDR_M1_R1_CFG_2       , pipe_en);
                end
                {RANK1, 8'd3} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_DDR_M1_R1_CFG_3       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_DDR_M1_R1_CFG_3       , pipe_en);
                end
                {RANK1, 8'd4} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_DDR_M1_R1_CFG_4       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_DDR_M1_R1_CFG_4       , pipe_en);
                end
                {RANK1, 8'd5} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_DDR_M1_R1_CFG_5       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_DDR_M1_R1_CFG_5       , pipe_en);
                end
                {RANK1, 8'd6} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_DDR_M1_R1_CFG_6       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_DDR_M1_R1_CFG_6       , pipe_en);
                end
                {RANK1, 8'd7} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_DDR_M1_R1_CFG_7       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_DDR_M1_R1_CFG_7       , pipe_en);
                end
                {RANK1, 8'd8} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_DDR_M1_R1_CFG_8       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_DDR_M1_R1_CFG_8       , pipe_en);
                end
                {RANK1, 8'd9} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_DDR_M1_R1_CFG_9       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_DDR_M1_R1_CFG_9       , pipe_en);
                end
                {RANK1, 8'd10} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_DDR_M1_R1_CFG_10       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_DDR_M1_R1_CFG_10       , pipe_en);
                end
                default: begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_DDR_M1_R0_CFG_0       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_DDR_M1_R0_CFG_0       , pipe_en);
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_DDR_M1_R0_CFG_1       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_DDR_M1_R0_CFG_1       , pipe_en);
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_DDR_M1_R0_CFG_2       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_DDR_M1_R0_CFG_2       , pipe_en);
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_DDR_M1_R0_CFG_3       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_DDR_M1_R0_CFG_3       , pipe_en);
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_DDR_M1_R0_CFG_4       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_DDR_M1_R0_CFG_4       , pipe_en);
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_DDR_M1_R0_CFG_5       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_DDR_M1_R0_CFG_5       , pipe_en);
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_DDR_M1_R0_CFG_6       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_DDR_M1_R0_CFG_6       , pipe_en);
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_DDR_M1_R0_CFG_7       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_DDR_M1_R0_CFG_7       , pipe_en);
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_DDR_M1_R0_CFG_8       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_DDR_M1_R0_CFG_8       , pipe_en);
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_DDR_M1_R0_CFG_9       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_DDR_M1_R0_CFG_9       , pipe_en);
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_DDR_M1_R0_CFG_10       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_DDR_M1_R0_CFG_10       , pipe_en);
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_DDR_M1_R1_CFG_0       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_DDR_M1_R1_CFG_0       , pipe_en);
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_DDR_M1_R1_CFG_1       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_DDR_M1_R1_CFG_1       , pipe_en);
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_DDR_M1_R1_CFG_2       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_DDR_M1_R1_CFG_2       , pipe_en);
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_DDR_M1_R1_CFG_3       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_DDR_M1_R1_CFG_3       , pipe_en);
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_DDR_M1_R1_CFG_4       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_DDR_M1_R1_CFG_4       , pipe_en);
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_DDR_M1_R1_CFG_5       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_DDR_M1_R1_CFG_5       , pipe_en);
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_DDR_M1_R1_CFG_6       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_DDR_M1_R1_CFG_6       , pipe_en);
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_DDR_M1_R1_CFG_7       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_DDR_M1_R1_CFG_7       , pipe_en);
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_DDR_M1_R1_CFG_8       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_DDR_M1_R1_CFG_8       , pipe_en);
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_DDR_M1_R1_CFG_9       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_DDR_M1_R1_CFG_9       , pipe_en);
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_DDR_M1_R1_CFG_10       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_DDR_M1_R1_CFG_10       , pipe_en);
                end
            endcase
        end
    end
endtask

task automatic set_txdq_qdr_x_sel_m1;
    input byte_sel_t     byte_sel;
    input rank_sel_t     rank_sel;
    input logic    [7:0] dq;
    input logic   [31:0] x_sel;
    begin
        if((byte_sel == DQ0) || (byte_sel == DQ_ALL) || (byte_sel == ALL)) begin
            case ({rank_sel,dq})
                {RANK0, 8'd0} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M1_R0_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M1_R0_CFG_0 , x_sel  );
                end
                {RANK0, 8'd1} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M1_R0_CFG_1 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M1_R0_CFG_1 , x_sel  );
                end
                {RANK0, 8'd2} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M1_R0_CFG_2 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M1_R0_CFG_2 , x_sel  );
                end
                {RANK0, 8'd3} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M1_R0_CFG_3 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M1_R0_CFG_3 , x_sel  );
                end
                {RANK0, 8'd4} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M1_R0_CFG_4 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M1_R0_CFG_4 , x_sel  );
                end
                {RANK0, 8'd5} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M1_R0_CFG_5 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M1_R0_CFG_5 , x_sel  );
                end
                {RANK0, 8'd6} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M1_R0_CFG_6 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M1_R0_CFG_6 , x_sel  );
                end
                {RANK0, 8'd7} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M1_R0_CFG_7 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M1_R0_CFG_7 , x_sel  );
                end
                {RANK0, 8'd8} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M1_R0_CFG_8 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M1_R0_CFG_8 , x_sel  );
                end
                {RANK1, 8'd0} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M1_R1_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M1_R1_CFG_0 , x_sel  );
                end
                {RANK1, 8'd1} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M1_R1_CFG_1 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M1_R1_CFG_1 , x_sel  );
                end
                {RANK1, 8'd2} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M1_R1_CFG_2 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M1_R1_CFG_2 , x_sel  );
                end
                {RANK1, 8'd3} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M1_R1_CFG_3 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M1_R1_CFG_3 , x_sel  );
                end
                {RANK1, 8'd4} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M1_R1_CFG_4 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M1_R1_CFG_4 , x_sel  );
                end
                {RANK1, 8'd5} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M1_R1_CFG_5 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M1_R1_CFG_5 , x_sel  );
                end
                {RANK1, 8'd6} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M1_R1_CFG_6 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M1_R1_CFG_6 , x_sel  );
                end
                {RANK1, 8'd7} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M1_R1_CFG_7 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M1_R1_CFG_7 , x_sel  );
                end
                {RANK1, 8'd8} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M1_R1_CFG_8 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M1_R1_CFG_8 , x_sel  );
                end
                default: begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M1_R0_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M1_R1_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M1_R0_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M1_R1_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M1_R0_CFG_1 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M1_R1_CFG_1 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M1_R0_CFG_1 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M1_R1_CFG_1 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M1_R0_CFG_2 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M1_R1_CFG_2 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M1_R0_CFG_2 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M1_R1_CFG_2 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M1_R0_CFG_3 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M1_R1_CFG_3 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M1_R0_CFG_3 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M1_R1_CFG_3 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M1_R0_CFG_4 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M1_R1_CFG_4 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M1_R0_CFG_4 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M1_R1_CFG_4 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M1_R0_CFG_5 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M1_R1_CFG_5 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M1_R0_CFG_5 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M1_R1_CFG_5 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M1_R0_CFG_6 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M1_R1_CFG_6 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M1_R0_CFG_6 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M1_R1_CFG_6 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M1_R0_CFG_7 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M1_R1_CFG_7 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M1_R0_CFG_7 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M1_R1_CFG_7 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M1_R0_CFG_8 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M1_R1_CFG_8 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M1_R0_CFG_8 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M1_R1_CFG_8 , x_sel  );
                end
            endcase
        end
        if((byte_sel == DQ1) || (byte_sel == DQ_ALL) || (byte_sel == ALL)) begin
            case ({rank_sel,dq})
                {RANK0, 8'd0} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M1_R0_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M1_R0_CFG_0 , x_sel  );
                end
                {RANK0, 8'd1} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M1_R0_CFG_1 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M1_R0_CFG_1 , x_sel  );
                end
                {RANK0, 8'd2} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M1_R0_CFG_2 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M1_R0_CFG_2 , x_sel  );
                end
                {RANK0, 8'd3} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M1_R0_CFG_3 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M1_R0_CFG_3 , x_sel  );
                end
                {RANK0, 8'd4} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M1_R0_CFG_4 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M1_R0_CFG_4 , x_sel  );
                end
                {RANK0, 8'd5} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M1_R0_CFG_5 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M1_R0_CFG_5 , x_sel  );
                end
                {RANK0, 8'd6} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M1_R0_CFG_6 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M1_R0_CFG_6 , x_sel  );
                end
                {RANK0, 8'd7} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M1_R0_CFG_7 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M1_R0_CFG_7 , x_sel  );
                end
                {RANK0, 8'd8} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M1_R0_CFG_8 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M1_R0_CFG_8 , x_sel  );
                end
                {RANK1, 8'd0} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M1_R1_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M1_R1_CFG_0 , x_sel  );
                end
                {RANK1, 8'd1} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M1_R1_CFG_1 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M1_R1_CFG_1 , x_sel  );
                end
                {RANK1, 8'd2} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M1_R1_CFG_2 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M1_R1_CFG_2 , x_sel  );
                end
                {RANK1, 8'd3} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M1_R1_CFG_3 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M1_R1_CFG_3 , x_sel  );
                end
                {RANK1, 8'd4} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M1_R1_CFG_4 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M1_R1_CFG_4 , x_sel  );
                end
                {RANK1, 8'd5} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M1_R1_CFG_5 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M1_R1_CFG_5 , x_sel  );
                end
                {RANK1, 8'd6} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M1_R1_CFG_6 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M1_R1_CFG_6 , x_sel  );
                end
                {RANK1, 8'd7} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M1_R1_CFG_7 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M1_R1_CFG_7 , x_sel  );
                end
                {RANK1, 8'd8} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M1_R1_CFG_8 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M1_R1_CFG_8 , x_sel  );
                end
                default: begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M1_R0_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M1_R1_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M1_R0_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M1_R1_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M1_R0_CFG_1 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M1_R1_CFG_1 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M1_R0_CFG_1 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M1_R1_CFG_1 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M1_R0_CFG_2 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M1_R1_CFG_2 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M1_R0_CFG_2 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M1_R1_CFG_2 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M1_R0_CFG_3 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M1_R1_CFG_3 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M1_R0_CFG_3 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M1_R1_CFG_3 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M1_R0_CFG_4 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M1_R1_CFG_4 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M1_R0_CFG_4 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M1_R1_CFG_4 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M1_R0_CFG_5 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M1_R1_CFG_5 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M1_R0_CFG_5 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M1_R1_CFG_5 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M1_R0_CFG_6 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M1_R1_CFG_6 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M1_R0_CFG_6 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M1_R1_CFG_6 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M1_R0_CFG_7 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M1_R1_CFG_7 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M1_R0_CFG_7 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M1_R1_CFG_7 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M1_R0_CFG_8 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M1_R1_CFG_8 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M1_R0_CFG_8 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M1_R1_CFG_8 , x_sel  );
                end
            endcase
        end
        if((byte_sel == CA) || (byte_sel == ALL)) begin
            case ({rank_sel,dq})
                {RANK0, 8'd0} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_QDR_X_SEL_M1_R0_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_QDR_X_SEL_M1_R0_CFG_0 , x_sel  );
                end
                {RANK0, 8'd1} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_QDR_X_SEL_M1_R0_CFG_1 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_QDR_X_SEL_M1_R0_CFG_1 , x_sel  );
                end
                {RANK0, 8'd2} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_QDR_X_SEL_M1_R0_CFG_2 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_QDR_X_SEL_M1_R0_CFG_2 , x_sel  );
                end
                {RANK0, 8'd3} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_QDR_X_SEL_M1_R0_CFG_3 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_QDR_X_SEL_M1_R0_CFG_3 , x_sel  );
                end
                {RANK0, 8'd4} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_QDR_X_SEL_M1_R0_CFG_4 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_QDR_X_SEL_M1_R0_CFG_4 , x_sel  );
                end
                {RANK0, 8'd5} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_QDR_X_SEL_M1_R0_CFG_5 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_QDR_X_SEL_M1_R0_CFG_5 , x_sel  );
                end
                {RANK0, 8'd6} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_QDR_X_SEL_M1_R0_CFG_6 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_QDR_X_SEL_M1_R0_CFG_6 , x_sel  );
                end
                {RANK0, 8'd7} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_QDR_X_SEL_M1_R0_CFG_7 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_QDR_X_SEL_M1_R0_CFG_7 , x_sel  );
                end
                {RANK0, 8'd8} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_QDR_X_SEL_M1_R0_CFG_8 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_QDR_X_SEL_M1_R0_CFG_8 , x_sel  );
                end
                {RANK0, 8'd9} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_QDR_X_SEL_M1_R0_CFG_9 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_QDR_X_SEL_M1_R0_CFG_9 , x_sel  );
                end
                {RANK0, 8'd10} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_QDR_X_SEL_M1_R0_CFG_10 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_QDR_X_SEL_M1_R0_CFG_10 , x_sel  );
                end
                {RANK1, 8'd0} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_QDR_X_SEL_M1_R1_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_QDR_X_SEL_M1_R1_CFG_0 , x_sel  );
                end
                {RANK1, 8'd1} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_QDR_X_SEL_M1_R1_CFG_1 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_QDR_X_SEL_M1_R1_CFG_1 , x_sel  );
                end
                {RANK1, 8'd2} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_QDR_X_SEL_M1_R1_CFG_2 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_QDR_X_SEL_M1_R1_CFG_2 , x_sel  );
                end
                {RANK1, 8'd3} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_QDR_X_SEL_M1_R1_CFG_3 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_QDR_X_SEL_M1_R1_CFG_3 , x_sel  );
                end
                {RANK1, 8'd4} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_QDR_X_SEL_M1_R1_CFG_4 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_QDR_X_SEL_M1_R1_CFG_4 , x_sel  );
                end
                {RANK1, 8'd5} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_QDR_X_SEL_M1_R1_CFG_5 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_QDR_X_SEL_M1_R1_CFG_5 , x_sel  );
                end
                {RANK1, 8'd6} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_QDR_X_SEL_M1_R1_CFG_6 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_QDR_X_SEL_M1_R1_CFG_6 , x_sel  );
                end
                {RANK1, 8'd7} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_QDR_X_SEL_M1_R1_CFG_7 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_QDR_X_SEL_M1_R1_CFG_7 , x_sel  );
                end
                {RANK1, 8'd8} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_QDR_X_SEL_M1_R1_CFG_8 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_QDR_X_SEL_M1_R1_CFG_8 , x_sel  );
                end
                {RANK1, 8'd9} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_QDR_X_SEL_M1_R1_CFG_9 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_QDR_X_SEL_M1_R1_CFG_9 , x_sel  );
                end
                {RANK1, 8'd10} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_QDR_X_SEL_M1_R1_CFG_10 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_QDR_X_SEL_M1_R1_CFG_10 , x_sel  );
                end
                default: begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_QDR_X_SEL_M1_R0_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_QDR_X_SEL_M1_R1_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_QDR_X_SEL_M1_R0_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_QDR_X_SEL_M1_R1_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_QDR_X_SEL_M1_R0_CFG_1 , x_sel  );
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_QDR_X_SEL_M1_R1_CFG_1 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_QDR_X_SEL_M1_R0_CFG_1 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_QDR_X_SEL_M1_R1_CFG_1 , x_sel  );
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_QDR_X_SEL_M1_R0_CFG_2 , x_sel  );
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_QDR_X_SEL_M1_R1_CFG_2 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_QDR_X_SEL_M1_R0_CFG_2 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_QDR_X_SEL_M1_R1_CFG_2 , x_sel  );
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_QDR_X_SEL_M1_R0_CFG_3 , x_sel  );
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_QDR_X_SEL_M1_R1_CFG_3 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_QDR_X_SEL_M1_R0_CFG_3 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_QDR_X_SEL_M1_R1_CFG_3 , x_sel  );
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_QDR_X_SEL_M1_R0_CFG_4 , x_sel  );
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_QDR_X_SEL_M1_R1_CFG_4 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_QDR_X_SEL_M1_R0_CFG_4 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_QDR_X_SEL_M1_R1_CFG_4 , x_sel  );
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_QDR_X_SEL_M1_R0_CFG_5 , x_sel  );
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_QDR_X_SEL_M1_R1_CFG_5 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_QDR_X_SEL_M1_R0_CFG_5 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_QDR_X_SEL_M1_R1_CFG_5 , x_sel  );
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_QDR_X_SEL_M1_R0_CFG_6 , x_sel  );
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_QDR_X_SEL_M1_R1_CFG_6 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_QDR_X_SEL_M1_R0_CFG_6 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_QDR_X_SEL_M1_R1_CFG_6 , x_sel  );
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_QDR_X_SEL_M1_R0_CFG_7 , x_sel  );
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_QDR_X_SEL_M1_R1_CFG_7 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_QDR_X_SEL_M1_R0_CFG_7 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_QDR_X_SEL_M1_R1_CFG_7 , x_sel  );
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_QDR_X_SEL_M1_R0_CFG_8 , x_sel  );
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_QDR_X_SEL_M1_R1_CFG_8 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_QDR_X_SEL_M1_R0_CFG_8 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_QDR_X_SEL_M1_R1_CFG_8 , x_sel  );
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_QDR_X_SEL_M1_R0_CFG_9 , x_sel  );
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_QDR_X_SEL_M1_R1_CFG_9 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_QDR_X_SEL_M1_R0_CFG_9 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_QDR_X_SEL_M1_R1_CFG_9 , x_sel  );
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_QDR_X_SEL_M1_R0_CFG_10 , x_sel  );
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_QDR_X_SEL_M1_R1_CFG_10 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_QDR_X_SEL_M1_R0_CFG_10 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_QDR_X_SEL_M1_R1_CFG_10 , x_sel  );
                end
            endcase
        end
    end
endtask

task automatic set_txdq_qdr_pipe_en_m1 ;
    input byte_sel_t     byte_sel;
    input rank_sel_t     rank_sel;
    input logic    [7:0] dq;
    input logic   [31:0] pipe_en;
    begin
        if((byte_sel == DQ0) || (byte_sel == DQ_ALL) || (byte_sel == ALL)) begin
            case ({rank_sel,dq})
                {RANK0, 8'd0} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_M1_R0_CFG_0       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_M1_R0_CFG_0       , pipe_en);
                end
                {RANK0, 8'd1} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_M1_R0_CFG_1       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_M1_R0_CFG_1       , pipe_en);
                end
                {RANK0, 8'd2} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_M1_R0_CFG_2       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_M1_R0_CFG_2       , pipe_en);
                end
                {RANK0, 8'd3} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_M1_R0_CFG_3       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_M1_R0_CFG_3       , pipe_en);
                end
                {RANK0, 8'd4} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_M1_R0_CFG_4       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_M1_R0_CFG_4       , pipe_en);
                end
                {RANK0, 8'd5} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_M1_R0_CFG_5       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_M1_R0_CFG_5       , pipe_en);
                end
                {RANK0, 8'd6} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_M1_R0_CFG_6       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_M1_R0_CFG_6       , pipe_en);
                end
                {RANK0, 8'd7} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_M1_R0_CFG_7       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_M1_R0_CFG_7       , pipe_en);
                end
                {RANK0, 8'd8} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_M1_R0_CFG_8       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_M1_R0_CFG_8       , pipe_en);
                end
                {RANK1, 8'd0} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_M1_R1_CFG_0       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_M1_R1_CFG_0       , pipe_en);
                end
                {RANK1, 8'd1} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_M1_R1_CFG_1       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_M1_R1_CFG_1       , pipe_en);
                end
                {RANK1, 8'd2} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_M1_R1_CFG_2       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_M1_R1_CFG_2       , pipe_en);
                end
                {RANK1, 8'd3} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_M1_R1_CFG_3       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_M1_R1_CFG_3       , pipe_en);
                end
                {RANK1, 8'd4} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_M1_R1_CFG_4       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_M1_R1_CFG_4       , pipe_en);
                end
                {RANK1, 8'd5} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_M1_R1_CFG_5       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_M1_R1_CFG_5       , pipe_en);
                end
                {RANK1, 8'd6} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_M1_R1_CFG_6       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_M1_R1_CFG_6       , pipe_en);
                end
                {RANK1, 8'd7} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_M1_R1_CFG_7       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_M1_R1_CFG_7       , pipe_en);
                end
                {RANK1, 8'd8} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_M1_R1_CFG_8       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_M1_R1_CFG_8       , pipe_en);
                end
                default: begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_M1_R0_CFG_0       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_M1_R0_CFG_0       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_M1_R0_CFG_1       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_M1_R0_CFG_1       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_M1_R0_CFG_2       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_M1_R0_CFG_2       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_M1_R0_CFG_3       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_M1_R0_CFG_3       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_M1_R0_CFG_4       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_M1_R0_CFG_4       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_M1_R0_CFG_5       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_M1_R0_CFG_5       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_M1_R0_CFG_6       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_M1_R0_CFG_6       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_M1_R0_CFG_7       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_M1_R0_CFG_7       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_M1_R0_CFG_8       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_M1_R0_CFG_8       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_M1_R1_CFG_0       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_M1_R1_CFG_0       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_M1_R1_CFG_1       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_M1_R1_CFG_1       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_M1_R1_CFG_2       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_M1_R1_CFG_2       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_M1_R1_CFG_3       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_M1_R1_CFG_3       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_M1_R1_CFG_4       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_M1_R1_CFG_4       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_M1_R1_CFG_5       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_M1_R1_CFG_5       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_M1_R1_CFG_6       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_M1_R1_CFG_6       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_M1_R1_CFG_7       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_M1_R1_CFG_7       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_M1_R1_CFG_8       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_M1_R1_CFG_8       , pipe_en);
                end
            endcase
        end
        if((byte_sel == DQ1) || (byte_sel == DQ_ALL) || (byte_sel == ALL)) begin
            case ({rank_sel,dq})
                {RANK0, 8'd0} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_M1_R0_CFG_0       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_M1_R0_CFG_0       , pipe_en);
                end
                {RANK0, 8'd1} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_M1_R0_CFG_1       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_M1_R0_CFG_1       , pipe_en);
                end
                {RANK0, 8'd2} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_M1_R0_CFG_2       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_M1_R0_CFG_2       , pipe_en);
                end
                {RANK0, 8'd3} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_M1_R0_CFG_3       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_M1_R0_CFG_3       , pipe_en);
                end
                {RANK0, 8'd4} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_M1_R0_CFG_4       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_M1_R0_CFG_4       , pipe_en);
                end
                {RANK0, 8'd5} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_M1_R0_CFG_5       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_M1_R0_CFG_5       , pipe_en);
                end
                {RANK0, 8'd6} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_M1_R0_CFG_6       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_M1_R0_CFG_6       , pipe_en);
                end
                {RANK0, 8'd7} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_M1_R0_CFG_7       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_M1_R0_CFG_7       , pipe_en);
                end
                {RANK0, 8'd8} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_M1_R0_CFG_8       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_M1_R0_CFG_8       , pipe_en);
                end
                {RANK1, 8'd0} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_M1_R1_CFG_0       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_M1_R1_CFG_0       , pipe_en);
                end
                {RANK1, 8'd1} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_M1_R1_CFG_1       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_M1_R1_CFG_1       , pipe_en);
                end
                {RANK1, 8'd2} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_M1_R1_CFG_2       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_M1_R1_CFG_2       , pipe_en);
                end
                {RANK1, 8'd3} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_M1_R1_CFG_3       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_M1_R1_CFG_3       , pipe_en);
                end
                {RANK1, 8'd4} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_M1_R1_CFG_4       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_M1_R1_CFG_4       , pipe_en);
                end
                {RANK1, 8'd5} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_M1_R1_CFG_5       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_M1_R1_CFG_5       , pipe_en);
                end
                {RANK1, 8'd6} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_M1_R1_CFG_6       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_M1_R1_CFG_6       , pipe_en);
                end
                {RANK1, 8'd7} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_M1_R1_CFG_7       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_M1_R1_CFG_7       , pipe_en);
                end
                {RANK1, 8'd8} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_M1_R1_CFG_8       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_M1_R1_CFG_8       , pipe_en);
                end
                default: begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_M1_R0_CFG_0       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_M1_R0_CFG_0       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_M1_R0_CFG_1       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_M1_R0_CFG_1       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_M1_R0_CFG_2       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_M1_R0_CFG_2       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_M1_R0_CFG_3       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_M1_R0_CFG_3       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_M1_R0_CFG_4       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_M1_R0_CFG_4       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_M1_R0_CFG_5       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_M1_R0_CFG_5       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_M1_R0_CFG_6       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_M1_R0_CFG_6       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_M1_R0_CFG_7       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_M1_R0_CFG_7       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_M1_R0_CFG_8       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_M1_R0_CFG_8       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_M1_R1_CFG_0       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_M1_R1_CFG_0       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_M1_R1_CFG_1       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_M1_R1_CFG_1       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_M1_R1_CFG_2       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_M1_R1_CFG_2       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_M1_R1_CFG_3       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_M1_R1_CFG_3       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_M1_R1_CFG_4       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_M1_R1_CFG_4       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_M1_R1_CFG_5       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_M1_R1_CFG_5       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_M1_R1_CFG_6       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_M1_R1_CFG_6       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_M1_R1_CFG_7       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_M1_R1_CFG_7       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_M1_R1_CFG_8       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_M1_R1_CFG_8       , pipe_en);
                end
            endcase
        end
        if((byte_sel == CA) || (byte_sel == ALL)) begin
            case ({rank_sel,dq})
                {RANK0, 8'd0} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_QDR_M1_R0_CFG_0       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_QDR_M1_R0_CFG_0       , pipe_en);
                end
                {RANK0, 8'd1} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_QDR_M1_R0_CFG_1       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_QDR_M1_R0_CFG_1       , pipe_en);
                end
                {RANK0, 8'd2} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_QDR_M1_R0_CFG_2       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_QDR_M1_R0_CFG_2       , pipe_en);
                end
                {RANK0, 8'd3} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_QDR_M1_R0_CFG_3       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_QDR_M1_R0_CFG_3       , pipe_en);
                end
                {RANK0, 8'd4} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_QDR_M1_R0_CFG_4       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_QDR_M1_R0_CFG_4       , pipe_en);
                end
                {RANK0, 8'd5} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_QDR_M1_R0_CFG_5       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_QDR_M1_R0_CFG_5       , pipe_en);
                end
                {RANK0, 8'd6} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_QDR_M1_R0_CFG_6       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_QDR_M1_R0_CFG_6       , pipe_en);
                end
                {RANK0, 8'd7} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_QDR_M1_R0_CFG_7       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_QDR_M1_R0_CFG_7       , pipe_en);
                end
                {RANK0, 8'd8} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_QDR_M1_R0_CFG_8       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_QDR_M1_R0_CFG_8       , pipe_en);
                end
                {RANK0, 8'd9} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_QDR_M1_R0_CFG_9       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_QDR_M1_R0_CFG_9       , pipe_en);
                end
                {RANK0, 8'd10} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_QDR_M1_R0_CFG_10       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_QDR_M1_R0_CFG_10       , pipe_en);
                end
                {RANK1, 8'd0} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_QDR_M1_R1_CFG_0       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_QDR_M1_R1_CFG_0       , pipe_en);
                end
                {RANK1, 8'd1} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_QDR_M1_R1_CFG_1       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_QDR_M1_R1_CFG_1       , pipe_en);
                end
                {RANK1, 8'd2} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_QDR_M1_R1_CFG_2       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_QDR_M1_R1_CFG_2       , pipe_en);
                end
                {RANK1, 8'd3} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_QDR_M1_R1_CFG_3       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_QDR_M1_R1_CFG_3       , pipe_en);
                end
                {RANK1, 8'd4} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_QDR_M1_R1_CFG_4       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_QDR_M1_R1_CFG_4       , pipe_en);
                end
                {RANK1, 8'd5} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_QDR_M1_R1_CFG_5       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_QDR_M1_R1_CFG_5       , pipe_en);
                end
                {RANK1, 8'd6} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_QDR_M1_R1_CFG_6       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_QDR_M1_R1_CFG_6       , pipe_en);
                end
                {RANK1, 8'd7} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_QDR_M1_R1_CFG_7       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_QDR_M1_R1_CFG_7       , pipe_en);
                end
                {RANK1, 8'd8} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_QDR_M1_R1_CFG_8       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_QDR_M1_R1_CFG_8       , pipe_en);
                end
                {RANK1, 8'd9} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_QDR_M1_R1_CFG_9       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_QDR_M1_R1_CFG_9       , pipe_en);
                end
                {RANK1, 8'd10} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_QDR_M1_R1_CFG_10       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_QDR_M1_R1_CFG_10       , pipe_en);
                end
                default: begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_QDR_M1_R0_CFG_0       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_QDR_M1_R0_CFG_0       , pipe_en);
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_QDR_M1_R0_CFG_1       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_QDR_M1_R0_CFG_1       , pipe_en);
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_QDR_M1_R0_CFG_2       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_QDR_M1_R0_CFG_2       , pipe_en);
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_QDR_M1_R0_CFG_3       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_QDR_M1_R0_CFG_3       , pipe_en);
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_QDR_M1_R0_CFG_4       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_QDR_M1_R0_CFG_4       , pipe_en);
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_QDR_M1_R0_CFG_5       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_QDR_M1_R0_CFG_5       , pipe_en);
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_QDR_M1_R0_CFG_6       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_QDR_M1_R0_CFG_6       , pipe_en);
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_QDR_M1_R0_CFG_7       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_QDR_M1_R0_CFG_7       , pipe_en);
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_QDR_M1_R0_CFG_8       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_QDR_M1_R0_CFG_8       , pipe_en);
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_QDR_M1_R0_CFG_9       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_QDR_M1_R0_CFG_9       , pipe_en);
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_QDR_M1_R0_CFG_10       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_QDR_M1_R0_CFG_10       , pipe_en);
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_QDR_M1_R1_CFG_0       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_QDR_M1_R1_CFG_0       , pipe_en);
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_QDR_M1_R1_CFG_1       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_QDR_M1_R1_CFG_1       , pipe_en);
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_QDR_M1_R1_CFG_2       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_QDR_M1_R1_CFG_2       , pipe_en);
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_QDR_M1_R1_CFG_3       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_QDR_M1_R1_CFG_3       , pipe_en);
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_QDR_M1_R1_CFG_4       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_QDR_M1_R1_CFG_4       , pipe_en);
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_QDR_M1_R1_CFG_5       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_QDR_M1_R1_CFG_5       , pipe_en);
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_QDR_M1_R1_CFG_6       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_QDR_M1_R1_CFG_6       , pipe_en);
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_QDR_M1_R1_CFG_7       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_QDR_M1_R1_CFG_7       , pipe_en);
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_QDR_M1_R1_CFG_8       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_QDR_M1_R1_CFG_8       , pipe_en);
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_QDR_M1_R1_CFG_9       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_QDR_M1_R1_CFG_9       , pipe_en);
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_QDR_M1_R1_CFG_10       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_QDR_M1_R1_CFG_10       , pipe_en);
                end
            endcase
        end
    end
endtask

task automatic set_txdqs_sdr_fc_dly_m1;
    input byte_sel_t     byte_sel;
    input rank_sel_t     rank_sel;
    input logic    [7:0] dqs;
    input logic   [31:0] fc_dly;
    begin
        if((byte_sel == DQ0) || (byte_sel == DQ_ALL) || (byte_sel == ALL)) begin
            case ({rank_sel,dqs})
                {RANK0, 8'd0} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R0_CFG_0, fc_dly );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R0_CFG_0, fc_dly );
                end
                {RANK0, 8'd1} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R0_CFG_1, fc_dly );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R0_CFG_1, fc_dly );
                end
                {RANK0, 8'd2} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R0_CFG_2, fc_dly );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R0_CFG_2, fc_dly );
                end
                {RANK0, 8'd3} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R0_CFG_3, fc_dly );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R0_CFG_3, fc_dly );
                end
                {RANK0, 8'd4} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R0_CFG_4, fc_dly );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R0_CFG_4, fc_dly );
                end
                {RANK0, 8'd5} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R0_CFG_5, fc_dly );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R0_CFG_5, fc_dly );
                end
                {RANK0, 8'd6} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R0_CFG_6, fc_dly );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R0_CFG_6, fc_dly );
                end
                {RANK0, 8'd7} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R0_CFG_7, fc_dly );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R0_CFG_7, fc_dly );
                end
                {RANK0, 8'd8} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R0_CFG_8, fc_dly );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R0_CFG_8, fc_dly );
                end
                {RANK1, 8'd0} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R1_CFG_0, fc_dly );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R1_CFG_0, fc_dly );
                end
                {RANK1, 8'd1} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R1_CFG_1, fc_dly );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R1_CFG_1, fc_dly );
                end
                {RANK1, 8'd2} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R1_CFG_2, fc_dly );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R1_CFG_2, fc_dly );
                end
                {RANK1, 8'd3} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R1_CFG_3, fc_dly );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R1_CFG_3, fc_dly );
                end
                {RANK1, 8'd4} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R1_CFG_4, fc_dly );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R1_CFG_4, fc_dly );
                end
                {RANK1, 8'd5} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R1_CFG_5, fc_dly );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R1_CFG_5, fc_dly );
                end
                {RANK1, 8'd6} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R1_CFG_6, fc_dly );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R1_CFG_6, fc_dly );
                end
                {RANK1, 8'd7} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R1_CFG_7, fc_dly );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R1_CFG_7, fc_dly );
                end
                {RANK1, 8'd8} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R1_CFG_8, fc_dly );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R1_CFG_8, fc_dly );
                end
                {RANK_ALL, 8'd0} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R0_CFG_0, fc_dly );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R0_CFG_0, fc_dly );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R1_CFG_0, fc_dly );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R1_CFG_0, fc_dly );
                end
                {RANK_ALL, 8'd1} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R0_CFG_1, fc_dly );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R0_CFG_1, fc_dly );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R1_CFG_1, fc_dly );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R1_CFG_1, fc_dly );
                end
                {RANK_ALL, 8'd2} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R0_CFG_2, fc_dly );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R0_CFG_2, fc_dly );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R1_CFG_2, fc_dly );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R1_CFG_2, fc_dly );
                end
                {RANK_ALL, 8'd3} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R0_CFG_3, fc_dly );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R0_CFG_3, fc_dly );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R1_CFG_3, fc_dly );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R1_CFG_3, fc_dly );
                end
                {RANK_ALL, 8'd4} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R0_CFG_4, fc_dly );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R0_CFG_4, fc_dly );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R1_CFG_4, fc_dly );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R1_CFG_4, fc_dly );
                end
                {RANK_ALL, 8'd5} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R0_CFG_5, fc_dly );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R0_CFG_5, fc_dly );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R1_CFG_5, fc_dly );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R1_CFG_5, fc_dly );
                end
                {RANK_ALL, 8'd6} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R0_CFG_6, fc_dly );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R0_CFG_6, fc_dly );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R1_CFG_6, fc_dly );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R1_CFG_6, fc_dly );
                end
                {RANK_ALL, 8'd7} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R0_CFG_7, fc_dly );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R0_CFG_7, fc_dly );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R1_CFG_7, fc_dly );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R1_CFG_7, fc_dly );
                end
                {RANK_ALL, 8'd8} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R0_CFG_8, fc_dly );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R0_CFG_8, fc_dly );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R1_CFG_8, fc_dly );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R1_CFG_8, fc_dly );
                end
                default: begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R0_CFG_0, fc_dly );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R0_CFG_0, fc_dly );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R0_CFG_1, fc_dly );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R0_CFG_1, fc_dly );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R0_CFG_2, fc_dly );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R0_CFG_2, fc_dly );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R0_CFG_3, fc_dly );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R0_CFG_3, fc_dly );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R0_CFG_4, fc_dly );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R0_CFG_4, fc_dly );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R0_CFG_5, fc_dly );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R0_CFG_5, fc_dly );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R0_CFG_6, fc_dly );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R0_CFG_6, fc_dly );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R0_CFG_7, fc_dly );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R0_CFG_7, fc_dly );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R0_CFG_8, fc_dly );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R0_CFG_8, fc_dly );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R1_CFG_0, fc_dly );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R1_CFG_0, fc_dly );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R1_CFG_1, fc_dly );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R1_CFG_1, fc_dly );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R1_CFG_2, fc_dly );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R1_CFG_2, fc_dly );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R1_CFG_3, fc_dly );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R1_CFG_3, fc_dly );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R1_CFG_4, fc_dly );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R1_CFG_4, fc_dly );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R1_CFG_5, fc_dly );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R1_CFG_5, fc_dly );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R1_CFG_6, fc_dly );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R1_CFG_6, fc_dly );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R1_CFG_7, fc_dly );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R1_CFG_7, fc_dly );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R1_CFG_8, fc_dly );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R1_CFG_8, fc_dly );
                end
            endcase
        end
        if((byte_sel == DQ1) || (byte_sel == DQ_ALL) || (byte_sel == ALL)) begin
            case ({rank_sel,dqs})
                {RANK0, 8'd0} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R0_CFG_0, fc_dly );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R0_CFG_0, fc_dly );
                end
                {RANK0, 8'd1} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R0_CFG_1, fc_dly );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R0_CFG_1, fc_dly );
                end
                {RANK0, 8'd2} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R0_CFG_2, fc_dly );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R0_CFG_2, fc_dly );
                end
                {RANK0, 8'd3} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R0_CFG_3, fc_dly );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R0_CFG_3, fc_dly );
                end
                {RANK0, 8'd4} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R0_CFG_4, fc_dly );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R0_CFG_4, fc_dly );
                end
                {RANK0, 8'd5} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R0_CFG_5, fc_dly );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R0_CFG_5, fc_dly );
                end
                {RANK0, 8'd6} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R0_CFG_6, fc_dly );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R0_CFG_6, fc_dly );
                end
                {RANK0, 8'd7} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R0_CFG_7, fc_dly );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R0_CFG_7, fc_dly );
                end
                {RANK0, 8'd8} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R0_CFG_8, fc_dly );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R0_CFG_8, fc_dly );
                end
                {RANK1, 8'd0} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R1_CFG_0, fc_dly );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R1_CFG_0, fc_dly );
                end
                {RANK1, 8'd1} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R1_CFG_1, fc_dly );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R1_CFG_1, fc_dly );
                end
                {RANK1, 8'd2} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R1_CFG_2, fc_dly );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R1_CFG_2, fc_dly );
                end
                {RANK1, 8'd3} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R1_CFG_3, fc_dly );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R1_CFG_3, fc_dly );
                end
                {RANK1, 8'd4} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R1_CFG_4, fc_dly );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R1_CFG_4, fc_dly );
                end
                {RANK1, 8'd5} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R1_CFG_5, fc_dly );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R1_CFG_5, fc_dly );
                end
                {RANK1, 8'd6} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R1_CFG_6, fc_dly );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R1_CFG_6, fc_dly );
                end
                {RANK1, 8'd7} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R1_CFG_7, fc_dly );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R1_CFG_7, fc_dly );
                end
                {RANK1, 8'd8} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R1_CFG_8, fc_dly );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R1_CFG_8, fc_dly );
                end
                {RANK_ALL, 8'd0} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R0_CFG_0, fc_dly );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R0_CFG_0, fc_dly );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R1_CFG_0, fc_dly );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R1_CFG_0, fc_dly );
                end
                {RANK_ALL, 8'd1} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R0_CFG_1, fc_dly );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R0_CFG_1, fc_dly );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R1_CFG_1, fc_dly );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R1_CFG_1, fc_dly );
                end
                {RANK_ALL, 8'd2} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R0_CFG_2, fc_dly );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R0_CFG_2, fc_dly );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R1_CFG_2, fc_dly );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R1_CFG_2, fc_dly );
                end
                {RANK_ALL, 8'd3} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R0_CFG_3, fc_dly );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R0_CFG_3, fc_dly );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R1_CFG_3, fc_dly );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R1_CFG_3, fc_dly );
                end
                {RANK_ALL, 8'd4} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R0_CFG_4, fc_dly );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R0_CFG_4, fc_dly );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R1_CFG_4, fc_dly );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R1_CFG_4, fc_dly );
                end
                {RANK_ALL, 8'd5} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R0_CFG_5, fc_dly );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R0_CFG_5, fc_dly );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R1_CFG_5, fc_dly );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R1_CFG_5, fc_dly );
                end
                {RANK_ALL, 8'd6} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R0_CFG_6, fc_dly );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R0_CFG_6, fc_dly );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R1_CFG_6, fc_dly );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R1_CFG_6, fc_dly );
                end
                {RANK_ALL, 8'd7} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R0_CFG_7, fc_dly );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R0_CFG_7, fc_dly );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R1_CFG_7, fc_dly );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R1_CFG_7, fc_dly );
                end
                {RANK_ALL, 8'd8} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R0_CFG_8, fc_dly );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R0_CFG_8, fc_dly );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R1_CFG_8, fc_dly );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R1_CFG_8, fc_dly );
                end
                default: begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R0_CFG_0, fc_dly );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R0_CFG_0, fc_dly );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R0_CFG_1, fc_dly );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R0_CFG_1, fc_dly );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R0_CFG_2, fc_dly );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R0_CFG_2, fc_dly );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R0_CFG_3, fc_dly );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R0_CFG_3, fc_dly );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R0_CFG_4, fc_dly );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R0_CFG_4, fc_dly );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R0_CFG_5, fc_dly );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R0_CFG_5, fc_dly );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R0_CFG_6, fc_dly );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R0_CFG_6, fc_dly );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R0_CFG_7, fc_dly );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R0_CFG_7, fc_dly );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R0_CFG_8, fc_dly );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R0_CFG_8, fc_dly );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R1_CFG_0, fc_dly );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R1_CFG_0, fc_dly );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R1_CFG_1, fc_dly );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R1_CFG_1, fc_dly );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R1_CFG_2, fc_dly );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R1_CFG_2, fc_dly );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R1_CFG_3, fc_dly );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R1_CFG_3, fc_dly );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R1_CFG_4, fc_dly );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R1_CFG_4, fc_dly );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R1_CFG_5, fc_dly );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R1_CFG_5, fc_dly );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R1_CFG_6, fc_dly );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R1_CFG_6, fc_dly );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R1_CFG_7, fc_dly );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R1_CFG_7, fc_dly );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R1_CFG_8, fc_dly );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M1_R1_CFG_8, fc_dly );
                end
            endcase
        end
        if((byte_sel == CA) || (byte_sel == ALL)) begin
            case ({rank_sel,dqs})
                {RANK0, 8'd0} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQS_TX_SDR_FC_DLY_M1_R0_CFG_0, fc_dly );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQS_TX_SDR_FC_DLY_M1_R0_CFG_0, fc_dly );
                end
                {RANK1, 8'd0} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQS_TX_SDR_FC_DLY_M1_R1_CFG_0, fc_dly );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQS_TX_SDR_FC_DLY_M1_R1_CFG_0, fc_dly );
                end
                {RANK_ALL, 8'd0} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQS_TX_SDR_FC_DLY_M1_R0_CFG_0, fc_dly );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQS_TX_SDR_FC_DLY_M1_R0_CFG_0, fc_dly );
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQS_TX_SDR_FC_DLY_M1_R1_CFG_0, fc_dly );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQS_TX_SDR_FC_DLY_M1_R1_CFG_0, fc_dly );
                end
                default: begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQS_TX_SDR_FC_DLY_M1_R0_CFG_0, fc_dly );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQS_TX_SDR_FC_DLY_M1_R0_CFG_0, fc_dly );
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQS_TX_SDR_FC_DLY_M1_R1_CFG_0, fc_dly );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQS_TX_SDR_FC_DLY_M1_R1_CFG_0, fc_dly );
                end
            endcase
        end
    end
endtask

task automatic set_txdqs_rt_pipe_en_m1;
    input byte_sel_t     byte_sel;
    input rank_sel_t     rank_sel;
    input logic   [31:0] pipe_en;
    begin
        if((byte_sel == DQ0) || (byte_sel == DQ_ALL) || (byte_sel == ALL)) begin
            case ({rank_sel})
                {RANK0} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_RT_M1_R0_CFG, pipe_en );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_RT_M1_R0_CFG, pipe_en );
                end
                {RANK1} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_RT_M1_R1_CFG, pipe_en );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_RT_M1_R1_CFG, pipe_en );
                end
                default: begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_RT_M1_R0_CFG, pipe_en );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_RT_M1_R1_CFG, pipe_en );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_RT_M1_R0_CFG, pipe_en );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_RT_M1_R1_CFG, pipe_en );
                end
            endcase
        end
        if((byte_sel == DQ1) || (byte_sel == DQ_ALL) || (byte_sel == ALL)) begin
            case ({rank_sel})
                {RANK0} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_RT_M1_R0_CFG, pipe_en );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_RT_M1_R0_CFG, pipe_en );
                end
                {RANK1} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_RT_M1_R1_CFG, pipe_en );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_RT_M1_R1_CFG, pipe_en );
                end
                default: begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_RT_M1_R0_CFG, pipe_en );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_RT_M1_R1_CFG, pipe_en );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_RT_M1_R0_CFG, pipe_en );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_RT_M1_R1_CFG, pipe_en );
                end
            endcase
        end
        if((byte_sel == CA) || (byte_sel == ALL)) begin
            case ({rank_sel})
                {RANK0} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQS_TX_RT_M1_R0_CFG, pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQS_TX_RT_M1_R0_CFG, pipe_en);
                end
                {RANK1} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQS_TX_RT_M1_R1_CFG, pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQS_TX_RT_M1_R1_CFG, pipe_en);
                end
                default: begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQS_TX_RT_M1_R0_CFG, pipe_en );
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQS_TX_RT_M1_R1_CFG, pipe_en );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQS_TX_RT_M1_R0_CFG, pipe_en );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQS_TX_RT_M1_R1_CFG, pipe_en );
                end
            endcase
        end
    end
endtask

task automatic set_txdqs_sdr_x_sel_m1;
    input byte_sel_t     byte_sel;
    input rank_sel_t     rank_sel;
    input logic    [7:0] dqs;
    input logic   [31:0] x_sel;
    begin
        if((byte_sel == DQ0) || (byte_sel == DQ_ALL) || (byte_sel == ALL)) begin
            case ({rank_sel,dqs})
                {RANK0, 8'd0} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R0_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R0_CFG_0 , x_sel  );
                end
                {RANK0, 8'd1} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R0_CFG_1 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R0_CFG_1 , x_sel  );
                end
                {RANK0, 8'd2} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R0_CFG_2 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R0_CFG_2 , x_sel  );
                end
                {RANK0, 8'd3} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R0_CFG_3 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R0_CFG_3 , x_sel  );
                end
                {RANK0, 8'd4} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R0_CFG_4 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R0_CFG_4 , x_sel  );
                end
                {RANK0, 8'd5} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R0_CFG_5 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R0_CFG_5 , x_sel  );
                end
                {RANK0, 8'd6} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R0_CFG_6 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R0_CFG_6 , x_sel  );
                end
                {RANK0, 8'd7} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R0_CFG_7 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R0_CFG_7 , x_sel  );
                end
                {RANK0, 8'd8} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R0_CFG_8 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R0_CFG_8 , x_sel  );
                end
                {RANK1, 8'd0} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R1_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R1_CFG_0 , x_sel  );
                end
                {RANK1, 8'd1} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R1_CFG_1 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R1_CFG_1 , x_sel  );
                end
                {RANK1, 8'd2} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R1_CFG_2 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R1_CFG_2 , x_sel  );
                end
                {RANK1, 8'd3} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R1_CFG_3 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R1_CFG_3 , x_sel  );
                end
                {RANK1, 8'd4} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R1_CFG_4 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R1_CFG_4 , x_sel  );
                end
                {RANK1, 8'd5} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R1_CFG_5 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R1_CFG_5 , x_sel  );
                end
                {RANK1, 8'd6} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R1_CFG_6 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R1_CFG_6 , x_sel  );
                end
                {RANK1, 8'd7} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R1_CFG_7 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R1_CFG_7 , x_sel  );
                end
                {RANK1, 8'd8} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R1_CFG_8 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R1_CFG_8 , x_sel  );
                end
                {RANK_ALL, 8'd0} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R0_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R0_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R1_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R1_CFG_0 , x_sel  );
                end
                {RANK_ALL, 8'd1} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R0_CFG_1 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R0_CFG_1 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R1_CFG_1 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R1_CFG_1 , x_sel  );
                end
                {RANK_ALL, 8'd2} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R0_CFG_2 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R0_CFG_2 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R1_CFG_2 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R1_CFG_2 , x_sel  );
                end
                {RANK_ALL, 8'd3} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R0_CFG_3 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R0_CFG_3 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R1_CFG_3 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R1_CFG_3 , x_sel  );
                end
                {RANK_ALL, 8'd4} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R0_CFG_4 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R0_CFG_4 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R1_CFG_4 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R1_CFG_4 , x_sel  );
                end
                {RANK_ALL, 8'd5} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R0_CFG_5 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R0_CFG_5 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R1_CFG_5 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R1_CFG_5 , x_sel  );
                end
                {RANK_ALL, 8'd6} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R0_CFG_6 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R0_CFG_6 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R1_CFG_6 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R1_CFG_6 , x_sel  );
                end
                {RANK_ALL, 8'd7} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R0_CFG_7 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R0_CFG_7 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R1_CFG_7 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R1_CFG_7 , x_sel  );
                end
                {RANK_ALL, 8'd8} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R0_CFG_8 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R0_CFG_8 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R1_CFG_8 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R1_CFG_8 , x_sel  );
                end
                default: begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R0_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R0_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R0_CFG_1 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R0_CFG_1 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R0_CFG_2 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R0_CFG_2 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R0_CFG_3 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R0_CFG_3 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R0_CFG_4 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R0_CFG_4 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R0_CFG_5 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R0_CFG_5 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R0_CFG_6 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R0_CFG_6 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R0_CFG_7 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R0_CFG_7 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R0_CFG_8 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R0_CFG_8 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R1_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R1_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R1_CFG_1 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R1_CFG_1 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R1_CFG_2 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R1_CFG_2 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R1_CFG_3 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R1_CFG_3 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R1_CFG_4 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R1_CFG_4 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R1_CFG_5 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R1_CFG_5 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R1_CFG_6 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R1_CFG_6 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R1_CFG_7 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R1_CFG_7 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R1_CFG_8 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R1_CFG_8 , x_sel  );
                end
            endcase
        end
        if((byte_sel == DQ1) || (byte_sel == DQ_ALL) || (byte_sel == ALL)) begin
            case ({rank_sel,dqs})
                {RANK0, 8'd0} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R0_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R0_CFG_0 , x_sel  );
                end
                {RANK0, 8'd1} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R0_CFG_1 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R0_CFG_1 , x_sel  );
                end
                {RANK0, 8'd2} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R0_CFG_2 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R0_CFG_2 , x_sel  );
                end
                {RANK0, 8'd3} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R0_CFG_3 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R0_CFG_3 , x_sel  );
                end
                {RANK0, 8'd4} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R0_CFG_4 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R0_CFG_4 , x_sel  );
                end
                {RANK0, 8'd5} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R0_CFG_5 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R0_CFG_5 , x_sel  );
                end
                {RANK0, 8'd6} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R0_CFG_6 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R0_CFG_6 , x_sel  );
                end
                {RANK0, 8'd7} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R0_CFG_7 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R0_CFG_7 , x_sel  );
                end
                {RANK0, 8'd8} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R0_CFG_8 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R0_CFG_8 , x_sel  );
                end
                {RANK1, 8'd0} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R1_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R1_CFG_0 , x_sel  );
                end
                {RANK1, 8'd1} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R1_CFG_1 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R1_CFG_1 , x_sel  );
                end
                {RANK1, 8'd2} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R1_CFG_2 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R1_CFG_2 , x_sel  );
                end
                {RANK1, 8'd3} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R1_CFG_3 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R1_CFG_3 , x_sel  );
                end
                {RANK1, 8'd4} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R1_CFG_4 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R1_CFG_4 , x_sel  );
                end
                {RANK1, 8'd5} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R1_CFG_5 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R1_CFG_5 , x_sel  );
                end
                {RANK1, 8'd6} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R1_CFG_6 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R1_CFG_6 , x_sel  );
                end
                {RANK1, 8'd7} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R1_CFG_7 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R1_CFG_7 , x_sel  );
                end
                {RANK1, 8'd8} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R1_CFG_8 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R1_CFG_8 , x_sel  );
                end
                {RANK_ALL, 8'd0} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R0_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R0_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R1_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R1_CFG_0 , x_sel  );
                end
                {RANK_ALL, 8'd1} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R0_CFG_1 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R0_CFG_1 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R1_CFG_1 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R1_CFG_1 , x_sel  );
                end
                {RANK_ALL, 8'd2} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R0_CFG_2 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R0_CFG_2 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R1_CFG_2 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R1_CFG_2 , x_sel  );
                end
                {RANK_ALL, 8'd3} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R0_CFG_3 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R0_CFG_3 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R1_CFG_3 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R1_CFG_3 , x_sel  );
                end
                {RANK_ALL, 8'd4} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R0_CFG_4 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R0_CFG_4 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R1_CFG_4 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R1_CFG_4 , x_sel  );
                end
                {RANK_ALL, 8'd5} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R0_CFG_5 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R0_CFG_5 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R1_CFG_5 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R1_CFG_5 , x_sel  );
                end
                {RANK_ALL, 8'd6} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R0_CFG_6 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R0_CFG_6 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R1_CFG_6 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R1_CFG_6 , x_sel  );
                end
                {RANK_ALL, 8'd7} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R0_CFG_7 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R0_CFG_7 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R1_CFG_7 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R1_CFG_7 , x_sel  );
                end
                {RANK_ALL, 8'd8} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R0_CFG_8 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R0_CFG_8 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R1_CFG_8 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R1_CFG_8 , x_sel  );
                end
                default: begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R0_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R0_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R0_CFG_1 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R0_CFG_1 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R0_CFG_2 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R0_CFG_2 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R0_CFG_3 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R0_CFG_3 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R0_CFG_4 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R0_CFG_4 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R0_CFG_5 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R0_CFG_5 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R0_CFG_6 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R0_CFG_6 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R0_CFG_7 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R0_CFG_7 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R0_CFG_8 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R0_CFG_8 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R1_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R1_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R1_CFG_1 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R1_CFG_1 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R1_CFG_2 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R1_CFG_2 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R1_CFG_3 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R1_CFG_3 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R1_CFG_4 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R1_CFG_4 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R1_CFG_5 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R1_CFG_5 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R1_CFG_6 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R1_CFG_6 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R1_CFG_7 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R1_CFG_7 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R1_CFG_8 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M1_R1_CFG_8 , x_sel  );
                end
            endcase
        end
        if((byte_sel == CA) || (byte_sel == ALL)) begin
            case ({rank_sel,dqs})
                {RANK0, 8'd0} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQS_TX_SDR_X_SEL_M1_R0_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQS_TX_SDR_X_SEL_M1_R0_CFG_0 , x_sel  );
                end
                {RANK1, 8'd0} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQS_TX_SDR_X_SEL_M1_R1_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQS_TX_SDR_X_SEL_M1_R1_CFG_0 , x_sel  );
                end
                {RANK_ALL, 8'd0} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQS_TX_SDR_X_SEL_M1_R0_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQS_TX_SDR_X_SEL_M1_R0_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQS_TX_SDR_X_SEL_M1_R1_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQS_TX_SDR_X_SEL_M1_R1_CFG_0 , x_sel  );
                end
                default: begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQS_TX_SDR_X_SEL_M1_R0_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQS_TX_SDR_X_SEL_M1_R0_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQS_TX_SDR_X_SEL_M1_R1_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQS_TX_SDR_X_SEL_M1_R1_CFG_0 , x_sel  );
                end
            endcase
        end
    end
endtask

task automatic set_txdqs_sdr_pipe_en_m1 ;
    input byte_sel_t     byte_sel;
    input rank_sel_t     rank_sel;
    input logic    [7:0] dqs;
    input logic   [31:0] pipe_en;
    begin
        if((byte_sel == DQ0) || (byte_sel == DQ_ALL) || (byte_sel == ALL)) begin
            case ({rank_sel,dqs})
                {RANK0, 8'd0} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_M1_R0_CFG_0       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_M1_R0_CFG_0       , pipe_en);
                end
                {RANK0, 8'd1} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_M1_R0_CFG_1       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_M1_R0_CFG_1       , pipe_en);
                end
                {RANK0, 8'd2} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_M1_R0_CFG_2       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_M1_R0_CFG_2       , pipe_en);
                end
                {RANK0, 8'd3} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_M1_R0_CFG_3       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_M1_R0_CFG_3       , pipe_en);
                end
                {RANK0, 8'd4} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_M1_R0_CFG_4       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_M1_R0_CFG_4       , pipe_en);
                end
                {RANK0, 8'd5} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_M1_R0_CFG_5       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_M1_R0_CFG_5       , pipe_en);
                end
                {RANK0, 8'd6} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_M1_R0_CFG_6       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_M1_R0_CFG_6       , pipe_en);
                end
                {RANK0, 8'd7} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_M1_R0_CFG_7       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_M1_R0_CFG_7       , pipe_en);
                end
                {RANK0, 8'd8} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_M1_R0_CFG_8       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_M1_R0_CFG_8       , pipe_en);
                end
                {RANK1, 8'd0} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_M1_R1_CFG_0       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_M1_R1_CFG_0       , pipe_en);
                end
                {RANK1, 8'd1} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_M1_R1_CFG_1       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_M1_R1_CFG_1       , pipe_en);
                end
                {RANK1, 8'd2} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_M1_R1_CFG_2       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_M1_R1_CFG_2       , pipe_en);
                end
                {RANK1, 8'd3} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_M1_R1_CFG_3       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_M1_R1_CFG_3       , pipe_en);
                end
                {RANK1, 8'd4} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_M1_R1_CFG_4       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_M1_R1_CFG_4       , pipe_en);
                end
                {RANK1, 8'd5} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_M1_R1_CFG_5       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_M1_R1_CFG_5       , pipe_en);
                end
                {RANK1, 8'd6} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_M1_R1_CFG_6       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_M1_R1_CFG_6       , pipe_en);
                end
                {RANK1, 8'd7} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_M1_R1_CFG_7       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_M1_R1_CFG_7       , pipe_en);
                end
                {RANK1, 8'd8} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_M1_R1_CFG_8       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_M1_R1_CFG_8       , pipe_en);
                end
                default: begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_M1_R0_CFG_0       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_M1_R0_CFG_0       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_M1_R0_CFG_1       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_M1_R0_CFG_1       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_M1_R0_CFG_2       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_M1_R0_CFG_2       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_M1_R0_CFG_3       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_M1_R0_CFG_3       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_M1_R0_CFG_4       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_M1_R0_CFG_4       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_M1_R0_CFG_5       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_M1_R0_CFG_5       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_M1_R0_CFG_6       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_M1_R0_CFG_6       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_M1_R0_CFG_7       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_M1_R0_CFG_7       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_M1_R0_CFG_8       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_M1_R0_CFG_8       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_M1_R1_CFG_0       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_M1_R1_CFG_0       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_M1_R1_CFG_1       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_M1_R1_CFG_1       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_M1_R1_CFG_2       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_M1_R1_CFG_2       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_M1_R1_CFG_3       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_M1_R1_CFG_3       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_M1_R1_CFG_4       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_M1_R1_CFG_4       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_M1_R1_CFG_5       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_M1_R1_CFG_5       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_M1_R1_CFG_6       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_M1_R1_CFG_6       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_M1_R1_CFG_7       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_M1_R1_CFG_7       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_M1_R1_CFG_8       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_M1_R1_CFG_8       , pipe_en);
                end
            endcase
        end
        if((byte_sel == DQ1) || (byte_sel == DQ_ALL) || (byte_sel == ALL)) begin
            case ({rank_sel,dqs})
                {RANK0, 8'd0} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_M1_R0_CFG_0       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_M1_R0_CFG_0       , pipe_en);
                end
                {RANK0, 8'd1} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_M1_R0_CFG_1       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_M1_R0_CFG_1       , pipe_en);
                end
                {RANK0, 8'd2} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_M1_R0_CFG_2       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_M1_R0_CFG_2       , pipe_en);
                end
                {RANK0, 8'd3} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_M1_R0_CFG_3       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_M1_R0_CFG_3       , pipe_en);
                end
                {RANK0, 8'd4} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_M1_R0_CFG_4       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_M1_R0_CFG_4       , pipe_en);
                end
                {RANK0, 8'd5} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_M1_R0_CFG_5       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_M1_R0_CFG_5       , pipe_en);
                end
                {RANK0, 8'd6} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_M1_R0_CFG_6       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_M1_R0_CFG_6       , pipe_en);
                end
                {RANK0, 8'd7} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_M1_R0_CFG_7       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_M1_R0_CFG_7       , pipe_en);
                end
                {RANK0, 8'd8} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_M1_R0_CFG_8       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_M1_R0_CFG_8       , pipe_en);
                end
                {RANK1, 8'd0} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_M1_R1_CFG_0       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_M1_R1_CFG_0       , pipe_en);
                end
                {RANK1, 8'd1} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_M1_R1_CFG_1       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_M1_R1_CFG_1       , pipe_en);
                end
                {RANK1, 8'd2} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_M1_R1_CFG_2       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_M1_R1_CFG_2       , pipe_en);
                end
                {RANK1, 8'd3} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_M1_R1_CFG_3       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_M1_R1_CFG_3       , pipe_en);
                end
                {RANK1, 8'd4} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_M1_R1_CFG_4       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_M1_R1_CFG_4       , pipe_en);
                end
                {RANK1, 8'd5} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_M1_R1_CFG_5       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_M1_R1_CFG_5       , pipe_en);
                end
                {RANK1, 8'd6} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_M1_R1_CFG_6       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_M1_R1_CFG_6       , pipe_en);
                end
                {RANK1, 8'd7} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_M1_R1_CFG_7       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_M1_R1_CFG_7       , pipe_en);
                end
                {RANK1, 8'd8} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_M1_R1_CFG_8       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_M1_R1_CFG_8       , pipe_en);
                end
                default: begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_M1_R0_CFG_0       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_M1_R0_CFG_0       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_M1_R0_CFG_1       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_M1_R0_CFG_1       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_M1_R0_CFG_2       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_M1_R0_CFG_2       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_M1_R0_CFG_3       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_M1_R0_CFG_3       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_M1_R0_CFG_4       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_M1_R0_CFG_4       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_M1_R0_CFG_5       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_M1_R0_CFG_5       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_M1_R0_CFG_6       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_M1_R0_CFG_6       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_M1_R0_CFG_7       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_M1_R0_CFG_7       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_M1_R0_CFG_8       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_M1_R0_CFG_8       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_M1_R1_CFG_0       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_M1_R1_CFG_0       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_M1_R1_CFG_1       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_M1_R1_CFG_1       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_M1_R1_CFG_2       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_M1_R1_CFG_2       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_M1_R1_CFG_3       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_M1_R1_CFG_3       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_M1_R1_CFG_4       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_M1_R1_CFG_4       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_M1_R1_CFG_5       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_M1_R1_CFG_5       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_M1_R1_CFG_6       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_M1_R1_CFG_6       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_M1_R1_CFG_7       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_M1_R1_CFG_7       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_M1_R1_CFG_8       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_M1_R1_CFG_8       , pipe_en);
                end
            endcase
        end
        if((byte_sel == CA) || (byte_sel == ALL)) begin
            case ({rank_sel,dqs})
                {RANK0, 8'd0} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQS_TX_SDR_M1_R0_CFG_0       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQS_TX_SDR_M1_R0_CFG_0       , pipe_en);
                end
                {RANK1, 8'd0} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQS_TX_SDR_M1_R1_CFG_0       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQS_TX_SDR_M1_R1_CFG_0       , pipe_en);
                end
                default: begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQS_TX_SDR_M1_R0_CFG_0       , pipe_en);
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQS_TX_SDR_M1_R1_CFG_0       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQS_TX_SDR_M1_R0_CFG_0       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQS_TX_SDR_M1_R1_CFG_0       , pipe_en);
                end
            endcase
        end
    end
endtask

task automatic set_txdqs_ddr_x_sel_m1;
    input byte_sel_t     byte_sel;
    input rank_sel_t     rank_sel;
    input logic    [7:0] dqs;
    input logic   [31:0] x_sel;
    begin
        if((byte_sel == DQ0) || (byte_sel == DQ_ALL) || (byte_sel == ALL)) begin
            case ({rank_sel,dqs})
                {RANK0, 8'd0} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M1_R0_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M1_R0_CFG_0 , x_sel  );
                end
                {RANK0, 8'd1} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M1_R0_CFG_1 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M1_R0_CFG_1 , x_sel  );
                end
                {RANK0, 8'd2} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M1_R0_CFG_2 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M1_R0_CFG_2 , x_sel  );
                end
                {RANK0, 8'd3} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M1_R0_CFG_3 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M1_R0_CFG_3 , x_sel  );
                end
                {RANK0, 8'd4} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M1_R0_CFG_4 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M1_R0_CFG_4 , x_sel  );
                end
                {RANK0, 8'd5} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M1_R0_CFG_5 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M1_R0_CFG_5 , x_sel  );
                end
                {RANK0, 8'd6} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M1_R0_CFG_6 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M1_R0_CFG_6 , x_sel  );
                end
                {RANK0, 8'd7} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M1_R0_CFG_7 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M1_R0_CFG_7 , x_sel  );
                end
                {RANK0, 8'd8} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M1_R0_CFG_8 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M1_R0_CFG_8 , x_sel  );
                end
                {RANK1, 8'd0} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M1_R1_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M1_R1_CFG_0 , x_sel  );
                end
                {RANK1, 8'd1} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M1_R1_CFG_1 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M1_R1_CFG_1 , x_sel  );
                end
                {RANK1, 8'd2} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M1_R1_CFG_2 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M1_R1_CFG_2 , x_sel  );
                end
                {RANK1, 8'd3} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M1_R1_CFG_3 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M1_R1_CFG_3 , x_sel  );
                end
                {RANK1, 8'd4} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M1_R1_CFG_4 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M1_R1_CFG_4 , x_sel  );
                end
                {RANK1, 8'd5} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M1_R1_CFG_5 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M1_R1_CFG_5 , x_sel  );
                end
                {RANK1, 8'd6} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M1_R1_CFG_6 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M1_R1_CFG_6 , x_sel  );
                end
                {RANK1, 8'd7} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M1_R1_CFG_7 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M1_R1_CFG_7 , x_sel  );
                end
                {RANK1, 8'd8} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M1_R1_CFG_8 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M1_R1_CFG_8 , x_sel  );
                end
                default: begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M1_R0_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M1_R0_CFG_1 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M1_R0_CFG_2 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M1_R0_CFG_3 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M1_R0_CFG_4 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M1_R0_CFG_5 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M1_R0_CFG_6 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M1_R0_CFG_7 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M1_R0_CFG_8 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M1_R1_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M1_R1_CFG_1 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M1_R1_CFG_2 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M1_R1_CFG_3 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M1_R1_CFG_4 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M1_R1_CFG_5 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M1_R1_CFG_6 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M1_R1_CFG_7 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M1_R1_CFG_8 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M1_R0_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M1_R0_CFG_1 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M1_R0_CFG_2 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M1_R0_CFG_3 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M1_R0_CFG_4 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M1_R0_CFG_5 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M1_R0_CFG_6 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M1_R0_CFG_7 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M1_R0_CFG_8 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M1_R1_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M1_R1_CFG_1 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M1_R1_CFG_2 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M1_R1_CFG_3 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M1_R1_CFG_4 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M1_R1_CFG_5 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M1_R1_CFG_6 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M1_R1_CFG_7 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M1_R1_CFG_8 , x_sel  );
                end
            endcase
        end
        if((byte_sel == DQ1) || (byte_sel == DQ_ALL) || (byte_sel == ALL)) begin
            case ({rank_sel,dqs})
                {RANK0, 8'd0} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M1_R0_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M1_R0_CFG_0 , x_sel  );
                end
                {RANK0, 8'd1} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M1_R0_CFG_1 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M1_R0_CFG_1 , x_sel  );
                end
                {RANK0, 8'd2} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M1_R0_CFG_2 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M1_R0_CFG_2 , x_sel  );
                end
                {RANK0, 8'd3} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M1_R0_CFG_3 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M1_R0_CFG_3 , x_sel  );
                end
                {RANK0, 8'd4} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M1_R0_CFG_4 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M1_R0_CFG_4 , x_sel  );
                end
                {RANK0, 8'd5} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M1_R0_CFG_5 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M1_R0_CFG_5 , x_sel  );
                end
                {RANK0, 8'd6} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M1_R0_CFG_6 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M1_R0_CFG_6 , x_sel  );
                end
                {RANK0, 8'd7} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M1_R0_CFG_7 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M1_R0_CFG_7 , x_sel  );
                end
                {RANK0, 8'd8} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M1_R0_CFG_8 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M1_R0_CFG_8 , x_sel  );
                end
                {RANK1, 8'd0} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M1_R1_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M1_R1_CFG_0 , x_sel  );
                end
                {RANK1, 8'd1} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M1_R1_CFG_1 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M1_R1_CFG_1 , x_sel  );
                end
                {RANK1, 8'd2} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M1_R1_CFG_2 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M1_R1_CFG_2 , x_sel  );
                end
                {RANK1, 8'd3} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M1_R1_CFG_3 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M1_R1_CFG_3 , x_sel  );
                end
                {RANK1, 8'd4} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M1_R1_CFG_4 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M1_R1_CFG_4 , x_sel  );
                end
                {RANK1, 8'd5} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M1_R1_CFG_5 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M1_R1_CFG_5 , x_sel  );
                end
                {RANK1, 8'd6} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M1_R1_CFG_6 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M1_R1_CFG_6 , x_sel  );
                end
                {RANK1, 8'd7} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M1_R1_CFG_7 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M1_R1_CFG_7 , x_sel  );
                end
                {RANK1, 8'd8} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M1_R1_CFG_8 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M1_R1_CFG_8 , x_sel  );
                end
                default: begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M1_R0_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M1_R0_CFG_1 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M1_R0_CFG_2 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M1_R0_CFG_3 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M1_R0_CFG_4 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M1_R0_CFG_5 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M1_R0_CFG_6 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M1_R0_CFG_7 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M1_R0_CFG_8 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M1_R1_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M1_R1_CFG_1 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M1_R1_CFG_2 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M1_R1_CFG_3 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M1_R1_CFG_4 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M1_R1_CFG_5 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M1_R1_CFG_6 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M1_R1_CFG_7 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M1_R1_CFG_8 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M1_R0_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M1_R0_CFG_1 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M1_R0_CFG_2 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M1_R0_CFG_3 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M1_R0_CFG_4 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M1_R0_CFG_5 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M1_R0_CFG_6 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M1_R0_CFG_7 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M1_R0_CFG_8 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M1_R1_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M1_R1_CFG_1 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M1_R1_CFG_2 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M1_R1_CFG_3 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M1_R1_CFG_4 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M1_R1_CFG_5 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M1_R1_CFG_6 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M1_R1_CFG_7 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M1_R1_CFG_8 , x_sel  );
                end
            endcase
        end
        if((byte_sel == CA) || (byte_sel == ALL)) begin
            case ({rank_sel,dqs})
                {RANK0, 8'd0} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQS_TX_DDR_X_SEL_M1_R0_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQS_TX_DDR_X_SEL_M1_R0_CFG_0 , x_sel  );
                end
                {RANK1, 8'd0} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQS_TX_DDR_X_SEL_M1_R1_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQS_TX_DDR_X_SEL_M1_R1_CFG_0 , x_sel  );
                end
                default: begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQS_TX_DDR_X_SEL_M1_R0_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQS_TX_DDR_X_SEL_M1_R1_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQS_TX_DDR_X_SEL_M1_R0_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQS_TX_DDR_X_SEL_M1_R1_CFG_0 , x_sel  );
                end
            endcase
        end
    end
endtask

task automatic set_txdqs_ddr_pipe_en_m1;
    input byte_sel_t     byte_sel;
    input rank_sel_t     rank_sel;
    input logic    [7:0] dqs;
    input logic  [31:0]  pipe_en;
    begin
        if((byte_sel == DQ0) || (byte_sel == DQ_ALL) || (byte_sel == ALL)) begin
            case ({rank_sel,dqs})
                {RANK0, 8'd0} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET, DDR_DQ_DQS_TX_DDR_M1_R0_CFG_0, pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET, DDR_DQ_DQS_TX_DDR_M1_R0_CFG_0, pipe_en);
                end
                {RANK0, 8'd1} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET, DDR_DQ_DQS_TX_DDR_M1_R0_CFG_1, pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET, DDR_DQ_DQS_TX_DDR_M1_R0_CFG_1, pipe_en);
                end
                {RANK0, 8'd2} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET, DDR_DQ_DQS_TX_DDR_M1_R0_CFG_2, pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET, DDR_DQ_DQS_TX_DDR_M1_R0_CFG_2, pipe_en);
                end
                {RANK0, 8'd3} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET, DDR_DQ_DQS_TX_DDR_M1_R0_CFG_3, pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET, DDR_DQ_DQS_TX_DDR_M1_R0_CFG_3, pipe_en);
                end
                {RANK0, 8'd4} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET, DDR_DQ_DQS_TX_DDR_M1_R0_CFG_4, pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET, DDR_DQ_DQS_TX_DDR_M1_R0_CFG_4, pipe_en);
                end
                {RANK0, 8'd5} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET, DDR_DQ_DQS_TX_DDR_M1_R0_CFG_5, pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET, DDR_DQ_DQS_TX_DDR_M1_R0_CFG_5, pipe_en);
                end
                {RANK0, 8'd6} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET, DDR_DQ_DQS_TX_DDR_M1_R0_CFG_6, pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET, DDR_DQ_DQS_TX_DDR_M1_R0_CFG_6, pipe_en);
                end
                {RANK0, 8'd7} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET, DDR_DQ_DQS_TX_DDR_M1_R0_CFG_7, pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET, DDR_DQ_DQS_TX_DDR_M1_R0_CFG_7, pipe_en);
                end
                {RANK0, 8'd8} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET, DDR_DQ_DQS_TX_DDR_M1_R0_CFG_8, pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET, DDR_DQ_DQS_TX_DDR_M1_R0_CFG_8, pipe_en);
                end
                {RANK1, 8'd0} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET, DDR_DQ_DQS_TX_DDR_M1_R1_CFG_0, pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET, DDR_DQ_DQS_TX_DDR_M1_R1_CFG_0, pipe_en);
                end
                {RANK1, 8'd1} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET, DDR_DQ_DQS_TX_DDR_M1_R1_CFG_1, pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET, DDR_DQ_DQS_TX_DDR_M1_R1_CFG_1, pipe_en);
                end
                {RANK1, 8'd2} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET, DDR_DQ_DQS_TX_DDR_M1_R1_CFG_2, pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET, DDR_DQ_DQS_TX_DDR_M1_R1_CFG_2, pipe_en);
                end
                {RANK1, 8'd3} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET, DDR_DQ_DQS_TX_DDR_M1_R1_CFG_3, pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET, DDR_DQ_DQS_TX_DDR_M1_R1_CFG_3, pipe_en);
                end
                {RANK1, 8'd4} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET, DDR_DQ_DQS_TX_DDR_M1_R1_CFG_4, pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET, DDR_DQ_DQS_TX_DDR_M1_R1_CFG_4, pipe_en);
                end
                {RANK1, 8'd5} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET, DDR_DQ_DQS_TX_DDR_M1_R1_CFG_5, pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET, DDR_DQ_DQS_TX_DDR_M1_R1_CFG_5, pipe_en);
                end
                {RANK1, 8'd6} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET, DDR_DQ_DQS_TX_DDR_M1_R1_CFG_6, pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET, DDR_DQ_DQS_TX_DDR_M1_R1_CFG_6, pipe_en);
                end
                {RANK1, 8'd7} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET, DDR_DQ_DQS_TX_DDR_M1_R1_CFG_7, pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET, DDR_DQ_DQS_TX_DDR_M1_R1_CFG_7, pipe_en);
                end
                {RANK1, 8'd8} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET, DDR_DQ_DQS_TX_DDR_M1_R1_CFG_8, pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET, DDR_DQ_DQS_TX_DDR_M1_R1_CFG_8, pipe_en);
                end
                default: begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET, DDR_DQ_DQS_TX_DDR_M1_R0_CFG_0, pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET, DDR_DQ_DQS_TX_DDR_M1_R0_CFG_0, pipe_en);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET, DDR_DQ_DQS_TX_DDR_M1_R0_CFG_1, pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET, DDR_DQ_DQS_TX_DDR_M1_R0_CFG_1, pipe_en);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET, DDR_DQ_DQS_TX_DDR_M1_R0_CFG_2, pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET, DDR_DQ_DQS_TX_DDR_M1_R0_CFG_2, pipe_en);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET, DDR_DQ_DQS_TX_DDR_M1_R0_CFG_3, pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET, DDR_DQ_DQS_TX_DDR_M1_R0_CFG_3, pipe_en);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET, DDR_DQ_DQS_TX_DDR_M1_R0_CFG_4, pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET, DDR_DQ_DQS_TX_DDR_M1_R0_CFG_4, pipe_en);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET, DDR_DQ_DQS_TX_DDR_M1_R0_CFG_5, pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET, DDR_DQ_DQS_TX_DDR_M1_R0_CFG_5, pipe_en);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET, DDR_DQ_DQS_TX_DDR_M1_R0_CFG_6, pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET, DDR_DQ_DQS_TX_DDR_M1_R0_CFG_6, pipe_en);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET, DDR_DQ_DQS_TX_DDR_M1_R0_CFG_7, pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET, DDR_DQ_DQS_TX_DDR_M1_R0_CFG_7, pipe_en);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET, DDR_DQ_DQS_TX_DDR_M1_R0_CFG_8, pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET, DDR_DQ_DQS_TX_DDR_M1_R0_CFG_8, pipe_en);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET, DDR_DQ_DQS_TX_DDR_M1_R1_CFG_0, pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET, DDR_DQ_DQS_TX_DDR_M1_R1_CFG_0, pipe_en);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET, DDR_DQ_DQS_TX_DDR_M1_R1_CFG_1, pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET, DDR_DQ_DQS_TX_DDR_M1_R1_CFG_1, pipe_en);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET, DDR_DQ_DQS_TX_DDR_M1_R1_CFG_2, pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET, DDR_DQ_DQS_TX_DDR_M1_R1_CFG_2, pipe_en);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET, DDR_DQ_DQS_TX_DDR_M1_R1_CFG_3, pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET, DDR_DQ_DQS_TX_DDR_M1_R1_CFG_3, pipe_en);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET, DDR_DQ_DQS_TX_DDR_M1_R1_CFG_4, pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET, DDR_DQ_DQS_TX_DDR_M1_R1_CFG_4, pipe_en);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET, DDR_DQ_DQS_TX_DDR_M1_R1_CFG_5, pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET, DDR_DQ_DQS_TX_DDR_M1_R1_CFG_5, pipe_en);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET, DDR_DQ_DQS_TX_DDR_M1_R1_CFG_6, pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET, DDR_DQ_DQS_TX_DDR_M1_R1_CFG_6, pipe_en);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET, DDR_DQ_DQS_TX_DDR_M1_R1_CFG_7, pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET, DDR_DQ_DQS_TX_DDR_M1_R1_CFG_7, pipe_en);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET, DDR_DQ_DQS_TX_DDR_M1_R1_CFG_8, pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET, DDR_DQ_DQS_TX_DDR_M1_R1_CFG_8, pipe_en);
                end
            endcase
        end
        if((byte_sel == DQ1) || (byte_sel == DQ_ALL) || (byte_sel == ALL)) begin
            case ({rank_sel,dqs})
                {RANK0, 8'd0} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET, DDR_DQ_DQS_TX_DDR_M1_R0_CFG_0, pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET, DDR_DQ_DQS_TX_DDR_M1_R0_CFG_0, pipe_en);
                end
                {RANK0, 8'd1} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET, DDR_DQ_DQS_TX_DDR_M1_R0_CFG_1, pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET, DDR_DQ_DQS_TX_DDR_M1_R0_CFG_1, pipe_en);
                end
                {RANK0, 8'd2} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET, DDR_DQ_DQS_TX_DDR_M1_R0_CFG_2, pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET, DDR_DQ_DQS_TX_DDR_M1_R0_CFG_2, pipe_en);
                end
                {RANK0, 8'd3} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET, DDR_DQ_DQS_TX_DDR_M1_R0_CFG_3, pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET, DDR_DQ_DQS_TX_DDR_M1_R0_CFG_3, pipe_en);
                end
                {RANK0, 8'd4} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET, DDR_DQ_DQS_TX_DDR_M1_R0_CFG_4, pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET, DDR_DQ_DQS_TX_DDR_M1_R0_CFG_4, pipe_en);
                end
                {RANK0, 8'd5} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET, DDR_DQ_DQS_TX_DDR_M1_R0_CFG_5, pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET, DDR_DQ_DQS_TX_DDR_M1_R0_CFG_5, pipe_en);
                end
                {RANK0, 8'd6} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET, DDR_DQ_DQS_TX_DDR_M1_R0_CFG_6, pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET, DDR_DQ_DQS_TX_DDR_M1_R0_CFG_6, pipe_en);
                end
                {RANK0, 8'd7} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET, DDR_DQ_DQS_TX_DDR_M1_R0_CFG_7, pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET, DDR_DQ_DQS_TX_DDR_M1_R0_CFG_7, pipe_en);
                end
                {RANK0, 8'd8} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET, DDR_DQ_DQS_TX_DDR_M1_R0_CFG_8, pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET, DDR_DQ_DQS_TX_DDR_M1_R0_CFG_8, pipe_en);
                end
                {RANK1, 8'd0} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET, DDR_DQ_DQS_TX_DDR_M1_R1_CFG_0, pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET, DDR_DQ_DQS_TX_DDR_M1_R1_CFG_0, pipe_en);
                end
                {RANK1, 8'd1} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET, DDR_DQ_DQS_TX_DDR_M1_R1_CFG_1, pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET, DDR_DQ_DQS_TX_DDR_M1_R1_CFG_1, pipe_en);
                end
                {RANK1, 8'd2} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET, DDR_DQ_DQS_TX_DDR_M1_R1_CFG_2, pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET, DDR_DQ_DQS_TX_DDR_M1_R1_CFG_2, pipe_en);
                end
                {RANK1, 8'd3} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET, DDR_DQ_DQS_TX_DDR_M1_R1_CFG_3, pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET, DDR_DQ_DQS_TX_DDR_M1_R1_CFG_3, pipe_en);
                end
                {RANK1, 8'd4} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET, DDR_DQ_DQS_TX_DDR_M1_R1_CFG_4, pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET, DDR_DQ_DQS_TX_DDR_M1_R1_CFG_4, pipe_en);
                end
                {RANK1, 8'd5} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET, DDR_DQ_DQS_TX_DDR_M1_R1_CFG_5, pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET, DDR_DQ_DQS_TX_DDR_M1_R1_CFG_5, pipe_en);
                end
                {RANK1, 8'd6} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET, DDR_DQ_DQS_TX_DDR_M1_R1_CFG_6, pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET, DDR_DQ_DQS_TX_DDR_M1_R1_CFG_6, pipe_en);
                end
                {RANK1, 8'd7} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET, DDR_DQ_DQS_TX_DDR_M1_R1_CFG_7, pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET, DDR_DQ_DQS_TX_DDR_M1_R1_CFG_7, pipe_en);
                end
                {RANK1, 8'd8} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET, DDR_DQ_DQS_TX_DDR_M1_R1_CFG_8, pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET, DDR_DQ_DQS_TX_DDR_M1_R1_CFG_8, pipe_en);
                end
                default: begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET, DDR_DQ_DQS_TX_DDR_M1_R0_CFG_0, pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET, DDR_DQ_DQS_TX_DDR_M1_R0_CFG_0, pipe_en);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET, DDR_DQ_DQS_TX_DDR_M1_R0_CFG_1, pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET, DDR_DQ_DQS_TX_DDR_M1_R0_CFG_1, pipe_en);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET, DDR_DQ_DQS_TX_DDR_M1_R0_CFG_2, pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET, DDR_DQ_DQS_TX_DDR_M1_R0_CFG_2, pipe_en);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET, DDR_DQ_DQS_TX_DDR_M1_R0_CFG_3, pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET, DDR_DQ_DQS_TX_DDR_M1_R0_CFG_3, pipe_en);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET, DDR_DQ_DQS_TX_DDR_M1_R0_CFG_4, pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET, DDR_DQ_DQS_TX_DDR_M1_R0_CFG_4, pipe_en);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET, DDR_DQ_DQS_TX_DDR_M1_R0_CFG_5, pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET, DDR_DQ_DQS_TX_DDR_M1_R0_CFG_5, pipe_en);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET, DDR_DQ_DQS_TX_DDR_M1_R0_CFG_6, pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET, DDR_DQ_DQS_TX_DDR_M1_R0_CFG_6, pipe_en);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET, DDR_DQ_DQS_TX_DDR_M1_R0_CFG_7, pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET, DDR_DQ_DQS_TX_DDR_M1_R0_CFG_7, pipe_en);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET, DDR_DQ_DQS_TX_DDR_M1_R0_CFG_8, pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET, DDR_DQ_DQS_TX_DDR_M1_R0_CFG_8, pipe_en);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET, DDR_DQ_DQS_TX_DDR_M1_R1_CFG_0, pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET, DDR_DQ_DQS_TX_DDR_M1_R1_CFG_0, pipe_en);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET, DDR_DQ_DQS_TX_DDR_M1_R1_CFG_1, pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET, DDR_DQ_DQS_TX_DDR_M1_R1_CFG_1, pipe_en);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET, DDR_DQ_DQS_TX_DDR_M1_R1_CFG_2, pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET, DDR_DQ_DQS_TX_DDR_M1_R1_CFG_2, pipe_en);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET, DDR_DQ_DQS_TX_DDR_M1_R1_CFG_3, pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET, DDR_DQ_DQS_TX_DDR_M1_R1_CFG_3, pipe_en);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET, DDR_DQ_DQS_TX_DDR_M1_R1_CFG_4, pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET, DDR_DQ_DQS_TX_DDR_M1_R1_CFG_4, pipe_en);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET, DDR_DQ_DQS_TX_DDR_M1_R1_CFG_5, pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET, DDR_DQ_DQS_TX_DDR_M1_R1_CFG_5, pipe_en);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET, DDR_DQ_DQS_TX_DDR_M1_R1_CFG_6, pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET, DDR_DQ_DQS_TX_DDR_M1_R1_CFG_6, pipe_en);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET, DDR_DQ_DQS_TX_DDR_M1_R1_CFG_7, pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET, DDR_DQ_DQS_TX_DDR_M1_R1_CFG_7, pipe_en);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET, DDR_DQ_DQS_TX_DDR_M1_R1_CFG_8, pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET, DDR_DQ_DQS_TX_DDR_M1_R1_CFG_8, pipe_en);
                end
            endcase
        end
        if((byte_sel == CA) || (byte_sel == ALL)) begin
            case ({rank_sel,dqs})
                {RANK0, 8'd0} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET, DDR_CA_DQS_TX_DDR_M1_R0_CFG_0, pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET, DDR_CA_DQS_TX_DDR_M1_R0_CFG_0, pipe_en);
                end
                {RANK1, 8'd0} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET, DDR_CA_DQS_TX_DDR_M1_R1_CFG_0, pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET, DDR_CA_DQS_TX_DDR_M1_R1_CFG_0, pipe_en);
                end
                default: begin
                    `CSR_WR(DDR_CH0_CA_OFFSET, DDR_CA_DQS_TX_DDR_M1_R0_CFG_0, pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET, DDR_CA_DQS_TX_DDR_M1_R0_CFG_0, pipe_en);
                    `CSR_WR(DDR_CH0_CA_OFFSET, DDR_CA_DQS_TX_DDR_M1_R1_CFG_0, pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET, DDR_CA_DQS_TX_DDR_M1_R1_CFG_0, pipe_en);
                end
            endcase
        end
    end
endtask

task automatic set_txdqs_qdr_x_sel_m1;
    input byte_sel_t     byte_sel;
    input rank_sel_t     rank_sel;
    input logic    [7:0] dqs;
    input logic   [31:0] x_sel;
    begin
        if((byte_sel == DQ0) || (byte_sel == DQ_ALL) || (byte_sel == ALL)) begin
            case ({rank_sel,dqs})
                {RANK0, 8'd0} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M1_R0_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M1_R0_CFG_0 , x_sel  );
                end
                {RANK0, 8'd1} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M1_R0_CFG_1 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M1_R0_CFG_1 , x_sel  );
                end
                {RANK0, 8'd2} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M1_R0_CFG_2 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M1_R0_CFG_2 , x_sel  );
                end
                {RANK0, 8'd3} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M1_R0_CFG_3 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M1_R0_CFG_3 , x_sel  );
                end
                {RANK0, 8'd4} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M1_R0_CFG_4 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M1_R0_CFG_4 , x_sel  );
                end
                {RANK0, 8'd5} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M1_R0_CFG_5 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M1_R0_CFG_5 , x_sel  );
                end
                {RANK0, 8'd6} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M1_R0_CFG_6 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M1_R0_CFG_6 , x_sel  );
                end
                {RANK0, 8'd7} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M1_R0_CFG_7 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M1_R0_CFG_7 , x_sel  );
                end
                {RANK0, 8'd8} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M1_R0_CFG_8 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M1_R0_CFG_8 , x_sel  );
                end
                {RANK1, 8'd0} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M1_R1_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M1_R1_CFG_0 , x_sel  );
                end
                {RANK1, 8'd1} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M1_R1_CFG_1 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M1_R1_CFG_1 , x_sel  );
                end
                {RANK1, 8'd2} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M1_R1_CFG_2 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M1_R1_CFG_2 , x_sel  );
                end
                {RANK1, 8'd3} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M1_R1_CFG_3 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M1_R1_CFG_3 , x_sel  );
                end
                {RANK1, 8'd4} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M1_R1_CFG_4 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M1_R1_CFG_4 , x_sel  );
                end
                {RANK1, 8'd5} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M1_R1_CFG_5 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M1_R1_CFG_5 , x_sel  );
                end
                {RANK1, 8'd6} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M1_R1_CFG_6 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M1_R1_CFG_6 , x_sel  );
                end
                {RANK1, 8'd7} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M1_R1_CFG_7 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M1_R1_CFG_7 , x_sel  );
                end
                {RANK1, 8'd8} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M1_R1_CFG_8 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M1_R1_CFG_8 , x_sel  );
                end
                default: begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M1_R0_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M1_R0_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M1_R0_CFG_1 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M1_R0_CFG_1 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M1_R0_CFG_2 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M1_R0_CFG_2 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M1_R0_CFG_3 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M1_R0_CFG_3 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M1_R0_CFG_4 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M1_R0_CFG_4 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M1_R0_CFG_5 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M1_R0_CFG_5 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M1_R0_CFG_6 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M1_R0_CFG_6 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M1_R0_CFG_7 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M1_R0_CFG_7 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M1_R0_CFG_8 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M1_R0_CFG_8 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M1_R1_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M1_R1_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M1_R1_CFG_1 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M1_R1_CFG_1 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M1_R1_CFG_2 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M1_R1_CFG_2 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M1_R1_CFG_3 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M1_R1_CFG_3 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M1_R1_CFG_4 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M1_R1_CFG_4 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M1_R1_CFG_5 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M1_R1_CFG_5 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M1_R1_CFG_6 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M1_R1_CFG_6 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M1_R1_CFG_7 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M1_R1_CFG_7 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M1_R1_CFG_8 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M1_R1_CFG_8 , x_sel  );
                end
            endcase
        end
        if((byte_sel == DQ1) || (byte_sel == DQ_ALL) || (byte_sel == ALL)) begin
            case ({rank_sel,dqs})
                {RANK0, 8'd0} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M1_R0_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M1_R0_CFG_0 , x_sel  );
                end
                {RANK0, 8'd1} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M1_R0_CFG_1 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M1_R0_CFG_1 , x_sel  );
                end
                {RANK0, 8'd2} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M1_R0_CFG_2 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M1_R0_CFG_2 , x_sel  );
                end
                {RANK0, 8'd3} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M1_R0_CFG_3 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M1_R0_CFG_3 , x_sel  );
                end
                {RANK0, 8'd4} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M1_R0_CFG_4 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M1_R0_CFG_4 , x_sel  );
                end
                {RANK0, 8'd5} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M1_R0_CFG_5 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M1_R0_CFG_5 , x_sel  );
                end
                {RANK0, 8'd6} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M1_R0_CFG_6 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M1_R0_CFG_6 , x_sel  );
                end
                {RANK0, 8'd7} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M1_R0_CFG_7 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M1_R0_CFG_7 , x_sel  );
                end
                {RANK0, 8'd8} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M1_R0_CFG_8 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M1_R0_CFG_8 , x_sel  );
                end
                {RANK1, 8'd0} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M1_R1_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M1_R1_CFG_0 , x_sel  );
                end
                {RANK1, 8'd1} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M1_R1_CFG_1 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M1_R1_CFG_1 , x_sel  );
                end
                {RANK1, 8'd2} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M1_R1_CFG_2 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M1_R1_CFG_2 , x_sel  );
                end
                {RANK1, 8'd3} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M1_R1_CFG_3 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M1_R1_CFG_3 , x_sel  );
                end
                {RANK1, 8'd4} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M1_R1_CFG_4 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M1_R1_CFG_4 , x_sel  );
                end
                {RANK1, 8'd5} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M1_R1_CFG_5 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M1_R1_CFG_5 , x_sel  );
                end
                {RANK1, 8'd6} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M1_R1_CFG_6 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M1_R1_CFG_6 , x_sel  );
                end
                {RANK1, 8'd7} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M1_R1_CFG_7 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M1_R1_CFG_7 , x_sel  );
                end
                {RANK1, 8'd8} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M1_R1_CFG_8 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M1_R1_CFG_8 , x_sel  );
                end
                default: begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M1_R0_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M1_R0_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M1_R0_CFG_1 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M1_R0_CFG_1 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M1_R0_CFG_2 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M1_R0_CFG_2 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M1_R0_CFG_3 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M1_R0_CFG_3 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M1_R0_CFG_4 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M1_R0_CFG_4 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M1_R0_CFG_5 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M1_R0_CFG_5 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M1_R0_CFG_6 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M1_R0_CFG_6 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M1_R0_CFG_7 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M1_R0_CFG_7 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M1_R0_CFG_8 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M1_R0_CFG_8 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M1_R1_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M1_R1_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M1_R1_CFG_1 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M1_R1_CFG_1 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M1_R1_CFG_2 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M1_R1_CFG_2 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M1_R1_CFG_3 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M1_R1_CFG_3 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M1_R1_CFG_4 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M1_R1_CFG_4 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M1_R1_CFG_5 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M1_R1_CFG_5 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M1_R1_CFG_6 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M1_R1_CFG_6 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M1_R1_CFG_7 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M1_R1_CFG_7 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M1_R1_CFG_8 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M1_R1_CFG_8 , x_sel  );
                end
            endcase
        end
        if((byte_sel == CA) || (byte_sel == ALL)) begin
            case ({rank_sel,dqs})
                {RANK0, 8'd0} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQS_TX_QDR_X_SEL_M1_R0_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQS_TX_QDR_X_SEL_M1_R0_CFG_0 , x_sel  );
                end
                {RANK1, 8'd0} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQS_TX_QDR_X_SEL_M1_R1_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQS_TX_QDR_X_SEL_M1_R1_CFG_0 , x_sel  );
                end
                default: begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQS_TX_QDR_X_SEL_M1_R0_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQS_TX_QDR_X_SEL_M1_R0_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQS_TX_QDR_X_SEL_M1_R1_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQS_TX_QDR_X_SEL_M1_R1_CFG_0 , x_sel  );
                end
            endcase
        end
    end
endtask

task automatic set_txdqs_qdr_pipe_en_m1;
    input byte_sel_t     byte_sel;
    input rank_sel_t     rank_sel;
    input logic    [7:0] dqs;
    input logic   [31:0] pipe_en;
    begin
        if((byte_sel == DQ0) || (byte_sel == DQ_ALL) || (byte_sel == ALL)) begin
            case ({rank_sel,dqs})
                {RANK0, 8'd0} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET, DDR_DQ_DQS_TX_QDR_M1_R0_CFG_0, pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET, DDR_DQ_DQS_TX_QDR_M1_R0_CFG_0, pipe_en);
                end
                {RANK0, 8'd1} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET, DDR_DQ_DQS_TX_QDR_M1_R0_CFG_1, pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET, DDR_DQ_DQS_TX_QDR_M1_R0_CFG_1, pipe_en);
                end
                {RANK0, 8'd2} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET, DDR_DQ_DQS_TX_QDR_M1_R0_CFG_2, pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET, DDR_DQ_DQS_TX_QDR_M1_R0_CFG_2, pipe_en);
                end
                {RANK0, 8'd3} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET, DDR_DQ_DQS_TX_QDR_M1_R0_CFG_3, pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET, DDR_DQ_DQS_TX_QDR_M1_R0_CFG_3, pipe_en);
                end
                {RANK0, 8'd4} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET, DDR_DQ_DQS_TX_QDR_M1_R0_CFG_4, pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET, DDR_DQ_DQS_TX_QDR_M1_R0_CFG_4, pipe_en);
                end
                {RANK0, 8'd5} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET, DDR_DQ_DQS_TX_QDR_M1_R0_CFG_5, pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET, DDR_DQ_DQS_TX_QDR_M1_R0_CFG_5, pipe_en);
                end
                {RANK0, 8'd6} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET, DDR_DQ_DQS_TX_QDR_M1_R0_CFG_6, pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET, DDR_DQ_DQS_TX_QDR_M1_R0_CFG_6, pipe_en);
                end
                {RANK0, 8'd7} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET, DDR_DQ_DQS_TX_QDR_M1_R0_CFG_7, pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET, DDR_DQ_DQS_TX_QDR_M1_R0_CFG_7, pipe_en);
                end
                {RANK0, 8'd8} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET, DDR_DQ_DQS_TX_QDR_M1_R0_CFG_8, pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET, DDR_DQ_DQS_TX_QDR_M1_R0_CFG_8, pipe_en);
                end
                {RANK1, 8'd0} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET, DDR_DQ_DQS_TX_QDR_M1_R1_CFG_0, pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET, DDR_DQ_DQS_TX_QDR_M1_R1_CFG_0, pipe_en);
                end
                {RANK1, 8'd1} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET, DDR_DQ_DQS_TX_QDR_M1_R1_CFG_1, pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET, DDR_DQ_DQS_TX_QDR_M1_R1_CFG_1, pipe_en);
                end
                {RANK1, 8'd2} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET, DDR_DQ_DQS_TX_QDR_M1_R1_CFG_2, pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET, DDR_DQ_DQS_TX_QDR_M1_R1_CFG_2, pipe_en);
                end
                {RANK1, 8'd3} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET, DDR_DQ_DQS_TX_QDR_M1_R1_CFG_3, pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET, DDR_DQ_DQS_TX_QDR_M1_R1_CFG_3, pipe_en);
                end
                {RANK1, 8'd4} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET, DDR_DQ_DQS_TX_QDR_M1_R1_CFG_4, pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET, DDR_DQ_DQS_TX_QDR_M1_R1_CFG_4, pipe_en);
                end
                {RANK1, 8'd5} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET, DDR_DQ_DQS_TX_QDR_M1_R1_CFG_5, pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET, DDR_DQ_DQS_TX_QDR_M1_R1_CFG_5, pipe_en);
                end
                {RANK1, 8'd6} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET, DDR_DQ_DQS_TX_QDR_M1_R1_CFG_6, pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET, DDR_DQ_DQS_TX_QDR_M1_R1_CFG_6, pipe_en);
                end
                {RANK1, 8'd7} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET, DDR_DQ_DQS_TX_QDR_M1_R1_CFG_7, pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET, DDR_DQ_DQS_TX_QDR_M1_R1_CFG_7, pipe_en);
                end
                {RANK1, 8'd8} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET, DDR_DQ_DQS_TX_QDR_M1_R1_CFG_8, pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET, DDR_DQ_DQS_TX_QDR_M1_R1_CFG_8, pipe_en);
                end
                default: begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET, DDR_DQ_DQS_TX_QDR_M1_R0_CFG_0, pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET, DDR_DQ_DQS_TX_QDR_M1_R0_CFG_0, pipe_en);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET, DDR_DQ_DQS_TX_QDR_M1_R0_CFG_1, pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET, DDR_DQ_DQS_TX_QDR_M1_R0_CFG_1, pipe_en);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET, DDR_DQ_DQS_TX_QDR_M1_R0_CFG_2, pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET, DDR_DQ_DQS_TX_QDR_M1_R0_CFG_2, pipe_en);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET, DDR_DQ_DQS_TX_QDR_M1_R0_CFG_3, pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET, DDR_DQ_DQS_TX_QDR_M1_R0_CFG_3, pipe_en);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET, DDR_DQ_DQS_TX_QDR_M1_R0_CFG_4, pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET, DDR_DQ_DQS_TX_QDR_M1_R0_CFG_4, pipe_en);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET, DDR_DQ_DQS_TX_QDR_M1_R0_CFG_5, pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET, DDR_DQ_DQS_TX_QDR_M1_R0_CFG_5, pipe_en);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET, DDR_DQ_DQS_TX_QDR_M1_R0_CFG_6, pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET, DDR_DQ_DQS_TX_QDR_M1_R0_CFG_6, pipe_en);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET, DDR_DQ_DQS_TX_QDR_M1_R0_CFG_7, pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET, DDR_DQ_DQS_TX_QDR_M1_R0_CFG_7, pipe_en);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET, DDR_DQ_DQS_TX_QDR_M1_R0_CFG_8, pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET, DDR_DQ_DQS_TX_QDR_M1_R0_CFG_8, pipe_en);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET, DDR_DQ_DQS_TX_QDR_M1_R1_CFG_0, pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET, DDR_DQ_DQS_TX_QDR_M1_R1_CFG_0, pipe_en);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET, DDR_DQ_DQS_TX_QDR_M1_R1_CFG_1, pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET, DDR_DQ_DQS_TX_QDR_M1_R1_CFG_1, pipe_en);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET, DDR_DQ_DQS_TX_QDR_M1_R1_CFG_2, pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET, DDR_DQ_DQS_TX_QDR_M1_R1_CFG_2, pipe_en);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET, DDR_DQ_DQS_TX_QDR_M1_R1_CFG_3, pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET, DDR_DQ_DQS_TX_QDR_M1_R1_CFG_3, pipe_en);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET, DDR_DQ_DQS_TX_QDR_M1_R1_CFG_4, pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET, DDR_DQ_DQS_TX_QDR_M1_R1_CFG_4, pipe_en);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET, DDR_DQ_DQS_TX_QDR_M1_R1_CFG_5, pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET, DDR_DQ_DQS_TX_QDR_M1_R1_CFG_5, pipe_en);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET, DDR_DQ_DQS_TX_QDR_M1_R1_CFG_6, pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET, DDR_DQ_DQS_TX_QDR_M1_R1_CFG_6, pipe_en);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET, DDR_DQ_DQS_TX_QDR_M1_R1_CFG_7, pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET, DDR_DQ_DQS_TX_QDR_M1_R1_CFG_7, pipe_en);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET, DDR_DQ_DQS_TX_QDR_M1_R1_CFG_8, pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET, DDR_DQ_DQS_TX_QDR_M1_R1_CFG_8, pipe_en);
                end
            endcase
        end
        if((byte_sel == DQ1) || (byte_sel == DQ_ALL) || (byte_sel == ALL)) begin
            case ({rank_sel,dqs})
                {RANK0, 8'd0} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET, DDR_DQ_DQS_TX_QDR_M1_R0_CFG_0, pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET, DDR_DQ_DQS_TX_QDR_M1_R0_CFG_0, pipe_en);
                end
                {RANK0, 8'd1} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET, DDR_DQ_DQS_TX_QDR_M1_R0_CFG_1, pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET, DDR_DQ_DQS_TX_QDR_M1_R0_CFG_1, pipe_en);
                end
                {RANK0, 8'd2} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET, DDR_DQ_DQS_TX_QDR_M1_R0_CFG_2, pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET, DDR_DQ_DQS_TX_QDR_M1_R0_CFG_2, pipe_en);
                end
                {RANK0, 8'd3} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET, DDR_DQ_DQS_TX_QDR_M1_R0_CFG_3, pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET, DDR_DQ_DQS_TX_QDR_M1_R0_CFG_3, pipe_en);
                end
                {RANK0, 8'd4} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET, DDR_DQ_DQS_TX_QDR_M1_R0_CFG_4, pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET, DDR_DQ_DQS_TX_QDR_M1_R0_CFG_4, pipe_en);
                end
                {RANK0, 8'd5} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET, DDR_DQ_DQS_TX_QDR_M1_R0_CFG_5, pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET, DDR_DQ_DQS_TX_QDR_M1_R0_CFG_5, pipe_en);
                end
                {RANK0, 8'd6} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET, DDR_DQ_DQS_TX_QDR_M1_R0_CFG_6, pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET, DDR_DQ_DQS_TX_QDR_M1_R0_CFG_6, pipe_en);
                end
                {RANK0, 8'd7} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET, DDR_DQ_DQS_TX_QDR_M1_R0_CFG_7, pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET, DDR_DQ_DQS_TX_QDR_M1_R0_CFG_7, pipe_en);
                end
                {RANK0, 8'd8} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET, DDR_DQ_DQS_TX_QDR_M1_R0_CFG_8, pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET, DDR_DQ_DQS_TX_QDR_M1_R0_CFG_8, pipe_en);
                end
                {RANK1, 8'd0} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET, DDR_DQ_DQS_TX_QDR_M1_R1_CFG_0, pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET, DDR_DQ_DQS_TX_QDR_M1_R1_CFG_0, pipe_en);
                end
                {RANK1, 8'd1} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET, DDR_DQ_DQS_TX_QDR_M1_R1_CFG_1, pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET, DDR_DQ_DQS_TX_QDR_M1_R1_CFG_1, pipe_en);
                end
                {RANK1, 8'd2} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET, DDR_DQ_DQS_TX_QDR_M1_R1_CFG_2, pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET, DDR_DQ_DQS_TX_QDR_M1_R1_CFG_2, pipe_en);
                end
                {RANK1, 8'd3} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET, DDR_DQ_DQS_TX_QDR_M1_R1_CFG_3, pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET, DDR_DQ_DQS_TX_QDR_M1_R1_CFG_3, pipe_en);
                end
                {RANK1, 8'd4} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET, DDR_DQ_DQS_TX_QDR_M1_R1_CFG_4, pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET, DDR_DQ_DQS_TX_QDR_M1_R1_CFG_4, pipe_en);
                end
                {RANK1, 8'd5} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET, DDR_DQ_DQS_TX_QDR_M1_R1_CFG_5, pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET, DDR_DQ_DQS_TX_QDR_M1_R1_CFG_5, pipe_en);
                end
                {RANK1, 8'd6} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET, DDR_DQ_DQS_TX_QDR_M1_R1_CFG_6, pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET, DDR_DQ_DQS_TX_QDR_M1_R1_CFG_6, pipe_en);
                end
                {RANK1, 8'd7} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET, DDR_DQ_DQS_TX_QDR_M1_R1_CFG_7, pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET, DDR_DQ_DQS_TX_QDR_M1_R1_CFG_7, pipe_en);
                end
                {RANK1, 8'd8} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET, DDR_DQ_DQS_TX_QDR_M1_R1_CFG_8, pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET, DDR_DQ_DQS_TX_QDR_M1_R1_CFG_8, pipe_en);
                end
                default: begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET, DDR_DQ_DQS_TX_QDR_M1_R0_CFG_0, pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET, DDR_DQ_DQS_TX_QDR_M1_R0_CFG_0, pipe_en);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET, DDR_DQ_DQS_TX_QDR_M1_R0_CFG_1, pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET, DDR_DQ_DQS_TX_QDR_M1_R0_CFG_1, pipe_en);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET, DDR_DQ_DQS_TX_QDR_M1_R0_CFG_2, pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET, DDR_DQ_DQS_TX_QDR_M1_R0_CFG_2, pipe_en);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET, DDR_DQ_DQS_TX_QDR_M1_R0_CFG_3, pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET, DDR_DQ_DQS_TX_QDR_M1_R0_CFG_3, pipe_en);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET, DDR_DQ_DQS_TX_QDR_M1_R0_CFG_4, pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET, DDR_DQ_DQS_TX_QDR_M1_R0_CFG_4, pipe_en);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET, DDR_DQ_DQS_TX_QDR_M1_R0_CFG_5, pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET, DDR_DQ_DQS_TX_QDR_M1_R0_CFG_5, pipe_en);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET, DDR_DQ_DQS_TX_QDR_M1_R0_CFG_6, pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET, DDR_DQ_DQS_TX_QDR_M1_R0_CFG_6, pipe_en);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET, DDR_DQ_DQS_TX_QDR_M1_R0_CFG_7, pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET, DDR_DQ_DQS_TX_QDR_M1_R0_CFG_7, pipe_en);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET, DDR_DQ_DQS_TX_QDR_M1_R0_CFG_8, pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET, DDR_DQ_DQS_TX_QDR_M1_R0_CFG_8, pipe_en);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET, DDR_DQ_DQS_TX_QDR_M1_R1_CFG_0, pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET, DDR_DQ_DQS_TX_QDR_M1_R1_CFG_0, pipe_en);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET, DDR_DQ_DQS_TX_QDR_M1_R1_CFG_1, pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET, DDR_DQ_DQS_TX_QDR_M1_R1_CFG_1, pipe_en);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET, DDR_DQ_DQS_TX_QDR_M1_R1_CFG_2, pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET, DDR_DQ_DQS_TX_QDR_M1_R1_CFG_2, pipe_en);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET, DDR_DQ_DQS_TX_QDR_M1_R1_CFG_3, pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET, DDR_DQ_DQS_TX_QDR_M1_R1_CFG_3, pipe_en);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET, DDR_DQ_DQS_TX_QDR_M1_R1_CFG_4, pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET, DDR_DQ_DQS_TX_QDR_M1_R1_CFG_4, pipe_en);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET, DDR_DQ_DQS_TX_QDR_M1_R1_CFG_5, pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET, DDR_DQ_DQS_TX_QDR_M1_R1_CFG_5, pipe_en);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET, DDR_DQ_DQS_TX_QDR_M1_R1_CFG_6, pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET, DDR_DQ_DQS_TX_QDR_M1_R1_CFG_6, pipe_en);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET, DDR_DQ_DQS_TX_QDR_M1_R1_CFG_7, pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET, DDR_DQ_DQS_TX_QDR_M1_R1_CFG_7, pipe_en);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET, DDR_DQ_DQS_TX_QDR_M1_R1_CFG_8, pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET, DDR_DQ_DQS_TX_QDR_M1_R1_CFG_8, pipe_en);
                end
            endcase
        end
        if((byte_sel == CA) || (byte_sel == ALL)) begin
            case ({rank_sel,dqs})
                {RANK0, 8'd0} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET, DDR_CA_DQS_TX_QDR_M1_R0_CFG_0, pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET, DDR_CA_DQS_TX_QDR_M1_R0_CFG_0, pipe_en);
                end
                {RANK1, 8'd0} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET, DDR_CA_DQS_TX_QDR_M1_R1_CFG_0, pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET, DDR_CA_DQS_TX_QDR_M1_R1_CFG_0, pipe_en);
                end
                default: begin
                    `CSR_WR(DDR_CH0_CA_OFFSET, DDR_CA_DQS_TX_QDR_M1_R0_CFG_0, pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET, DDR_CA_DQS_TX_QDR_M1_R0_CFG_0, pipe_en);
                    `CSR_WR(DDR_CH0_CA_OFFSET, DDR_CA_DQS_TX_QDR_M1_R1_CFG_0, pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET, DDR_CA_DQS_TX_QDR_M1_R1_CFG_0, pipe_en);
                end
            endcase
        end
    end
endtask

//-----------------------------------------------------------------------
// DQ DP APIs - End
//-----------------------------------------------------------------------

task automatic set_dfi_paden_pext_cfg_m1;
    input logic [7:0] wrd_oe_cycles;
    input logic [7:0] wrd_en_cycles;
    input logic [7:0] wck_oe_cycles;
    input logic [7:0] ie_cycles;
    input logic [7:0] re_cycles;
    input logic [7:0] ren_cycles;
    input logic [7:0] rcs_cycles;
    begin
        `CSR_WRF2(DDR_DFICH0_OFFSET,DDR_DFICH_CTRL5_M1_CFG   , IE_PHASE_EXT, RE_PHASE_EXT, ie_cycles, re_cycles);
        `CSR_WRF1(DDR_DFICH0_OFFSET,DDR_DFICH_CTRL3_M1_CFG   , WRD_OE_PHASE_EXT, wrd_oe_cycles);
        `CSR_WRF1(DDR_DFICH0_OFFSET,DDR_DFICH_CTRL4_M1_CFG   , WCK_OE_PHASE_EXT, wck_oe_cycles);
        `CSR_WRF1(DDR_DFICH0_OFFSET,DDR_DFICH_CTRL3_M1_CFG   , WRD_EN_PHASE_EXT, wrd_en_cycles);
        `CSR_WRF2(DDR_DFICH0_OFFSET,DDR_DFICH_CTRL5_M1_CFG   , REN_PHASE_EXT, RCS_PHASE_EXT, ren_cycles, rcs_cycles);
    end
endtask

task automatic set_dfi_clken_pext_cfg_m1;
    input logic [3:0] wr_clken_cycles;
    input logic [3:0] rd_clken_cycles;
    input logic [3:0] ca_clken_cycles;
    begin
        `CSR_WRF3(DDR_DFICH0_OFFSET,DDR_DFICH_CTRL2_M1_CFG, DQ_WRCLK_EN_PULSE_EXT, DQS_WRCLK_EN_PULSE_EXT, RDCLK_EN_PULSE_EXT,wr_clken_cycles,wr_clken_cycles,rd_clken_cycles );
        `CSR_WRF2(DDR_DFICH0_OFFSET,DDR_DFICH_CTRL2_M1_CFG, CA_CLK_EN_PULSE_EXT, CK_CLK_EN_PULSE_EXT , ca_clken_cycles, ca_clken_cycles );
    end
endtask

task automatic set_dfi_traffic_ovr_cfg_m1;
    input logic  sw_en ;
    input logic  sw_mode ;
    begin
        `CSR_WRF2(DDR_DFICH0_OFFSET,DDR_DFICH_CTRL1_M1_CFG, DQ_WRTRAFFIC_OVR,      CA_TRAFFIC_OVR,     sw_en , sw_en );
        `CSR_WRF2(DDR_DFICH0_OFFSET,DDR_DFICH_CTRL1_M1_CFG, DQS_WRTRAFFIC_OVR,     CK_TRAFFIC_OVR,     sw_en , sw_en );
        `CSR_WRF2(DDR_DFICH0_OFFSET,DDR_DFICH_CTRL1_M1_CFG, DQ_WRTRAFFIC_OVR_SEL,  CA_TRAFFIC_OVR_SEL, sw_mode , sw_mode );
        `CSR_WRF2(DDR_DFICH0_OFFSET,DDR_DFICH_CTRL1_M1_CFG, DQS_WRTRAFFIC_OVR_SEL, CK_TRAFFIC_OVR_SEL, sw_mode , sw_mode );
        `CSR_WRF2(DDR_DFICH0_OFFSET,DDR_DFICH_CTRL1_M1_CFG, DQ_WRTRAFFIC_OVR,      CA_TRAFFIC_OVR,     sw_en , sw_en );
        `CSR_WRF2(DDR_DFICH0_OFFSET,DDR_DFICH_CTRL1_M1_CFG, DQS_WRTRAFFIC_OVR,     CK_TRAFFIC_OVR,     sw_en , sw_en );
        `CSR_WRF2(DDR_DFICH0_OFFSET,DDR_DFICH_CTRL1_M1_CFG, DQ_WRTRAFFIC_OVR_SEL,  CA_TRAFFIC_OVR_SEL, sw_mode , sw_mode );
        `CSR_WRF2(DDR_DFICH0_OFFSET,DDR_DFICH_CTRL1_M1_CFG, DQS_WRTRAFFIC_OVR_SEL, CK_TRAFFIC_OVR_SEL, sw_mode , sw_mode );
    end
endtask



task automatic set_dfiwctrl_wdp_cfg_m1;
    input dwgb_t       gb_mode;
    input logic [2:0]  gb_pipe_dly;
    input logic        pre_gb_pipe_en;
    begin
        `CSR_WRF3(DDR_DFICH0_OFFSET,DDR_DFICH_WCTRL_M1_CFG  ,POST_GB_FC_DLY, GB_MODE, PIPE_EN, gb_pipe_dly, gb_mode, pre_gb_pipe_en);
    end
endtask

task automatic set_dfiwenctrl_wdp_cfg_m1;
    input dwgb_t       gb_mode;
    input logic [2:0]  gb_pipe_dly;
    input logic        pre_gb_pipe_en;
    begin
        `CSR_WRF3(DDR_DFICH0_OFFSET,DDR_DFICH_WENCTRL_M1_CFG  ,POST_GB_FC_DLY, GB_MODE, PIPE_EN, gb_pipe_dly, gb_mode, pre_gb_pipe_en);
    end
endtask

task automatic set_dfiwckctrl_wdp_cfg_m1;
    input dwgb_t       gb_mode;
    input logic [2:0]  gb_pipe_dly;
    input logic        pre_gb_pipe_en;
    begin
        `CSR_WRF3(DDR_DFICH0_OFFSET,DDR_DFICH_WCKCTRL_M1_CFG,POST_GB_FC_DLY, GB_MODE, PIPE_EN, gb_pipe_dly, gb_mode, pre_gb_pipe_en);
    end
endtask

task automatic set_dfirctrl_wdp_cfg_m1;
    input dwgb_t       gb_mode;
    input logic [2:0]  gb_pipe_dly;
    input logic        pre_gb_pipe_en;
    begin
        `CSR_WRF3(DDR_DFICH0_OFFSET,DDR_DFICH_RCTRL_M1_CFG  ,POST_GB_FC_DLY, GB_MODE, PIPE_EN, gb_pipe_dly, gb_mode, pre_gb_pipe_en);
    end
endtask

task automatic set_dfiwrcctrl_wdp_cfg_m1;

    input dwgb_t  gb_mode;
    input logic [2:0]  gb_pipe_dly;
    input logic   pre_gb_pipe_en;
    begin
        `CSR_WRF3(DDR_DFICH0_OFFSET,DDR_DFICH_WRCCTRL_M1_CFG    ,POST_GB_FC_DLY, GB_MODE, PIPE_EN, gb_pipe_dly, gb_mode, pre_gb_pipe_en);
    end
endtask

task automatic set_dfickctrl_wdp_cfg_m1;

    input dwgb_t  gb_mode;
    input logic [2:0]  gb_pipe_dly;
    input logic   pre_gb_pipe_en;
    begin
        `CSR_WRF3(DDR_DFICH0_OFFSET,DDR_DFICH_CKCTRL_M1_CFG    ,POST_GB_FC_DLY, GB_MODE, PIPE_EN, gb_pipe_dly, gb_mode, pre_gb_pipe_en);
    end
endtask

task automatic set_dfiwrd_wdp_cfg_m1;

    input dwgb_t  gb_mode;
    input logic [2:0]  gb_pipe_dly;
    input logic   pre_gb_pipe_en;
    begin
        `CSR_WRF3(DDR_DFICH0_OFFSET,DDR_DFICH_WRD_M1_CFG    ,POST_GB_FC_DLY, GB_MODE, PIPE_EN, gb_pipe_dly, gb_mode, pre_gb_pipe_en);
        `CSR_WRF3(DDR_DFICH0_OFFSET,DDR_DFICH_WRC_M1_CFG    ,POST_GB_FC_DLY, GB_MODE, PIPE_EN, gb_pipe_dly, gb_mode, pre_gb_pipe_en);
    end
endtask


task automatic set_dfi_rdgb_mode_m1;
    input drgb_t gbmode;
    begin
        `CSR_WRF1(DDR_DFICH0_OFFSET,DDR_DFICH_RDD_M1_CFG,GB_MODE, gbmode);
    end
endtask

task automatic set_sa_lpde_dly_m1;
    input byte_sel_t  byte_sel;
    input rank_sel_t  rank_sel;
    input integer     dq;
    input logic [1:0] gear;
    input logic [7:0] r0_dly;
    input logic [7:0] r1_dly;
    begin
        if((byte_sel == DQ0) || (byte_sel == DQ_ALL) || (byte_sel == ALL)) begin
            case({rank_sel,dq})
                {RANK0,8'd0} : begin
                    `CSR_WRF8(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M1_R0_CFG_0,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r0_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M1_R0_CFG_0,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r0_dly,gear,0,0,0,0,0,0);
                end
                {RANK0,8'd1}: begin
                    `CSR_WRF8(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M1_R0_CFG_1,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r0_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M1_R0_CFG_1,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r0_dly,gear,0,0,0,0,0,0);
                end
                {RANK0,8'd2}: begin
                    `CSR_WRF8(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M1_R0_CFG_2,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r0_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M1_R0_CFG_2,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r0_dly,gear,0,0,0,0,0,0);
                end
                {RANK0,8'd3}: begin
                    `CSR_WRF8(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M1_R0_CFG_3,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r0_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M1_R0_CFG_3,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r0_dly,gear,0,0,0,0,0,0);
                end
                {RANK0,8'd4}: begin
                    `CSR_WRF8(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M1_R0_CFG_4,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r0_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M1_R0_CFG_4,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r0_dly,gear,0,0,0,0,0,0);
                end
                {RANK0,8'd5}: begin
                    `CSR_WRF8(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M1_R0_CFG_5,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r0_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M1_R0_CFG_5,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r0_dly,gear,0,0,0,0,0,0);
                end
                {RANK0,8'd6}: begin
                    `CSR_WRF8(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M1_R0_CFG_6,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r0_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M1_R0_CFG_5,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r0_dly,gear,0,0,0,0,0,0);
                end
                {RANK0,8'd6}: begin
                    `CSR_WRF8(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M1_R0_CFG_6,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r0_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M1_R0_CFG_6,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r0_dly,gear,0,0,0,0,0,0);
                end
                {RANK0,8'd7}: begin
                    `CSR_WRF8(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M1_R0_CFG_7,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r0_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M1_R0_CFG_7,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r0_dly,gear,0,0,0,0,0,0);
                end
                {RANK0,8'd8}: begin
                    `CSR_WRF8(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M1_R0_CFG_8,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r0_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M1_R0_CFG_8,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r0_dly,gear,0,0,0,0,0,0);
                end
                {RANK1,8'd0}: begin
                    `CSR_WRF8(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M1_R1_CFG_0,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r1_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M1_R1_CFG_0,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r1_dly,gear,0,0,0,0,0,0);
                end
                {RANK1,8'd1}: begin
                    `CSR_WRF8(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M1_R1_CFG_1,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r1_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M1_R1_CFG_1,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r1_dly,gear,0,0,0,0,0,0);
                end
                {RANK1,8'd2}: begin
                    `CSR_WRF8(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M1_R1_CFG_2,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r1_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M1_R1_CFG_2,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r1_dly,gear,0,0,0,0,0,0);
                end
                {RANK1,8'd3}: begin
                    `CSR_WRF8(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M1_R1_CFG_3,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r1_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M1_R1_CFG_3,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r1_dly,gear,0,0,0,0,0,0);
                end
                {RANK1,8'd4}: begin
                    `CSR_WRF8(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M1_R1_CFG_4,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r1_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M1_R1_CFG_4,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r1_dly,gear,0,0,0,0,0,0);
                end
                {RANK1,8'd5}: begin
                    `CSR_WRF8(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M1_R1_CFG_5,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r1_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M1_R1_CFG_5,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r1_dly,gear,0,0,0,0,0,0);
                end
                {RANK1,8'd6}: begin
                    `CSR_WRF8(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M1_R1_CFG_6,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r1_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M1_R1_CFG_6,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r1_dly,gear,0,0,0,0,0,0);
                end
                {RANK1,8'd7}: begin
                    `CSR_WRF8(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M1_R1_CFG_7,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r1_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M1_R1_CFG_7,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r1_dly,gear,0,0,0,0,0,0);
                end
                {RANK1,8'd8}: begin
                    `CSR_WRF8(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M1_R1_CFG_8,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r1_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M1_R1_CFG_8,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r1_dly,gear,0,0,0,0,0,0);
                end
                default : begin
                    `CSR_WRF8(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M1_R0_CFG_0,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r0_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M1_R0_CFG_1,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r0_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M1_R0_CFG_2,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r0_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M1_R0_CFG_3,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r0_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M1_R0_CFG_4,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r0_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M1_R0_CFG_5,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r0_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M1_R0_CFG_6,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r0_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M1_R0_CFG_7,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r0_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M1_R0_CFG_8,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r0_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M1_R0_CFG_0,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r0_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M1_R0_CFG_1,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r0_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M1_R0_CFG_2,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r0_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M1_R0_CFG_3,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r0_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M1_R0_CFG_4,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r0_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M1_R0_CFG_5,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r0_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M1_R0_CFG_6,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r0_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M1_R0_CFG_7,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r0_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M1_R0_CFG_8,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r0_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M1_R1_CFG_0,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r1_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M1_R1_CFG_1,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r1_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M1_R1_CFG_2,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r1_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M1_R1_CFG_3,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r1_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M1_R1_CFG_4,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r1_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M1_R1_CFG_5,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r1_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M1_R1_CFG_6,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r1_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M1_R1_CFG_7,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r1_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M1_R1_CFG_8,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r1_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M1_R1_CFG_0,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r1_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M1_R1_CFG_1,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r1_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M1_R1_CFG_2,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r1_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M1_R1_CFG_3,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r1_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M1_R1_CFG_4,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r1_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M1_R1_CFG_5,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r1_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M1_R1_CFG_6,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r1_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M1_R1_CFG_7,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r1_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M1_R1_CFG_8,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r1_dly,gear,0,0,0,0,0,0);
                end
            endcase
        end
        if((byte_sel == DQ1) || (byte_sel == DQ_ALL) || (byte_sel == ALL)) begin
            case({rank_sel,dq})
                {RANK0,8'd0} : begin
                    `CSR_WRF8(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M1_R0_CFG_0,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r0_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M1_R0_CFG_0,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r0_dly,gear,0,0,0,0,0,0);
                end
                {RANK0,8'd1}: begin
                    `CSR_WRF8(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M1_R0_CFG_1,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r0_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M1_R0_CFG_1,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r0_dly,gear,0,0,0,0,0,0);
                end
                {RANK0,8'd2}: begin
                    `CSR_WRF8(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M1_R0_CFG_2,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r0_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M1_R0_CFG_2,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r0_dly,gear,0,0,0,0,0,0);
                end
                {RANK0,8'd3}: begin
                    `CSR_WRF8(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M1_R0_CFG_3,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r0_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M1_R0_CFG_3,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r0_dly,gear,0,0,0,0,0,0);
                end
                {RANK0,8'd4}: begin
                    `CSR_WRF8(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M1_R0_CFG_4,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r0_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M1_R0_CFG_4,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r0_dly,gear,0,0,0,0,0,0);
                end
                {RANK0,8'd5}: begin
                    `CSR_WRF8(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M1_R0_CFG_5,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r0_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M1_R0_CFG_5,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r0_dly,gear,0,0,0,0,0,0);
                end
                {RANK0,8'd6}: begin
                    `CSR_WRF8(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M1_R0_CFG_6,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r0_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M1_R0_CFG_6,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r0_dly,gear,0,0,0,0,0,0);
                end
                {RANK0,8'd7}: begin
                    `CSR_WRF8(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M1_R0_CFG_7,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r0_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M1_R0_CFG_7,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r0_dly,gear,0,0,0,0,0,0);
                end
                {RANK0,8'd8}: begin
                    `CSR_WRF8(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M1_R0_CFG_8,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r0_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M1_R0_CFG_8,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r0_dly,gear,0,0,0,0,0,0);
                end
                {RANK1,8'd0}: begin
                    `CSR_WRF8(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M1_R1_CFG_0,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r1_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M1_R1_CFG_0,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r1_dly,gear,0,0,0,0,0,0);
                end
                {RANK1,8'd1}: begin
                    `CSR_WRF8(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M1_R1_CFG_1,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r1_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M1_R1_CFG_1,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r1_dly,gear,0,0,0,0,0,0);
                end
                {RANK1,8'd2}: begin
                    `CSR_WRF8(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M1_R1_CFG_2,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r1_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M1_R1_CFG_2,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r1_dly,gear,0,0,0,0,0,0);
                end
                {RANK1,8'd3}: begin
                    `CSR_WRF8(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M1_R1_CFG_3,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r1_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M1_R1_CFG_3,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r1_dly,gear,0,0,0,0,0,0);
                end
                {RANK1,8'd4}: begin
                    `CSR_WRF8(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M1_R1_CFG_4,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r1_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M1_R1_CFG_4,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r1_dly,gear,0,0,0,0,0,0);
                end
                {RANK1,8'd5}: begin
                    `CSR_WRF8(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M1_R1_CFG_5,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r1_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M1_R1_CFG_5,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r1_dly,gear,0,0,0,0,0,0);
                end
                {RANK1,8'd6}: begin
                    `CSR_WRF8(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M1_R1_CFG_6,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r1_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M1_R1_CFG_6,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r1_dly,gear,0,0,0,0,0,0);
                end
                {RANK1,8'd7}: begin
                    `CSR_WRF8(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M1_R1_CFG_7,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r1_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M1_R1_CFG_7,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r1_dly,gear,0,0,0,0,0,0);
                end
                {RANK1,8'd8}: begin
                    `CSR_WRF8(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M1_R1_CFG_8,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r1_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M1_R1_CFG_8,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r1_dly,gear,0,0,0,0,0,0);
                end
                default : begin
                    `CSR_WRF8(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M1_R0_CFG_0,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r0_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M1_R0_CFG_1,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r0_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M1_R0_CFG_2,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r0_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M1_R0_CFG_3,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r0_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M1_R0_CFG_4,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r0_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M1_R0_CFG_5,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r0_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M1_R0_CFG_6,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r0_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M1_R0_CFG_7,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r0_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M1_R0_CFG_8,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r0_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M1_R0_CFG_0,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r0_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M1_R0_CFG_1,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r0_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M1_R0_CFG_2,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r0_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M1_R0_CFG_3,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r0_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M1_R0_CFG_4,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r0_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M1_R0_CFG_5,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r0_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M1_R0_CFG_6,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r0_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M1_R0_CFG_7,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r0_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M1_R0_CFG_8,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r0_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M1_R1_CFG_0,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r1_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M1_R1_CFG_1,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r1_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M1_R1_CFG_2,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r1_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M1_R1_CFG_3,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r1_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M1_R1_CFG_4,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r1_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M1_R1_CFG_5,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r1_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M1_R1_CFG_6,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r1_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M1_R1_CFG_7,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r1_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M1_R1_CFG_8,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r1_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M1_R1_CFG_0,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r1_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M1_R1_CFG_1,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r1_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M1_R1_CFG_2,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r1_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M1_R1_CFG_3,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r1_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M1_R1_CFG_4,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r1_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M1_R1_CFG_5,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r1_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M1_R1_CFG_6,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r1_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M1_R1_CFG_7,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r1_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M1_R1_CFG_8,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r1_dly,gear,0,0,0,0,0,0);
                end
            endcase
        end
    end
endtask

