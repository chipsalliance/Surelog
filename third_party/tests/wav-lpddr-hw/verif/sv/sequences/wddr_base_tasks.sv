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
//-----------------------------------------------------------------------
// CMN/PLL APIs - Begin
//-----------------------------------------------------------------------

task automatic reset_pll_core;
    begin
        csr_read(DDR_PLL_OFFSET,`MVP_PLL_CORE_OVERRIDES, wdata);
        wdata[`MVP_PLL_CORE_OVERRIDES__CORE_RESET]=1'b1;
        wdata[`MVP_PLL_CORE_OVERRIDES__CORE_RESET_MUX]=1'b1;
        csr_write(DDR_PLL_OFFSET,`MVP_PLL_CORE_OVERRIDES, wdata);
        #100ns;
        csr_read(DDR_PLL_OFFSET,`MVP_PLL_CORE_OVERRIDES, wdata);
        wdata[`MVP_PLL_CORE_OVERRIDES__CORE_RESET]=1'b0;
        wdata[`MVP_PLL_CORE_OVERRIDES__CORE_RESET_MUX]=1'b1;
        csr_write(DDR_PLL_OFFSET,`MVP_PLL_CORE_OVERRIDES, wdata);

        // `CSR_WRF1(PLL_OFFSET,DDR_CMN_VCO0_CFG,VCO0_ENA,en);
        // `CSR_WRF1(PLL_OFFSET,DDR_CMN_VCO1_CFG,VCO1_ENA,en);
        // `CSR_WRF1(PLL_OFFSET,DDR_CMN_VCO2_CFG,VCO2_ENA,en);
    end
endtask

task automatic set_vcos_byp;
    input logic byp;
    begin
        csr_read(DDR_PLL_OFFSET,`MVP_PLL_VCO1_CONTROL, wdata);
        wdata[`MVP_PLL_VCO1_CONTROL__VCO1_BYP_CLK_SEL]= byp ;
        csr_write(DDR_PLL_OFFSET,`MVP_PLL_VCO1_CONTROL, wdata);

        csr_read(DDR_PLL_OFFSET,`MVP_PLL_VCO2_CONTROL, wdata);
        wdata[`MVP_PLL_VCO2_CONTROL__VCO2_BYP_CLK_SEL]= byp;
        csr_write(DDR_PLL_OFFSET,`MVP_PLL_VCO2_CONTROL, wdata);

        csr_read(DDR_PLL_OFFSET,`MVP_PLL_VCO0_CONTROL, wdata);
        wdata[`MVP_PLL_VCO0_CONTROL__VCO0_BYP_CLK_SEL]= byp;
        csr_write(DDR_PLL_OFFSET,`MVP_PLL_VCO0_CONTROL, wdata);
        // `CSR_WRF1(PLL_OFFSET,DDR_CMN_VCO0_CFG,VCO0_ENA,en);
        // `CSR_WRF1(PLL_OFFSET,DDR_CMN_VCO1_CFG,VCO1_ENA,en);
        // `CSR_WRF1(PLL_OFFSET,DDR_CMN_VCO2_CFG,VCO2_ENA,en);
    end
endtask

task automatic set_vcos_en;
    input logic en;
    begin
        csr_read(DDR_PLL_OFFSET,`MVP_PLL_VCO1_CONTROL, wdata);
        wdata[`MVP_PLL_VCO1_CONTROL__VCO1_ENA]=en;
        wdata[`MVP_PLL_VCO1_CONTROL__VCO1_ENA_MUX]=1'b1;
        csr_write(DDR_PLL_OFFSET,`MVP_PLL_VCO1_CONTROL, wdata);

        csr_read(DDR_PLL_OFFSET,`MVP_PLL_VCO2_CONTROL, wdata);
        wdata[`MVP_PLL_VCO2_CONTROL__VCO2_ENA]=en;
        wdata[`MVP_PLL_VCO2_CONTROL__VCO2_ENA_MUX]=1'b1;
        csr_write(DDR_PLL_OFFSET,`MVP_PLL_VCO2_CONTROL, wdata);

        // `CSR_WRF1(PLL_OFFSET,DDR_CMN_VCO0_CFG,VCO0_ENA,en);
        // `CSR_WRF1(PLL_OFFSET,DDR_CMN_VCO1_CFG,VCO1_ENA,en);
        // `CSR_WRF1(PLL_OFFSET,DDR_CMN_VCO2_CFG,VCO2_ENA,en);
    end
endtask

task automatic get_band_fbdiv_postdiv_hp_values;
    input  integer vco_freq_MHz;
    input  integer vco_sel;
    output [63:0] vco_band_val;
    output [1:0] vco_post_div;
    output integer vco_fbdiv_val;
    output [5:0] vco_fine_val;
    begin
        case(vco_freq_MHz)
            230:  begin vco_band_val = 'h03; vco_fine_val = 'h11; vco_post_div=2; vco_fbdiv_val=24; end // 230.4 Mhz
            422:  begin vco_band_val = 'h03; vco_fine_val = 'h11; vco_post_div=1; vco_fbdiv_val=22; end // 422.4 Mhz
            652:  begin vco_band_val = 'h08; vco_fine_val = 'h14; vco_post_div=1; vco_fbdiv_val=34; end // 652.8 Mhz
            806:  begin vco_band_val = 'h03; vco_fine_val = 'h0D; vco_post_div=0; vco_fbdiv_val=21; end // 806.4 Mhz
            1075: begin vco_band_val = 'h05; vco_fine_val = 'h12; vco_post_div=0; vco_fbdiv_val=28; end // 1075.2 Mhz
            1344: begin vco_band_val = 'h08; vco_fine_val = 'h11; vco_post_div=0; vco_fbdiv_val=35; end // 1344 Mhz
            1612: begin vco_band_val = 'h0A; vco_fine_val = 'h17; vco_post_div=0; vco_fbdiv_val=42; end // 1612.8 Mhz
            1881: begin vco_band_val = 'h0D; vco_fine_val = 'h19; vco_post_div=0; vco_fbdiv_val=49; end // 1881.6 Mhz
            2112: begin vco_band_val = 'h0F; vco_fine_val = 'h1F; vco_post_div=0; vco_fbdiv_val=55; end // 2112 Mhz
            2134: begin vco_band_val = 'h0F; vco_fine_val = 'h1F; vco_post_div=2'b00; vco_fbdiv_val=112;end
            //    2380: begin vco_band_val = 'h13; vco_fine_val = 'h1D; vco_post_div=2'b00; vco_fbdiv_val=; end
            //    2688: begin vco_band_val = 'h18; vco_fine_val = 'h1F; vco_post_div=2'b00; vco_fbdiv_val=; end
            //    3187: begin vco_band_val = 'h22; vco_fine_val = 'h1E; vco_post_div=2'b00; vco_fbdiv_val=; end
            default: $display ("Error:  VCO freq select is incorrect, valid values are 230, 422, 652, 806, 1075, 1344, 1612, 1881, 2112 received=%d", vco_freq_MHz);
        endcase
    end
endtask

task automatic set_band_vco_hp_value;
    input  integer vco_freq_MHz;
    input  integer vco_sel;
    logic [63:0] vco_band_val;
    logic [1:0] vco_post_div;
    integer vco_fbdiv_val;
    logic [31:0] wdata;
    logic [5:0] vco_fine_val;

    begin
        get_band_fbdiv_postdiv_hp_values (.vco_freq_MHz(vco_freq_MHz),.vco_sel(vco_sel),.vco_band_val(vco_band_val),.vco_post_div(vco_post_div),.vco_fbdiv_val(vco_fbdiv_val),.vco_fine_val(vco_fine_val));
        if(vco_sel==1) begin
            csr_read(DDR_PLL_OFFSET,`MVP_PLL_VCO1_BAND, wdata);
            wdata[`MVP_PLL_VCO1_BAND__VCO1_BAND_MUX]=1'b1;
            wdata[`MVP_PLL_VCO1_BAND__VCO1_BAND]=vco_band_val;
            wdata[`MVP_PLL_VCO1_BAND__VCO1_FINE]=vco_fine_val;
            csr_write(DDR_PLL_OFFSET,`MVP_PLL_VCO1_BAND, wdata);

            csr_read(DDR_PLL_OFFSET,`MVP_PLL_VCO1_CONTROL, wdata);
            wdata[`MVP_PLL_VCO1_CONTROL__VCO1_POST_DIV]=vco_post_div;
            csr_write(DDR_PLL_OFFSET,`MVP_PLL_VCO1_CONTROL, wdata);

            // `CSR_WRF1(PLL_OFFSET,DDR_CMN_VCO1_BAND_CFG0,VCO1_BAND,vco_band_val[31:0]);
            // `CSR_WRF1(PLL_OFFSET,DDR_CMN_VCO1_BAND_CFG1,VCO1_BAND,vco_band_val[63:32]);
            // `CSR_WRF1(PLL_OFFSET,DDR_CMN_VCO1_CFG,VCO1_POST_DIV,vco_post_div);
        end
        else if(vco_sel==2) begin
            csr_read(DDR_PLL_OFFSET,`MVP_PLL_VCO2_BAND, wdata);
            wdata[`MVP_PLL_VCO2_BAND__VCO2_BAND_MUX]=1'b1;
            wdata[`MVP_PLL_VCO2_BAND__VCO2_BAND]=vco_band_val;
            wdata[`MVP_PLL_VCO2_BAND__VCO2_FINE]=vco_fine_val;
            //wdata[`MVP_PLL_VCO2_BAND__VCO2_BAND]='d41;
            csr_write(DDR_PLL_OFFSET,`MVP_PLL_VCO2_BAND, wdata);

            csr_read(DDR_PLL_OFFSET,`MVP_PLL_VCO2_CONTROL, wdata);
            wdata[`MVP_PLL_VCO2_CONTROL__VCO2_POST_DIV]=vco_post_div;
            csr_write(DDR_PLL_OFFSET,`MVP_PLL_VCO2_CONTROL, wdata);

            //  `CSR_WRF1(PLL_OFFSET,DDR_CMN_VCO2_BAND_CFG0,VCO2_BAND,vco_band_val[31:0]);
            //  `CSR_WRF1(PLL_OFFSET,DDR_CMN_VCO2_BAND_CFG1,VCO2_BAND,vco_band_val[63:32]);
            //  `CSR_WRF1(PLL_OFFSET,DDR_CMN_VCO2_CFG,VCO2_POST_DIV,vco_post_div);
        end
        else begin
            $display ("Error:  VCO band select is incorrect, valid values are 1 or 2, received=%d", vco_sel);
        end
    end
endtask

task automatic set_fbdiv_vco_value;
    input  integer vco_freq_MHz;
    input  integer vco_sel;
    logic [63:0] vco_band_val;
    logic [1:0] vco_post_div;
    integer vco_fbdiv_val;
    logic [5:0] vco_fine_val;

    begin

        if(vco_sel==0) begin
            //vco_fbdiv_val=vco_freq_MHz/38.4;
            vco_fbdiv_val=vco_freq_MHz/19.2;

            csr_read(DDR_PLL_OFFSET,`MVP_PLL_ANALOG_EN_RESET, wdata);
            wdata[`MVP_PLL_ANALOG_EN_RESET__VCO_SEL]=vco_sel;
            wdata[`MVP_PLL_ANALOG_EN_RESET__VCO_SEL_MUX]=1'b1;
            wdata[`MVP_PLL_ANALOG_EN_RESET__FBDIV_SEL]=vco_fbdiv_val;
            wdata[`MVP_PLL_ANALOG_EN_RESET__FBDIV_SEL_MUX]=1'b1;
            csr_write(DDR_PLL_OFFSET,`MVP_PLL_ANALOG_EN_RESET, wdata);

            // `CSR_WRF1(PLL_OFFSET,DDR_CMN_CTRL0_CFG,VCO_SEL,vco_sel);
            // `CSR_WRF1(PLL_OFFSET,DDR_CMN_CTRL2_CFG,FBDIV_SEL,vco_fbdiv_val);
        end
        else begin
            get_band_fbdiv_postdiv_hp_values (.vco_freq_MHz(vco_freq_MHz),.vco_sel(vco_sel),.vco_band_val(vco_band_val),.vco_post_div(vco_post_div),.vco_fbdiv_val(vco_fbdiv_val),.vco_fine_val(vco_fine_val));

            csr_read(DDR_PLL_OFFSET,`MVP_PLL_ANALOG_EN_RESET, wdata);
            wdata[`MVP_PLL_ANALOG_EN_RESET__VCO_SEL]=vco_sel;
            wdata[`MVP_PLL_ANALOG_EN_RESET__VCO_SEL_MUX]=1'b1;
            wdata[`MVP_PLL_ANALOG_EN_RESET__FBDIV_SEL]=vco_fbdiv_val;
            wdata[`MVP_PLL_ANALOG_EN_RESET__FBDIV_SEL_MUX]=1'b1;
            csr_write(DDR_PLL_OFFSET,`MVP_PLL_ANALOG_EN_RESET, wdata);

            // `CSR_WRF1(PLL_OFFSET,DDR_CMN_CTRL0_CFG,VCO_SEL,vco_sel);
            // `CSR_WRF1(PLL_OFFSET,DDR_CMN_CTRL2_CFG,FBDIV_SEL,vco_fbdiv_val);

            if(vco_sel==1) begin
                csr_read(DDR_PLL_OFFSET,`MVP_PLL_VCO1_CONTROL, wdata);
                wdata[`MVP_PLL_VCO1_CONTROL__VCO1_POST_DIV]=vco_post_div;
                wdata[`MVP_PLL_VCO1_CONTROL__VCO1_ENA_MUX]=1'b1;
                csr_write(DDR_PLL_OFFSET,`MVP_PLL_VCO1_CONTROL, wdata);
                // `CSR_WRF1(PLL_OFFSET,DDR_CMN_VCO1_CFG,VCO1_POST_DIV,vco_post_div);
            end
            else if(vco_sel==2) begin
                csr_read(DDR_PLL_OFFSET,`MVP_PLL_VCO2_CONTROL, wdata);
                wdata[`MVP_PLL_VCO2_CONTROL__VCO2_POST_DIV]=vco_post_div;
                wdata[`MVP_PLL_VCO2_CONTROL__VCO2_ENA_MUX]=1'b1;
                csr_write(DDR_PLL_OFFSET,`MVP_PLL_VCO2_CONTROL, wdata);
                // `CSR_WRF1(PLL_OFFSET,DDR_CMN_VCO2_CFG,VCO2_POST_DIV,vco_post_div);
            end
            else begin
                $display ("Error:  VCO select is incorrect, valid values are 0, 1 or 2, received=%d", vco_sel);
            end
        end
    end
endtask

task automatic get_band_fbdiv_postdiv_lp_values;
    input  integer vco_freq_MHz;
    output integer vco_band_val;
    output integer vco_fbdiv_val;
    begin
        case(vco_freq_MHz)
            //150: begin vco_band_val = 'd4; vco_fbdiv_val=4; end
            //200: begin vco_band_val = 'd12; vco_fbdiv_val=5; end
            422: begin vco_band_val = 'd2; vco_fbdiv_val=40; end
            default: $display ("Error:  VCO LP freq select is incorrect, valid values are 422 received=%d", vco_freq_MHz);
        endcase
    end
endtask

task automatic set_band_vco_lp_value;
    input  integer vco_freq_MHz;
    integer vco_band_val;
    integer vco_fbdiv_val;
    logic [31:0] wdata;
    begin
        get_band_fbdiv_postdiv_lp_values (.vco_freq_MHz(vco_freq_MHz),.vco_band_val(vco_band_val),.vco_fbdiv_val(vco_fbdiv_val));

        csr_read(DDR_PLL_OFFSET,`MVP_PLL_VCO0_BAND, wdata);
        wdata[`MVP_PLL_VCO0_BAND__VCO0_BAND]=vco_band_val;
        //wdata[`MVP_PLL_VCO0_BAND__VCO0_BAND_MUX]=1'b0;
        csr_write(DDR_PLL_OFFSET,`MVP_PLL_VCO0_BAND, wdata);

        // `CSR_WRF1(PLL_OFFSET,DDR_CMN_VCO0_BAND_CFG0,VCO0_BAND,vco_band_val[31:0]);
        // `CSR_WRF1(PLL_OFFSET,DDR_CMN_VCO0_BAND_CFG1,VCO0_BAND,vco_band_val[63:32]);

    end
endtask
//
task automatic set_pll_init;
    logic [31:0] wdata;
    begin
        //
        //   // PLL performace registers
        //   // find out if these are for char or training  TODO
        csr_read(DDR_PLL_OFFSET,`MVP_PLL_INTR_PROP_GAINS_OVERRIDE, wdata);

        //wdata[`MVP_PLL_INTR_PROP_GAINS_OVERRIDE__IUP_PROP_MUX]=1'b1;
        //wdata[`MVP_PLL_INTR_PROP_GAINS_OVERRIDE__IDN_PROP_MUX]=1'b1;
        //wdata[`MVP_PLL_INTR_PROP_GAINS_OVERRIDE__IUP_INT_MUX]=1'b1;
        //wdata[`MVP_PLL_INTR_PROP_GAINS_OVERRIDE__IDN_INT_MUX]=1'b1;
        //wdata[`MVP_PLL_INTR_PROP_GAINS_OVERRIDE__IUP_PROP]='d20;
        //wdata[`MVP_PLL_INTR_PROP_GAINS_OVERRIDE__IDN_PROP]='d20;
        //wdata[`MVP_PLL_INTR_PROP_GAINS_OVERRIDE__IUP_INT]='d20;
        //wdata[`MVP_PLL_INTR_PROP_GAINS_OVERRIDE__IDN_INT]='d20;

        wdata[`MVP_PLL_INTR_PROP_GAINS_OVERRIDE__PROP_GAIN_MUX]=1'b1;
        wdata[`MVP_PLL_INTR_PROP_GAINS_OVERRIDE__INT_GAIN_MUX]=1'b1;
        wdata[`MVP_PLL_INTR_PROP_GAINS_OVERRIDE__PROP_GAIN]='d10;
        wdata[`MVP_PLL_INTR_PROP_GAINS_OVERRIDE__INT_GAIN]='d15;

        csr_write(DDR_PLL_OFFSET,`MVP_PLL_INTR_PROP_GAINS_OVERRIDE, wdata);

        csr_read(DDR_PLL_OFFSET,`MVP_PLL_PROP_CTRLS, wdata);
        wdata[`MVP_PLL_PROP_CTRLS__PROP_R_CTRL]='d2;
        wdata[`MVP_PLL_PROP_CTRLS__PROP_C_CTRL]='d2;
        csr_write(DDR_PLL_OFFSET,`MVP_PLL_PROP_CTRLS, wdata);

        csr_read(DDR_PLL_OFFSET,`MVP_PLL_MODE_DTST_MISC, wdata);
        wdata[`MVP_PLL_MODE_DTST_MISC__BIAS_LVL]='d8;
        csr_write(DDR_PLL_OFFSET,`MVP_PLL_MODE_DTST_MISC, wdata);

        csr_read(DDR_PLL_OFFSET,`MVP_PLL_VCO0_BAND, wdata);
        wdata[`MVP_PLL_VCO0_BAND__VCO0_FINE_MUX]=1'b1;
        wdata[`MVP_PLL_VCO0_BAND__VCO0_FINE]='d0;
        csr_write(DDR_PLL_OFFSET,`MVP_PLL_VCO0_BAND, wdata);
        csr_read(DDR_PLL_OFFSET,`MVP_PLL_VCO1_BAND, wdata);
        wdata[`MVP_PLL_VCO1_BAND__VCO1_FINE_MUX]=1'b1;
        wdata[`MVP_PLL_VCO1_BAND__VCO1_FINE]='d0;
        csr_write(DDR_PLL_OFFSET,`MVP_PLL_VCO1_BAND, wdata);
        csr_read(DDR_PLL_OFFSET,`MVP_PLL_VCO2_BAND, wdata);
        wdata[`MVP_PLL_VCO2_BAND__VCO2_FINE_MUX]=1'b1;
        wdata[`MVP_PLL_VCO2_BAND__VCO2_FINE]='d0;
        csr_write(DDR_PLL_OFFSET,`MVP_PLL_VCO2_BAND, wdata);
        //
        //         `CSR_WRF1(PLL_OFFSET,MVP_PLL_VCO0_INTR_PROP_GAINS,__VCO0_IDN_PROP,'d20);
        //         `CSR_WRF1(PLL_OFFSET,DDR_CMN_CTRL1_CFG,IUP_PROP,'d20);
        //         `CSR_WRF1(PLL_OFFSET,DDR_CMN_CTRL1_CFG,PROP_C_CTRL,'d2);
        //         `CSR_WRF1(PLL_OFFSET,DDR_CMN_CTRL1_CFG,PROP_R_CTRL,'d2);
        //         `CSR_WRF1(PLL_OFFSET,DDR_CMN_CTRL0_CFG,IDN_INT,'d20);
        //         `CSR_WRF1(PLL_OFFSET,DDR_CMN_CTRL0_CFG,IUP_INT,'d20);
        //         `CSR_WRF1(PLL_OFFSET,DDR_CMN_CTRL0_CFG,BIAS_LVL,'d8);
        //
    end
endtask

typedef enum bit[1:0]{
    MVP_VCO0 = 2'b00,
    MVP_VCO1 = 2'b01,
    MVP_VCO2 = 2'b10
} mvp_pll_vco_t;

task new_set_int_frac;
    input real ref_clk_MHz;
    input real vco_clk_MHz;
    input [1:0] vco_sel;
    logic [31:0] wdata;
    real comp_val;
    bit [8:0] integer_comp;
    bit [15:0] frac_comp;
    // real ssc_stepsize_real;
    // bit [9:0] ssc_stepsize;
    // bit [16:0] ssc_amp;
    // bit [6:0] prop_pa;
    // real ref_clk_Hz=19.2e6;
    begin

        comp_val = vco_clk_MHz / (ref_clk_MHz);
        integer_comp = $floor(comp_val);
        frac_comp = (comp_val - integer_comp) * (2**16);

        if(vco_sel==0) begin
            csr_read(DDR_PLL_OFFSET,`MVP_PLL_VCO0_INT_FRAC_SETTINGS, wdata);
            wdata[`MVP_PLL_VCO0_INT_FRAC_SETTINGS__VCO0_FRAC]=frac_comp;
            wdata[`MVP_PLL_VCO0_INT_FRAC_SETTINGS__VCO0_INT]=integer_comp;
            csr_write(DDR_PLL_OFFSET,`MVP_PLL_VCO0_INT_FRAC_SETTINGS, wdata);
        end
        else if(vco_sel==1) begin
            csr_read(DDR_PLL_OFFSET,`MVP_PLL_VCO1_INT_FRAC_SETTINGS, wdata);
            wdata[`MVP_PLL_VCO1_INT_FRAC_SETTINGS__VCO1_FRAC]=frac_comp;
            wdata[`MVP_PLL_VCO1_INT_FRAC_SETTINGS__VCO1_INT]=integer_comp;
            csr_write(DDR_PLL_OFFSET,`MVP_PLL_VCO1_INT_FRAC_SETTINGS, wdata);
        end
        else if(vco_sel==2) begin
            csr_read(DDR_PLL_OFFSET,`MVP_PLL_VCO2_INT_FRAC_SETTINGS, wdata);
            wdata[`MVP_PLL_VCO2_INT_FRAC_SETTINGS__VCO2_FRAC]=frac_comp;
            wdata[`MVP_PLL_VCO2_INT_FRAC_SETTINGS__VCO2_INT]=integer_comp;
            csr_write(DDR_PLL_OFFSET,`MVP_PLL_VCO2_INT_FRAC_SETTINGS, wdata);
        end
        else begin
            $display ("Error:  VCO select is incorrect, valid values are 0, 1 or 2, received=%d", vco_sel);
        end
        $display ("Info: PLL settings : VCO clk = %.1f ref clk = %.1f integer_comp = %x  frac_comp = %x",vco_clk_MHz, ref_clk_MHz,integer_comp, frac_comp );

    end
endtask

task automatic new_set_vco_band;
    input [5:0] band;
    input [5:0] fine;
    input integer vco_sel;
    logic [31:0] wdata;
    begin

        if(vco_sel==0) begin
            csr_read(DDR_PLL_OFFSET,`MVP_PLL_VCO0_BAND, wdata);
            wdata[`MVP_PLL_VCO0_BAND__VCO0_FINE_MUX]='b1;
            wdata[`MVP_PLL_VCO0_BAND__VCO0_FINE]=fine;
            wdata[`MVP_PLL_VCO0_BAND__VCO0_BAND_MUX]='b1;
            wdata[`MVP_PLL_VCO0_BAND__VCO0_BAND]=band;
            csr_write(DDR_PLL_OFFSET,`MVP_PLL_VCO0_BAND, wdata);
        end
        else if(vco_sel==1) begin
            csr_read(DDR_PLL_OFFSET,`MVP_PLL_VCO1_BAND, wdata);
            wdata[`MVP_PLL_VCO1_BAND__VCO1_FINE_MUX]='b1;
            wdata[`MVP_PLL_VCO1_BAND__VCO1_FINE]=fine;
            wdata[`MVP_PLL_VCO1_BAND__VCO1_BAND_MUX]='b1;
            wdata[`MVP_PLL_VCO1_BAND__VCO1_BAND]=band;
            csr_write(DDR_PLL_OFFSET,`MVP_PLL_VCO1_BAND, wdata);
        end
        else if(vco_sel==2) begin
            csr_read(DDR_PLL_OFFSET,`MVP_PLL_VCO2_BAND, wdata);
            wdata[`MVP_PLL_VCO2_BAND__VCO2_FINE_MUX]='b1;
            wdata[`MVP_PLL_VCO2_BAND__VCO2_FINE]=fine;
            wdata[`MVP_PLL_VCO2_BAND__VCO2_BAND_MUX]='b1;
            wdata[`MVP_PLL_VCO2_BAND__VCO2_BAND]=band;
            csr_write(DDR_PLL_OFFSET,`MVP_PLL_VCO2_BAND, wdata);
        end
        else begin
            $display ("Error:  VCO select is incorrect, valid values are 0, 1 or 2, received=%d", vco_sel);
        end

    end
endtask

task automatic new_set_vco_sel;
    input integer vco_sel;
    logic [31:0] wdata;
    begin

        csr_read(DDR_PLL_OFFSET,`MVP_PLL_CORE_OVERRIDES, wdata);
        wdata[`MVP_PLL_CORE_OVERRIDES__CORE_VCO_SEL_MUX]='b1;
        wdata[`MVP_PLL_CORE_OVERRIDES__CORE_VCO_SEL]=vco_sel;
        csr_write(DDR_PLL_OFFSET,`MVP_PLL_CORE_OVERRIDES, wdata);

    end
endtask

task automatic new_set_vco_prep;
    input real ref_clk_MHz;
    input real vco_clk_MHz;
    input integer vco_sel;
    input [5:0] band;
    input [5:0] fine;

    begin

        new_set_int_frac(.ref_clk_MHz(ref_clk_MHz),.vco_clk_MHz(vco_clk_MHz),.vco_sel(vco_sel));
        new_set_vco_band(.band(band),.fine(fine),.vco_sel(vco_sel));

        new_set_vco_sel(vco_sel);
    end
endtask

task automatic new_set_vco_switch;
    input logic en;
    logic [31:0] wdata;
    begin

        csr_read(DDR_PLL_OFFSET,`MVP_PLL_CORE_SWTICH_VCO_HW, wdata);
        wdata[`MVP_PLL_CORE_SWTICH_VCO_HW__CORE_SWITCH_VCO_HW_MUX]=en;
        wdata[`MVP_PLL_CORE_SWTICH_VCO_HW__CORE_SWITCH_VCO_HW]=en;
        csr_write(DDR_PLL_OFFSET,`MVP_PLL_CORE_SWTICH_VCO_HW, wdata);

    end

endtask

task automatic new_set_pll_init;
    logic [31:0] wdata;
    begin
        //new_set_int_frac(.vco_sel(MVP_VCO0), .freq(422*1e6));

        csr_read(DDR_PLL_OFFSET,`MVP_PLL_INTR_PROP_FL_GAINS, wdata);
        wdata[`MVP_PLL_INTR_PROP_FL_GAINS__FL_PROP_GAIN]='d10;
        wdata[`MVP_PLL_INTR_PROP_FL_GAINS__FL_INT_GAIN]='d15;
        csr_write(DDR_PLL_OFFSET,`MVP_PLL_INTR_PROP_FL_GAINS, wdata);

        csr_read(DDR_PLL_OFFSET,`MVP_PLL_LOCK_DET_SETTINGS, wdata);
        wdata[`MVP_PLL_LOCK_DET_SETTINGS__LD_RANGE]='h4;
        wdata[`MVP_PLL_LOCK_DET_SETTINGS__LD_REFCLK_CYCLES]='h200;
        csr_write(DDR_PLL_OFFSET,`MVP_PLL_LOCK_DET_SETTINGS, wdata);

        csr_read(DDR_PLL_OFFSET,`MVP_PLL_FASTLOCK_DET_SETTINGS, wdata);
        wdata[`MVP_PLL_FASTLOCK_DET_SETTINGS__FASTLD_RANGE]='h8;
        wdata[`MVP_PLL_FASTLOCK_DET_SETTINGS__FASTLD_REFCLK_CYCLES]='h100;
        csr_write(DDR_PLL_OFFSET,`MVP_PLL_FASTLOCK_DET_SETTINGS, wdata);

        csr_read(DDR_PLL_OFFSET,`MVP_PLL_VCO0_BAND, wdata);
        wdata[`MVP_PLL_VCO0_BAND__VCO0_BAND_MUX]=1'b1;
        wdata[`MVP_PLL_VCO0_BAND__VCO0_BAND]='d3;
        wdata[`MVP_PLL_VCO0_BAND__VCO0_FINE_MUX]=1'b1;
        wdata[`MVP_PLL_VCO0_BAND__VCO0_FINE]='d31;
        csr_write(DDR_PLL_OFFSET,`MVP_PLL_VCO0_BAND, wdata);

    end
endtask

task automatic new_poll_ready;
    output lock;
    logic [31:0] rdata;
    logic [31:0] wdata;
    begin
        csr_read(DDR_PLL_OFFSET,`MVP_PLL_CORE_STATUS, rdata);
        lock=rdata[0];   //CORE_READY

    end
endtask

task automatic new_cal_band_fll;
    input real ref_clk_MHz;
    input real vco_clk_MHz;
    input integer fll_refclk_count;
    input integer vco_sel;
    logic [31:0] wdata;
    real fll_vco_count_target;
    begin

        fll_vco_count_target = (fll_refclk_count*(1/ref_clk_MHz))/(2*(1/vco_clk_MHz));

        //csr_read(DDR_PLL_OFFSET,`MVP_PLL_VCO1_FLL_CONTROL2, wdata);
        //  wdata[`MVP_PLL_VCO1_FLL_CONTROL2__VCO1_FLL_REFCLK_COUNT]=fll_refclk_count;
        //  wdata[`MVP_PLL_VCO1_FLL_CONTROL2__VCO1_FLL_VCO_COUNT_TARGET]=fll_vco_count_target;
        //  wdata[`MVP_PLL_VCO1_FLL_CONTROL2__VCO1_FLL_RANGE]='d4;
        //csr_write(DDR_PLL_OFFSET,`MVP_PLL_VCO1_FLL_CONTROL2, wdata);

        //csr_read(DDR_PLL_OFFSET,`MVP_PLL_VCO1_FLL_CONTROL1, wdata);
        //  wdata[`MVP_PLL_VCO1_FLL_CONTROL1__VCO1_FLL_ENABLE]='b1;
        //csr_write(DDR_PLL_OFFSET,`MVP_PLL_VCO1_FLL_CONTROL1, wdata);

        if(vco_sel==0) begin
            csr_read(DDR_PLL_OFFSET,`MVP_PLL_VCO0_FLL_CONTROL2, wdata);
            wdata[`MVP_PLL_VCO0_FLL_CONTROL2__VCO0_FLL_REFCLK_COUNT]=fll_refclk_count;
            wdata[`MVP_PLL_VCO0_FLL_CONTROL2__VCO0_FLL_VCO_COUNT_TARGET]=fll_vco_count_target;
            wdata[`MVP_PLL_VCO0_FLL_CONTROL2__VCO0_FLL_RANGE]='d4;
            csr_write(DDR_PLL_OFFSET,`MVP_PLL_VCO0_FLL_CONTROL2, wdata);

            csr_read(DDR_PLL_OFFSET,`MVP_PLL_VCO0_FLL_CONTROL1, wdata);
            wdata[`MVP_PLL_VCO0_FLL_CONTROL1__VCO0_FLL_ENABLE]='b1;
            csr_write(DDR_PLL_OFFSET,`MVP_PLL_VCO0_FLL_CONTROL1, wdata);
        end
        else if(vco_sel==1) begin
            csr_read(DDR_PLL_OFFSET,`MVP_PLL_VCO1_FLL_CONTROL2, wdata);
            wdata[`MVP_PLL_VCO1_FLL_CONTROL2__VCO1_FLL_REFCLK_COUNT]=fll_refclk_count;
            wdata[`MVP_PLL_VCO1_FLL_CONTROL2__VCO1_FLL_VCO_COUNT_TARGET]=fll_vco_count_target;
            wdata[`MVP_PLL_VCO1_FLL_CONTROL2__VCO1_FLL_RANGE]='d4;
            csr_write(DDR_PLL_OFFSET,`MVP_PLL_VCO1_FLL_CONTROL2, wdata);

            csr_read(DDR_PLL_OFFSET,`MVP_PLL_VCO1_FLL_CONTROL1, wdata);
            wdata[`MVP_PLL_VCO1_FLL_CONTROL1__VCO1_FLL_ENABLE]='b1;
            csr_write(DDR_PLL_OFFSET,`MVP_PLL_VCO1_FLL_CONTROL1, wdata);
        end
        else if(vco_sel==2) begin
            csr_read(DDR_PLL_OFFSET,`MVP_PLL_VCO2_FLL_CONTROL2, wdata);
            wdata[`MVP_PLL_VCO2_FLL_CONTROL2__VCO2_FLL_REFCLK_COUNT]=fll_refclk_count;
            wdata[`MVP_PLL_VCO2_FLL_CONTROL2__VCO2_FLL_VCO_COUNT_TARGET]=fll_vco_count_target;
            wdata[`MVP_PLL_VCO2_FLL_CONTROL2__VCO2_FLL_RANGE]='d4;
            csr_write(DDR_PLL_OFFSET,`MVP_PLL_VCO2_FLL_CONTROL2, wdata);

            csr_read(DDR_PLL_OFFSET,`MVP_PLL_VCO2_FLL_CONTROL1, wdata);
            wdata[`MVP_PLL_VCO2_FLL_CONTROL1__VCO2_FLL_ENABLE]='b1;
            csr_write(DDR_PLL_OFFSET,`MVP_PLL_VCO2_FLL_CONTROL1, wdata);
        end
        else begin
            $display ("Error:  VCO select is incorrect, valid values are 1 or 2, received=%d", vco_sel);
        end

        //csr_read(DDR_PLL_OFFSET,`MVP_PLL_CORE_STATUS, rdata);
        //lock=rdata[0];   //CORE_READY

    end
endtask

task automatic new_read_band_fll_val;
    output logic [5:0] rdata_fine;
    output logic [5:0] rdata_band;
    logic [31:0] rdata;
    input integer vco_sel;
    begin
        if(vco_sel==0) begin
            csr_read(DDR_PLL_OFFSET,`MVP_PLL_VCO0_FLL_BAND_STATUS, rdata);
            rdata_fine=rdata[`MVP_PLL_VCO0_FLL_BAND_STATUS__VCO0_FINE_STATUS];
            rdata_band=rdata[`MVP_PLL_VCO0_FLL_BAND_STATUS__VCO0_BAND_STATUS];
        end
        else if(vco_sel==1) begin
            csr_read(DDR_PLL_OFFSET,`MVP_PLL_VCO1_FLL_BAND_STATUS, rdata);
            rdata_fine=rdata[`MVP_PLL_VCO1_FLL_BAND_STATUS__VCO1_FINE_STATUS];
            rdata_band=rdata[`MVP_PLL_VCO1_FLL_BAND_STATUS__VCO1_BAND_STATUS];
        end
        else if(vco_sel==2) begin
            csr_read(DDR_PLL_OFFSET,`MVP_PLL_VCO2_FLL_BAND_STATUS, rdata);
            rdata_fine=rdata[`MVP_PLL_VCO2_FLL_BAND_STATUS__VCO2_FINE_STATUS];
            rdata_band=rdata[`MVP_PLL_VCO2_FLL_BAND_STATUS__VCO2_BAND_STATUS];
        end
        else begin
            $display ("Error:  VCO select is incorrect, valid values are 1 or 2, received=%d", vco_sel);
        end

    end
endtask

task automatic set_pll_fast_run;
    //static logic [5:0] band_vco1_val='h1B;
    //static logic [5:0] fine_vco1_val='h01;
    //static logic [5:0] band_vco2_val='h06;
    //static logic [5:0] fine_vco2_val='h06;
    static logic [5:0] band_vco1_val='h1A;
    static logic [5:0] fine_vco1_val='h04;
    static logic [5:0] band_vco2_val='h04;
    static logic [5:0] fine_vco2_val='h1C;
    logic pll_core_ready;
    input  integer pll_vco1_freq_MHz;
    input  integer pll_vco2_freq_MHz;
    input  integer vco_sel;
    output int err;
    logic [1:0] unused_1;
    integer     unused_2;
    begin
        // igen enable
        set_ibias_en(1'b1);
        #10ns;
        set_ldo_en(1'b1);
        #10ns;
        // refgen
        set_refgen_en(1'b1);

        new_set_pll_init ( );
        reset_pll_core;

        // wait for VCO0 to lock (open loop= 200ns, closed loop=300us)
        wait_time_pll_lock();

        // check PLL core ready after VCO0 lock
        new_poll_ready(pll_core_ready);
        //$display("PLL CORE READY=%b", pll_core_ready);
        if(pll_core_ready!==1'b1) begin
            err=err+1;
            $display("ERROR: pll_sanity_open pll_core_ready !== 1");
        end

        //aquire the band values for particular frequencies
        `ifdef MVP_PLL_NO_FLL
        `else
            new_cal_band_fll(.ref_clk_MHz(REFCLK_FREQ),.vco_clk_MHz(pll_vco1_freq_MHz),.fll_refclk_count(128),.vco_sel(1));
            new_cal_band_fll(.ref_clk_MHz(REFCLK_FREQ),.vco_clk_MHz(pll_vco2_freq_MHz),.fll_refclk_count(128),.vco_sel(2));

            //#200us;
            #500us;
            // set bands for VCO1 and VCO2 after FLL calibration
            new_read_band_fll_val(.rdata_band(band_vco1_val),.rdata_fine(fine_vco1_val),.vco_sel(1));
            $display("INFO: VCO1 BAND VAL=%h, FINE VAL=%h at %t", band_vco1_val, fine_vco1_val,$realtime);
            new_read_band_fll_val(.rdata_band(band_vco2_val),.rdata_fine(fine_vco2_val),.vco_sel(2));
            $display("INFO: VCO2 BAND VAL=%h, FINE VAL=%h at %t", band_vco2_val, fine_vco2_val,$realtime);
        `endif
        `ifdef MVP_PLL_NO_FLL
            get_band_fbdiv_postdiv_hp_values (.vco_freq_MHz(pll_vco1_freq_MHz),.vco_sel(0),.vco_band_val(band_vco1_val),.vco_post_div(unused_1),.vco_fbdiv_val(unused_2),.vco_fine_val(fine_vco1_val));
            get_band_fbdiv_postdiv_hp_values (.vco_freq_MHz(pll_vco2_freq_MHz),.vco_sel(0),.vco_band_val(band_vco2_val),.vco_post_div(unused_1),.vco_fbdiv_val(unused_2),.vco_fine_val(fine_vco2_val));
        `endif

        //set band values to VCOs (determined from FLL run)
        new_set_vco_prep(.ref_clk_MHz(REFCLK_FREQ),.vco_clk_MHz(pll_vco1_freq_MHz),.vco_sel(1),.band(band_vco1_val),.fine(fine_vco1_val));
        new_set_vco_prep(.ref_clk_MHz(REFCLK_FREQ),.vco_clk_MHz(pll_vco2_freq_MHz),.vco_sel(2),.band(band_vco2_val),.fine(fine_vco2_val));
        //new_set_vco_prep(.ref_clk_MHz(REFCLK_FREQ),.vco_clk_MHz(2112),.vco_sel(1),.band('h2B),.fine('h1A));
        //new_set_vco_prep(.ref_clk_MHz(REFCLK_FREQ),.vco_clk_MHz(1075),.vco_sel(2),.band('h0C),.fine('h00));

        new_set_vco_sel(.vco_sel(vco_sel));

        // switch feedback to VCO2
        new_set_vco_switch(.en(1'b1));
        // enable  VCO1 (and VCO2, already enabled with set_vco_switch)
        set_vcos_en(1'b1);
        #200ns;
        new_set_vco_switch(.en(1'b0));

    end
endtask

task automatic wait_time_pll_lock;
    bit force_pll;
    begin
        force_pll=0;
        if ($test$plusargs("MVP_FORCE_PLL"))
            force_pll = 1;

        if(force_pll)
            #2us;
        else
            #300us;
    end
endtask

task automatic set_refgen_en;
    input logic en;
    logic [8:0] ctrl_field=9'hFA;
    begin
        `CSR_WRF1(DDR_CMN_OFFSET,DDR_CMN_VREF_M0_CFG,EN,en);
        `CSR_WRF1(DDR_CMN_OFFSET,DDR_CMN_VREF_M0_CFG,CTRL,ctrl_field);
        `CSR_WRF1(DDR_CMN_OFFSET,DDR_CMN_VREF_M1_CFG,EN,en);
        `CSR_WRF1(DDR_CMN_OFFSET,DDR_CMN_VREF_M1_CFG,CTRL,ctrl_field);
    end
endtask

task automatic set_ibias_en;
    input logic en;
    begin
        `CSR_WRF1(DDR_CMN_OFFSET,DDR_CMN_IBIAS_CFG,EN,en);
    end
endtask

task automatic set_ldo_en;
    input logic en;
    begin
        `CSR_WRF1(DDR_CMN_OFFSET,DDR_CMN_LDO_M0_CFG,EN,en);
        `CSR_WRF1(DDR_CMN_OFFSET,DDR_CMN_LDO_M1_CFG,EN,en);
    end
endtask

//ZQCAL tasks
task automatic set_zqcal_en;
    input logic en;
    begin
        `CSR_WRF1(DDR_CMN_OFFSET,DDR_CMN_ZQCAL_CFG,CAL_EN,en);
    end
endtask

task automatic set_zqcal_pd_sel;
    input logic en;
    begin
        `CSR_WRF1(DDR_CMN_OFFSET,DDR_CMN_ZQCAL_CFG,PD_SEL,en);
    end
endtask

task automatic set_zqcal_ncal_code;
    input logic [4:0] value;
    begin
        `CSR_WRF1(DDR_CMN_OFFSET,DDR_CMN_ZQCAL_CFG,NCAL,value);
    end
endtask

task automatic set_zqcal_pcal_code;
    input logic [5:0] value;
    begin
        `CSR_WRF1(DDR_CMN_OFFSET,DDR_CMN_ZQCAL_CFG,PCAL,value);
    end
endtask

task automatic set_zqcal_voh0p6_sel;
    input logic en;
    begin
        `CSR_WRF1(DDR_CMN_OFFSET,DDR_CMN_ZQCAL_CFG,VOL_0P6_SEL,en);
    end
endtask

task automatic read_zqcal_comp_val;
    output logic val;
    begin
        `CSR_RDF1(DDR_CMN_OFFSET,DDR_CMN_ZQCAL_STA,COMP, val);
    end
endtask

//CLK CTRL
task automatic set_gfcm_en;
    input logic en;
    begin
        `CSR_WRF1(DDR_CMN_OFFSET,DDR_CMN_CLK_CTRL_CFG,GFCM_EN,en);
    end
endtask

task automatic set_pll0_div_clk_rst;
    input logic rst;
    begin
        `CSR_WRF1(DDR_CMN_OFFSET,DDR_CMN_CLK_CTRL_CFG,PLL0_DIV_CLK_RST,rst);
    end
endtask
task automatic set_pll0_div_clk_en;
    input logic en;
    begin
        `CSR_WRF1(DDR_CMN_OFFSET,DDR_CMN_CLK_CTRL_CFG,PLL0_DIV_CLK_EN,en);
    end
endtask
task automatic set_pmon_ana_nand_en;
    input logic en;
    begin
        `CSR_WRF1(DDR_CMN_OFFSET,DDR_CMN_PMON_ANA_CFG,NAND_EN,en);
    end
endtask
task automatic set_pmon_ana_nor_en;
    input logic en;
    begin
        `CSR_WRF1(DDR_CMN_OFFSET,DDR_CMN_PMON_ANA_CFG,NOR_EN,en);
    end
endtask
task automatic rst_pmon_dig;
    input logic en;
    begin
        `CSR_WRF1(DDR_CMN_OFFSET,DDR_CMN_PMON_DIG_CFG,REFCLK_RST,en);
    end
endtask
task automatic set_pmon_dig_nand_en;
    input logic en;
    begin
        `CSR_WRF1(DDR_CMN_OFFSET,DDR_CMN_PMON_DIG_NAND_CFG,COUNT_EN,en);
    end
endtask
task automatic set_pmon_dig_nor_en;
    input logic en;
    begin
        `CSR_WRF1(DDR_CMN_OFFSET,DDR_CMN_PMON_DIG_NOR_CFG,COUNT_EN,en);
    end
endtask
task automatic set_pmon_dig_init;
    begin
        `CSR_WRF1(DDR_CMN_OFFSET,DDR_CMN_PMON_DIG_NAND_CFG,REFCOUNT,'h00FF);
        `CSR_WRF1(DDR_CMN_OFFSET,DDR_CMN_PMON_DIG_NOR_CFG,REFCOUNT,'h00FF);
    end
endtask
task automatic read_pmon_dig_nand_done;
    output logic val;
    begin
        `CSR_RDF1(DDR_CMN_OFFSET,DDR_CMN_PMON_NAND_STA,DONE, val);
    end
endtask
task automatic read_pmon_dig_nand_val;
    output logic [23:0] val;
    begin
        `CSR_RDF1(DDR_CMN_OFFSET,DDR_CMN_PMON_NAND_STA,COUNT, val);
    end
endtask
task automatic read_pmon_dig_nor_done;
    output logic val;
    begin
        `CSR_RDF1(DDR_CMN_OFFSET,DDR_CMN_PMON_NOR_STA,DONE, val);
    end
endtask
task automatic read_pmon_dig_nor_val;
    output logic [23:0] val;
    begin
        `CSR_RDF1(DDR_CMN_OFFSET,DDR_CMN_PMON_NOR_STA,COUNT, val);
    end
endtask
task automatic set_ldo_vref_ctrl_val;
    input logic [7:0] val;
    begin
        `CSR_WRF1(DDR_CMN_OFFSET,DDR_CMN_LDO_M0_CFG,VREF_CTRL, val);
    end
endtask

//   task automatic measure_freq;
//      input logic i_signal;
//      output real o_period_sig;
//      integer x;
//      real posedge_sig = 0.0;
//      real posedge_sig_pre = 0.0;
//      begin
//       fork : f
//         begin
//            for(x=0;x<10;x=x+1) begin
//               //$display("X=%d",x);
//            //forever begin
//               @(posedge i_signal)
//               posedge_sig = $realtime;
//               o_period_sig = posedge_sig - posedge_sig_pre;
//               posedge_sig_pre = posedge_sig;
//            end
//            disable f;
//         end
//         begin
//            #100ns;
//            disable f;
//         end
//       join
////      $display("VCO0 period = %f", o_period_sig);
//      end
//   endtask

//-----------------------------------------------------------------------
// CMN/PLL APIs - End
//-----------------------------------------------------------------------

//-----------------------------------------------------------------------
// CSP APIs - End
//-----------------------------------------------------------------------

task sw_phy_clk_en;
    input logic en;
    begin
        `CSR_WRF1(DDR_FSW_OFFSET, DDR_FSW_CSP_1_CFG, CLK_DISABLE_OVR_VAL, ~en );
    end
endtask

task set_csp_cgc_sw_en;
    input logic ovr;
    input logic ovr_val;
    begin
        `CSR_WRF2(DDR_FSW_OFFSET, DDR_FSW_CSP_1_CFG, CGC_EN_OVR, CGC_EN_OVR_VAL, ovr, ovr_val );
    end
endtask

task sw_csp_byte_sync;
    logic val;
    begin
        `CSR_WRF2(DDR_FSW_OFFSET, DDR_FSW_CSP_1_CFG, REQ_OVR, REQ_OVR_VAL, 1'b1, 1'b1 );
        wait_hclk  (3);
        do begin
            `CSR_RDF1(DDR_FSW_OFFSET,DDR_FSW_CSP_STA,REQ_COMPLETE, val);
        end while (val != 1'b1 );
        `CSR_WRF2(DDR_FSW_OFFSET, DDR_FSW_CSP_1_CFG, REQ_OVR, REQ_OVR_VAL, 1'b1, 1'b0 );
        `CSR_WRF2(DDR_FSW_OFFSET, DDR_FSW_CSP_1_CFG, REQ_OVR, REQ_OVR_VAL, 1'b0, 1'b0 );
    end
endtask

//-----------------------------------------------------------------------
// CSP APIs - End
//-----------------------------------------------------------------------
///-----------------------------------------------------------------------
// CTRL APIs - Begin
//-----------------------------------------------------------------------
task set_mcu_clk_sel;
    input logic  sel;
    begin
        `CSR_WRF1(DDR_CTRL_OFFSET, DDR_CTRL_CLK_CFG, MCU_GFM_SEL, sel );
    end
endtask

task set_vco0_pll_clk_en;
    input logic en;
    begin
        `CSR_WRF1(DDR_CTRL_OFFSET, DDR_CTRL_CLK_CFG, PLL_CLK_EN, en );
    end
endtask

///-----------------------------------------------------------------------
// CTRL APIs - Begin
//-----------------------------------------------------------------------

///-----------------------------------------------------------------------
// MCU APIs - Begin
//-----------------------------------------------------------------------
task automatic set_mcu_en;
    input logic         fetch_en;
    input logic         debug_en;
    begin
        `CSR_WRF2(DDR_MCUTOP_OFFSET,WAV_MCUTOP_CFG, DEBUG_EN, FETCH_EN, debug_en, fetch_en);
    end
endtask

//task check_mcu_exec_status ;
//   output logic err;
//   logic [31:0] data;
//   string str;
//begin
//
//   wait (`MCU_GP_REG_HIER.mcu_gp3_cfg_q[0] == 1'b1);
//   if (`MCU_GP_REG_HIER.mcu_gp3_cfg_q[31:16] == 16'h0) begin
//       $display ("INFO: MCU Program Execution Completed Succefully.\n" );
//   end
//   else begin
//       $display ("ERROR: MCU Program Execution Completed with an Error code. The 2byte error code = %x ", `MCU_GP_REG_HIER.ctrl_mcu_gp3_cfg_q[31:16] );
//       err = 1'b1 ;
//   end
//end
//endtask
//-----------------------------------------------------------------------
// MCU APIs - End
//-----------------------------------------------------------------------

//-----------------------------------------------------------------------
// DQ DP APIs - Begin
//-----------------------------------------------------------------------

task automatic set_fifo_clr;
    begin
        `CSR_WRF1(DDR_CH0_DQ0_OFFSET,DDR_DQ_TOP_CFG,FIFO_CLR,1'b1);
        `CSR_WRF1(DDR_CH0_DQ1_OFFSET,DDR_DQ_TOP_CFG,FIFO_CLR,1'b1);
        `CSR_WRF1(DDR_CH0_CA_OFFSET ,DDR_CA_TOP_CFG,FIFO_CLR,1'b1);
        `CSR_WRF1(DDR_CH0_DQ0_OFFSET,DDR_DQ_TOP_CFG,FIFO_CLR,1'b0);
        `CSR_WRF1(DDR_CH0_DQ1_OFFSET,DDR_DQ_TOP_CFG,FIFO_CLR,1'b0);
        `CSR_WRF1(DDR_CH0_CA_OFFSET ,DDR_CA_TOP_CFG,FIFO_CLR,1'b0);
        `CSR_WRF1(DDR_CH1_DQ0_OFFSET,DDR_DQ_TOP_CFG,FIFO_CLR,1'b1);
        `CSR_WRF1(DDR_CH1_DQ1_OFFSET,DDR_DQ_TOP_CFG,FIFO_CLR,1'b1);
        `CSR_WRF1(DDR_CH1_CA_OFFSET ,DDR_CA_TOP_CFG,FIFO_CLR,1'b1);
        `CSR_WRF1(DDR_CH1_DQ0_OFFSET,DDR_DQ_TOP_CFG,FIFO_CLR,1'b0);
        `CSR_WRF1(DDR_CH1_DQ1_OFFSET,DDR_DQ_TOP_CFG,FIFO_CLR,1'b0);
        `CSR_WRF1(DDR_CH1_CA_OFFSET ,DDR_CA_TOP_CFG,FIFO_CLR,1'b0);
    end
endtask

task automatic set_rx_gb;
    input byte_sel_t    byte_sel;
    input dgb_t         rgb_mode;
    input fgb_t         fgb_mode;
    input logic         wck_mode;
    begin
        if((byte_sel == DQ0) || (byte_sel == DQ_ALL) || (byte_sel == ALL)) begin
            `CSR_WRF3(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_RX_M0_CFG,RGB_MODE,FGB_MODE,WCK_MODE,rgb_mode,fgb_mode,wck_mode);
            `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_RX_M0_CFG,RGB_MODE,FGB_MODE,rgb_mode,fgb_mode);
            `CSR_WRF3(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_RX_M0_CFG,RGB_MODE,FGB_MODE,WCK_MODE,rgb_mode,fgb_mode,wck_mode);
            `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_RX_M0_CFG,RGB_MODE,FGB_MODE,rgb_mode,fgb_mode);
        end
        if((byte_sel == DQ1) || (byte_sel == DQ_ALL) || (byte_sel == ALL)) begin
            `CSR_WRF3(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_RX_M0_CFG,RGB_MODE,FGB_MODE,WCK_MODE,rgb_mode,fgb_mode,wck_mode);
            `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_RX_M0_CFG,RGB_MODE,FGB_MODE,rgb_mode,fgb_mode);
            `CSR_WRF3(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_RX_M0_CFG,RGB_MODE,FGB_MODE,WCK_MODE,rgb_mode,fgb_mode,wck_mode);
            `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_RX_M0_CFG,RGB_MODE,FGB_MODE,rgb_mode,fgb_mode);
        end
        if((byte_sel == CA) || (byte_sel == ALL)) begin
            `CSR_WRF3(DDR_CH0_CA_OFFSET,DDR_CA_DQS_RX_M0_CFG,RGB_MODE,FGB_MODE,WCK_MODE,rgb_mode,fgb_mode,wck_mode);
            `CSR_WRF2(DDR_CH0_CA_OFFSET,DDR_CA_DQ_RX_M0_CFG,RGB_MODE,FGB_MODE,rgb_mode,fgb_mode);
            `CSR_WRF3(DDR_CH1_CA_OFFSET,DDR_CA_DQS_RX_M0_CFG,RGB_MODE,FGB_MODE,WCK_MODE,rgb_mode,fgb_mode,wck_mode);
            `CSR_WRF2(DDR_CH1_CA_OFFSET,DDR_CA_DQ_RX_M0_CFG,RGB_MODE,FGB_MODE,rgb_mode,fgb_mode);
        end
    end
endtask

task automatic set_tx_gb;
    input byte_sel_t   byte_sel;
    input dgb_t        tgb_mode;
    input wgb_t        wgb_mode;
    begin
        if((byte_sel == DQ0) || (byte_sel == DQ_ALL) || (byte_sel == ALL)) begin
            `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_M0_CFG,TGB_MODE,WGB_MODE, tgb_mode, wgb_mode);
            `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_M0_CFG,TGB_MODE,WGB_MODE, tgb_mode, wgb_mode);
        end
        if((byte_sel == DQ1) || (byte_sel == DQ_ALL) || (byte_sel == ALL)) begin
            `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_M0_CFG,TGB_MODE,WGB_MODE, tgb_mode, wgb_mode);
            `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_M0_CFG,TGB_MODE,WGB_MODE, tgb_mode, wgb_mode);
        end
        if((byte_sel == CA)  || (byte_sel == ALL)) begin
            `CSR_WRF2(DDR_CH0_CA_OFFSET,DDR_CA_DQS_TX_M0_CFG,TGB_MODE,WGB_MODE, tgb_mode, wgb_mode);
            `CSR_WRF2(DDR_CH1_CA_OFFSET,DDR_CA_DQS_TX_M0_CFG,TGB_MODE,WGB_MODE, tgb_mode, wgb_mode);
        end
    end
endtask

task automatic set_dqs_egress_mode;
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
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_EGRESS_ANA_M0_CFG_0, ana_mode);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_EGRESS_DIG_M0_CFG_0, dig_mode);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_EGRESS_ANA_M0_CFG_0, ana_mode);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_EGRESS_DIG_M0_CFG_0, dig_mode);
                end
                {8'd1} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_EGRESS_ANA_M0_CFG_1, ana_mode);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_EGRESS_DIG_M0_CFG_1, dig_mode);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_EGRESS_ANA_M0_CFG_1, ana_mode);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_EGRESS_DIG_M0_CFG_1, dig_mode);
                end
                {8'd2} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_EGRESS_ANA_M0_CFG_2, ana_mode);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_EGRESS_DIG_M0_CFG_2, dig_mode);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_EGRESS_ANA_M0_CFG_2, ana_mode);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_EGRESS_DIG_M0_CFG_2, dig_mode);
                end
                {8'd3} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_EGRESS_ANA_M0_CFG_3, ana_mode);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_EGRESS_DIG_M0_CFG_3, dig_mode);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_EGRESS_ANA_M0_CFG_3, ana_mode);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_EGRESS_DIG_M0_CFG_3, dig_mode);
                end
                {8'd4} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_EGRESS_ANA_M0_CFG_4, ana_mode);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_EGRESS_DIG_M0_CFG_4, dig_mode);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_EGRESS_ANA_M0_CFG_4, ana_mode);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_EGRESS_DIG_M0_CFG_4, dig_mode);
                end
                {8'd5} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_EGRESS_ANA_M0_CFG_5, ana_mode);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_EGRESS_DIG_M0_CFG_5, dig_mode);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_EGRESS_ANA_M0_CFG_5, ana_mode);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_EGRESS_DIG_M0_CFG_5, dig_mode);
                end
                {8'd6} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_EGRESS_ANA_M0_CFG_6, ana_mode);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_EGRESS_DIG_M0_CFG_6, dig_mode);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_EGRESS_ANA_M0_CFG_6, ana_mode);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_EGRESS_DIG_M0_CFG_6, dig_mode);
                end
                {8'd7} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_EGRESS_ANA_M0_CFG_7, ana_mode);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_EGRESS_DIG_M0_CFG_7, dig_mode);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_EGRESS_ANA_M0_CFG_7, ana_mode);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_EGRESS_DIG_M0_CFG_7, dig_mode);
                end
                {8'd8} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_EGRESS_ANA_M0_CFG_8, ana_mode);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_EGRESS_DIG_M0_CFG_8, dig_mode);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_EGRESS_ANA_M0_CFG_8, ana_mode);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_EGRESS_DIG_M0_CFG_8, dig_mode);
                end
                default : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_EGRESS_ANA_M0_CFG_0, ana_mode);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_EGRESS_DIG_M0_CFG_0, dig_mode);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_EGRESS_ANA_M0_CFG_1, ana_mode);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_EGRESS_DIG_M0_CFG_1, dig_mode);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_EGRESS_ANA_M0_CFG_2, ana_mode);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_EGRESS_DIG_M0_CFG_2, dig_mode);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_EGRESS_ANA_M0_CFG_3, ana_mode);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_EGRESS_DIG_M0_CFG_3, dig_mode);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_EGRESS_ANA_M0_CFG_4, ana_mode);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_EGRESS_DIG_M0_CFG_4, dig_mode);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_EGRESS_ANA_M0_CFG_5, ana_mode);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_EGRESS_DIG_M0_CFG_5, dig_mode);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_EGRESS_ANA_M0_CFG_6, ana_mode);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_EGRESS_DIG_M0_CFG_6, dig_mode);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_EGRESS_ANA_M0_CFG_7, ana_mode);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_EGRESS_DIG_M0_CFG_7, dig_mode);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_EGRESS_ANA_M0_CFG_8, ana_mode);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_EGRESS_DIG_M0_CFG_8, dig_mode);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_EGRESS_ANA_M0_CFG_0, ana_mode);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_EGRESS_DIG_M0_CFG_0, dig_mode);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_EGRESS_ANA_M0_CFG_1, ana_mode);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_EGRESS_DIG_M0_CFG_1, dig_mode);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_EGRESS_ANA_M0_CFG_2, ana_mode);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_EGRESS_DIG_M0_CFG_2, dig_mode);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_EGRESS_ANA_M0_CFG_3, ana_mode);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_EGRESS_DIG_M0_CFG_3, dig_mode);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_EGRESS_ANA_M0_CFG_4, ana_mode);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_EGRESS_DIG_M0_CFG_4, dig_mode);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_EGRESS_ANA_M0_CFG_5, ana_mode);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_EGRESS_DIG_M0_CFG_5, dig_mode);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_EGRESS_ANA_M0_CFG_6, ana_mode);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_EGRESS_DIG_M0_CFG_6, dig_mode);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_EGRESS_ANA_M0_CFG_7, ana_mode);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_EGRESS_DIG_M0_CFG_7, dig_mode);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_EGRESS_ANA_M0_CFG_8, ana_mode);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_EGRESS_DIG_M0_CFG_8, dig_mode);
                end
            endcase
        end
        if((byte_sel == DQ1 ) || (byte_sel == DQ_ALL) || (byte_sel == ALL)) begin
            case(dqs)
                {8'd0} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_EGRESS_ANA_M0_CFG_0, ana_mode);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_EGRESS_DIG_M0_CFG_0, dig_mode);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_EGRESS_ANA_M0_CFG_0, ana_mode);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_EGRESS_DIG_M0_CFG_0, dig_mode);
                end
                {8'd1} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_EGRESS_ANA_M0_CFG_1, ana_mode);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_EGRESS_DIG_M0_CFG_1, dig_mode);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_EGRESS_ANA_M0_CFG_1, ana_mode);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_EGRESS_DIG_M0_CFG_1, dig_mode);
                end
                {8'd2} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_EGRESS_ANA_M0_CFG_2, ana_mode);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_EGRESS_DIG_M0_CFG_2, dig_mode);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_EGRESS_ANA_M0_CFG_2, ana_mode);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_EGRESS_DIG_M0_CFG_2, dig_mode);
                end
                {8'd3} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_EGRESS_ANA_M0_CFG_3, ana_mode);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_EGRESS_DIG_M0_CFG_3, dig_mode);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_EGRESS_ANA_M0_CFG_3, ana_mode);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_EGRESS_DIG_M0_CFG_3, dig_mode);
                end
                {8'd4} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_EGRESS_ANA_M0_CFG_4, ana_mode);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_EGRESS_DIG_M0_CFG_4, dig_mode);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_EGRESS_ANA_M0_CFG_4, ana_mode);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_EGRESS_DIG_M0_CFG_4, dig_mode);
                end
                {8'd5} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_EGRESS_ANA_M0_CFG_5, ana_mode);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_EGRESS_DIG_M0_CFG_5, dig_mode);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_EGRESS_ANA_M0_CFG_5, ana_mode);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_EGRESS_DIG_M0_CFG_5, dig_mode);
                end
                {8'd6} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_EGRESS_ANA_M0_CFG_6, ana_mode);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_EGRESS_DIG_M0_CFG_6, dig_mode);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_EGRESS_ANA_M0_CFG_6, ana_mode);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_EGRESS_DIG_M0_CFG_6, dig_mode);
                end
                {8'd7} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_EGRESS_ANA_M0_CFG_7, ana_mode);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_EGRESS_DIG_M0_CFG_7, dig_mode);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_EGRESS_ANA_M0_CFG_7, ana_mode);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_EGRESS_DIG_M0_CFG_7, dig_mode);
                end
                {8'd8} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_EGRESS_ANA_M0_CFG_8, ana_mode);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_EGRESS_DIG_M0_CFG_8, dig_mode);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_EGRESS_ANA_M0_CFG_8, ana_mode);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_EGRESS_DIG_M0_CFG_8, dig_mode);
                end
                default : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_EGRESS_ANA_M0_CFG_0, ana_mode);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_EGRESS_DIG_M0_CFG_0, dig_mode);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_EGRESS_ANA_M0_CFG_1, ana_mode);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_EGRESS_DIG_M0_CFG_1, dig_mode);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_EGRESS_ANA_M0_CFG_2, ana_mode);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_EGRESS_DIG_M0_CFG_2, dig_mode);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_EGRESS_ANA_M0_CFG_3, ana_mode);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_EGRESS_DIG_M0_CFG_3, dig_mode);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_EGRESS_ANA_M0_CFG_4, ana_mode);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_EGRESS_DIG_M0_CFG_4, dig_mode);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_EGRESS_ANA_M0_CFG_5, ana_mode);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_EGRESS_DIG_M0_CFG_5, dig_mode);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_EGRESS_ANA_M0_CFG_6, ana_mode);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_EGRESS_DIG_M0_CFG_6, dig_mode);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_EGRESS_ANA_M0_CFG_7, ana_mode);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_EGRESS_DIG_M0_CFG_7, dig_mode);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_EGRESS_ANA_M0_CFG_8, ana_mode);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_EGRESS_DIG_M0_CFG_8, dig_mode);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_EGRESS_ANA_M0_CFG_0, ana_mode);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_EGRESS_DIG_M0_CFG_0, dig_mode);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_EGRESS_ANA_M0_CFG_1, ana_mode);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_EGRESS_DIG_M0_CFG_1, dig_mode);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_EGRESS_ANA_M0_CFG_2, ana_mode);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_EGRESS_DIG_M0_CFG_2, dig_mode);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_EGRESS_ANA_M0_CFG_3, ana_mode);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_EGRESS_DIG_M0_CFG_3, dig_mode);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_EGRESS_ANA_M0_CFG_4, ana_mode);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_EGRESS_DIG_M0_CFG_4, dig_mode);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_EGRESS_ANA_M0_CFG_5, ana_mode);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_EGRESS_DIG_M0_CFG_5, dig_mode);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_EGRESS_ANA_M0_CFG_6, ana_mode);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_EGRESS_DIG_M0_CFG_6, dig_mode);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_EGRESS_ANA_M0_CFG_7, ana_mode);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_EGRESS_DIG_M0_CFG_7, dig_mode);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_EGRESS_ANA_M0_CFG_8, ana_mode);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_EGRESS_DIG_M0_CFG_8, dig_mode);
                end
            endcase
        end
        if((byte_sel == CA) || (byte_sel == ALL)) begin
            case(dqs)
                {8'd0} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQS_TX_EGRESS_ANA_M0_CFG_0, ana_mode);
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQS_TX_EGRESS_DIG_M0_CFG_0, dig_mode);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQS_TX_EGRESS_ANA_M0_CFG_0, ana_mode);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQS_TX_EGRESS_DIG_M0_CFG_0, dig_mode);
                end
                default : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQS_TX_EGRESS_ANA_M0_CFG_0, ana_mode);
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQS_TX_EGRESS_DIG_M0_CFG_0, dig_mode);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQS_TX_EGRESS_ANA_M0_CFG_0, ana_mode);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQS_TX_EGRESS_DIG_M0_CFG_0, dig_mode);
                end
            endcase
        end
    end
endtask

task automatic set_dq_egress_mode;
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
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_EGRESS_ANA_M0_CFG_0, ana_mode);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_EGRESS_DIG_M0_CFG_0, dig_mode);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_EGRESS_ANA_M0_CFG_0, ana_mode);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_EGRESS_DIG_M0_CFG_0, dig_mode);
                end
                {8'd1} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_EGRESS_ANA_M0_CFG_1, ana_mode);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_EGRESS_DIG_M0_CFG_1, dig_mode);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_EGRESS_ANA_M0_CFG_1, ana_mode);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_EGRESS_DIG_M0_CFG_1, dig_mode);
                end
                {8'd2} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_EGRESS_ANA_M0_CFG_2, ana_mode);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_EGRESS_DIG_M0_CFG_2, dig_mode);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_EGRESS_ANA_M0_CFG_2, ana_mode);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_EGRESS_DIG_M0_CFG_2, dig_mode);
                end
                {8'd3} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_EGRESS_ANA_M0_CFG_3, ana_mode);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_EGRESS_DIG_M0_CFG_3, dig_mode);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_EGRESS_ANA_M0_CFG_3, ana_mode);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_EGRESS_DIG_M0_CFG_3, dig_mode);
                end
                {8'd4} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_EGRESS_ANA_M0_CFG_4, ana_mode);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_EGRESS_DIG_M0_CFG_4, dig_mode);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_EGRESS_ANA_M0_CFG_4, ana_mode);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_EGRESS_DIG_M0_CFG_4, dig_mode);
                end
                {8'd5} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_EGRESS_ANA_M0_CFG_5, ana_mode);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_EGRESS_DIG_M0_CFG_5, dig_mode);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_EGRESS_ANA_M0_CFG_5, ana_mode);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_EGRESS_DIG_M0_CFG_5, dig_mode);
                end
                {8'd6} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_EGRESS_ANA_M0_CFG_6, ana_mode);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_EGRESS_DIG_M0_CFG_6, dig_mode);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_EGRESS_ANA_M0_CFG_6, ana_mode);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_EGRESS_DIG_M0_CFG_6, dig_mode);
                end
                {8'd7} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_EGRESS_ANA_M0_CFG_7, ana_mode);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_EGRESS_DIG_M0_CFG_7, dig_mode);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_EGRESS_ANA_M0_CFG_7, ana_mode);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_EGRESS_DIG_M0_CFG_7, dig_mode);
                end
                {8'd8} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_EGRESS_ANA_M0_CFG_8, ana_mode);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_EGRESS_DIG_M0_CFG_8, dig_mode);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_EGRESS_ANA_M0_CFG_8, ana_mode);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_EGRESS_DIG_M0_CFG_8, dig_mode);
                end
                default : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_EGRESS_ANA_M0_CFG_0, ana_mode);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_EGRESS_DIG_M0_CFG_0, dig_mode);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_EGRESS_ANA_M0_CFG_1, ana_mode);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_EGRESS_DIG_M0_CFG_1, dig_mode);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_EGRESS_ANA_M0_CFG_2, ana_mode);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_EGRESS_DIG_M0_CFG_2, dig_mode);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_EGRESS_ANA_M0_CFG_3, ana_mode);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_EGRESS_DIG_M0_CFG_3, dig_mode);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_EGRESS_ANA_M0_CFG_4, ana_mode);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_EGRESS_DIG_M0_CFG_4, dig_mode);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_EGRESS_ANA_M0_CFG_5, ana_mode);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_EGRESS_DIG_M0_CFG_5, dig_mode);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_EGRESS_ANA_M0_CFG_6, ana_mode);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_EGRESS_DIG_M0_CFG_6, dig_mode);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_EGRESS_ANA_M0_CFG_7, ana_mode);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_EGRESS_DIG_M0_CFG_7, dig_mode);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_EGRESS_ANA_M0_CFG_8, ana_mode);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_EGRESS_DIG_M0_CFG_8, dig_mode);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_EGRESS_ANA_M0_CFG_0, ana_mode);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_EGRESS_DIG_M0_CFG_0, dig_mode);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_EGRESS_ANA_M0_CFG_1, ana_mode);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_EGRESS_DIG_M0_CFG_1, dig_mode);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_EGRESS_ANA_M0_CFG_2, ana_mode);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_EGRESS_DIG_M0_CFG_2, dig_mode);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_EGRESS_ANA_M0_CFG_3, ana_mode);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_EGRESS_DIG_M0_CFG_3, dig_mode);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_EGRESS_ANA_M0_CFG_4, ana_mode);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_EGRESS_DIG_M0_CFG_4, dig_mode);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_EGRESS_ANA_M0_CFG_5, ana_mode);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_EGRESS_DIG_M0_CFG_5, dig_mode);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_EGRESS_ANA_M0_CFG_6, ana_mode);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_EGRESS_DIG_M0_CFG_6, dig_mode);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_EGRESS_ANA_M0_CFG_7, ana_mode);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_EGRESS_DIG_M0_CFG_7, dig_mode);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_EGRESS_ANA_M0_CFG_8, ana_mode);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_EGRESS_DIG_M0_CFG_8, dig_mode);
                end
            endcase
        end
        if((byte_sel == DQ1 ) || (byte_sel == DQ_ALL) || (byte_sel == ALL)) begin
            case(dq)
                {8'd0} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_EGRESS_ANA_M0_CFG_0, ana_mode);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_EGRESS_DIG_M0_CFG_0, dig_mode);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_EGRESS_ANA_M0_CFG_0, ana_mode);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_EGRESS_DIG_M0_CFG_0, dig_mode);
                end
                {8'd1} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_EGRESS_ANA_M0_CFG_1, ana_mode);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_EGRESS_DIG_M0_CFG_1, dig_mode);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_EGRESS_ANA_M0_CFG_1, ana_mode);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_EGRESS_DIG_M0_CFG_1, dig_mode);
                end
                {8'd2} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_EGRESS_ANA_M0_CFG_2, ana_mode);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_EGRESS_DIG_M0_CFG_2, dig_mode);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_EGRESS_ANA_M0_CFG_2, ana_mode);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_EGRESS_DIG_M0_CFG_2, dig_mode);
                end
                {8'd3} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_EGRESS_ANA_M0_CFG_3, ana_mode);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_EGRESS_DIG_M0_CFG_3, dig_mode);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_EGRESS_ANA_M0_CFG_3, ana_mode);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_EGRESS_DIG_M0_CFG_3, dig_mode);
                end
                {8'd4} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_EGRESS_ANA_M0_CFG_4, ana_mode);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_EGRESS_DIG_M0_CFG_4, dig_mode);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_EGRESS_ANA_M0_CFG_4, ana_mode);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_EGRESS_DIG_M0_CFG_4, dig_mode);
                end
                {8'd5} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_EGRESS_ANA_M0_CFG_5, ana_mode);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_EGRESS_DIG_M0_CFG_5, dig_mode);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_EGRESS_ANA_M0_CFG_5, ana_mode);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_EGRESS_DIG_M0_CFG_5, dig_mode);
                end
                {8'd6} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_EGRESS_ANA_M0_CFG_6, ana_mode);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_EGRESS_DIG_M0_CFG_6, dig_mode);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_EGRESS_ANA_M0_CFG_6, ana_mode);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_EGRESS_DIG_M0_CFG_6, dig_mode);
                end
                {8'd7} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_EGRESS_ANA_M0_CFG_7, ana_mode);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_EGRESS_DIG_M0_CFG_7, dig_mode);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_EGRESS_ANA_M0_CFG_7, ana_mode);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_EGRESS_DIG_M0_CFG_7, dig_mode);
                end
                {8'd8} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_EGRESS_ANA_M0_CFG_8, ana_mode);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_EGRESS_DIG_M0_CFG_8, dig_mode);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_EGRESS_ANA_M0_CFG_8, ana_mode);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_EGRESS_DIG_M0_CFG_8, dig_mode);
                end
                default : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_EGRESS_ANA_M0_CFG_0, ana_mode);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_EGRESS_DIG_M0_CFG_0, dig_mode);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_EGRESS_ANA_M0_CFG_1, ana_mode);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_EGRESS_DIG_M0_CFG_1, dig_mode);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_EGRESS_ANA_M0_CFG_2, ana_mode);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_EGRESS_DIG_M0_CFG_2, dig_mode);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_EGRESS_ANA_M0_CFG_3, ana_mode);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_EGRESS_DIG_M0_CFG_3, dig_mode);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_EGRESS_ANA_M0_CFG_4, ana_mode);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_EGRESS_DIG_M0_CFG_4, dig_mode);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_EGRESS_ANA_M0_CFG_5, ana_mode);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_EGRESS_DIG_M0_CFG_5, dig_mode);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_EGRESS_ANA_M0_CFG_6, ana_mode);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_EGRESS_DIG_M0_CFG_6, dig_mode);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_EGRESS_ANA_M0_CFG_7, ana_mode);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_EGRESS_DIG_M0_CFG_7, dig_mode);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_EGRESS_ANA_M0_CFG_8, ana_mode);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_EGRESS_DIG_M0_CFG_8, dig_mode);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_EGRESS_ANA_M0_CFG_0, ana_mode);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_EGRESS_DIG_M0_CFG_0, dig_mode);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_EGRESS_ANA_M0_CFG_1, ana_mode);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_EGRESS_DIG_M0_CFG_1, dig_mode);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_EGRESS_ANA_M0_CFG_2, ana_mode);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_EGRESS_DIG_M0_CFG_2, dig_mode);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_EGRESS_ANA_M0_CFG_3, ana_mode);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_EGRESS_DIG_M0_CFG_3, dig_mode);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_EGRESS_ANA_M0_CFG_4, ana_mode);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_EGRESS_DIG_M0_CFG_4, dig_mode);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_EGRESS_ANA_M0_CFG_5, ana_mode);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_EGRESS_DIG_M0_CFG_5, dig_mode);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_EGRESS_ANA_M0_CFG_6, ana_mode);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_EGRESS_DIG_M0_CFG_6, dig_mode);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_EGRESS_ANA_M0_CFG_7, ana_mode);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_EGRESS_DIG_M0_CFG_7, dig_mode);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_EGRESS_ANA_M0_CFG_8, ana_mode);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_EGRESS_DIG_M0_CFG_8, dig_mode);
                end
            endcase
        end
        if((byte_sel == CA) || (byte_sel == ALL)) begin
            case(dq)
                {8'd0} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_EGRESS_ANA_M0_CFG_0, ana_mode);
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_EGRESS_DIG_M0_CFG_0, dig_mode);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_EGRESS_ANA_M0_CFG_0, ana_mode);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_EGRESS_DIG_M0_CFG_0, dig_mode);
                end
                {8'd1} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_EGRESS_ANA_M0_CFG_1, ana_mode);
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_EGRESS_DIG_M0_CFG_1, dig_mode);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_EGRESS_ANA_M0_CFG_1, ana_mode);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_EGRESS_DIG_M0_CFG_1, dig_mode);
                end
                {8'd2} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_EGRESS_ANA_M0_CFG_2, ana_mode);
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_EGRESS_DIG_M0_CFG_2, dig_mode);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_EGRESS_ANA_M0_CFG_2, ana_mode);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_EGRESS_DIG_M0_CFG_2, dig_mode);
                end
                {8'd3} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_EGRESS_ANA_M0_CFG_3, ana_mode);
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_EGRESS_DIG_M0_CFG_3, dig_mode);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_EGRESS_ANA_M0_CFG_3, ana_mode);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_EGRESS_DIG_M0_CFG_3, dig_mode);
                end
                {8'd4} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_EGRESS_ANA_M0_CFG_4, ana_mode);
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_EGRESS_DIG_M0_CFG_4, dig_mode);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_EGRESS_ANA_M0_CFG_4, ana_mode);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_EGRESS_DIG_M0_CFG_4, dig_mode);
                end
                {8'd5} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_EGRESS_ANA_M0_CFG_5, ana_mode);
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_EGRESS_DIG_M0_CFG_5, dig_mode);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_EGRESS_ANA_M0_CFG_5, ana_mode);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_EGRESS_DIG_M0_CFG_5, dig_mode);
                end
                {8'd6} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_EGRESS_ANA_M0_CFG_6, ana_mode);
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_EGRESS_DIG_M0_CFG_6, dig_mode);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_EGRESS_ANA_M0_CFG_6, ana_mode);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_EGRESS_DIG_M0_CFG_6, dig_mode);
                end
                {8'd7} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_EGRESS_ANA_M0_CFG_7, ana_mode);
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_EGRESS_DIG_M0_CFG_7, dig_mode);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_EGRESS_ANA_M0_CFG_7, ana_mode);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_EGRESS_DIG_M0_CFG_7, dig_mode);
                end
                {8'd8} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_EGRESS_ANA_M0_CFG_8, ana_mode);
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_EGRESS_DIG_M0_CFG_8, dig_mode);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_EGRESS_ANA_M0_CFG_8, ana_mode);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_EGRESS_DIG_M0_CFG_8, dig_mode);
                end
                {8'd9} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_EGRESS_ANA_M0_CFG_9, ana_mode);
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_EGRESS_DIG_M0_CFG_9, dig_mode);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_EGRESS_ANA_M0_CFG_9, ana_mode);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_EGRESS_DIG_M0_CFG_9, dig_mode);
                end
                {8'd10} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_EGRESS_ANA_M0_CFG_10, ana_mode);
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_EGRESS_DIG_M0_CFG_10, dig_mode);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_EGRESS_ANA_M0_CFG_10, ana_mode);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_EGRESS_DIG_M0_CFG_10, dig_mode);
                end
                default : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_EGRESS_ANA_M0_CFG_0, ana_mode);
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_EGRESS_DIG_M0_CFG_0, dig_mode);
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_EGRESS_ANA_M0_CFG_1, ana_mode);
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_EGRESS_DIG_M0_CFG_1, dig_mode);
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_EGRESS_ANA_M0_CFG_2, ana_mode);
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_EGRESS_DIG_M0_CFG_2, dig_mode);
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_EGRESS_ANA_M0_CFG_3, ana_mode);
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_EGRESS_DIG_M0_CFG_3, dig_mode);
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_EGRESS_ANA_M0_CFG_4, ana_mode);
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_EGRESS_DIG_M0_CFG_4, dig_mode);
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_EGRESS_ANA_M0_CFG_5, ana_mode);
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_EGRESS_DIG_M0_CFG_5, dig_mode);
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_EGRESS_ANA_M0_CFG_6, ana_mode);
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_EGRESS_DIG_M0_CFG_6, dig_mode);
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_EGRESS_ANA_M0_CFG_7, ana_mode);
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_EGRESS_DIG_M0_CFG_7, dig_mode);
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_EGRESS_ANA_M0_CFG_8, ana_mode);
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_EGRESS_DIG_M0_CFG_8, dig_mode);
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_EGRESS_ANA_M0_CFG_9, ana_mode);
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_EGRESS_DIG_M0_CFG_9, dig_mode);
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_EGRESS_ANA_M0_CFG_10, ana_mode);
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_EGRESS_DIG_M0_CFG_10, dig_mode);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_EGRESS_ANA_M0_CFG_0, ana_mode);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_EGRESS_DIG_M0_CFG_0, dig_mode);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_EGRESS_ANA_M0_CFG_1, ana_mode);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_EGRESS_DIG_M0_CFG_1, dig_mode);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_EGRESS_ANA_M0_CFG_2, ana_mode);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_EGRESS_DIG_M0_CFG_2, dig_mode);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_EGRESS_ANA_M0_CFG_3, ana_mode);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_EGRESS_DIG_M0_CFG_3, dig_mode);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_EGRESS_ANA_M0_CFG_4, ana_mode);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_EGRESS_DIG_M0_CFG_4, dig_mode);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_EGRESS_ANA_M0_CFG_5, ana_mode);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_EGRESS_DIG_M0_CFG_5, dig_mode);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_EGRESS_ANA_M0_CFG_6, ana_mode);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_EGRESS_DIG_M0_CFG_6, dig_mode);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_EGRESS_ANA_M0_CFG_7, ana_mode);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_EGRESS_DIG_M0_CFG_7, dig_mode);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_EGRESS_ANA_M0_CFG_8, ana_mode);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_EGRESS_DIG_M0_CFG_8, dig_mode);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_EGRESS_ANA_M0_CFG_9, ana_mode);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_EGRESS_DIG_M0_CFG_9, dig_mode);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_EGRESS_ANA_M0_CFG_10, ana_mode);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_EGRESS_DIG_M0_CFG_10, dig_mode);
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
task automatic set_dq_dqs_drvr_cfg_1;
    input byte_sel_t  byte_sel;
    input integer  dqs_freq_MHz ;
    input integer  lb_mode ;
    input integer  wck_mode ;
    input integer  se_mode ;
    input integer  termination ;
    input bit tx_rx_mode;
    input bit [2:0] select;
    logic [2:0] tx_impd;
    logic ovrd_val_t;
    logic ovrd_val_c;
    logic [2:0] ovrd;
    logic [2:0] rx_impd;
    logic [2:0] dq_ovrd;
    logic dq_ovrd_val;
    int i=1;
    int j=1;
    int k=1;
    begin
        /* if(lb_mode == 1 ) begin
            tx_impd      = i;
            rx_impd      = 3'h6;
            i++;
                 if(i == 7) begin
                        i=1;
                 end
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
         end else begin

         end
            if (termination == 0) begin
           ovrd_val_t  = 1'h0;
           ovrd_val_c  = 1'h1;
           ovrd        = 3'h1 ;
           dq_ovrd_val    = 1'h0;
           dq_ovrd        = 3'h0;
         end else if (termination == 1) begin
           ovrd_val_t  = 1'h1;
           ovrd_val_c  = 1'h1;
           ovrd        = tx_impd ;
           dq_ovrd_val    = 1'h0;
           dq_ovrd        = tx_impd;*/
        // end
        if(lb_mode == 0 && termination == 0) begin
            if(tx_rx_mode == 1) begin
                tx_impd      = 3'h5;
                rx_impd      = 0;
                ovrd_val_t  = 1'h0;
                ovrd_val_c  = 1'h0;
                ovrd        =1;
                dq_ovrd_val    = 1'h0;
                dq_ovrd        = 1;
            end else begin
                rx_impd      = select;
                tx_impd      = 3'h5;
                ovrd_val_t  = 1'h0;
                ovrd_val_c  = 1'h0;
                ovrd        =0;
                dq_ovrd_val    = 1'h0;
                dq_ovrd        = 0;
            end
        end else if(lb_mode == 0 && termination == 1) begin
            rx_impd      = select;
            tx_impd      = 3'h6;
            ovrd_val_t  = 1'h1;
            ovrd_val_c  = 1'h1;
            ovrd        = select ;
            dq_ovrd_val    = 1'h1;
            dq_ovrd        = select;
        end else if(lb_mode == 1 && termination == 0) begin
            rx_impd      = select;
            tx_impd      = 3'h6;
            ovrd_val_t  = 1'h0;
            ovrd_val_c  = 1'h0;
            ovrd        = select ;
            dq_ovrd_val    = 1'h0;
            dq_ovrd        =select;
        end else if(lb_mode == 1 && termination == 1)begin
            rx_impd      = select;
            tx_impd      = 3'h6;
            ovrd_val_t  = 1'h0;
            ovrd_val_c  = 1'h1;
            ovrd        = select ;
            dq_ovrd_val    = 1'h0;
            dq_ovrd        = tx_impd;
        end

        case({byte_sel})
            {DQ0}: begin
                `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_IO_CMN_M0_R0_CFG, LPBK_EN, SE_MODE, lb_mode, se_mode);
                `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_IO_CMN_M0_R1_CFG, LPBK_EN, SE_MODE, lb_mode, se_mode);
                if (wck_mode == 1) begin
                    `CSR_WRF3(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_IO_M0_CFG_0, OVRD_SEL, OVRD_VAL_C, OVRD_VAL_T, ovrd, ovrd_val_c, ovrd_val_t);
                    `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_IO_M0_CFG_0, TX_IMPD, RX_IMPD, tx_impd, rx_impd );
                end else begin
                    `CSR_WRF3(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_IO_M0_CFG_1, OVRD_SEL, OVRD_VAL_C, OVRD_VAL_T, ovrd, ovrd_val_c, ovrd_val_t);
                    `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_IO_M0_CFG_1, TX_IMPD, RX_IMPD, tx_impd, rx_impd );
                end
                `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_0 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
                `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_0 ,  TX_IMPD, RX_IMPD, tx_impd, rx_impd );
                // FIXME: DQ bus HIz
                // `CSR_WRF2(DDR_CH::`u::_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_`i ,  TX_IMPD, RX_IMPD, tx_impd, rx_impd );
                `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_1 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
                `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_1 ,  TX_IMPD, RX_IMPD, tx_impd, rx_impd );
                // FIXME: DQ bus HIz
                // `CSR_WRF2(DDR_CH::`u::_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_`i ,  TX_IMPD, RX_IMPD, tx_impd, rx_impd );
                `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_2 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
                `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_2 ,  TX_IMPD, RX_IMPD, tx_impd, rx_impd );
                // FIXME: DQ bus HIz
                // `CSR_WRF2(DDR_CH::`u::_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_`i ,  TX_IMPD, RX_IMPD, tx_impd, rx_impd );
                `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_3 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
                `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_3 ,  TX_IMPD, RX_IMPD, tx_impd, rx_impd );
                // FIXME: DQ bus HIz
                // `CSR_WRF2(DDR_CH::`u::_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_`i ,  TX_IMPD, RX_IMPD, tx_impd, rx_impd );
                `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_4 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
                `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_4 ,  TX_IMPD, RX_IMPD, tx_impd, rx_impd );
                // FIXME: DQ bu
                // `CSR_WRF2(DDR_CH::`u::_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_`i ,  TX_IMPD, RX_IMPD, tx_impd, rx_impd );
                `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_5 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
                `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_5 ,  TX_IMPD, RX_IMPD, tx_impd, rx_impd );
                // FIXME: DQ bus HIz
                // `CSR_WRF2(DDR_CH::`u::_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_`i ,  TX_IMPD, RX_IMPD, tx_impd, rx_impd );
                `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_6 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
                `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_6 ,  TX_IMPD, RX_IMPD, tx_impd, rx_impd );
                // FIXME: DQ bus HIz
                // `CSR_WRF2(DDR_CH::`u::_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_`i ,  TX_IMPD, RX_IMPD, tx_impd, rx_impd );
                `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_7 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
                `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_7 ,  TX_IMPD, RX_IMPD, tx_impd, rx_impd );
                // FIXME: DQ bus HIz
                // `CSR_WRF2(DDR_CH::`u::_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_`i ,  TX_IMPD, RX_IMPD, tx_impd, rx_impd );
                `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_8 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
                `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_8 ,  TX_IMPD, RX_IMPD, tx_impd, rx_impd );
                // FIXME: DQ bus HIz
                // `CSR_WRF2(DDR_CH::`u::_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_`i ,  TX_IMPD, RX_IMPD, tx_impd, rx_impd );
                `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_IO_CMN_M0_R0_CFG, LPBK_EN, SE_MODE, lb_mode, se_mode);
                `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_IO_CMN_M0_R1_CFG, LPBK_EN, SE_MODE, lb_mode, se_mode);
                if (wck_mode == 1) begin
                    `CSR_WRF3(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_IO_M0_CFG_0, OVRD_SEL, OVRD_VAL_C, OVRD_VAL_T, ovrd, ovrd_val_c, ovrd_val_t);
                    `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_IO_M0_CFG_0, TX_IMPD, RX_IMPD, tx_impd, rx_impd );
                end else begin
                    `CSR_WRF3(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_IO_M0_CFG_1, OVRD_SEL, OVRD_VAL_C, OVRD_VAL_T, ovrd, ovrd_val_c, ovrd_val_t);
                    `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_IO_M0_CFG_1, TX_IMPD, RX_IMPD, tx_impd, rx_impd );
                end
                `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_0 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
                // FIXME: DQ bus HIz
                // `CSR_WRF2(DDR_CH::`u::_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_`i ,  TX_IMPD, RX_IMPD, tx_impd, rx_impd );
                `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_1 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
                // FIXME: DQ bus HIz
                // `CSR_WRF2(DDR_CH::`u::_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_`i ,  TX_IMPD, RX_IMPD, tx_impd, rx_impd );
                `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_2 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
                // FIXME: DQ bus HIz
                // `CSR_WRF2(DDR_CH::`u::_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_`i ,  TX_IMPD, RX_IMPD, tx_impd, rx_impd );
                `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_3 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
                // FIXME: DQ bus HIz
                // `CSR_WRF2(DDR_CH::`u::_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_`i ,  TX_IMPD, RX_IMPD, tx_impd, rx_impd );
                `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_4 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
                // FIXME: DQ bus HIz
                // `CSR_WRF2(DDR_CH::`u::_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_`i ,  TX_IMPD, RX_IMPD, tx_impd, rx_impd );
                `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_5 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
                // FIXME: DQ bus HIz
                // `CSR_WRF2(DDR_CH::`u::_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_`i ,  TX_IMPD, RX_IMPD, tx_impd, rx_impd );
                `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_6 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
                // FIXME: DQ bus HIz
                // `CSR_WRF2(DDR_CH::`u::_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_`i ,  TX_IMPD, RX_IMPD, tx_impd, rx_impd );
                `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_7 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
                // FIXME: DQ bus HIz
                // `CSR_WRF2(DDR_CH::`u::_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_`i ,  TX_IMPD, RX_IMPD, tx_impd, rx_impd );
                `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_8 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
                // FIXME: DQ bus HIz
                // `CSR_WRF2(DDR_CH::`u::_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_`i ,  TX_IMPD, RX_IMPD, tx_impd, rx_impd );
            end
            {DQ1}: begin
                `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_IO_CMN_M0_R0_CFG, LPBK_EN, SE_MODE, lb_mode, se_mode);
                `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_IO_CMN_M0_R1_CFG, LPBK_EN, SE_MODE, lb_mode, se_mode);
                if (wck_mode == 1) begin
                    `CSR_WRF3(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_IO_M0_CFG_0, OVRD_SEL, OVRD_VAL_C, OVRD_VAL_T, ovrd, ovrd_val_c, ovrd_val_t);
                    `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_IO_M0_CFG_0, TX_IMPD, RX_IMPD, tx_impd, rx_impd );
                end else begin
                    `CSR_WRF3(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_IO_M0_CFG_1, OVRD_SEL, OVRD_VAL_C, OVRD_VAL_T, ovrd, ovrd_val_c, ovrd_val_t);
                    `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_IO_M0_CFG_1, TX_IMPD, RX_IMPD, tx_impd, rx_impd );
                end
                `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_0 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
                //`CSR_WRF2(DDR_CH::`u::_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_`i ,  TX_IMPD, RX_IMPD, tx_impd, rx_impd );
                `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_1 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
                //`CSR_WRF2(DDR_CH::`u::_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_`i ,  TX_IMPD, RX_IMPD, tx_impd, rx_impd );
                `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_2 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
                //`CSR_WRF2(DDR_CH::`u::_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_`i ,  TX_IMPD, RX_IMPD, tx_impd, rx_impd );
                `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_3 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
                //`CSR_WRF2(DDR_CH::`u::_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_`i ,  TX_IMPD, RX_IMPD, tx_impd, rx_impd );
                `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_4 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
                //`CSR_WRF2(DDR_CH::`u::_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_`i ,  TX_IMPD, RX_IMPD, tx_impd, rx_impd );
                `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_5 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
                //`CSR_WRF2(DDR_CH::`u::_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_`i ,  TX_IMPD, RX_IMPD, tx_impd, rx_impd );
                `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_6 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
                //`CSR_WRF2(DDR_CH::`u::_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_`i ,  TX_IMPD, RX_IMPD, tx_impd, rx_impd );
                `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_7 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
                //`CSR_WRF2(DDR_CH::`u::_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_`i ,  TX_IMPD, RX_IMPD, tx_impd, rx_impd );
                `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_8 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
                //`CSR_WRF2(DDR_CH::`u::_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_`i ,  TX_IMPD, RX_IMPD, tx_impd, rx_impd );
                `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_IO_CMN_M0_R0_CFG, LPBK_EN, SE_MODE, lb_mode, se_mode);
                `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_IO_CMN_M0_R1_CFG, LPBK_EN, SE_MODE, lb_mode, se_mode);
                if (wck_mode == 1) begin
                    `CSR_WRF3(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_IO_M0_CFG_0, OVRD_SEL, OVRD_VAL_C, OVRD_VAL_T, ovrd, ovrd_val_c, ovrd_val_t);
                    `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_IO_M0_CFG_0, TX_IMPD, RX_IMPD, tx_impd, rx_impd );
                end else begin
                    `CSR_WRF3(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_IO_M0_CFG_1, OVRD_SEL, OVRD_VAL_C, OVRD_VAL_T, ovrd, ovrd_val_c, ovrd_val_t);
                    `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_IO_M0_CFG_1, TX_IMPD, RX_IMPD, tx_impd, rx_impd );
                end
                `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_0 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
                //`CSR_WRF2(DDR_CH::`u::_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_`i ,  TX_IMPD, RX_IMPD, tx_impd, rx_impd );
                `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_1 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
                //`CSR_WRF2(DDR_CH::`u::_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_`i ,  TX_IMPD, RX_IMPD, tx_impd, rx_impd );
                `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_2 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
                //`CSR_WRF2(DDR_CH::`u::_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_`i ,  TX_IMPD, RX_IMPD, tx_impd, rx_impd );
                `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_3 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
                //`CSR_WRF2(DDR_CH::`u::_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_`i ,  TX_IMPD, RX_IMPD, tx_impd, rx_impd );
                `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_4 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
                //`CSR_WRF2(DDR_CH::`u::_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_`i ,  TX_IMPD, RX_IMPD, tx_impd, rx_impd );
                `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_5 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
                //`CSR_WRF2(DDR_CH::`u::_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_`i ,  TX_IMPD, RX_IMPD, tx_impd, rx_impd );
                `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_6 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
                //`CSR_WRF2(DDR_CH::`u::_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_`i ,  TX_IMPD, RX_IMPD, tx_impd, rx_impd );
                `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_7 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
                //`CSR_WRF2(DDR_CH::`u::_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_`i ,  TX_IMPD, RX_IMPD, tx_impd, rx_impd );
                `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_8 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
                //`CSR_WRF2(DDR_CH::`u::_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_`i ,  TX_IMPD, RX_IMPD, tx_impd, rx_impd );
            end
            {DQ_ALL}: begin
                `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_IO_CMN_M0_R0_CFG, LPBK_EN, SE_MODE, lb_mode, se_mode);
                `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_IO_CMN_M0_R1_CFG, LPBK_EN, SE_MODE, lb_mode, se_mode);
                if (wck_mode == 1) begin
                    `CSR_WRF3(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_IO_M0_CFG_0, OVRD_SEL, OVRD_VAL_C, OVRD_VAL_T, ovrd, ovrd_val_c, ovrd_val_t);
                    `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_IO_M0_CFG_0, TX_IMPD, RX_IMPD, tx_impd, rx_impd );
                end else begin
                    `CSR_WRF3(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_IO_M0_CFG_1, OVRD_SEL, OVRD_VAL_C, OVRD_VAL_T, ovrd, ovrd_val_c, ovrd_val_t);
                    `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_IO_M0_CFG_1, TX_IMPD, RX_IMPD, tx_impd, rx_impd );
                end
                `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_IO_CMN_M0_R0_CFG, LPBK_EN, SE_MODE, lb_mode, se_mode);
                `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_IO_CMN_M0_R1_CFG, LPBK_EN, SE_MODE, lb_mode, se_mode);
                if (wck_mode == 1) begin
                    `CSR_WRF3(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_IO_M0_CFG_0, OVRD_SEL, OVRD_VAL_C, OVRD_VAL_T, ovrd, ovrd_val_c, ovrd_val_t);
                    `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_IO_M0_CFG_0, TX_IMPD, RX_IMPD, tx_impd, rx_impd );
                end else begin
                    `CSR_WRF3(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_IO_M0_CFG_1, OVRD_SEL, OVRD_VAL_C, OVRD_VAL_T, ovrd, ovrd_val_c, ovrd_val_t);
                    `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_IO_M0_CFG_1, TX_IMPD, RX_IMPD, tx_impd, rx_impd );
                end
                `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_0 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
                //`CSR_WRF2(DDR_CH::`u::_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_`i ,  TX_IMPD, RX_IMPD, tx_impd, rx_impd );
                `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_0 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
                //`CSR_WRF2(DDR_CH::`u::_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_`i ,  TX_IMPD, RX_IMPD, tx_impd, rx_impd );
                `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_1 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
                //`CSR_WRF2(DDR_CH::`u::_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_`i ,  TX_IMPD, RX_IMPD, tx_impd, rx_impd );
                `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_1 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
                //`CSR_WRF2(DDR_CH::`u::_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_`i ,  TX_IMPD, RX_IMPD, tx_impd, rx_impd );
                `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_2 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
                //`CSR_WRF2(DDR_CH::`u::_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_`i ,  TX_IMPD, RX_IMPD, tx_impd, rx_impd );
                `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_2 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
                //`CSR_WRF2(DDR_CH::`u::_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_`i ,  TX_IMPD, RX_IMPD, tx_impd, rx_impd );
                `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_3 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
                //`CSR_WRF2(DDR_CH::`u::_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_`i ,  TX_IMPD, RX_IMPD, tx_impd, rx_impd );
                `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_3 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
                //`CSR_WRF2(DDR_CH::`u::_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_`i ,  TX_IMPD, RX_IMPD, tx_impd, rx_impd );
                `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_4 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
                //`CSR_WRF2(DDR_CH::`u::_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_`i ,  TX_IMPD, RX_IMPD, tx_impd, rx_impd );
                `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_4 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
                //`CSR_WRF2(DDR_CH::`u::_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_`i ,  TX_IMPD, RX_IMPD, tx_impd, rx_impd );
                `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_5 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
                //`CSR_WRF2(DDR_CH::`u::_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_`i ,  TX_IMPD, RX_IMPD, tx_impd, rx_impd );
                `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_5 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
                //`CSR_WRF2(DDR_CH::`u::_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_`i ,  TX_IMPD, RX_IMPD, tx_impd, rx_impd );
                `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_6 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
                //`CSR_WRF2(DDR_CH::`u::_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_`i ,  TX_IMPD, RX_IMPD, tx_impd, rx_impd );
                `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_6 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
                //`CSR_WRF2(DDR_CH::`u::_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_`i ,  TX_IMPD, RX_IMPD, tx_impd, rx_impd );
                `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_7 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
                //`CSR_WRF2(DDR_CH::`u::_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_`i ,  TX_IMPD, RX_IMPD, tx_impd, rx_impd );
                `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_7 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
                //`CSR_WRF2(DDR_CH::`u::_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_`i ,  TX_IMPD, RX_IMPD, tx_impd, rx_impd );
                `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_8 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
                //`CSR_WRF2(DDR_CH::`u::_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_`i ,  TX_IMPD, RX_IMPD, tx_impd, rx_impd );
                `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_8 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
                //`CSR_WRF2(DDR_CH::`u::_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_`i ,  TX_IMPD, RX_IMPD, tx_impd, rx_impd );
                `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_IO_CMN_M0_R0_CFG, LPBK_EN, SE_MODE, lb_mode, se_mode);
                `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_IO_CMN_M0_R1_CFG, LPBK_EN, SE_MODE, lb_mode, se_mode);
                if (wck_mode == 1) begin
                    `CSR_WRF3(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_IO_M0_CFG_0, OVRD_SEL, OVRD_VAL_C, OVRD_VAL_T, ovrd, ovrd_val_c, ovrd_val_t);
                    `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_IO_M0_CFG_0, TX_IMPD, RX_IMPD, tx_impd, rx_impd );
                end else begin
                    `CSR_WRF3(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_IO_M0_CFG_1, OVRD_SEL, OVRD_VAL_C, OVRD_VAL_T, ovrd, ovrd_val_c, ovrd_val_t);
                    `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_IO_M0_CFG_1, TX_IMPD, RX_IMPD, tx_impd, rx_impd );
                end
                `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_IO_CMN_M0_R0_CFG, LPBK_EN, SE_MODE, lb_mode, se_mode);
                `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_IO_CMN_M0_R1_CFG, LPBK_EN, SE_MODE, lb_mode, se_mode);
                if (wck_mode == 1) begin
                    `CSR_WRF3(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_IO_M0_CFG_0, OVRD_SEL, OVRD_VAL_C, OVRD_VAL_T, ovrd, ovrd_val_c, ovrd_val_t);
                    `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_IO_M0_CFG_0, TX_IMPD, RX_IMPD, tx_impd, rx_impd );
                end else begin
                    `CSR_WRF3(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_IO_M0_CFG_1, OVRD_SEL, OVRD_VAL_C, OVRD_VAL_T, ovrd, ovrd_val_c, ovrd_val_t);
                    `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_IO_M0_CFG_1, TX_IMPD, RX_IMPD, tx_impd, rx_impd );
                end
                `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_0 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
                //`CSR_WRF2(DDR_CH::`u::_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_`i ,  TX_IMPD, RX_IMPD, tx_impd, rx_impd );
                `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_0 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
                //`CSR_WRF2(DDR_CH::`u::_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_`i ,  TX_IMPD, RX_IMPD, tx_impd, rx_impd );
                `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_1 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
                //`CSR_WRF2(DDR_CH::`u::_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_`i ,  TX_IMPD, RX_IMPD, tx_impd, rx_impd );
                `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_1 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
                //`CSR_WRF2(DDR_CH::`u::_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_`i ,  TX_IMPD, RX_IMPD, tx_impd, rx_impd );
                `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_2 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
                //`CSR_WRF2(DDR_CH::`u::_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_`i ,  TX_IMPD, RX_IMPD, tx_impd, rx_impd );
                `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_2 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
                //`CSR_WRF2(DDR_CH::`u::_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_`i ,  TX_IMPD, RX_IMPD, tx_impd, rx_impd );
                `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_3 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
                //`CSR_WRF2(DDR_CH::`u::_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_`i ,  TX_IMPD, RX_IMPD, tx_impd, rx_impd );
                `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_3 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
                //`CSR_WRF2(DDR_CH::`u::_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_`i ,  TX_IMPD, RX_IMPD, tx_impd, rx_impd );
                `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_4 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
                //`CSR_WRF2(DDR_CH::`u::_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_`i ,  TX_IMPD, RX_IMPD, tx_impd, rx_impd );
                `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_4 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
                //`CSR_WRF2(DDR_CH::`u::_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_`i ,  TX_IMPD, RX_IMPD, tx_impd, rx_impd );
                `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_5 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
                //`CSR_WRF2(DDR_CH::`u::_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_`i ,  TX_IMPD, RX_IMPD, tx_impd, rx_impd );
                `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_5 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
                //`CSR_WRF2(DDR_CH::`u::_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_`i ,  TX_IMPD, RX_IMPD, tx_impd, rx_impd );
                `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_6 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
                //`CSR_WRF2(DDR_CH::`u::_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_`i ,  TX_IMPD, RX_IMPD, tx_impd, rx_impd );
                `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_6 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
                //`CSR_WRF2(DDR_CH::`u::_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_`i ,  TX_IMPD, RX_IMPD, tx_impd, rx_impd );
                `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_7 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
                //`CSR_WRF2(DDR_CH::`u::_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_`i ,  TX_IMPD, RX_IMPD, tx_impd, rx_impd );
                `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_7 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
                //`CSR_WRF2(DDR_CH::`u::_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_`i ,  TX_IMPD, RX_IMPD, tx_impd, rx_impd );
                `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_8 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
                //`CSR_WRF2(DDR_CH::`u::_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_`i ,  TX_IMPD, RX_IMPD, tx_impd, rx_impd );
                `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_8 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
                //`CSR_WRF2(DDR_CH::`u::_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_`i ,  TX_IMPD, RX_IMPD, tx_impd, rx_impd );
            end
        endcase

    end
endtask

task automatic set_dq_dqs_drvr_cfg;
    input byte_sel_t  byte_sel;
    input integer  dqs_freq_MHz ;
    input integer  lb_mode ;
    input integer  wck_mode ;
    input integer  se_mode ;
    input integer  termination ;
    logic [2:0] tx_impd;
    logic [2:0] rx_impd;
    logic [2:0] dq_tx_impd;
    logic [2:0] dq_rx_impd;
    logic [2:0] ovrd;
    logic ovrd_val_t;
    logic ovrd_val_c;
    logic [2:0] dq_ovrd;
    logic dq_ovrd_val;
    begin

        if(lb_mode == 1 ) begin
            tx_impd      = 3'h6;
            rx_impd      = 3'h6;
            dq_tx_impd   = 3'h6 ;
            dq_rx_impd   = 3'h6 ;
        end else if (dqs_freq_MHz >= 2136) begin
            tx_impd      = 3'h5;
            rx_impd      = 3'h5;
            dq_tx_impd   = 3'h1 ;
            dq_rx_impd   = 3'h0 ;
        end else if (dqs_freq_MHz >= 1075) begin
            tx_impd      = 3'h3;
            rx_impd      = 3'h3;
            dq_tx_impd   = 3'h1 ;
            dq_rx_impd   = 3'h0 ;
        end else begin
            tx_impd      = 3'h1;
            rx_impd      = (termination != 0) ? 3'h1 : 3'h0 ;
            dq_tx_impd   = 3'h1 ;
            dq_rx_impd   = 3'h0 ;
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
            `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_IO_CMN_M0_R0_CFG, LPBK_EN, SE_MODE, lb_mode, se_mode);
            `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_IO_CMN_M0_R1_CFG, LPBK_EN, SE_MODE, lb_mode, se_mode);
            if (wck_mode == 1) begin
               `CSR_WRF3(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_IO_M0_CFG_0, OVRD_SEL, OVRD_VAL_C, OVRD_VAL_T, ovrd, ovrd_val_c, ovrd_val_t);
               `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_IO_M0_CFG_0, TX_IMPD, RX_IMPD, tx_impd, rx_impd );
            end else begin
               `CSR_WRF3(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_IO_M0_CFG_1, OVRD_SEL, OVRD_VAL_C, OVRD_VAL_T, ovrd, ovrd_val_c, ovrd_val_t);
               `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_IO_M0_CFG_1, TX_IMPD, RX_IMPD, tx_impd, rx_impd );
            end
            `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_0 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
            `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_0 ,  TX_IMPD, RX_IMPD, dq_tx_impd, dq_rx_impd );
            `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_1 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
            `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_1 ,  TX_IMPD, RX_IMPD, dq_tx_impd, dq_rx_impd );
            `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_2 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
            `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_2 ,  TX_IMPD, RX_IMPD, dq_tx_impd, dq_rx_impd );
            `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_3 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
            `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_3 ,  TX_IMPD, RX_IMPD, dq_tx_impd, dq_rx_impd );
            `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_4 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
            `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_4 ,  TX_IMPD, RX_IMPD, dq_tx_impd, dq_rx_impd );
            `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_5 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
            `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_5 ,  TX_IMPD, RX_IMPD, dq_tx_impd, dq_rx_impd );
            `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_6 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
            `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_6 ,  TX_IMPD, RX_IMPD, dq_tx_impd, dq_rx_impd );
            `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_7 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
            `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_7 ,  TX_IMPD, RX_IMPD, dq_tx_impd, dq_rx_impd );
            `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_8 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
            `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_8 ,  TX_IMPD, RX_IMPD, dq_tx_impd, dq_rx_impd );
            `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_IO_CMN_M0_R0_CFG, LPBK_EN, SE_MODE, lb_mode, se_mode);
            `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_IO_CMN_M0_R1_CFG, LPBK_EN, SE_MODE, lb_mode, se_mode);
            if (wck_mode == 1) begin
               `CSR_WRF3(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_IO_M0_CFG_0, OVRD_SEL, OVRD_VAL_C, OVRD_VAL_T, ovrd, ovrd_val_c, ovrd_val_t);
               `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_IO_M0_CFG_0, TX_IMPD, RX_IMPD, tx_impd, rx_impd );
            end else begin
               `CSR_WRF3(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_IO_M0_CFG_1, OVRD_SEL, OVRD_VAL_C, OVRD_VAL_T, ovrd, ovrd_val_c, ovrd_val_t);
               `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_IO_M0_CFG_1, TX_IMPD, RX_IMPD, tx_impd, rx_impd );
            end
            `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_0 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
            `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_0 ,  TX_IMPD, RX_IMPD, dq_tx_impd, dq_rx_impd );
            `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_1 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
            `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_1 ,  TX_IMPD, RX_IMPD, dq_tx_impd, dq_rx_impd );
            `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_2 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
            `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_2 ,  TX_IMPD, RX_IMPD, dq_tx_impd, dq_rx_impd );
            `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_3 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
            `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_3 ,  TX_IMPD, RX_IMPD, dq_tx_impd, dq_rx_impd );
            `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_4 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
            `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_4 ,  TX_IMPD, RX_IMPD, dq_tx_impd, dq_rx_impd );
            `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_5 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
            `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_5 ,  TX_IMPD, RX_IMPD, dq_tx_impd, dq_rx_impd );
            `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_6 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
            `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_6 ,  TX_IMPD, RX_IMPD, dq_tx_impd, dq_rx_impd );
            `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_7 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
            `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_7 ,  TX_IMPD, RX_IMPD, dq_tx_impd, dq_rx_impd );
            `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_8 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
            `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_8 ,  TX_IMPD, RX_IMPD, dq_tx_impd, dq_rx_impd );

         end
         {DQ1}: begin
            `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_IO_CMN_M0_R0_CFG, LPBK_EN, SE_MODE, lb_mode, se_mode);
            `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_IO_CMN_M0_R1_CFG, LPBK_EN, SE_MODE, lb_mode, se_mode);
            if (wck_mode == 1) begin
               `CSR_WRF3(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_IO_M0_CFG_0, OVRD_SEL, OVRD_VAL_C, OVRD_VAL_T, ovrd, ovrd_val_c, ovrd_val_t);
               `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_IO_M0_CFG_0, TX_IMPD, RX_IMPD, tx_impd, rx_impd );
            end else begin
               `CSR_WRF3(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_IO_M0_CFG_1, OVRD_SEL, OVRD_VAL_C, OVRD_VAL_T, ovrd, ovrd_val_c, ovrd_val_t);
               `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_IO_M0_CFG_1, TX_IMPD, RX_IMPD, tx_impd, rx_impd );
            end
            `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_0 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
            `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_0 ,  TX_IMPD, RX_IMPD, dq_tx_impd, dq_rx_impd );
            `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_1 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
            `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_1 ,  TX_IMPD, RX_IMPD, dq_tx_impd, dq_rx_impd );
            `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_2 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
            `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_2 ,  TX_IMPD, RX_IMPD, dq_tx_impd, dq_rx_impd );
            `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_3 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
            `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_3 ,  TX_IMPD, RX_IMPD, dq_tx_impd, dq_rx_impd );
            `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_4 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
            `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_4 ,  TX_IMPD, RX_IMPD, dq_tx_impd, dq_rx_impd );
            `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_5 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
            `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_5 ,  TX_IMPD, RX_IMPD, dq_tx_impd, dq_rx_impd );
            `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_6 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
            `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_6 ,  TX_IMPD, RX_IMPD, dq_tx_impd, dq_rx_impd );
            `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_7 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
            `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_7 ,  TX_IMPD, RX_IMPD, dq_tx_impd, dq_rx_impd );
            `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_8 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
            `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_8 ,  TX_IMPD, RX_IMPD, dq_tx_impd, dq_rx_impd );
            `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_IO_CMN_M0_R0_CFG, LPBK_EN, SE_MODE, lb_mode, se_mode);
            `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_IO_CMN_M0_R1_CFG, LPBK_EN, SE_MODE, lb_mode, se_mode);
            if (wck_mode == 1) begin
               `CSR_WRF3(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_IO_M0_CFG_0, OVRD_SEL, OVRD_VAL_C, OVRD_VAL_T, ovrd, ovrd_val_c, ovrd_val_t);
               `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_IO_M0_CFG_0, TX_IMPD, RX_IMPD, tx_impd, rx_impd );
            end else begin
               `CSR_WRF3(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_IO_M0_CFG_1, OVRD_SEL, OVRD_VAL_C, OVRD_VAL_T, ovrd, ovrd_val_c, ovrd_val_t);
               `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_IO_M0_CFG_1, TX_IMPD, RX_IMPD, tx_impd, rx_impd );
            end
            `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_0 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
            `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_0 ,  TX_IMPD, RX_IMPD, dq_tx_impd, dq_rx_impd );
            `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_1 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
            `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_1 ,  TX_IMPD, RX_IMPD, dq_tx_impd, dq_rx_impd );
            `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_2 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
            `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_2 ,  TX_IMPD, RX_IMPD, dq_tx_impd, dq_rx_impd );
            `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_3 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
            `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_3 ,  TX_IMPD, RX_IMPD, dq_tx_impd, dq_rx_impd );
            `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_4 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
            `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_4 ,  TX_IMPD, RX_IMPD, dq_tx_impd, dq_rx_impd );
            `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_5 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
            `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_5 ,  TX_IMPD, RX_IMPD, dq_tx_impd, dq_rx_impd );
            `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_6 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
            `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_6 ,  TX_IMPD, RX_IMPD, dq_tx_impd, dq_rx_impd );
            `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_7 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
            `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_7 ,  TX_IMPD, RX_IMPD, dq_tx_impd, dq_rx_impd );
            `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_8 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
            `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_8 ,  TX_IMPD, RX_IMPD, dq_tx_impd, dq_rx_impd );
         end
         {CA}: begin
            `CSR_WRF2(DDR_CH0_CA_OFFSET,DDR_CA_DQS_TX_IO_CMN_M0_R0_CFG, LPBK_EN, SE_MODE, lb_mode, se_mode);
            `CSR_WRF2(DDR_CH0_CA_OFFSET,DDR_CA_DQS_TX_IO_CMN_M0_R1_CFG, LPBK_EN, SE_MODE, lb_mode, se_mode);
            `CSR_WRF3(DDR_CH0_CA_OFFSET,DDR_CA_DQS_TX_IO_M0_CFG_0, OVRD_SEL, OVRD_VAL_C, OVRD_VAL_T, ovrd, ovrd_val_c, ovrd_val_t);
            `CSR_WRF2(DDR_CH0_CA_OFFSET,DDR_CA_DQS_TX_IO_M0_CFG_0, TX_IMPD, RX_IMPD, tx_impd, rx_impd );
            `CSR_WRF2(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_IO_M0_CFG_0 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
            `CSR_WRF2(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_IO_M0_CFG_0 ,  TX_IMPD, RX_IMPD, dq_tx_impd, dq_rx_impd );
            `CSR_WRF2(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_IO_M0_CFG_1 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
            `CSR_WRF2(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_IO_M0_CFG_1 ,  TX_IMPD, RX_IMPD, dq_tx_impd, dq_rx_impd );
            `CSR_WRF2(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_IO_M0_CFG_2 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
            `CSR_WRF2(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_IO_M0_CFG_2 ,  TX_IMPD, RX_IMPD, dq_tx_impd, dq_rx_impd );
            `CSR_WRF2(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_IO_M0_CFG_3 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
            `CSR_WRF2(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_IO_M0_CFG_3 ,  TX_IMPD, RX_IMPD, dq_tx_impd, dq_rx_impd );
            `CSR_WRF2(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_IO_M0_CFG_4 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
            `CSR_WRF2(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_IO_M0_CFG_4 ,  TX_IMPD, RX_IMPD, dq_tx_impd, dq_rx_impd );
            `CSR_WRF2(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_IO_M0_CFG_5 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
            `CSR_WRF2(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_IO_M0_CFG_5 ,  TX_IMPD, RX_IMPD, dq_tx_impd, dq_rx_impd );
            `CSR_WRF2(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_IO_M0_CFG_6 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
            `CSR_WRF2(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_IO_M0_CFG_6 ,  TX_IMPD, RX_IMPD, dq_tx_impd, dq_rx_impd );
            `CSR_WRF2(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_IO_M0_CFG_7 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
            `CSR_WRF2(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_IO_M0_CFG_7 ,  TX_IMPD, RX_IMPD, dq_tx_impd, dq_rx_impd );
            `CSR_WRF2(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_IO_M0_CFG_8 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
            `CSR_WRF2(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_IO_M0_CFG_8 ,  TX_IMPD, RX_IMPD, dq_tx_impd, dq_rx_impd );
            `CSR_WRF2(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_IO_M0_CFG_9 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
            `CSR_WRF2(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_IO_M0_CFG_9 ,  TX_IMPD, RX_IMPD, dq_tx_impd, dq_rx_impd );
            `CSR_WRF2(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_IO_M0_CFG_10 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
            `CSR_WRF2(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_IO_M0_CFG_10 ,  TX_IMPD, RX_IMPD, dq_tx_impd, dq_rx_impd );
            `CSR_WRF2(DDR_CH1_CA_OFFSET,DDR_CA_DQS_TX_IO_CMN_M0_R0_CFG, LPBK_EN, SE_MODE, lb_mode, se_mode);
            `CSR_WRF2(DDR_CH1_CA_OFFSET,DDR_CA_DQS_TX_IO_CMN_M0_R1_CFG, LPBK_EN, SE_MODE, lb_mode, se_mode);
            `CSR_WRF3(DDR_CH1_CA_OFFSET,DDR_CA_DQS_TX_IO_M0_CFG_0, OVRD_SEL, OVRD_VAL_C, OVRD_VAL_T, ovrd, ovrd_val_c, ovrd_val_t);
            `CSR_WRF2(DDR_CH1_CA_OFFSET,DDR_CA_DQS_TX_IO_M0_CFG_0, TX_IMPD, RX_IMPD, tx_impd, rx_impd );
            `CSR_WRF2(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_IO_M0_CFG_0 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
            `CSR_WRF2(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_IO_M0_CFG_0 ,  TX_IMPD, RX_IMPD, dq_tx_impd, dq_rx_impd );
            `CSR_WRF2(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_IO_M0_CFG_1 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
            `CSR_WRF2(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_IO_M0_CFG_1 ,  TX_IMPD, RX_IMPD, dq_tx_impd, dq_rx_impd );
            `CSR_WRF2(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_IO_M0_CFG_2 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
            `CSR_WRF2(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_IO_M0_CFG_2 ,  TX_IMPD, RX_IMPD, dq_tx_impd, dq_rx_impd );
            `CSR_WRF2(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_IO_M0_CFG_3 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
            `CSR_WRF2(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_IO_M0_CFG_3 ,  TX_IMPD, RX_IMPD, dq_tx_impd, dq_rx_impd );
            `CSR_WRF2(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_IO_M0_CFG_4 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
            `CSR_WRF2(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_IO_M0_CFG_4 ,  TX_IMPD, RX_IMPD, dq_tx_impd, dq_rx_impd );
            `CSR_WRF2(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_IO_M0_CFG_5 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
            `CSR_WRF2(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_IO_M0_CFG_5 ,  TX_IMPD, RX_IMPD, dq_tx_impd, dq_rx_impd );
            `CSR_WRF2(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_IO_M0_CFG_6 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
            `CSR_WRF2(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_IO_M0_CFG_6 ,  TX_IMPD, RX_IMPD, dq_tx_impd, dq_rx_impd );
            `CSR_WRF2(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_IO_M0_CFG_7 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
            `CSR_WRF2(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_IO_M0_CFG_7 ,  TX_IMPD, RX_IMPD, dq_tx_impd, dq_rx_impd );
            `CSR_WRF2(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_IO_M0_CFG_8 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
            `CSR_WRF2(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_IO_M0_CFG_8 ,  TX_IMPD, RX_IMPD, dq_tx_impd, dq_rx_impd );
            `CSR_WRF2(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_IO_M0_CFG_9 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
            `CSR_WRF2(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_IO_M0_CFG_9 ,  TX_IMPD, RX_IMPD, dq_tx_impd, dq_rx_impd );
            `CSR_WRF2(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_IO_M0_CFG_10 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
            `CSR_WRF2(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_IO_M0_CFG_10 ,  TX_IMPD, RX_IMPD, dq_tx_impd, dq_rx_impd );
         end
         {DQ_ALL}: begin
            `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_IO_CMN_M0_R0_CFG, LPBK_EN, SE_MODE, lb_mode, se_mode);
            `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_IO_CMN_M0_R1_CFG, LPBK_EN, SE_MODE, lb_mode, se_mode);
            if (wck_mode == 1) begin
               `CSR_WRF3(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_IO_M0_CFG_0, OVRD_SEL, OVRD_VAL_C, OVRD_VAL_T, ovrd, ovrd_val_c, ovrd_val_t);
               `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_IO_M0_CFG_0, TX_IMPD, RX_IMPD, tx_impd, rx_impd );
            end else begin
               `CSR_WRF3(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_IO_M0_CFG_1, OVRD_SEL, OVRD_VAL_C, OVRD_VAL_T, ovrd, ovrd_val_c, ovrd_val_t);
               `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_IO_M0_CFG_1, TX_IMPD, RX_IMPD, tx_impd, rx_impd );
            end
            `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_IO_CMN_M0_R0_CFG, LPBK_EN, SE_MODE, lb_mode, se_mode);
            `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_IO_CMN_M0_R1_CFG, LPBK_EN, SE_MODE, lb_mode, se_mode);
            if (wck_mode == 1) begin
               `CSR_WRF3(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_IO_M0_CFG_0, OVRD_SEL, OVRD_VAL_C, OVRD_VAL_T, ovrd, ovrd_val_c, ovrd_val_t);
               `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_IO_M0_CFG_0, TX_IMPD, RX_IMPD, tx_impd, rx_impd );
            end else begin
               `CSR_WRF3(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_IO_M0_CFG_1, OVRD_SEL, OVRD_VAL_C, OVRD_VAL_T, ovrd, ovrd_val_c, ovrd_val_t);
               `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_IO_M0_CFG_1, TX_IMPD, RX_IMPD, tx_impd, rx_impd );
            end
            `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_0 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
            `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_0 ,  TX_IMPD, RX_IMPD, dq_tx_impd, dq_rx_impd );
            `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_0 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
            `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_0 ,  TX_IMPD, RX_IMPD, dq_tx_impd, dq_rx_impd );
            `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_1 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
            `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_1 ,  TX_IMPD, RX_IMPD, dq_tx_impd, dq_rx_impd );
            `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_1 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
            `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_1 ,  TX_IMPD, RX_IMPD, dq_tx_impd, dq_rx_impd );
            `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_2 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
            `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_2 ,  TX_IMPD, RX_IMPD, dq_tx_impd, dq_rx_impd );
            `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_2 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
            `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_2 ,  TX_IMPD, RX_IMPD, dq_tx_impd, dq_rx_impd );
            `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_3 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
            `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_3 ,  TX_IMPD, RX_IMPD, dq_tx_impd, dq_rx_impd );
            `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_3 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
            `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_3 ,  TX_IMPD, RX_IMPD, dq_tx_impd, dq_rx_impd );
            `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_4 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
            `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_4 ,  TX_IMPD, RX_IMPD, dq_tx_impd, dq_rx_impd );
            `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_4 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
            `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_4 ,  TX_IMPD, RX_IMPD, dq_tx_impd, dq_rx_impd );
            `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_5 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
            `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_5 ,  TX_IMPD, RX_IMPD, dq_tx_impd, dq_rx_impd );
            `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_5 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
            `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_5 ,  TX_IMPD, RX_IMPD, dq_tx_impd, dq_rx_impd );
            `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_6 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
            `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_6 ,  TX_IMPD, RX_IMPD, dq_tx_impd, dq_rx_impd );
            `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_6 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
            `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_6 ,  TX_IMPD, RX_IMPD, dq_tx_impd, dq_rx_impd );
            `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_7 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
            `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_7 ,  TX_IMPD, RX_IMPD, dq_tx_impd, dq_rx_impd );
            `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_7 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
            `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_7 ,  TX_IMPD, RX_IMPD, dq_tx_impd, dq_rx_impd );
            `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_8 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
            `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_8 ,  TX_IMPD, RX_IMPD, dq_tx_impd, dq_rx_impd );
            `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_8 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
            `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_8 ,  TX_IMPD, RX_IMPD, dq_tx_impd, dq_rx_impd );
            `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_IO_CMN_M0_R0_CFG, LPBK_EN, SE_MODE, lb_mode, se_mode);
            `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_IO_CMN_M0_R1_CFG, LPBK_EN, SE_MODE, lb_mode, se_mode);
            if (wck_mode == 1) begin
               `CSR_WRF3(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_IO_M0_CFG_0, OVRD_SEL, OVRD_VAL_C, OVRD_VAL_T, ovrd, ovrd_val_c, ovrd_val_t);
               `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_IO_M0_CFG_0, TX_IMPD, RX_IMPD, tx_impd, rx_impd );
            end else begin
               `CSR_WRF3(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_IO_M0_CFG_1, OVRD_SEL, OVRD_VAL_C, OVRD_VAL_T, ovrd, ovrd_val_c, ovrd_val_t);
               `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_IO_M0_CFG_1, TX_IMPD, RX_IMPD, tx_impd, rx_impd );
            end
            `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_IO_CMN_M0_R0_CFG, LPBK_EN, SE_MODE, lb_mode, se_mode);
            `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_IO_CMN_M0_R1_CFG, LPBK_EN, SE_MODE, lb_mode, se_mode);
            if (wck_mode == 1) begin
               `CSR_WRF3(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_IO_M0_CFG_0, OVRD_SEL, OVRD_VAL_C, OVRD_VAL_T, ovrd, ovrd_val_c, ovrd_val_t);
               `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_IO_M0_CFG_0, TX_IMPD, RX_IMPD, tx_impd, rx_impd );
            end else begin
               `CSR_WRF3(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_IO_M0_CFG_1, OVRD_SEL, OVRD_VAL_C, OVRD_VAL_T, ovrd, ovrd_val_c, ovrd_val_t);
               `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_IO_M0_CFG_1, TX_IMPD, RX_IMPD, tx_impd, rx_impd );
            end
            `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_0 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
            `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_0 ,  TX_IMPD, RX_IMPD, dq_tx_impd, dq_rx_impd );
            `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_0 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
            `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_0 ,  TX_IMPD, RX_IMPD, dq_tx_impd, dq_rx_impd );
            `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_1 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
            `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_1 ,  TX_IMPD, RX_IMPD, dq_tx_impd, dq_rx_impd );
            `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_1 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
            `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_1 ,  TX_IMPD, RX_IMPD, dq_tx_impd, dq_rx_impd );
            `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_2 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
            `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_2 ,  TX_IMPD, RX_IMPD, dq_tx_impd, dq_rx_impd );
            `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_2 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
            `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_2 ,  TX_IMPD, RX_IMPD, dq_tx_impd, dq_rx_impd );
            `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_3 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
            `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_3 ,  TX_IMPD, RX_IMPD, dq_tx_impd, dq_rx_impd );
            `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_3 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
            `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_3 ,  TX_IMPD, RX_IMPD, dq_tx_impd, dq_rx_impd );
            `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_4 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
            `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_4 ,  TX_IMPD, RX_IMPD, dq_tx_impd, dq_rx_impd );
            `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_4 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
            `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_4 ,  TX_IMPD, RX_IMPD, dq_tx_impd, dq_rx_impd );
            `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_5 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
            `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_5 ,  TX_IMPD, RX_IMPD, dq_tx_impd, dq_rx_impd );
            `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_5 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
            `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_5 ,  TX_IMPD, RX_IMPD, dq_tx_impd, dq_rx_impd );
            `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_6 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
            `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_6 ,  TX_IMPD, RX_IMPD, dq_tx_impd, dq_rx_impd );
            `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_6 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
            `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_6 ,  TX_IMPD, RX_IMPD, dq_tx_impd, dq_rx_impd );
            `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_7 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
            `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_7 ,  TX_IMPD, RX_IMPD, dq_tx_impd, dq_rx_impd );
            `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_7 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
            `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_7 ,  TX_IMPD, RX_IMPD, dq_tx_impd, dq_rx_impd );
            `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_8 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
            `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_8 ,  TX_IMPD, RX_IMPD, dq_tx_impd, dq_rx_impd );
            `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_8 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
            `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_8 ,  TX_IMPD, RX_IMPD, dq_tx_impd, dq_rx_impd );
         end
         {ALL}: begin
            `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_IO_CMN_M0_R0_CFG, LPBK_EN, SE_MODE, lb_mode, se_mode);
            `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_IO_CMN_M0_R1_CFG, LPBK_EN, SE_MODE, lb_mode, se_mode);
            if (wck_mode == 1) begin
               `CSR_WRF3(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_IO_M0_CFG_0, OVRD_SEL, OVRD_VAL_C, OVRD_VAL_T, ovrd, ovrd_val_c, ovrd_val_t);
               `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_IO_M0_CFG_0, TX_IMPD, RX_IMPD, tx_impd, rx_impd );
            end else begin
               `CSR_WRF3(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_IO_M0_CFG_1, OVRD_SEL, OVRD_VAL_C, OVRD_VAL_T, ovrd, ovrd_val_c, ovrd_val_t);
               `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_IO_M0_CFG_1, TX_IMPD, RX_IMPD, tx_impd, rx_impd );
            end
            `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_IO_CMN_M0_R0_CFG, LPBK_EN, SE_MODE, lb_mode, se_mode);
            `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_IO_CMN_M0_R1_CFG, LPBK_EN, SE_MODE, lb_mode, se_mode);
            if (wck_mode == 1) begin
               `CSR_WRF3(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_IO_M0_CFG_0, OVRD_SEL, OVRD_VAL_C, OVRD_VAL_T, ovrd, ovrd_val_c, ovrd_val_t);
               `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_IO_M0_CFG_0, TX_IMPD, RX_IMPD, tx_impd, rx_impd );
            end else begin
               `CSR_WRF3(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_IO_M0_CFG_1, OVRD_SEL, OVRD_VAL_C, OVRD_VAL_T, ovrd, ovrd_val_c, ovrd_val_t);
               `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_IO_M0_CFG_1, TX_IMPD, RX_IMPD, tx_impd, rx_impd );
            end
            `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_0 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
            `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_0 ,  TX_IMPD, RX_IMPD, dq_tx_impd, dq_rx_impd );
            `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_0 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
            `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_0 ,  TX_IMPD, RX_IMPD, dq_tx_impd, dq_rx_impd );
            `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_1 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
            `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_1 ,  TX_IMPD, RX_IMPD, dq_tx_impd, dq_rx_impd );
            `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_1 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
            `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_1 ,  TX_IMPD, RX_IMPD, dq_tx_impd, dq_rx_impd );
            `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_2 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
            `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_2 ,  TX_IMPD, RX_IMPD, dq_tx_impd, dq_rx_impd );
            `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_2 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
            `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_2 ,  TX_IMPD, RX_IMPD, dq_tx_impd, dq_rx_impd );
            `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_3 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
            `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_3 ,  TX_IMPD, RX_IMPD, dq_tx_impd, dq_rx_impd );
            `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_3 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
            `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_3 ,  TX_IMPD, RX_IMPD, dq_tx_impd, dq_rx_impd );
            `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_4 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
            `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_4 ,  TX_IMPD, RX_IMPD, dq_tx_impd, dq_rx_impd );
            `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_4 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
            `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_4 ,  TX_IMPD, RX_IMPD, dq_tx_impd, dq_rx_impd );
            `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_5 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
            `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_5 ,  TX_IMPD, RX_IMPD, dq_tx_impd, dq_rx_impd );
            `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_5 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
            `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_5 ,  TX_IMPD, RX_IMPD, dq_tx_impd, dq_rx_impd );
            `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_6 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
            `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_6 ,  TX_IMPD, RX_IMPD, dq_tx_impd, dq_rx_impd );
            `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_6 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
            `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_6 ,  TX_IMPD, RX_IMPD, dq_tx_impd, dq_rx_impd );
            `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_7 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
            `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_7 ,  TX_IMPD, RX_IMPD, dq_tx_impd, dq_rx_impd );
            `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_7 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
            `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_7 ,  TX_IMPD, RX_IMPD, dq_tx_impd, dq_rx_impd );
            `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_8 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
            `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_8 ,  TX_IMPD, RX_IMPD, dq_tx_impd, dq_rx_impd );
            `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_8 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
            `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_8 ,  TX_IMPD, RX_IMPD, dq_tx_impd, dq_rx_impd );
            `CSR_WRF2(DDR_CH0_CA_OFFSET,DDR_CA_DQS_TX_IO_CMN_M0_R0_CFG, LPBK_EN, SE_MODE, lb_mode, se_mode);
            `CSR_WRF2(DDR_CH0_CA_OFFSET,DDR_CA_DQS_TX_IO_CMN_M0_R1_CFG, LPBK_EN, SE_MODE, lb_mode, se_mode);
            `CSR_WRF3(DDR_CH0_CA_OFFSET,DDR_CA_DQS_TX_IO_M0_CFG_0, OVRD_SEL, OVRD_VAL_C, OVRD_VAL_T, ovrd, ovrd_val_c, ovrd_val_t);
            `CSR_WRF2(DDR_CH0_CA_OFFSET,DDR_CA_DQS_TX_IO_M0_CFG_0, TX_IMPD, RX_IMPD, tx_impd, rx_impd );
            `CSR_WRF2(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_IO_M0_CFG_0 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
            `CSR_WRF2(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_IO_M0_CFG_0 ,  TX_IMPD, RX_IMPD, dq_tx_impd, dq_rx_impd );
            `CSR_WRF2(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_IO_M0_CFG_1 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
            `CSR_WRF2(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_IO_M0_CFG_1 ,  TX_IMPD, RX_IMPD, dq_tx_impd, dq_rx_impd );
            `CSR_WRF2(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_IO_M0_CFG_2 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
            `CSR_WRF2(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_IO_M0_CFG_2 ,  TX_IMPD, RX_IMPD, dq_tx_impd, dq_rx_impd );
            `CSR_WRF2(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_IO_M0_CFG_3 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
            `CSR_WRF2(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_IO_M0_CFG_3 ,  TX_IMPD, RX_IMPD, dq_tx_impd, dq_rx_impd );
            `CSR_WRF2(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_IO_M0_CFG_4 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
            `CSR_WRF2(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_IO_M0_CFG_4 ,  TX_IMPD, RX_IMPD, dq_tx_impd, dq_rx_impd );
            `CSR_WRF2(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_IO_M0_CFG_5 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
            `CSR_WRF2(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_IO_M0_CFG_5 ,  TX_IMPD, RX_IMPD, dq_tx_impd, dq_rx_impd );
            `CSR_WRF2(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_IO_M0_CFG_6 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
            `CSR_WRF2(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_IO_M0_CFG_6 ,  TX_IMPD, RX_IMPD, dq_tx_impd, dq_rx_impd );
            `CSR_WRF2(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_IO_M0_CFG_7 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
            `CSR_WRF2(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_IO_M0_CFG_7 ,  TX_IMPD, RX_IMPD, dq_tx_impd, dq_rx_impd );
            `CSR_WRF2(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_IO_M0_CFG_8 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
            `CSR_WRF2(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_IO_M0_CFG_8 ,  TX_IMPD, RX_IMPD, dq_tx_impd, dq_rx_impd );
            `CSR_WRF2(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_IO_M0_CFG_9 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
            `CSR_WRF2(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_IO_M0_CFG_9 ,  TX_IMPD, RX_IMPD, dq_tx_impd, dq_rx_impd );
            `CSR_WRF2(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_IO_M0_CFG_10 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
            `CSR_WRF2(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_IO_M0_CFG_10 ,  TX_IMPD, RX_IMPD, dq_tx_impd, dq_rx_impd );
            `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_IO_CMN_M0_R0_CFG, LPBK_EN, SE_MODE, lb_mode, se_mode);
            `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_IO_CMN_M0_R1_CFG, LPBK_EN, SE_MODE, lb_mode, se_mode);
            if (wck_mode == 1) begin
               `CSR_WRF3(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_IO_M0_CFG_0, OVRD_SEL, OVRD_VAL_C, OVRD_VAL_T, ovrd, ovrd_val_c, ovrd_val_t);
               `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_IO_M0_CFG_0, TX_IMPD, RX_IMPD, tx_impd, rx_impd );
            end else begin
               `CSR_WRF3(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_IO_M0_CFG_1, OVRD_SEL, OVRD_VAL_C, OVRD_VAL_T, ovrd, ovrd_val_c, ovrd_val_t);
               `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_IO_M0_CFG_1, TX_IMPD, RX_IMPD, tx_impd, rx_impd );
            end
            `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_IO_CMN_M0_R0_CFG, LPBK_EN, SE_MODE, lb_mode, se_mode);
            `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_IO_CMN_M0_R1_CFG, LPBK_EN, SE_MODE, lb_mode, se_mode);
            if (wck_mode == 1) begin
               `CSR_WRF3(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_IO_M0_CFG_0, OVRD_SEL, OVRD_VAL_C, OVRD_VAL_T, ovrd, ovrd_val_c, ovrd_val_t);
               `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_IO_M0_CFG_0, TX_IMPD, RX_IMPD, tx_impd, rx_impd );
            end else begin
               `CSR_WRF3(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_IO_M0_CFG_1, OVRD_SEL, OVRD_VAL_C, OVRD_VAL_T, ovrd, ovrd_val_c, ovrd_val_t);
               `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_IO_M0_CFG_1, TX_IMPD, RX_IMPD, tx_impd, rx_impd );
            end
            `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_0 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
            `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_0 ,  TX_IMPD, RX_IMPD, dq_tx_impd, dq_rx_impd );
            `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_0 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
            `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_0 ,  TX_IMPD, RX_IMPD, dq_tx_impd, dq_rx_impd );
            `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_1 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
            `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_1 ,  TX_IMPD, RX_IMPD, dq_tx_impd, dq_rx_impd );
            `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_1 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
            `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_1 ,  TX_IMPD, RX_IMPD, dq_tx_impd, dq_rx_impd );
            `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_2 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
            `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_2 ,  TX_IMPD, RX_IMPD, dq_tx_impd, dq_rx_impd );
            `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_2 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
            `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_2 ,  TX_IMPD, RX_IMPD, dq_tx_impd, dq_rx_impd );
            `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_3 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
            `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_3 ,  TX_IMPD, RX_IMPD, dq_tx_impd, dq_rx_impd );
            `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_3 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
            `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_3 ,  TX_IMPD, RX_IMPD, dq_tx_impd, dq_rx_impd );
            `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_4 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
            `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_4 ,  TX_IMPD, RX_IMPD, dq_tx_impd, dq_rx_impd );
            `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_4 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
            `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_4 ,  TX_IMPD, RX_IMPD, dq_tx_impd, dq_rx_impd );
            `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_5 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
            `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_5 ,  TX_IMPD, RX_IMPD, dq_tx_impd, dq_rx_impd );
            `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_5 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
            `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_5 ,  TX_IMPD, RX_IMPD, dq_tx_impd, dq_rx_impd );
            `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_6 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
            `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_6 ,  TX_IMPD, RX_IMPD, dq_tx_impd, dq_rx_impd );
            `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_6 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
            `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_6 ,  TX_IMPD, RX_IMPD, dq_tx_impd, dq_rx_impd );
            `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_7 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
            `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_7 ,  TX_IMPD, RX_IMPD, dq_tx_impd, dq_rx_impd );
            `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_7 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
            `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_7 ,  TX_IMPD, RX_IMPD, dq_tx_impd, dq_rx_impd );
            `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_8 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
            `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_8 ,  TX_IMPD, RX_IMPD, dq_tx_impd, dq_rx_impd );
            `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_8 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
            `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_IO_M0_CFG_8 ,  TX_IMPD, RX_IMPD, dq_tx_impd, dq_rx_impd );
            `CSR_WRF2(DDR_CH1_CA_OFFSET,DDR_CA_DQS_TX_IO_CMN_M0_R0_CFG, LPBK_EN, SE_MODE, lb_mode, se_mode);
            `CSR_WRF2(DDR_CH1_CA_OFFSET,DDR_CA_DQS_TX_IO_CMN_M0_R1_CFG, LPBK_EN, SE_MODE, lb_mode, se_mode);
            `CSR_WRF3(DDR_CH1_CA_OFFSET,DDR_CA_DQS_TX_IO_M0_CFG_0, OVRD_SEL, OVRD_VAL_C, OVRD_VAL_T, ovrd, ovrd_val_c, ovrd_val_t);
            `CSR_WRF2(DDR_CH1_CA_OFFSET,DDR_CA_DQS_TX_IO_M0_CFG_0, TX_IMPD, RX_IMPD, tx_impd, rx_impd );
            `CSR_WRF2(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_IO_M0_CFG_0 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
            `CSR_WRF2(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_IO_M0_CFG_0 ,  TX_IMPD, RX_IMPD, dq_tx_impd, dq_rx_impd );
            `CSR_WRF2(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_IO_M0_CFG_1 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
            `CSR_WRF2(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_IO_M0_CFG_1 ,  TX_IMPD, RX_IMPD, dq_tx_impd, dq_rx_impd );
            `CSR_WRF2(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_IO_M0_CFG_2 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
            `CSR_WRF2(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_IO_M0_CFG_2 ,  TX_IMPD, RX_IMPD, dq_tx_impd, dq_rx_impd );
            `CSR_WRF2(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_IO_M0_CFG_3 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
            `CSR_WRF2(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_IO_M0_CFG_3 ,  TX_IMPD, RX_IMPD, dq_tx_impd, dq_rx_impd );
            `CSR_WRF2(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_IO_M0_CFG_4 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
            `CSR_WRF2(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_IO_M0_CFG_4 ,  TX_IMPD, RX_IMPD, dq_tx_impd, dq_rx_impd );
            `CSR_WRF2(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_IO_M0_CFG_5 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
            `CSR_WRF2(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_IO_M0_CFG_5 ,  TX_IMPD, RX_IMPD, dq_tx_impd, dq_rx_impd );
            `CSR_WRF2(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_IO_M0_CFG_6 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
            `CSR_WRF2(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_IO_M0_CFG_6 ,  TX_IMPD, RX_IMPD, dq_tx_impd, dq_rx_impd );
            `CSR_WRF2(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_IO_M0_CFG_7 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
            `CSR_WRF2(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_IO_M0_CFG_7 ,  TX_IMPD, RX_IMPD, dq_tx_impd, dq_rx_impd );
            `CSR_WRF2(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_IO_M0_CFG_8 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
            `CSR_WRF2(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_IO_M0_CFG_8 ,  TX_IMPD, RX_IMPD, dq_tx_impd, dq_rx_impd );
            `CSR_WRF2(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_IO_M0_CFG_9 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
            `CSR_WRF2(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_IO_M0_CFG_9 ,  TX_IMPD, RX_IMPD, dq_tx_impd, dq_rx_impd );
            `CSR_WRF2(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_IO_M0_CFG_10 ,  OVRD_SEL, OVRD_VAL, dq_ovrd, dq_ovrd_val );
            `CSR_WRF2(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_IO_M0_CFG_10 ,  TX_IMPD, RX_IMPD, dq_tx_impd, dq_rx_impd );
         end
      endcase

    end
endtask

task automatic set_dq_dqs_rcvr_cfg;
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
                `CSR_WRF3(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_RX_IO_CMN_M0_R0_CFG, FB_EN, DCPATH_EN, SE_MODE, fb_en, dcpath_en, se_mode);
                `CSR_WRF3(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_RX_IO_CMN_M0_R0_CFG, FB_EN, DCPATH_EN, SE_MODE, fb_en, dcpath_en, se_mode);
            end
            {RANK1,DQ0}: begin
                `CSR_WRF3(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_RX_IO_CMN_M0_R1_CFG, FB_EN, DCPATH_EN, SE_MODE, fb_en, dcpath_en, se_mode);
                `CSR_WRF3(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_RX_IO_CMN_M0_R1_CFG, FB_EN, DCPATH_EN, SE_MODE, fb_en, dcpath_en, se_mode);
            end
            {RANK_ALL,DQ0}: begin
                `CSR_WRF3(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_RX_IO_CMN_M0_R0_CFG, FB_EN, DCPATH_EN, SE_MODE, fb_en, dcpath_en, se_mode);
                `CSR_WRF3(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_RX_IO_CMN_M0_R1_CFG, FB_EN, DCPATH_EN, SE_MODE, fb_en, dcpath_en, se_mode);
                `CSR_WRF3(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_RX_IO_CMN_M0_R0_CFG, FB_EN, DCPATH_EN, SE_MODE, fb_en, dcpath_en, se_mode);
                `CSR_WRF3(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_RX_IO_CMN_M0_R1_CFG, FB_EN, DCPATH_EN, SE_MODE, fb_en, dcpath_en, se_mode);
            end
            {RANK0,DQ1}: begin
                `CSR_WRF3(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_RX_IO_CMN_M0_R0_CFG, FB_EN, DCPATH_EN, SE_MODE, fb_en, dcpath_en, se_mode);
                `CSR_WRF3(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_RX_IO_CMN_M0_R0_CFG, FB_EN, DCPATH_EN, SE_MODE, fb_en, dcpath_en, se_mode);
            end
            {RANK1,DQ1}: begin
                `CSR_WRF3(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_RX_IO_CMN_M0_R1_CFG, FB_EN, DCPATH_EN, SE_MODE, fb_en, dcpath_en, se_mode);
                `CSR_WRF3(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_RX_IO_CMN_M0_R1_CFG, FB_EN, DCPATH_EN, SE_MODE, fb_en, dcpath_en, se_mode);
            end
            {RANK_ALL,DQ1}: begin
                `CSR_WRF3(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_RX_IO_CMN_M0_R0_CFG, FB_EN, DCPATH_EN, SE_MODE, fb_en, dcpath_en, se_mode);
                `CSR_WRF3(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_RX_IO_CMN_M0_R1_CFG, FB_EN, DCPATH_EN, SE_MODE, fb_en, dcpath_en, se_mode);
                `CSR_WRF3(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_RX_IO_CMN_M0_R0_CFG, FB_EN, DCPATH_EN, SE_MODE, fb_en, dcpath_en, se_mode);
                `CSR_WRF3(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_RX_IO_CMN_M0_R1_CFG, FB_EN, DCPATH_EN, SE_MODE, fb_en, dcpath_en, se_mode);
            end
            {RANK0,DQ_ALL}: begin
                `CSR_WRF3(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_RX_IO_CMN_M0_R0_CFG, FB_EN, DCPATH_EN, SE_MODE, fb_en, dcpath_en, se_mode);
                `CSR_WRF3(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_RX_IO_CMN_M0_R0_CFG, FB_EN, DCPATH_EN, SE_MODE, fb_en, dcpath_en, se_mode);
                `CSR_WRF3(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_RX_IO_CMN_M0_R0_CFG, FB_EN, DCPATH_EN, SE_MODE, fb_en, dcpath_en, se_mode);
                `CSR_WRF3(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_RX_IO_CMN_M0_R0_CFG, FB_EN, DCPATH_EN, SE_MODE, fb_en, dcpath_en, se_mode);
            end
            {RANK1,DQ_ALL}: begin
                `CSR_WRF3(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_RX_IO_CMN_M0_R1_CFG, FB_EN, DCPATH_EN, SE_MODE, fb_en, dcpath_en, se_mode);
                `CSR_WRF3(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_RX_IO_CMN_M0_R1_CFG, FB_EN, DCPATH_EN, SE_MODE, fb_en, dcpath_en, se_mode);
                `CSR_WRF3(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_RX_IO_CMN_M0_R1_CFG, FB_EN, DCPATH_EN, SE_MODE, fb_en, dcpath_en, se_mode);
                `CSR_WRF3(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_RX_IO_CMN_M0_R1_CFG, FB_EN, DCPATH_EN, SE_MODE, fb_en, dcpath_en, se_mode);
            end
            {RANK_ALL,DQ_ALL}: begin
                `CSR_WRF3(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_RX_IO_CMN_M0_R0_CFG, FB_EN, DCPATH_EN, SE_MODE, fb_en, dcpath_en, se_mode);
                `CSR_WRF3(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_RX_IO_CMN_M0_R1_CFG, FB_EN, DCPATH_EN, SE_MODE, fb_en, dcpath_en, se_mode);
                `CSR_WRF3(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_RX_IO_CMN_M0_R0_CFG, FB_EN, DCPATH_EN, SE_MODE, fb_en, dcpath_en, se_mode);
                `CSR_WRF3(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_RX_IO_CMN_M0_R1_CFG, FB_EN, DCPATH_EN, SE_MODE, fb_en, dcpath_en, se_mode);
                `CSR_WRF3(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_RX_IO_CMN_M0_R0_CFG, FB_EN, DCPATH_EN, SE_MODE, fb_en, dcpath_en, se_mode);
                `CSR_WRF3(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_RX_IO_CMN_M0_R1_CFG, FB_EN, DCPATH_EN, SE_MODE, fb_en, dcpath_en, se_mode);
                `CSR_WRF3(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_RX_IO_CMN_M0_R0_CFG, FB_EN, DCPATH_EN, SE_MODE, fb_en, dcpath_en, se_mode);
                `CSR_WRF3(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_RX_IO_CMN_M0_R1_CFG, FB_EN, DCPATH_EN, SE_MODE, fb_en, dcpath_en, se_mode);
            end
        endcase
        case({rank_sel,byte_sel})
            {RANK0,DQ0}: begin
                `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_RX_IO_M0_R0_CFG_1,DLY_CTRL_T, DLY_CTRL_C, dly , dly);
                `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_RX_IO_M0_R0_CFG_1,DLY_CTRL_T, DLY_CTRL_C, dly , dly);
            end
            {RANK1,DQ0}: begin
                `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_RX_IO_M0_R1_CFG_1,DLY_CTRL_T, DLY_CTRL_C, dly, dly);
                `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_RX_IO_M0_R1_CFG_1,DLY_CTRL_T, DLY_CTRL_C, dly, dly);
            end
            {RANK_ALL,DQ0}: begin
                `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_RX_IO_M0_R0_CFG_1,DLY_CTRL_T, DLY_CTRL_C, dly, dly);
                `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_RX_IO_M0_R1_CFG_1,DLY_CTRL_T, DLY_CTRL_C, dly, dly);
                `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_RX_IO_M0_R0_CFG_1,DLY_CTRL_T, DLY_CTRL_C, dly, dly);
                `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_RX_IO_M0_R1_CFG_1,DLY_CTRL_T, DLY_CTRL_C, dly, dly);
            end
            {RANK0,DQ1}: begin
                `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_RX_IO_M0_R0_CFG_1,DLY_CTRL_T, DLY_CTRL_C, dly, dly);
                `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_RX_IO_M0_R0_CFG_1,DLY_CTRL_T, DLY_CTRL_C, dly, dly);
            end
            {RANK1,DQ1}: begin
                `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_RX_IO_M0_R1_CFG_1,DLY_CTRL_T, DLY_CTRL_C, dly, dly);
                `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_RX_IO_M0_R1_CFG_1,DLY_CTRL_T, DLY_CTRL_C, dly, dly);
            end
            {RANK_ALL,DQ1}: begin
                `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_RX_IO_M0_R0_CFG_1,DLY_CTRL_T, DLY_CTRL_C, dly, dly);
                `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_RX_IO_M0_R1_CFG_1,DLY_CTRL_T, DLY_CTRL_C, dly, dly);
                `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_RX_IO_M0_R0_CFG_1,DLY_CTRL_T, DLY_CTRL_C, dly, dly);
                `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_RX_IO_M0_R1_CFG_1,DLY_CTRL_T, DLY_CTRL_C, dly, dly);
            end
            {RANK0,DQ_ALL}: begin
                `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_RX_IO_M0_R0_CFG_1,DLY_CTRL_T, DLY_CTRL_C, dly, dly);
                `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_RX_IO_M0_R0_CFG_1,DLY_CTRL_T, DLY_CTRL_C, dly, dly);
                `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_RX_IO_M0_R0_CFG_1,DLY_CTRL_T, DLY_CTRL_C, dly, dly);
                `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_RX_IO_M0_R0_CFG_1,DLY_CTRL_T, DLY_CTRL_C, dly, dly);
            end
            {RANK1,DQ_ALL}: begin
                `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_RX_IO_M0_R1_CFG_1,DLY_CTRL_T, DLY_CTRL_C, dly, dly);
                `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_RX_IO_M0_R1_CFG_1,DLY_CTRL_T, DLY_CTRL_C, dly, dly);
                `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_RX_IO_M0_R1_CFG_1,DLY_CTRL_T, DLY_CTRL_C, dly, dly);
                `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_RX_IO_M0_R1_CFG_1,DLY_CTRL_T, DLY_CTRL_C, dly, dly);
            end
            {RANK_ALL,DQ_ALL}: begin
                `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_RX_IO_M0_R0_CFG_1,DLY_CTRL_T, DLY_CTRL_C, dly, dly);
                `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_RX_IO_M0_R1_CFG_1,DLY_CTRL_T, DLY_CTRL_C, dly, dly);
                `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_RX_IO_M0_R0_CFG_1,DLY_CTRL_T, DLY_CTRL_C, dly, dly);
                `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_RX_IO_M0_R1_CFG_1,DLY_CTRL_T, DLY_CTRL_C, dly, dly);
                `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_RX_IO_M0_R0_CFG_1,DLY_CTRL_T, DLY_CTRL_C, dly, dly);
                `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_RX_IO_M0_R1_CFG_1,DLY_CTRL_T, DLY_CTRL_C, dly, dly);
                `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_RX_IO_M0_R0_CFG_1,DLY_CTRL_T, DLY_CTRL_C, dly, dly);
                `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_RX_IO_M0_R1_CFG_1,DLY_CTRL_T, DLY_CTRL_C, dly, dly);
            end
        endcase
    end
endtask

task automatic set_rdqs_dly;
    input byte_sel_t  byte_sel;
    input rank_sel_t  rank_sel;
    input logic [7:0] r0_tdly;
    input logic [7:0] r0_cdly;
    input logic [7:0] r1_tdly;
    input logic [7:0] r1_cdly;
    begin
        case({rank_sel,byte_sel})
            {RANK0,DQ0}: begin
                `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_RX_IO_M0_R0_CFG_1,DLY_CTRL_T, DLY_CTRL_C, r0_tdly, r0_cdly);
                `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_RX_IO_M0_R0_CFG_1,DLY_CTRL_T, DLY_CTRL_C, r0_tdly, r0_cdly);
            end
            {RANK1,DQ0}: begin
                `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_RX_IO_M0_R1_CFG_1,DLY_CTRL_T, DLY_CTRL_C, r1_tdly, r1_cdly);
                `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_RX_IO_M0_R1_CFG_1,DLY_CTRL_T, DLY_CTRL_C, r1_tdly, r1_cdly);
            end
            {RANK_ALL,DQ0}: begin
                `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_RX_IO_M0_R0_CFG_1,DLY_CTRL_T, DLY_CTRL_C, r0_tdly, r0_cdly);
                `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_RX_IO_M0_R1_CFG_1,DLY_CTRL_T, DLY_CTRL_C, r1_tdly, r1_cdly);
                `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_RX_IO_M0_R0_CFG_1,DLY_CTRL_T, DLY_CTRL_C, r0_tdly, r0_cdly);
                `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_RX_IO_M0_R1_CFG_1,DLY_CTRL_T, DLY_CTRL_C, r1_tdly, r1_cdly);
            end
            {RANK0,DQ1}: begin
                `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_RX_IO_M0_R0_CFG_1,DLY_CTRL_T, DLY_CTRL_C, r0_tdly, r0_cdly);
                `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_RX_IO_M0_R0_CFG_1,DLY_CTRL_T, DLY_CTRL_C, r0_tdly, r0_cdly);
            end
            {RANK1,DQ1}: begin
                `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_RX_IO_M0_R1_CFG_1,DLY_CTRL_T, DLY_CTRL_C, r1_tdly, r1_cdly);
                `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_RX_IO_M0_R1_CFG_1,DLY_CTRL_T, DLY_CTRL_C, r1_tdly, r1_cdly);
            end
            {RANK_ALL,DQ1}: begin
                `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_RX_IO_M0_R0_CFG_1,DLY_CTRL_T, DLY_CTRL_C, r0_tdly, r0_cdly);
                `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_RX_IO_M0_R1_CFG_1,DLY_CTRL_T, DLY_CTRL_C, r1_tdly, r1_cdly);
                `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_RX_IO_M0_R0_CFG_1,DLY_CTRL_T, DLY_CTRL_C, r0_tdly, r0_cdly);
                `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_RX_IO_M0_R1_CFG_1,DLY_CTRL_T, DLY_CTRL_C, r1_tdly, r1_cdly);
            end
            {RANK0,DQ_ALL}: begin
                `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_RX_IO_M0_R0_CFG_1,DLY_CTRL_T, DLY_CTRL_C, r0_tdly, r0_cdly);
                `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_RX_IO_M0_R0_CFG_1,DLY_CTRL_T, DLY_CTRL_C, r0_tdly, r0_cdly);
                `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_RX_IO_M0_R0_CFG_1,DLY_CTRL_T, DLY_CTRL_C, r0_tdly, r0_cdly);
                `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_RX_IO_M0_R0_CFG_1,DLY_CTRL_T, DLY_CTRL_C, r0_tdly, r0_cdly);
            end
            {RANK1,DQ_ALL}: begin
                `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_RX_IO_M0_R1_CFG_1,DLY_CTRL_T, DLY_CTRL_C, r1_tdly, r1_cdly);
                `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_RX_IO_M0_R1_CFG_1,DLY_CTRL_T, DLY_CTRL_C, r1_tdly, r1_cdly);
                `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_RX_IO_M0_R1_CFG_1,DLY_CTRL_T, DLY_CTRL_C, r1_tdly, r1_cdly);
                `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_RX_IO_M0_R1_CFG_1,DLY_CTRL_T, DLY_CTRL_C, r1_tdly, r1_cdly);
            end
            {RANK_ALL,DQ_ALL}: begin
                `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_RX_IO_M0_R0_CFG_1,DLY_CTRL_T, DLY_CTRL_C, r0_tdly, r0_cdly);
                `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_RX_IO_M0_R1_CFG_1,DLY_CTRL_T, DLY_CTRL_C, r1_tdly, r1_cdly);
                `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_RX_IO_M0_R0_CFG_1,DLY_CTRL_T, DLY_CTRL_C, r0_tdly, r0_cdly);
                `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_RX_IO_M0_R1_CFG_1,DLY_CTRL_T, DLY_CTRL_C, r1_tdly, r1_cdly);
                `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_RX_IO_M0_R0_CFG_1,DLY_CTRL_T, DLY_CTRL_C, r0_tdly, r0_cdly);
                `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_RX_IO_M0_R1_CFG_1,DLY_CTRL_T, DLY_CTRL_C, r1_tdly, r1_cdly);
                `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_RX_IO_M0_R0_CFG_1,DLY_CTRL_T, DLY_CTRL_C, r0_tdly, r0_cdly);
                `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_RX_IO_M0_R1_CFG_1,DLY_CTRL_T, DLY_CTRL_C, r1_tdly, r1_cdly);
            end

        endcase
    end
endtask

task automatic set_rdsdr_lpde_dly;
    input byte_sel_t  byte_sel;
    input rank_sel_t  rank_sel;
    input logic [1:0] gear;
    input logic [7:0] r0_dly;
    input logic [7:0] r1_dly;
    begin
        if((byte_sel == DQ0) || (byte_sel == DQ_ALL) || (byte_sel == ALL)) begin
            case(rank_sel)
                RANK0 : begin
                    `CSR_WRF3(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_RX_SDR_LPDE_M0_R0_CFG,CTRL_BIN,GEAR,EN,r0_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_RX_SDR_LPDE_M0_R0_CFG,CTRL_BIN,GEAR,EN,r0_dly,gear,1'b1);
                end
                RANK1 : begin
                    `CSR_WRF3(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_RX_SDR_LPDE_M0_R1_CFG,CTRL_BIN,GEAR,EN,r1_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_RX_SDR_LPDE_M0_R1_CFG,CTRL_BIN,GEAR,EN,r1_dly,gear,1'b1);
                end
                RANK_ALL : begin
                    `CSR_WRF3(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_RX_SDR_LPDE_M0_R0_CFG,CTRL_BIN,GEAR,EN,r0_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_RX_SDR_LPDE_M0_R1_CFG,CTRL_BIN,GEAR,EN,r1_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_RX_SDR_LPDE_M0_R0_CFG,CTRL_BIN,GEAR,EN,r0_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_RX_SDR_LPDE_M0_R1_CFG,CTRL_BIN,GEAR,EN,r1_dly,gear,1'b1);
                end
            endcase
        end
        if((byte_sel == DQ1) || (byte_sel == DQ_ALL) || (byte_sel == ALL)) begin
            case(rank_sel)
                RANK0 : begin
                    `CSR_WRF3(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_RX_SDR_LPDE_M0_R0_CFG,CTRL_BIN,GEAR,EN,r0_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_RX_SDR_LPDE_M0_R0_CFG,CTRL_BIN,GEAR,EN,r0_dly,gear,1'b1);
                end
                RANK1 : begin
                    `CSR_WRF3(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_RX_SDR_LPDE_M0_R1_CFG,CTRL_BIN,GEAR,EN,r1_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_RX_SDR_LPDE_M0_R1_CFG,CTRL_BIN,GEAR,EN,r1_dly,gear,1'b1);
                end
                RANK_ALL : begin
                    `CSR_WRF3(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_RX_SDR_LPDE_M0_R0_CFG,CTRL_BIN,GEAR,EN,r0_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_RX_SDR_LPDE_M0_R1_CFG,CTRL_BIN,GEAR,EN,r1_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_RX_SDR_LPDE_M0_R0_CFG,CTRL_BIN,GEAR,EN,r0_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_RX_SDR_LPDE_M0_R1_CFG,CTRL_BIN,GEAR,EN,r1_dly,gear,1'b1);
                end
            endcase
        end
        if((byte_sel == CA) || (byte_sel == ALL)) begin
            case(rank_sel)
                RANK0 : begin
                    `CSR_WRF3(DDR_CH0_CA_OFFSET,DDR_CA_DQS_RX_SDR_LPDE_M0_R0_CFG,CTRL_BIN,GEAR,EN,r0_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH1_CA_OFFSET,DDR_CA_DQS_RX_SDR_LPDE_M0_R0_CFG,CTRL_BIN,GEAR,EN,r0_dly,gear,1'b1);
                end
                RANK1 : begin
                    `CSR_WRF3(DDR_CH0_CA_OFFSET,DDR_CA_DQS_RX_SDR_LPDE_M0_R1_CFG,CTRL_BIN,GEAR,EN,r1_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH1_CA_OFFSET,DDR_CA_DQS_RX_SDR_LPDE_M0_R1_CFG,CTRL_BIN,GEAR,EN,r1_dly,gear,1'b1);
                end
                RANK_ALL : begin
                    `CSR_WRF3(DDR_CH0_CA_OFFSET,DDR_CA_DQS_RX_SDR_LPDE_M0_R0_CFG,CTRL_BIN,GEAR,EN,r0_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH0_CA_OFFSET,DDR_CA_DQS_RX_SDR_LPDE_M0_R1_CFG,CTRL_BIN,GEAR,EN,r1_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH1_CA_OFFSET,DDR_CA_DQS_RX_SDR_LPDE_M0_R0_CFG,CTRL_BIN,GEAR,EN,r0_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH1_CA_OFFSET,DDR_CA_DQS_RX_SDR_LPDE_M0_R1_CFG,CTRL_BIN,GEAR,EN,r1_dly,gear,1'b1);
                end
            endcase
        end
    end
endtask

task automatic set_wrdq_lpde_dly;
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
                    `CSR_WRF3(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_LPDE_M0_R0_CFG_0,CTRL_BIN,GEAR,EN,r0_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_LPDE_M0_R0_CFG_0,CTRL_BIN,GEAR,EN,r0_dly,gear,1'b1);
                end
                {RANK0,8'd1} : begin
                    `CSR_WRF3(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_LPDE_M0_R0_CFG_1,CTRL_BIN,GEAR,EN,r0_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_LPDE_M0_R0_CFG_1,CTRL_BIN,GEAR,EN,r0_dly,gear,1'b1);
                end
                {RANK0,8'd2} : begin
                    `CSR_WRF3(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_LPDE_M0_R0_CFG_2,CTRL_BIN,GEAR,EN,r0_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_LPDE_M0_R0_CFG_2,CTRL_BIN,GEAR,EN,r0_dly,gear,1'b1);
                end
                {RANK0,8'd3} : begin
                    `CSR_WRF3(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_LPDE_M0_R0_CFG_3,CTRL_BIN,GEAR,EN,r0_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_LPDE_M0_R0_CFG_3,CTRL_BIN,GEAR,EN,r0_dly,gear,1'b1);
                end
                {RANK0,8'd4} : begin
                    `CSR_WRF3(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_LPDE_M0_R0_CFG_4,CTRL_BIN,GEAR,EN,r0_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_LPDE_M0_R0_CFG_4,CTRL_BIN,GEAR,EN,r0_dly,gear,1'b1);
                end
                {RANK0,8'd5} : begin
                    `CSR_WRF3(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_LPDE_M0_R0_CFG_5,CTRL_BIN,GEAR,EN,r0_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_LPDE_M0_R0_CFG_5,CTRL_BIN,GEAR,EN,r0_dly,gear,1'b1);
                end
                {RANK0,8'd6} : begin
                    `CSR_WRF3(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_LPDE_M0_R0_CFG_6,CTRL_BIN,GEAR,EN,r0_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_LPDE_M0_R0_CFG_6,CTRL_BIN,GEAR,EN,r0_dly,gear,1'b1);
                end
                {RANK0,8'd7} : begin
                    `CSR_WRF3(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_LPDE_M0_R0_CFG_7,CTRL_BIN,GEAR,EN,r0_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_LPDE_M0_R0_CFG_7,CTRL_BIN,GEAR,EN,r0_dly,gear,1'b1);
                end
                {RANK0,8'd8} : begin
                    `CSR_WRF3(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_LPDE_M0_R0_CFG_8,CTRL_BIN,GEAR,EN,r0_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_LPDE_M0_R0_CFG_8,CTRL_BIN,GEAR,EN,r0_dly,gear,1'b1);
                end
                {RANK1,8'd0} : begin
                    `CSR_WRF3(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_LPDE_M0_R1_CFG_0,CTRL_BIN,GEAR,EN,r1_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_LPDE_M0_R1_CFG_0,CTRL_BIN,GEAR,EN,r1_dly,gear,1'b1);
                end
                {RANK1,8'd1} : begin
                    `CSR_WRF3(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_LPDE_M0_R1_CFG_1,CTRL_BIN,GEAR,EN,r1_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_LPDE_M0_R1_CFG_1,CTRL_BIN,GEAR,EN,r1_dly,gear,1'b1);
                end
                {RANK1,8'd2} : begin
                    `CSR_WRF3(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_LPDE_M0_R1_CFG_2,CTRL_BIN,GEAR,EN,r1_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_LPDE_M0_R1_CFG_2,CTRL_BIN,GEAR,EN,r1_dly,gear,1'b1);
                end
                {RANK1,8'd3} : begin
                    `CSR_WRF3(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_LPDE_M0_R1_CFG_3,CTRL_BIN,GEAR,EN,r1_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_LPDE_M0_R1_CFG_3,CTRL_BIN,GEAR,EN,r1_dly,gear,1'b1);
                end
                {RANK1,8'd4} : begin
                    `CSR_WRF3(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_LPDE_M0_R1_CFG_4,CTRL_BIN,GEAR,EN,r1_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_LPDE_M0_R1_CFG_4,CTRL_BIN,GEAR,EN,r1_dly,gear,1'b1);
                end
                {RANK1,8'd5} : begin
                    `CSR_WRF3(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_LPDE_M0_R1_CFG_5,CTRL_BIN,GEAR,EN,r1_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_LPDE_M0_R1_CFG_5,CTRL_BIN,GEAR,EN,r1_dly,gear,1'b1);
                end
                {RANK1,8'd6} : begin
                    `CSR_WRF3(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_LPDE_M0_R1_CFG_6,CTRL_BIN,GEAR,EN,r1_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_LPDE_M0_R1_CFG_6,CTRL_BIN,GEAR,EN,r1_dly,gear,1'b1);
                end
                {RANK1,8'd7} : begin
                    `CSR_WRF3(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_LPDE_M0_R1_CFG_7,CTRL_BIN,GEAR,EN,r1_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_LPDE_M0_R1_CFG_7,CTRL_BIN,GEAR,EN,r1_dly,gear,1'b1);
                end
                {RANK1,8'd8} : begin
                    `CSR_WRF3(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_LPDE_M0_R1_CFG_8,CTRL_BIN,GEAR,EN,r1_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_LPDE_M0_R1_CFG_8,CTRL_BIN,GEAR,EN,r1_dly,gear,1'b1);
                end
                default : begin
                    `CSR_WRF3(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_LPDE_M0_R0_CFG_0,CTRL_BIN,GEAR,EN,r0_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_LPDE_M0_R0_CFG_1,CTRL_BIN,GEAR,EN,r0_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_LPDE_M0_R0_CFG_2,CTRL_BIN,GEAR,EN,r0_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_LPDE_M0_R0_CFG_3,CTRL_BIN,GEAR,EN,r0_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_LPDE_M0_R0_CFG_4,CTRL_BIN,GEAR,EN,r0_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_LPDE_M0_R0_CFG_5,CTRL_BIN,GEAR,EN,r0_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_LPDE_M0_R0_CFG_6,CTRL_BIN,GEAR,EN,r0_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_LPDE_M0_R0_CFG_7,CTRL_BIN,GEAR,EN,r0_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_LPDE_M0_R0_CFG_8,CTRL_BIN,GEAR,EN,r0_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_LPDE_M0_R0_CFG_0,CTRL_BIN,GEAR,EN,r0_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_LPDE_M0_R0_CFG_1,CTRL_BIN,GEAR,EN,r0_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_LPDE_M0_R0_CFG_2,CTRL_BIN,GEAR,EN,r0_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_LPDE_M0_R0_CFG_3,CTRL_BIN,GEAR,EN,r0_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_LPDE_M0_R0_CFG_4,CTRL_BIN,GEAR,EN,r0_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_LPDE_M0_R0_CFG_5,CTRL_BIN,GEAR,EN,r0_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_LPDE_M0_R0_CFG_6,CTRL_BIN,GEAR,EN,r0_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_LPDE_M0_R0_CFG_7,CTRL_BIN,GEAR,EN,r0_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_LPDE_M0_R0_CFG_8,CTRL_BIN,GEAR,EN,r0_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_LPDE_M0_R1_CFG_0,CTRL_BIN,GEAR,EN,r1_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_LPDE_M0_R1_CFG_1,CTRL_BIN,GEAR,EN,r1_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_LPDE_M0_R1_CFG_2,CTRL_BIN,GEAR,EN,r1_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_LPDE_M0_R1_CFG_3,CTRL_BIN,GEAR,EN,r1_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_LPDE_M0_R1_CFG_4,CTRL_BIN,GEAR,EN,r1_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_LPDE_M0_R1_CFG_5,CTRL_BIN,GEAR,EN,r1_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_LPDE_M0_R1_CFG_6,CTRL_BIN,GEAR,EN,r1_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_LPDE_M0_R1_CFG_7,CTRL_BIN,GEAR,EN,r1_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_LPDE_M0_R1_CFG_8,CTRL_BIN,GEAR,EN,r1_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_LPDE_M0_R1_CFG_0,CTRL_BIN,GEAR,EN,r1_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_LPDE_M0_R1_CFG_1,CTRL_BIN,GEAR,EN,r1_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_LPDE_M0_R1_CFG_2,CTRL_BIN,GEAR,EN,r1_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_LPDE_M0_R1_CFG_3,CTRL_BIN,GEAR,EN,r1_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_LPDE_M0_R1_CFG_4,CTRL_BIN,GEAR,EN,r1_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_LPDE_M0_R1_CFG_5,CTRL_BIN,GEAR,EN,r1_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_LPDE_M0_R1_CFG_6,CTRL_BIN,GEAR,EN,r1_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_LPDE_M0_R1_CFG_7,CTRL_BIN,GEAR,EN,r1_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_LPDE_M0_R1_CFG_8,CTRL_BIN,GEAR,EN,r1_dly,gear,1'b1);
                end
            endcase
        end
        if((byte_sel == DQ1) || (byte_sel == DQ_ALL) || (byte_sel == ALL)) begin
            case({rank_sel,dq})
                {RANK0,8'd0} : begin
                    `CSR_WRF3(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_LPDE_M0_R0_CFG_0,CTRL_BIN,GEAR,EN,r0_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_LPDE_M0_R0_CFG_0,CTRL_BIN,GEAR,EN,r0_dly,gear,1'b1);
                end
                {RANK0,8'd1} : begin
                    `CSR_WRF3(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_LPDE_M0_R0_CFG_1,CTRL_BIN,GEAR,EN,r0_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_LPDE_M0_R0_CFG_1,CTRL_BIN,GEAR,EN,r0_dly,gear,1'b1);
                end
                {RANK0,8'd2} : begin
                    `CSR_WRF3(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_LPDE_M0_R0_CFG_2,CTRL_BIN,GEAR,EN,r0_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_LPDE_M0_R0_CFG_2,CTRL_BIN,GEAR,EN,r0_dly,gear,1'b1);
                end
                {RANK0,8'd3} : begin
                    `CSR_WRF3(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_LPDE_M0_R0_CFG_3,CTRL_BIN,GEAR,EN,r0_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_LPDE_M0_R0_CFG_3,CTRL_BIN,GEAR,EN,r0_dly,gear,1'b1);
                end
                {RANK0,8'd4} : begin
                    `CSR_WRF3(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_LPDE_M0_R0_CFG_4,CTRL_BIN,GEAR,EN,r0_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_LPDE_M0_R0_CFG_4,CTRL_BIN,GEAR,EN,r0_dly,gear,1'b1);
                end
                {RANK0,8'd5} : begin
                    `CSR_WRF3(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_LPDE_M0_R0_CFG_5,CTRL_BIN,GEAR,EN,r0_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_LPDE_M0_R0_CFG_5,CTRL_BIN,GEAR,EN,r0_dly,gear,1'b1);
                end
                {RANK0,8'd6} : begin
                    `CSR_WRF3(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_LPDE_M0_R0_CFG_6,CTRL_BIN,GEAR,EN,r0_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_LPDE_M0_R0_CFG_6,CTRL_BIN,GEAR,EN,r0_dly,gear,1'b1);
                end
                {RANK0,8'd7} : begin
                    `CSR_WRF3(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_LPDE_M0_R0_CFG_7,CTRL_BIN,GEAR,EN,r0_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_LPDE_M0_R0_CFG_7,CTRL_BIN,GEAR,EN,r0_dly,gear,1'b1);
                end
                {RANK0,8'd8} : begin
                    `CSR_WRF3(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_LPDE_M0_R0_CFG_8,CTRL_BIN,GEAR,EN,r0_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_LPDE_M0_R0_CFG_8,CTRL_BIN,GEAR,EN,r0_dly,gear,1'b1);
                end
                {RANK1,8'd0} : begin
                    `CSR_WRF3(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_LPDE_M0_R1_CFG_0,CTRL_BIN,GEAR,EN,r1_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_LPDE_M0_R1_CFG_0,CTRL_BIN,GEAR,EN,r1_dly,gear,1'b1);
                end
                {RANK1,8'd1} : begin
                    `CSR_WRF3(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_LPDE_M0_R1_CFG_1,CTRL_BIN,GEAR,EN,r1_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_LPDE_M0_R1_CFG_1,CTRL_BIN,GEAR,EN,r1_dly,gear,1'b1);
                end
                {RANK1,8'd2} : begin
                    `CSR_WRF3(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_LPDE_M0_R1_CFG_2,CTRL_BIN,GEAR,EN,r1_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_LPDE_M0_R1_CFG_2,CTRL_BIN,GEAR,EN,r1_dly,gear,1'b1);
                end
                {RANK1,8'd3} : begin
                    `CSR_WRF3(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_LPDE_M0_R1_CFG_3,CTRL_BIN,GEAR,EN,r1_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_LPDE_M0_R1_CFG_3,CTRL_BIN,GEAR,EN,r1_dly,gear,1'b1);
                end
                {RANK1,8'd4} : begin
                    `CSR_WRF3(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_LPDE_M0_R1_CFG_4,CTRL_BIN,GEAR,EN,r1_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_LPDE_M0_R1_CFG_4,CTRL_BIN,GEAR,EN,r1_dly,gear,1'b1);
                end
                {RANK1,8'd5} : begin
                    `CSR_WRF3(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_LPDE_M0_R1_CFG_5,CTRL_BIN,GEAR,EN,r1_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_LPDE_M0_R1_CFG_5,CTRL_BIN,GEAR,EN,r1_dly,gear,1'b1);
                end
                {RANK1,8'd6} : begin
                    `CSR_WRF3(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_LPDE_M0_R1_CFG_6,CTRL_BIN,GEAR,EN,r1_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_LPDE_M0_R1_CFG_6,CTRL_BIN,GEAR,EN,r1_dly,gear,1'b1);
                end
                {RANK1,8'd7} : begin
                    `CSR_WRF3(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_LPDE_M0_R1_CFG_7,CTRL_BIN,GEAR,EN,r1_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_LPDE_M0_R1_CFG_7,CTRL_BIN,GEAR,EN,r1_dly,gear,1'b1);
                end
                {RANK1,8'd8} : begin
                    `CSR_WRF3(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_LPDE_M0_R1_CFG_8,CTRL_BIN,GEAR,EN,r1_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_LPDE_M0_R1_CFG_8,CTRL_BIN,GEAR,EN,r1_dly,gear,1'b1);
                end
                default : begin
                    `CSR_WRF3(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_LPDE_M0_R0_CFG_0,CTRL_BIN,GEAR,EN,r0_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_LPDE_M0_R0_CFG_1,CTRL_BIN,GEAR,EN,r0_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_LPDE_M0_R0_CFG_2,CTRL_BIN,GEAR,EN,r0_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_LPDE_M0_R0_CFG_3,CTRL_BIN,GEAR,EN,r0_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_LPDE_M0_R0_CFG_4,CTRL_BIN,GEAR,EN,r0_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_LPDE_M0_R0_CFG_5,CTRL_BIN,GEAR,EN,r0_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_LPDE_M0_R0_CFG_6,CTRL_BIN,GEAR,EN,r0_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_LPDE_M0_R0_CFG_7,CTRL_BIN,GEAR,EN,r0_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_LPDE_M0_R0_CFG_8,CTRL_BIN,GEAR,EN,r0_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_LPDE_M0_R0_CFG_0,CTRL_BIN,GEAR,EN,r0_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_LPDE_M0_R0_CFG_1,CTRL_BIN,GEAR,EN,r0_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_LPDE_M0_R0_CFG_2,CTRL_BIN,GEAR,EN,r0_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_LPDE_M0_R0_CFG_3,CTRL_BIN,GEAR,EN,r0_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_LPDE_M0_R0_CFG_4,CTRL_BIN,GEAR,EN,r0_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_LPDE_M0_R0_CFG_5,CTRL_BIN,GEAR,EN,r0_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_LPDE_M0_R0_CFG_6,CTRL_BIN,GEAR,EN,r0_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_LPDE_M0_R0_CFG_7,CTRL_BIN,GEAR,EN,r0_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_LPDE_M0_R0_CFG_8,CTRL_BIN,GEAR,EN,r0_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_LPDE_M0_R1_CFG_0,CTRL_BIN,GEAR,EN,r1_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_LPDE_M0_R1_CFG_1,CTRL_BIN,GEAR,EN,r1_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_LPDE_M0_R1_CFG_2,CTRL_BIN,GEAR,EN,r1_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_LPDE_M0_R1_CFG_3,CTRL_BIN,GEAR,EN,r1_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_LPDE_M0_R1_CFG_4,CTRL_BIN,GEAR,EN,r1_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_LPDE_M0_R1_CFG_5,CTRL_BIN,GEAR,EN,r1_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_LPDE_M0_R1_CFG_6,CTRL_BIN,GEAR,EN,r1_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_LPDE_M0_R1_CFG_7,CTRL_BIN,GEAR,EN,r1_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_LPDE_M0_R1_CFG_8,CTRL_BIN,GEAR,EN,r1_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_LPDE_M0_R1_CFG_0,CTRL_BIN,GEAR,EN,r1_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_LPDE_M0_R1_CFG_1,CTRL_BIN,GEAR,EN,r1_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_LPDE_M0_R1_CFG_2,CTRL_BIN,GEAR,EN,r1_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_LPDE_M0_R1_CFG_3,CTRL_BIN,GEAR,EN,r1_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_LPDE_M0_R1_CFG_4,CTRL_BIN,GEAR,EN,r1_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_LPDE_M0_R1_CFG_5,CTRL_BIN,GEAR,EN,r1_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_LPDE_M0_R1_CFG_6,CTRL_BIN,GEAR,EN,r1_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_LPDE_M0_R1_CFG_7,CTRL_BIN,GEAR,EN,r1_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_LPDE_M0_R1_CFG_8,CTRL_BIN,GEAR,EN,r1_dly,gear,1'b1);
                end
            endcase
        end
        if((byte_sel == CA) || (byte_sel == ALL)) begin
            case({rank_sel,dq})
                {RANK0,8'd0} : begin
                    `CSR_WRF3(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_LPDE_M0_R0_CFG_0,CTRL_BIN,GEAR,EN,r0_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_LPDE_M0_R0_CFG_0,CTRL_BIN,GEAR,EN,r0_dly,gear,1'b1);
                end
                {RANK0,8'd1} : begin
                    `CSR_WRF3(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_LPDE_M0_R0_CFG_1,CTRL_BIN,GEAR,EN,r0_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_LPDE_M0_R0_CFG_1,CTRL_BIN,GEAR,EN,r0_dly,gear,1'b1);
                end
                {RANK0,8'd2} : begin
                    `CSR_WRF3(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_LPDE_M0_R0_CFG_2,CTRL_BIN,GEAR,EN,r0_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_LPDE_M0_R0_CFG_2,CTRL_BIN,GEAR,EN,r0_dly,gear,1'b1);
                end
                {RANK0,8'd3} : begin
                    `CSR_WRF3(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_LPDE_M0_R0_CFG_3,CTRL_BIN,GEAR,EN,r0_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_LPDE_M0_R0_CFG_3,CTRL_BIN,GEAR,EN,r0_dly,gear,1'b1);
                end
                {RANK0,8'd4} : begin
                    `CSR_WRF3(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_LPDE_M0_R0_CFG_4,CTRL_BIN,GEAR,EN,r0_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_LPDE_M0_R0_CFG_4,CTRL_BIN,GEAR,EN,r0_dly,gear,1'b1);
                end
                {RANK0,8'd5} : begin
                    `CSR_WRF3(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_LPDE_M0_R0_CFG_5,CTRL_BIN,GEAR,EN,r0_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_LPDE_M0_R0_CFG_5,CTRL_BIN,GEAR,EN,r0_dly,gear,1'b1);
                end
                {RANK0,8'd6} : begin
                    `CSR_WRF3(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_LPDE_M0_R0_CFG_6,CTRL_BIN,GEAR,EN,r0_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_LPDE_M0_R0_CFG_6,CTRL_BIN,GEAR,EN,r0_dly,gear,1'b1);
                end
                {RANK0,8'd7} : begin
                    `CSR_WRF3(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_LPDE_M0_R0_CFG_7,CTRL_BIN,GEAR,EN,r0_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_LPDE_M0_R0_CFG_7,CTRL_BIN,GEAR,EN,r0_dly,gear,1'b1);
                end
                {RANK0,8'd8} : begin
                    `CSR_WRF3(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_LPDE_M0_R0_CFG_8,CTRL_BIN,GEAR,EN,r0_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_LPDE_M0_R0_CFG_8,CTRL_BIN,GEAR,EN,r0_dly,gear,1'b1);
                end
                {RANK0,8'd9} : begin
                    `CSR_WRF3(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_LPDE_M0_R0_CFG_9,CTRL_BIN,GEAR,EN,r0_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_LPDE_M0_R0_CFG_9,CTRL_BIN,GEAR,EN,r0_dly,gear,1'b1);
                end
                {RANK0,8'd10} : begin
                    `CSR_WRF3(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_LPDE_M0_R0_CFG_10,CTRL_BIN,GEAR,EN,r0_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_LPDE_M0_R0_CFG_10,CTRL_BIN,GEAR,EN,r0_dly,gear,1'b1);
                end
                {RANK1,8'd0} : begin
                    `CSR_WRF3(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_LPDE_M0_R1_CFG_0,CTRL_BIN,GEAR,EN,r1_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_LPDE_M0_R1_CFG_0,CTRL_BIN,GEAR,EN,r1_dly,gear,1'b1);
                end
                {RANK1,8'd1} : begin
                    `CSR_WRF3(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_LPDE_M0_R1_CFG_1,CTRL_BIN,GEAR,EN,r1_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_LPDE_M0_R1_CFG_1,CTRL_BIN,GEAR,EN,r1_dly,gear,1'b1);
                end
                {RANK1,8'd2} : begin
                    `CSR_WRF3(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_LPDE_M0_R1_CFG_2,CTRL_BIN,GEAR,EN,r1_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_LPDE_M0_R1_CFG_2,CTRL_BIN,GEAR,EN,r1_dly,gear,1'b1);
                end
                {RANK1,8'd3} : begin
                    `CSR_WRF3(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_LPDE_M0_R1_CFG_3,CTRL_BIN,GEAR,EN,r1_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_LPDE_M0_R1_CFG_3,CTRL_BIN,GEAR,EN,r1_dly,gear,1'b1);
                end
                {RANK1,8'd4} : begin
                    `CSR_WRF3(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_LPDE_M0_R1_CFG_4,CTRL_BIN,GEAR,EN,r1_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_LPDE_M0_R1_CFG_4,CTRL_BIN,GEAR,EN,r1_dly,gear,1'b1);
                end
                {RANK1,8'd5} : begin
                    `CSR_WRF3(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_LPDE_M0_R1_CFG_5,CTRL_BIN,GEAR,EN,r1_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_LPDE_M0_R1_CFG_5,CTRL_BIN,GEAR,EN,r1_dly,gear,1'b1);
                end
                {RANK1,8'd6} : begin
                    `CSR_WRF3(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_LPDE_M0_R1_CFG_6,CTRL_BIN,GEAR,EN,r1_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_LPDE_M0_R1_CFG_6,CTRL_BIN,GEAR,EN,r1_dly,gear,1'b1);
                end
                {RANK1,8'd7} : begin
                    `CSR_WRF3(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_LPDE_M0_R1_CFG_7,CTRL_BIN,GEAR,EN,r1_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_LPDE_M0_R1_CFG_7,CTRL_BIN,GEAR,EN,r1_dly,gear,1'b1);
                end
                {RANK1,8'd8} : begin
                    `CSR_WRF3(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_LPDE_M0_R1_CFG_8,CTRL_BIN,GEAR,EN,r1_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_LPDE_M0_R1_CFG_8,CTRL_BIN,GEAR,EN,r1_dly,gear,1'b1);
                end
                {RANK1,8'd9} : begin
                    `CSR_WRF3(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_LPDE_M0_R1_CFG_9,CTRL_BIN,GEAR,EN,r1_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_LPDE_M0_R1_CFG_9,CTRL_BIN,GEAR,EN,r1_dly,gear,1'b1);
                end
                {RANK1,8'd10} : begin
                    `CSR_WRF3(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_LPDE_M0_R1_CFG_10,CTRL_BIN,GEAR,EN,r1_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_LPDE_M0_R1_CFG_10,CTRL_BIN,GEAR,EN,r1_dly,gear,1'b1);
                end
                default : begin
                    `CSR_WRF3(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_LPDE_M0_R0_CFG_0,CTRL_BIN,GEAR,EN,r0_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_LPDE_M0_R0_CFG_1,CTRL_BIN,GEAR,EN,r0_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_LPDE_M0_R0_CFG_2,CTRL_BIN,GEAR,EN,r0_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_LPDE_M0_R0_CFG_3,CTRL_BIN,GEAR,EN,r0_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_LPDE_M0_R0_CFG_4,CTRL_BIN,GEAR,EN,r0_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_LPDE_M0_R0_CFG_5,CTRL_BIN,GEAR,EN,r0_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_LPDE_M0_R0_CFG_6,CTRL_BIN,GEAR,EN,r0_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_LPDE_M0_R0_CFG_7,CTRL_BIN,GEAR,EN,r0_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_LPDE_M0_R0_CFG_8,CTRL_BIN,GEAR,EN,r0_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_LPDE_M0_R0_CFG_9,CTRL_BIN,GEAR,EN,r0_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_LPDE_M0_R0_CFG_10,CTRL_BIN,GEAR,EN,r0_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_LPDE_M0_R0_CFG_0,CTRL_BIN,GEAR,EN,r0_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_LPDE_M0_R0_CFG_1,CTRL_BIN,GEAR,EN,r0_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_LPDE_M0_R0_CFG_2,CTRL_BIN,GEAR,EN,r0_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_LPDE_M0_R0_CFG_3,CTRL_BIN,GEAR,EN,r0_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_LPDE_M0_R0_CFG_4,CTRL_BIN,GEAR,EN,r0_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_LPDE_M0_R0_CFG_5,CTRL_BIN,GEAR,EN,r0_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_LPDE_M0_R0_CFG_6,CTRL_BIN,GEAR,EN,r0_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_LPDE_M0_R0_CFG_7,CTRL_BIN,GEAR,EN,r0_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_LPDE_M0_R0_CFG_8,CTRL_BIN,GEAR,EN,r0_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_LPDE_M0_R0_CFG_9,CTRL_BIN,GEAR,EN,r0_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_LPDE_M0_R0_CFG_10,CTRL_BIN,GEAR,EN,r0_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_LPDE_M0_R1_CFG_0,CTRL_BIN,GEAR,EN,r1_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_LPDE_M0_R1_CFG_1,CTRL_BIN,GEAR,EN,r1_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_LPDE_M0_R1_CFG_2,CTRL_BIN,GEAR,EN,r1_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_LPDE_M0_R1_CFG_3,CTRL_BIN,GEAR,EN,r1_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_LPDE_M0_R1_CFG_4,CTRL_BIN,GEAR,EN,r1_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_LPDE_M0_R1_CFG_5,CTRL_BIN,GEAR,EN,r1_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_LPDE_M0_R1_CFG_6,CTRL_BIN,GEAR,EN,r1_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_LPDE_M0_R1_CFG_7,CTRL_BIN,GEAR,EN,r1_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_LPDE_M0_R1_CFG_8,CTRL_BIN,GEAR,EN,r1_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_LPDE_M0_R1_CFG_9,CTRL_BIN,GEAR,EN,r1_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_LPDE_M0_R1_CFG_10,CTRL_BIN,GEAR,EN,r1_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_LPDE_M0_R1_CFG_0,CTRL_BIN,GEAR,EN,r1_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_LPDE_M0_R1_CFG_1,CTRL_BIN,GEAR,EN,r1_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_LPDE_M0_R1_CFG_2,CTRL_BIN,GEAR,EN,r1_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_LPDE_M0_R1_CFG_3,CTRL_BIN,GEAR,EN,r1_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_LPDE_M0_R1_CFG_4,CTRL_BIN,GEAR,EN,r1_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_LPDE_M0_R1_CFG_5,CTRL_BIN,GEAR,EN,r1_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_LPDE_M0_R1_CFG_6,CTRL_BIN,GEAR,EN,r1_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_LPDE_M0_R1_CFG_7,CTRL_BIN,GEAR,EN,r1_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_LPDE_M0_R1_CFG_8,CTRL_BIN,GEAR,EN,r1_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_LPDE_M0_R1_CFG_9,CTRL_BIN,GEAR,EN,r1_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_LPDE_M0_R1_CFG_10,CTRL_BIN,GEAR,EN,r1_dly,gear,1'b1);
                end
            endcase
        end
    end
endtask

task automatic set_wrdqs_lpde_dly;
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
                    `CSR_WRF3(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_LPDE_M0_R0_CFG_0,CTRL_BIN,GEAR,EN,r0_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_LPDE_M0_R0_CFG_0,CTRL_BIN,GEAR,EN,r0_dly,gear,1'b1);
                end
                {RANK0,8'd1} : begin
                    `CSR_WRF3(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_LPDE_M0_R0_CFG_1,CTRL_BIN,GEAR,EN,r0_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_LPDE_M0_R0_CFG_1,CTRL_BIN,GEAR,EN,r0_dly,gear,1'b1);
                end
                {RANK1,8'd0} : begin
                    `CSR_WRF3(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_LPDE_M0_R1_CFG_0,CTRL_BIN,GEAR,EN,r1_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_LPDE_M0_R1_CFG_0,CTRL_BIN,GEAR,EN,r1_dly,gear,1'b1);
                end
                {RANK1,8'd1} : begin
                    `CSR_WRF3(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_LPDE_M0_R1_CFG_1,CTRL_BIN,GEAR,EN,r1_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_LPDE_M0_R1_CFG_1,CTRL_BIN,GEAR,EN,r1_dly,gear,1'b1);
                end
                default: begin
                    `CSR_WRF3(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_LPDE_M0_R0_CFG_0,CTRL_BIN,GEAR,EN,r0_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_LPDE_M0_R0_CFG_1,CTRL_BIN,GEAR,EN,r0_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_LPDE_M0_R1_CFG_0,CTRL_BIN,GEAR,EN,r1_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_LPDE_M0_R1_CFG_1,CTRL_BIN,GEAR,EN,r1_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_LPDE_M0_R0_CFG_0,CTRL_BIN,GEAR,EN,r0_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_LPDE_M0_R0_CFG_1,CTRL_BIN,GEAR,EN,r0_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_LPDE_M0_R1_CFG_0,CTRL_BIN,GEAR,EN,r1_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_LPDE_M0_R1_CFG_1,CTRL_BIN,GEAR,EN,r1_dly,gear,1'b1);
                end
            endcase
        end
        if((byte_sel == DQ1) || (byte_sel == DQ_ALL) || (byte_sel == ALL)) begin
            case({rank_sel,dqs})
                {RANK0,8'd0} : begin
                    `CSR_WRF3(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_LPDE_M0_R0_CFG_0,CTRL_BIN,GEAR,EN,r0_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_LPDE_M0_R0_CFG_0,CTRL_BIN,GEAR,EN,r0_dly,gear,1'b1);
                end
                {RANK0,8'd1} : begin
                    `CSR_WRF3(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_LPDE_M0_R0_CFG_1,CTRL_BIN,GEAR,EN,r0_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_LPDE_M0_R0_CFG_1,CTRL_BIN,GEAR,EN,r0_dly,gear,1'b1);
                end
                {RANK1,8'd0} : begin
                    `CSR_WRF3(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_LPDE_M0_R1_CFG_0,CTRL_BIN,GEAR,EN,r1_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_LPDE_M0_R1_CFG_0,CTRL_BIN,GEAR,EN,r1_dly,gear,1'b1);
                end
                {RANK1,8'd1} : begin
                    `CSR_WRF3(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_LPDE_M0_R1_CFG_1,CTRL_BIN,GEAR,EN,r1_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_LPDE_M0_R1_CFG_1,CTRL_BIN,GEAR,EN,r1_dly,gear,1'b1);
                end
                default: begin
                    `CSR_WRF3(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_LPDE_M0_R0_CFG_0,CTRL_BIN,GEAR,EN,r0_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_LPDE_M0_R0_CFG_1,CTRL_BIN,GEAR,EN,r0_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_LPDE_M0_R1_CFG_0,CTRL_BIN,GEAR,EN,r1_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_LPDE_M0_R1_CFG_1,CTRL_BIN,GEAR,EN,r1_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_LPDE_M0_R0_CFG_0,CTRL_BIN,GEAR,EN,r0_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_LPDE_M0_R0_CFG_1,CTRL_BIN,GEAR,EN,r0_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_LPDE_M0_R1_CFG_0,CTRL_BIN,GEAR,EN,r1_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_LPDE_M0_R1_CFG_1,CTRL_BIN,GEAR,EN,r1_dly,gear,1'b1);
                end
            endcase
        end
        if((byte_sel == CA) || (byte_sel == ALL)) begin
            case({rank_sel,dqs})
                {RANK0,8'd0} : begin
                    `CSR_WRF3(DDR_CH0_CA_OFFSET,DDR_CA_DQS_TX_LPDE_M0_R0_CFG_0,CTRL_BIN,GEAR,EN,r0_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH1_CA_OFFSET,DDR_CA_DQS_TX_LPDE_M0_R0_CFG_0,CTRL_BIN,GEAR,EN,r0_dly,gear,1'b1);
                end
                {RANK1,8'd0} : begin
                    `CSR_WRF3(DDR_CH0_CA_OFFSET,DDR_CA_DQS_TX_LPDE_M0_R1_CFG_0,CTRL_BIN,GEAR,EN,r1_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH1_CA_OFFSET,DDR_CA_DQS_TX_LPDE_M0_R1_CFG_0,CTRL_BIN,GEAR,EN,r1_dly,gear,1'b1);
                end
                default: begin
                    `CSR_WRF3(DDR_CH0_CA_OFFSET,DDR_CA_DQS_TX_LPDE_M0_R0_CFG_0,CTRL_BIN,GEAR,EN,r0_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH1_CA_OFFSET,DDR_CA_DQS_TX_LPDE_M0_R0_CFG_0,CTRL_BIN,GEAR,EN,r0_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH0_CA_OFFSET,DDR_CA_DQS_TX_LPDE_M0_R1_CFG_0,CTRL_BIN,GEAR,EN,r1_dly,gear,1'b1);
                    `CSR_WRF3(DDR_CH1_CA_OFFSET,DDR_CA_DQS_TX_LPDE_M0_R1_CFG_0,CTRL_BIN,GEAR,EN,r1_dly,gear,1'b1);
                end
            endcase
        end
    end
endtask

task automatic set_tx_io_cmn_cfg;
    input byte_sel_t byte_sel;
    input rank_sel_t rank_sel;
    input logic      lpbk_en;
    begin
        if((byte_sel == DQ0 ) || (byte_sel == DQ_ALL) || (byte_sel == ALL)) begin
            case(rank_sel)
                RANK0 : begin
                    `CSR_WRF1(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_IO_CMN_M0_R0_CFG,LPBK_EN,lpbk_en);
                    `CSR_WRF1(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_IO_CMN_M0_R0_CFG,LPBK_EN,lpbk_en);
                end
                RANK1 : begin
                    `CSR_WRF1(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_IO_CMN_M0_R1_CFG,LPBK_EN,lpbk_en);
                    `CSR_WRF1(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_IO_CMN_M0_R1_CFG,LPBK_EN,lpbk_en);
                end
                RANK_ALL : begin
                    `CSR_WRF1(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_IO_CMN_M0_R0_CFG,LPBK_EN,lpbk_en);
                    `CSR_WRF1(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_IO_CMN_M0_R1_CFG,LPBK_EN,lpbk_en);
                    `CSR_WRF1(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_IO_CMN_M0_R0_CFG,LPBK_EN,lpbk_en);
                    `CSR_WRF1(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_IO_CMN_M0_R1_CFG,LPBK_EN,lpbk_en);
                end
            endcase
        end
        if((byte_sel == DQ1 ) || (byte_sel == DQ_ALL) || (byte_sel == ALL)) begin
            case(rank_sel)
                RANK0 : begin
                    `CSR_WRF1(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_IO_CMN_M0_R0_CFG,LPBK_EN,lpbk_en);
                    `CSR_WRF1(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_IO_CMN_M0_R0_CFG,LPBK_EN,lpbk_en);
                end
                RANK1 : begin
                    `CSR_WRF1(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_IO_CMN_M0_R1_CFG,LPBK_EN,lpbk_en);
                    `CSR_WRF1(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_IO_CMN_M0_R1_CFG,LPBK_EN,lpbk_en);
                end
                RANK_ALL : begin
                    `CSR_WRF1(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_IO_CMN_M0_R0_CFG,LPBK_EN,lpbk_en);
                    `CSR_WRF1(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_IO_CMN_M0_R1_CFG,LPBK_EN,lpbk_en);
                    `CSR_WRF1(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_IO_CMN_M0_R0_CFG,LPBK_EN,lpbk_en);
                    `CSR_WRF1(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_IO_CMN_M0_R1_CFG,LPBK_EN,lpbk_en);
                end
            endcase
        end
        if((byte_sel == CA) || (byte_sel == ALL)) begin
            case(rank_sel)
                RANK0 : begin
                    `CSR_WRF1(DDR_CH0_CA_OFFSET,DDR_CA_DQS_TX_IO_CMN_M0_R0_CFG,LPBK_EN,lpbk_en);
                    `CSR_WRF1(DDR_CH1_CA_OFFSET,DDR_CA_DQS_TX_IO_CMN_M0_R0_CFG,LPBK_EN,lpbk_en);
                end
                RANK1 : begin
                    `CSR_WRF1(DDR_CH0_CA_OFFSET,DDR_CA_DQS_TX_IO_CMN_M0_R1_CFG,LPBK_EN,lpbk_en);
                    `CSR_WRF1(DDR_CH1_CA_OFFSET,DDR_CA_DQS_TX_IO_CMN_M0_R1_CFG,LPBK_EN,lpbk_en);
                end
                RANK_ALL : begin
                    `CSR_WRF1(DDR_CH0_CA_OFFSET,DDR_CA_DQS_TX_IO_CMN_M0_R0_CFG,LPBK_EN,lpbk_en);
                    `CSR_WRF1(DDR_CH0_CA_OFFSET,DDR_CA_DQS_TX_IO_CMN_M0_R1_CFG,LPBK_EN,lpbk_en);
                    `CSR_WRF1(DDR_CH1_CA_OFFSET,DDR_CA_DQS_TX_IO_CMN_M0_R0_CFG,LPBK_EN,lpbk_en);
                    `CSR_WRF1(DDR_CH1_CA_OFFSET,DDR_CA_DQS_TX_IO_CMN_M0_R1_CFG,LPBK_EN,lpbk_en);
                end
            endcase
        end
    end
endtask

task automatic set_tx_io_cmn_cfg_dt;
    input byte_sel_t byte_sel;
    input rank_sel_t rank_sel;
    input logic      lpbk_en;
    input logic [4:0] ncal;
    input logic [5:0] pcal;
    begin
        if((byte_sel == DQ0 ) || (byte_sel == DQ_ALL) || (byte_sel == ALL)) begin
            case(rank_sel)
                RANK0 : begin
                    `CSR_WRF3(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_IO_CMN_M0_R0_CFG,LPBK_EN,NCAL,PCAL,lpbk_en,ncal,pcal);
                    `CSR_WRF3(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_IO_CMN_M0_R0_CFG,LPBK_EN,NCAL,PCAL,lpbk_en,ncal,pcal);
                end
                RANK1 : begin
                    `CSR_WRF3(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_IO_CMN_M0_R1_CFG,LPBK_EN,NCAL,PCAL,lpbk_en,ncal,pcal);
                    `CSR_WRF3(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_IO_CMN_M0_R1_CFG,LPBK_EN,NCAL,PCAL,lpbk_en,ncal,pcal);
                end
                RANK_ALL : begin
                    `CSR_WRF3(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_IO_CMN_M0_R0_CFG,LPBK_EN,NCAL,PCAL,lpbk_en,ncal,pcal);
                    `CSR_WRF3(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_IO_CMN_M0_R1_CFG,LPBK_EN,NCAL,PCAL,lpbk_en,ncal,pcal);
                    `CSR_WRF3(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_IO_CMN_M0_R0_CFG,LPBK_EN,NCAL,PCAL,lpbk_en,ncal,pcal);
                    `CSR_WRF3(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_IO_CMN_M0_R1_CFG,LPBK_EN,NCAL,PCAL,lpbk_en,ncal,pcal);
                end
            endcase
        end
        if((byte_sel == DQ1 ) || (byte_sel == DQ_ALL) || (byte_sel == ALL)) begin
            case(rank_sel)
                RANK0 : begin
                    `CSR_WRF3(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_IO_CMN_M0_R0_CFG,LPBK_EN,NCAL,PCAL,lpbk_en,ncal,pcal);
                    `CSR_WRF3(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_IO_CMN_M0_R0_CFG,LPBK_EN,NCAL,PCAL,lpbk_en,ncal,pcal);
                end
                RANK1 : begin
                    `CSR_WRF3(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_IO_CMN_M0_R1_CFG,LPBK_EN,NCAL,PCAL,lpbk_en,ncal,pcal);
                    `CSR_WRF3(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_IO_CMN_M0_R1_CFG,LPBK_EN,NCAL,PCAL,lpbk_en,ncal,pcal);
                end
                RANK_ALL : begin
                    `CSR_WRF3(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_IO_CMN_M0_R0_CFG,LPBK_EN,NCAL,PCAL,lpbk_en,ncal,pcal);
                    `CSR_WRF3(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_IO_CMN_M0_R1_CFG,LPBK_EN,NCAL,PCAL,lpbk_en,ncal,pcal);
                    `CSR_WRF3(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_IO_CMN_M0_R0_CFG,LPBK_EN,NCAL,PCAL,lpbk_en,ncal,pcal);
                    `CSR_WRF3(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_IO_CMN_M0_R1_CFG,LPBK_EN,NCAL,PCAL,lpbk_en,ncal,pcal);
                end
            endcase
        end
        if((byte_sel == CA) || (byte_sel == ALL)) begin
            case(rank_sel)
                RANK0 : begin
                    `CSR_WRF3(DDR_CH0_CA_OFFSET,DDR_CA_DQS_TX_IO_CMN_M0_R0_CFG,LPBK_EN,NCAL,PCAL,lpbk_en,ncal,pcal);
                    `CSR_WRF3(DDR_CH1_CA_OFFSET,DDR_CA_DQS_TX_IO_CMN_M0_R0_CFG,LPBK_EN,NCAL,PCAL,lpbk_en,ncal,pcal);
                end
                RANK1 : begin
                    `CSR_WRF3(DDR_CH0_CA_OFFSET,DDR_CA_DQS_TX_IO_CMN_M0_R1_CFG,LPBK_EN,NCAL,PCAL,lpbk_en,ncal,pcal);
                    `CSR_WRF3(DDR_CH1_CA_OFFSET,DDR_CA_DQS_TX_IO_CMN_M0_R1_CFG,LPBK_EN,NCAL,PCAL,lpbk_en,ncal,pcal);
                end
                RANK_ALL : begin
                    `CSR_WRF3(DDR_CH0_CA_OFFSET,DDR_CA_DQS_TX_IO_CMN_M0_R0_CFG,LPBK_EN,NCAL,PCAL,lpbk_en,ncal,pcal);
                    `CSR_WRF3(DDR_CH0_CA_OFFSET,DDR_CA_DQS_TX_IO_CMN_M0_R1_CFG,LPBK_EN,NCAL,PCAL,lpbk_en,ncal,pcal);
                    `CSR_WRF3(DDR_CH1_CA_OFFSET,DDR_CA_DQS_TX_IO_CMN_M0_R0_CFG,LPBK_EN,NCAL,PCAL,lpbk_en,ncal,pcal);
                    `CSR_WRF3(DDR_CH1_CA_OFFSET,DDR_CA_DQS_TX_IO_CMN_M0_R1_CFG,LPBK_EN,NCAL,PCAL,lpbk_en,ncal,pcal);
                end
            endcase
        end
    end
endtask

task automatic set_tx_dqs_qdr_pi_cfg;
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
                    `CSR_WRF3(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_QDR_PI_0_M0_R0_CFG,EN,CODE,GEAR,en,code,gear);
                    `CSR_WRF3(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_QDR_PI_0_M0_R0_CFG,EN,CODE,GEAR,en,code,gear);
                end
                {1'b1, RANK0} : begin
                    `CSR_WRF3(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_QDR_PI_1_M0_R0_CFG,EN,CODE,GEAR,en,code,gear);
                    `CSR_WRF3(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_QDR_PI_1_M0_R0_CFG,EN,CODE,GEAR,en,code,gear);
                end
                {1'b0, RANK1} : begin
                    `CSR_WRF3(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_QDR_PI_0_M0_R1_CFG,EN,CODE,GEAR,en,code,gear);
                    `CSR_WRF3(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_QDR_PI_0_M0_R1_CFG,EN,CODE,GEAR,en,code,gear);
                end
                {1'b1, RANK1} : begin
                    `CSR_WRF3(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_QDR_PI_1_M0_R1_CFG,EN,CODE,GEAR,en,code,gear);
                    `CSR_WRF3(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_QDR_PI_1_M0_R1_CFG,EN,CODE,GEAR,en,code,gear);
                end
                {1'b1, RANK_ALL} : begin
                    `CSR_WRF3(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_QDR_PI_1_M0_R1_CFG,EN,CODE,GEAR,en,code,gear);
                    `CSR_WRF3(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_QDR_PI_1_M0_R0_CFG,EN,CODE,GEAR,en,code,gear);
                    `CSR_WRF3(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_QDR_PI_1_M0_R1_CFG,EN,CODE,GEAR,en,code,gear);
                    `CSR_WRF3(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_QDR_PI_1_M0_R0_CFG,EN,CODE,GEAR,en,code,gear);
                end
                {1'b0, RANK_ALL} : begin
                    `CSR_WRF3(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_QDR_PI_0_M0_R1_CFG,EN,CODE,GEAR,en,code,gear);
                    `CSR_WRF3(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_QDR_PI_0_M0_R0_CFG,EN,CODE,GEAR,en,code,gear);
                    `CSR_WRF3(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_QDR_PI_0_M0_R1_CFG,EN,CODE,GEAR,en,code,gear);
                    `CSR_WRF3(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_QDR_PI_0_M0_R0_CFG,EN,CODE,GEAR,en,code,gear);
                end
            endcase
        end
        if((byte_sel == DQ1 ) || (byte_sel == DQ_ALL) || (byte_sel == ALL)) begin
            case({pi_sel, rank_sel})
                {1'b0, RANK0} : begin
                    `CSR_WRF3(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_QDR_PI_0_M0_R0_CFG,EN,CODE,GEAR,en,code,gear);
                    `CSR_WRF3(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_QDR_PI_0_M0_R0_CFG,EN,CODE,GEAR,en,code,gear);
                end
                {1'b1, RANK0} : begin
                    `CSR_WRF3(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_QDR_PI_1_M0_R0_CFG,EN,CODE,GEAR,en,code,gear);
                    `CSR_WRF3(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_QDR_PI_1_M0_R0_CFG,EN,CODE,GEAR,en,code,gear);
                end
                {1'b0, RANK1} : begin
                    `CSR_WRF3(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_QDR_PI_0_M0_R1_CFG,EN,CODE,GEAR,en,code,gear);
                    `CSR_WRF3(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_QDR_PI_0_M0_R1_CFG,EN,CODE,GEAR,en,code,gear);
                end
                {1'b1, RANK1} : begin
                    `CSR_WRF3(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_QDR_PI_1_M0_R1_CFG,EN,CODE,GEAR,en,code,gear);
                    `CSR_WRF3(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_QDR_PI_1_M0_R1_CFG,EN,CODE,GEAR,en,code,gear);
                end
                {1'b1, RANK_ALL} : begin
                    `CSR_WRF3(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_QDR_PI_1_M0_R1_CFG,EN,CODE,GEAR,en,code,gear);
                    `CSR_WRF3(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_QDR_PI_1_M0_R0_CFG,EN,CODE,GEAR,en,code,gear);
                    `CSR_WRF3(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_QDR_PI_1_M0_R1_CFG,EN,CODE,GEAR,en,code,gear);
                    `CSR_WRF3(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_QDR_PI_1_M0_R0_CFG,EN,CODE,GEAR,en,code,gear);
                end
                {1'b0, RANK_ALL} : begin
                    `CSR_WRF3(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_QDR_PI_0_M0_R1_CFG,EN,CODE,GEAR,en,code,gear);
                    `CSR_WRF3(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_QDR_PI_0_M0_R0_CFG,EN,CODE,GEAR,en,code,gear);
                    `CSR_WRF3(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_QDR_PI_0_M0_R1_CFG,EN,CODE,GEAR,en,code,gear);
                    `CSR_WRF3(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_QDR_PI_0_M0_R0_CFG,EN,CODE,GEAR,en,code,gear);
                end
            endcase
        end
        if((byte_sel == CA) || (byte_sel == ALL)) begin
            case({pi_sel, rank_sel})
                {1'b0, RANK0} : begin
                    `CSR_WRF3(DDR_CH0_CA_OFFSET,DDR_CA_DQS_TX_QDR_PI_0_M0_R0_CFG,EN,CODE,GEAR,en,code,gear);
                    `CSR_WRF3(DDR_CH1_CA_OFFSET,DDR_CA_DQS_TX_QDR_PI_0_M0_R0_CFG,EN,CODE,GEAR,en,code,gear);
                end
                {1'b1, RANK0} : begin
                    `CSR_WRF3(DDR_CH0_CA_OFFSET,DDR_CA_DQS_TX_QDR_PI_1_M0_R0_CFG,EN,CODE,GEAR,en,code,gear);
                    `CSR_WRF3(DDR_CH1_CA_OFFSET,DDR_CA_DQS_TX_QDR_PI_1_M0_R0_CFG,EN,CODE,GEAR,en,code,gear);
                end
                {1'b0, RANK1} : begin
                    `CSR_WRF3(DDR_CH0_CA_OFFSET,DDR_CA_DQS_TX_QDR_PI_0_M0_R1_CFG,EN,CODE,GEAR,en,code,gear);
                    `CSR_WRF3(DDR_CH1_CA_OFFSET,DDR_CA_DQS_TX_QDR_PI_0_M0_R1_CFG,EN,CODE,GEAR,en,code,gear);
                end
                {1'b1, RANK1} : begin
                    `CSR_WRF3(DDR_CH0_CA_OFFSET,DDR_CA_DQS_TX_QDR_PI_1_M0_R1_CFG,EN,CODE,GEAR,en,code,gear);
                    `CSR_WRF3(DDR_CH1_CA_OFFSET,DDR_CA_DQS_TX_QDR_PI_1_M0_R1_CFG,EN,CODE,GEAR,en,code,gear);
                end
                {1'b1, RANK_ALL} : begin
                    `CSR_WRF3(DDR_CH0_CA_OFFSET,DDR_CA_DQS_TX_QDR_PI_1_M0_R1_CFG,EN,CODE,GEAR,en,code,gear);
                    `CSR_WRF3(DDR_CH0_CA_OFFSET,DDR_CA_DQS_TX_QDR_PI_1_M0_R0_CFG,EN,CODE,GEAR,en,code,gear);
                    `CSR_WRF3(DDR_CH1_CA_OFFSET,DDR_CA_DQS_TX_QDR_PI_1_M0_R1_CFG,EN,CODE,GEAR,en,code,gear);
                    `CSR_WRF3(DDR_CH1_CA_OFFSET,DDR_CA_DQS_TX_QDR_PI_1_M0_R0_CFG,EN,CODE,GEAR,en,code,gear);
                end
                {1'b0, RANK_ALL} : begin
                    `CSR_WRF3(DDR_CH0_CA_OFFSET,DDR_CA_DQS_TX_QDR_PI_0_M0_R1_CFG,EN,CODE,GEAR,en,code,gear);
                    `CSR_WRF3(DDR_CH0_CA_OFFSET,DDR_CA_DQS_TX_QDR_PI_0_M0_R0_CFG,EN,CODE,GEAR,en,code,gear);
                    `CSR_WRF3(DDR_CH1_CA_OFFSET,DDR_CA_DQS_TX_QDR_PI_0_M0_R1_CFG,EN,CODE,GEAR,en,code,gear);
                    `CSR_WRF3(DDR_CH1_CA_OFFSET,DDR_CA_DQS_TX_QDR_PI_0_M0_R0_CFG,EN,CODE,GEAR,en,code,gear);
                end
            endcase
        end
    end
endtask

task automatic set_tx_dqs_ddr_pi_cfg;
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
                    `CSR_WRF3(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_DDR_PI_0_M0_R0_CFG,EN,CODE,GEAR,en,code,gear);
                    `CSR_WRF3(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_DDR_PI_0_M0_R0_CFG,EN,CODE,GEAR,en,code,gear);
                end
                {1'b1, RANK0} : begin
                    `CSR_WRF3(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_DDR_PI_1_M0_R0_CFG,EN,CODE,GEAR,en,code,gear);
                    `CSR_WRF3(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_DDR_PI_1_M0_R0_CFG,EN,CODE,GEAR,en,code,gear);
                end
                {1'b0, RANK1} : begin
                    `CSR_WRF3(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_DDR_PI_0_M0_R1_CFG,EN,CODE,GEAR,en,code,gear);
                    `CSR_WRF3(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_DDR_PI_0_M0_R1_CFG,EN,CODE,GEAR,en,code,gear);
                end
                {1'b1, RANK1} : begin
                    `CSR_WRF3(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_DDR_PI_1_M0_R1_CFG,EN,CODE,GEAR,en,code,gear);
                    `CSR_WRF3(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_DDR_PI_1_M0_R1_CFG,EN,CODE,GEAR,en,code,gear);
                end
                {1'b1, RANK_ALL} : begin
                    `CSR_WRF3(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_DDR_PI_1_M0_R0_CFG,EN,CODE,GEAR,en,code,gear);
                    `CSR_WRF3(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_DDR_PI_1_M0_R1_CFG,EN,CODE,GEAR,en,code,gear);
                    `CSR_WRF3(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_DDR_PI_1_M0_R0_CFG,EN,CODE,GEAR,en,code,gear);
                    `CSR_WRF3(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_DDR_PI_1_M0_R1_CFG,EN,CODE,GEAR,en,code,gear);
                end
                {1'b0, RANK_ALL} : begin
                    `CSR_WRF3(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_DDR_PI_0_M0_R0_CFG,EN,CODE,GEAR,en,code,gear);
                    `CSR_WRF3(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_DDR_PI_0_M0_R1_CFG,EN,CODE,GEAR,en,code,gear);
                    `CSR_WRF3(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_DDR_PI_0_M0_R0_CFG,EN,CODE,GEAR,en,code,gear);
                    `CSR_WRF3(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_DDR_PI_0_M0_R1_CFG,EN,CODE,GEAR,en,code,gear);
                end
            endcase
        end
        if((byte_sel == DQ1 ) || (byte_sel == DQ_ALL) || (byte_sel == ALL)) begin
            case({pi_sel, rank_sel})
                {1'b0, RANK0} : begin
                    `CSR_WRF3(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_DDR_PI_0_M0_R0_CFG,EN,CODE,GEAR,en,code,gear);
                    `CSR_WRF3(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_DDR_PI_0_M0_R0_CFG,EN,CODE,GEAR,en,code,gear);
                end
                {1'b1, RANK0} : begin
                    `CSR_WRF3(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_DDR_PI_1_M0_R0_CFG,EN,CODE,GEAR,en,code,gear);
                    `CSR_WRF3(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_DDR_PI_1_M0_R0_CFG,EN,CODE,GEAR,en,code,gear);
                end
                {1'b0, RANK1} : begin
                    `CSR_WRF3(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_DDR_PI_0_M0_R1_CFG,EN,CODE,GEAR,en,code,gear);
                    `CSR_WRF3(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_DDR_PI_0_M0_R1_CFG,EN,CODE,GEAR,en,code,gear);
                end
                {1'b1, RANK1} : begin
                    `CSR_WRF3(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_DDR_PI_1_M0_R1_CFG,EN,CODE,GEAR,en,code,gear);
                    `CSR_WRF3(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_DDR_PI_1_M0_R1_CFG,EN,CODE,GEAR,en,code,gear);
                end
                {1'b1, RANK_ALL} : begin
                    `CSR_WRF3(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_DDR_PI_1_M0_R0_CFG,EN,CODE,GEAR,en,code,gear);
                    `CSR_WRF3(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_DDR_PI_1_M0_R1_CFG,EN,CODE,GEAR,en,code,gear);
                    `CSR_WRF3(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_DDR_PI_1_M0_R0_CFG,EN,CODE,GEAR,en,code,gear);
                    `CSR_WRF3(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_DDR_PI_1_M0_R1_CFG,EN,CODE,GEAR,en,code,gear);
                end
                {1'b0, RANK_ALL} : begin
                    `CSR_WRF3(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_DDR_PI_0_M0_R0_CFG,EN,CODE,GEAR,en,code,gear);
                    `CSR_WRF3(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_DDR_PI_0_M0_R1_CFG,EN,CODE,GEAR,en,code,gear);
                    `CSR_WRF3(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_DDR_PI_0_M0_R0_CFG,EN,CODE,GEAR,en,code,gear);
                    `CSR_WRF3(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_DDR_PI_0_M0_R1_CFG,EN,CODE,GEAR,en,code,gear);
                end
            endcase
        end
        if((byte_sel == CA) || (byte_sel == ALL)) begin
            case({pi_sel, rank_sel})
                {1'b0, RANK0} : begin
                    `CSR_WRF3(DDR_CH0_CA_OFFSET,DDR_CA_DQS_TX_DDR_PI_0_M0_R0_CFG,EN,CODE,GEAR,en,code,gear);
                    `CSR_WRF3(DDR_CH1_CA_OFFSET,DDR_CA_DQS_TX_DDR_PI_0_M0_R0_CFG,EN,CODE,GEAR,en,code,gear);
                end
                {1'b1, RANK0} : begin
                    `CSR_WRF3(DDR_CH0_CA_OFFSET,DDR_CA_DQS_TX_DDR_PI_1_M0_R0_CFG,EN,CODE,GEAR,en,code,gear);
                    `CSR_WRF3(DDR_CH1_CA_OFFSET,DDR_CA_DQS_TX_DDR_PI_1_M0_R0_CFG,EN,CODE,GEAR,en,code,gear);
                end
                {1'b0, RANK1} : begin
                    `CSR_WRF3(DDR_CH0_CA_OFFSET,DDR_CA_DQS_TX_DDR_PI_0_M0_R1_CFG,EN,CODE,GEAR,en,code,gear);
                    `CSR_WRF3(DDR_CH1_CA_OFFSET,DDR_CA_DQS_TX_DDR_PI_0_M0_R1_CFG,EN,CODE,GEAR,en,code,gear);
                end
                {1'b1, RANK1} : begin
                    `CSR_WRF3(DDR_CH0_CA_OFFSET,DDR_CA_DQS_TX_DDR_PI_1_M0_R1_CFG,EN,CODE,GEAR,en,code,gear);
                    `CSR_WRF3(DDR_CH1_CA_OFFSET,DDR_CA_DQS_TX_DDR_PI_1_M0_R1_CFG,EN,CODE,GEAR,en,code,gear);
                end
                {1'b1, RANK_ALL} : begin
                    `CSR_WRF3(DDR_CH0_CA_OFFSET,DDR_CA_DQS_TX_DDR_PI_1_M0_R0_CFG,EN,CODE,GEAR,en,code,gear);
                    `CSR_WRF3(DDR_CH0_CA_OFFSET,DDR_CA_DQS_TX_DDR_PI_1_M0_R1_CFG,EN,CODE,GEAR,en,code,gear);
                    `CSR_WRF3(DDR_CH1_CA_OFFSET,DDR_CA_DQS_TX_DDR_PI_1_M0_R0_CFG,EN,CODE,GEAR,en,code,gear);
                    `CSR_WRF3(DDR_CH1_CA_OFFSET,DDR_CA_DQS_TX_DDR_PI_1_M0_R1_CFG,EN,CODE,GEAR,en,code,gear);
                end
                {1'b0, RANK_ALL} : begin
                    `CSR_WRF3(DDR_CH0_CA_OFFSET,DDR_CA_DQS_TX_DDR_PI_0_M0_R0_CFG,EN,CODE,GEAR,en,code,gear);
                    `CSR_WRF3(DDR_CH0_CA_OFFSET,DDR_CA_DQS_TX_DDR_PI_0_M0_R1_CFG,EN,CODE,GEAR,en,code,gear);
                    `CSR_WRF3(DDR_CH1_CA_OFFSET,DDR_CA_DQS_TX_DDR_PI_0_M0_R0_CFG,EN,CODE,GEAR,en,code,gear);
                    `CSR_WRF3(DDR_CH1_CA_OFFSET,DDR_CA_DQS_TX_DDR_PI_0_M0_R1_CFG,EN,CODE,GEAR,en,code,gear);
                end
            endcase
        end
    end
endtask

task automatic set_tx_dqs_sdr_rt_pi_cfg;
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
                    `CSR_WRF4(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_PI_RT_M0_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_PI_RT_M0_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                end
                {RANK1} : begin
                    `CSR_WRF4(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_PI_RT_M0_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_PI_RT_M0_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                end
                {RANK_ALL} : begin
                    `CSR_WRF4(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_PI_RT_M0_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_PI_RT_M0_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_PI_RT_M0_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_PI_RT_M0_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                end
            endcase
        end
        if((byte_sel == DQ1 ) || (byte_sel == DQ_ALL) || (byte_sel == ALL)) begin
            case({rank_sel})
                {RANK0} : begin
                    `CSR_WRF4(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_PI_RT_M0_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_PI_RT_M0_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                end
                {RANK1} : begin
                    `CSR_WRF4(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_PI_RT_M0_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_PI_RT_M0_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                end
                {RANK_ALL} : begin
                    `CSR_WRF4(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_PI_RT_M0_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_PI_RT_M0_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_PI_RT_M0_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_PI_RT_M0_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                end
            endcase
        end
        if((byte_sel == CA) || (byte_sel == ALL)) begin
            case({rank_sel})
                {RANK0} : begin
                    `CSR_WRF4(DDR_CH0_CA_OFFSET,DDR_CA_DQS_TX_PI_RT_M0_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_CA_OFFSET,DDR_CA_DQS_TX_PI_RT_M0_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                end
                {RANK1} : begin
                    `CSR_WRF4(DDR_CH0_CA_OFFSET,DDR_CA_DQS_TX_PI_RT_M0_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_CA_OFFSET,DDR_CA_DQS_TX_PI_RT_M0_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                end
                {RANK_ALL} : begin
                    `CSR_WRF4(DDR_CH0_CA_OFFSET,DDR_CA_DQS_TX_PI_RT_M0_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH0_CA_OFFSET,DDR_CA_DQS_TX_PI_RT_M0_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_CA_OFFSET,DDR_CA_DQS_TX_PI_RT_M0_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_CA_OFFSET,DDR_CA_DQS_TX_PI_RT_M0_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                end
            endcase
        end
    end
endtask

task automatic set_tx_match_pi_cfg;
    input byte_sel_t  byte_sel;
    input rank_sel_t  rank_sel;
    input logic       en;
    input logic [3:0] gear;
    input logic [3:0] xcpl;
    begin
        if((byte_sel == DQ0 ) || (byte_sel == DQ_ALL) || (byte_sel == ALL)) begin
            case({rank_sel})
                {RANK0} : begin
                    `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_PI_M0_R0_CFG,EN,GEAR,en,gear);
                    `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_DFI_PI_M0_R0_CFG,EN,GEAR,en,gear);
                    `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_PI_M0_R0_CFG,EN,GEAR,en,gear);
                    `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_DFI_PI_M0_R0_CFG,EN,GEAR,en,gear);
                end
                {RANK1} : begin
                    `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_PI_M0_R1_CFG,EN,GEAR,en,gear);
                    `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_DFI_PI_M0_R1_CFG,EN,GEAR,en,gear);
                    `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_PI_M0_R1_CFG,EN,GEAR,en,gear);
                    `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_DFI_PI_M0_R1_CFG,EN,GEAR,en,gear);
                end
                {RANK_ALL} : begin
                    `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_PI_M0_R0_CFG,EN,GEAR,en,gear);
                    `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_PI_M0_R1_CFG,EN,GEAR,en,gear);
                    `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_DFI_PI_M0_R0_CFG,EN,GEAR,en,gear);
                    `CSR_WRF2(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_DFI_PI_M0_R1_CFG,EN,GEAR,en,gear);
                    `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_PI_M0_R0_CFG,EN,GEAR,en,gear);
                    `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_PI_M0_R1_CFG,EN,GEAR,en,gear);
                    `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_DFI_PI_M0_R0_CFG,EN,GEAR,en,gear);
                    `CSR_WRF2(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_DFI_PI_M0_R1_CFG,EN,GEAR,en,gear);
                end
            endcase
        end
        if((byte_sel == DQ1 ) || (byte_sel == DQ_ALL) || (byte_sel == ALL)) begin
            case({rank_sel})
                {RANK0} : begin
                    `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_PI_M0_R0_CFG,EN,GEAR,en,gear);
                    `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_DFI_PI_M0_R0_CFG,EN,GEAR,en,gear);
                    `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_PI_M0_R0_CFG,EN,GEAR,en,gear);
                    `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_DFI_PI_M0_R0_CFG,EN,GEAR,en,gear);
                end
                {RANK1} : begin
                    `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_PI_M0_R1_CFG,EN,GEAR,en,gear);
                    `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_DFI_PI_M0_R1_CFG,EN,GEAR,en,gear);
                    `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_PI_M0_R1_CFG,EN,GEAR,en,gear);
                    `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_DFI_PI_M0_R1_CFG,EN,GEAR,en,gear);
                end
                {RANK_ALL} : begin
                    `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_PI_M0_R0_CFG,EN,GEAR,en,gear);
                    `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_PI_M0_R1_CFG,EN,GEAR,en,gear);
                    `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_DFI_PI_M0_R0_CFG,EN,GEAR,en,gear);
                    `CSR_WRF2(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_DFI_PI_M0_R1_CFG,EN,GEAR,en,gear);
                    `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_PI_M0_R0_CFG,EN,GEAR,en,gear);
                    `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_PI_M0_R1_CFG,EN,GEAR,en,gear);
                    `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_DFI_PI_M0_R0_CFG,EN,GEAR,en,gear);
                    `CSR_WRF2(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_DFI_PI_M0_R1_CFG,EN,GEAR,en,gear);
                end
            endcase
        end
        if((byte_sel == CA) || (byte_sel == ALL)) begin
            case({rank_sel})
                {RANK0} : begin
                    `CSR_WRF2(DDR_CH0_CA_OFFSET,DDR_CA_DQS_TX_SDR_PI_M0_R0_CFG,EN,GEAR,en,gear);
                    `CSR_WRF2(DDR_CH0_CA_OFFSET,DDR_CA_DQS_TX_DFI_PI_M0_R0_CFG,EN,GEAR,en,gear);
                    `CSR_WRF2(DDR_CH1_CA_OFFSET,DDR_CA_DQS_TX_SDR_PI_M0_R0_CFG,EN,GEAR,en,gear);
                    `CSR_WRF2(DDR_CH1_CA_OFFSET,DDR_CA_DQS_TX_DFI_PI_M0_R0_CFG,EN,GEAR,en,gear);
                end
                {RANK1} : begin
                    `CSR_WRF2(DDR_CH0_CA_OFFSET,DDR_CA_DQS_TX_SDR_PI_M0_R1_CFG,EN,GEAR,en,gear);
                    `CSR_WRF2(DDR_CH0_CA_OFFSET,DDR_CA_DQS_TX_DFI_PI_M0_R1_CFG,EN,GEAR,en,gear);
                    `CSR_WRF2(DDR_CH1_CA_OFFSET,DDR_CA_DQS_TX_SDR_PI_M0_R1_CFG,EN,GEAR,en,gear);
                    `CSR_WRF2(DDR_CH1_CA_OFFSET,DDR_CA_DQS_TX_DFI_PI_M0_R1_CFG,EN,GEAR,en,gear);
                end
                {RANK_ALL} : begin
                    `CSR_WRF2(DDR_CH0_CA_OFFSET,DDR_CA_DQS_TX_SDR_PI_M0_R0_CFG,EN,GEAR,en,gear);
                    `CSR_WRF2(DDR_CH0_CA_OFFSET,DDR_CA_DQS_TX_SDR_PI_M0_R1_CFG,EN,GEAR,en,gear);
                    `CSR_WRF2(DDR_CH0_CA_OFFSET,DDR_CA_DQS_TX_DFI_PI_M0_R0_CFG,EN,GEAR,en,gear);
                    `CSR_WRF2(DDR_CH0_CA_OFFSET,DDR_CA_DQS_TX_DFI_PI_M0_R1_CFG,EN,GEAR,en,gear);
                    `CSR_WRF2(DDR_CH1_CA_OFFSET,DDR_CA_DQS_TX_SDR_PI_M0_R0_CFG,EN,GEAR,en,gear);
                    `CSR_WRF2(DDR_CH1_CA_OFFSET,DDR_CA_DQS_TX_SDR_PI_M0_R1_CFG,EN,GEAR,en,gear);
                    `CSR_WRF2(DDR_CH1_CA_OFFSET,DDR_CA_DQS_TX_DFI_PI_M0_R0_CFG,EN,GEAR,en,gear);
                    `CSR_WRF2(DDR_CH1_CA_OFFSET,DDR_CA_DQS_TX_DFI_PI_M0_R1_CFG,EN,GEAR,en,gear);
                end
            endcase
        end
    end
endtask

task automatic set_tx_dq_qdr_pi_cfg;
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
                    `CSR_WRF4(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_PI_0_M0_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_PI_0_M0_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                end
                {1'b1, RANK0} : begin
                    `CSR_WRF4(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_PI_1_M0_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_PI_1_M0_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                end
                {1'b0, RANK1} : begin
                    `CSR_WRF4(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_PI_0_M0_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_PI_0_M0_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                end
                {1'b1, RANK1} : begin
                    `CSR_WRF4(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_PI_1_M0_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_PI_1_M0_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                end
                {1'b1, RANK_ALL} : begin
                    `CSR_WRF4(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_PI_1_M0_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_PI_1_M0_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_PI_1_M0_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_PI_1_M0_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                end
                {1'b0, RANK_ALL} : begin
                    `CSR_WRF4(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_PI_0_M0_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_PI_0_M0_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_PI_0_M0_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_PI_0_M0_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                end
            endcase
        end
        if((byte_sel == DQ1 ) || (byte_sel == DQ_ALL) || (byte_sel == ALL)) begin
            case({pi_sel, rank_sel})
                {1'b0, RANK0} : begin
                    `CSR_WRF4(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_PI_0_M0_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_PI_0_M0_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                end
                {1'b1, RANK0} : begin
                    `CSR_WRF4(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_PI_1_M0_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_PI_1_M0_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                end
                {1'b0, RANK1} : begin
                    `CSR_WRF4(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_PI_0_M0_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_PI_0_M0_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                end
                {1'b1, RANK1} : begin
                    `CSR_WRF4(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_PI_1_M0_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_PI_1_M0_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                end
                {1'b1, RANK_ALL} : begin
                    `CSR_WRF4(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_PI_1_M0_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_PI_1_M0_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_PI_1_M0_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_PI_1_M0_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                end
                {1'b0, RANK_ALL} : begin
                    `CSR_WRF4(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_PI_0_M0_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_PI_0_M0_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_PI_0_M0_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_PI_0_M0_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                end
            endcase
        end
        if((byte_sel == CA) || (byte_sel == ALL)) begin
            case({pi_sel, rank_sel})
                {1'b0, RANK0} : begin
                    `CSR_WRF4(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_QDR_PI_0_M0_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_QDR_PI_0_M0_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                end
                {1'b1, RANK0} : begin
                    `CSR_WRF4(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_QDR_PI_1_M0_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_QDR_PI_1_M0_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                end
                {1'b0, RANK1} : begin
                    `CSR_WRF4(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_QDR_PI_0_M0_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_QDR_PI_0_M0_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                end
                {1'b1, RANK1} : begin
                    `CSR_WRF4(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_QDR_PI_1_M0_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_QDR_PI_1_M0_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                end
                {1'b1, RANK_ALL} : begin
                    `CSR_WRF4(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_QDR_PI_1_M0_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_QDR_PI_1_M0_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_QDR_PI_1_M0_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_QDR_PI_1_M0_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                end
                {1'b0, RANK_ALL} : begin
                    `CSR_WRF4(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_QDR_PI_0_M0_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_QDR_PI_0_M0_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_QDR_PI_0_M0_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_QDR_PI_0_M0_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                end
            endcase
        end
    end
endtask

task automatic set_tx_dq_ddr_pi_cfg;
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
                    `CSR_WRF4(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_PI_0_M0_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_PI_0_M0_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                end
                {1'b1, RANK0} : begin
                    `CSR_WRF4(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_PI_1_M0_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_PI_1_M0_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                end
                {1'b0, RANK1} : begin
                    `CSR_WRF4(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_PI_0_M0_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_PI_0_M0_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                end
                {1'b1, RANK1} : begin
                    `CSR_WRF4(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_PI_1_M0_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_PI_1_M0_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                end
                {1'b1, RANK_ALL} : begin
                    `CSR_WRF4(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_PI_1_M0_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_PI_1_M0_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_PI_1_M0_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_PI_1_M0_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                end
                {1'b0, RANK_ALL} : begin
                    `CSR_WRF4(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_PI_0_M0_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_PI_0_M0_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_PI_0_M0_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_PI_0_M0_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                end
            endcase
        end
        if((byte_sel == DQ1 ) || (byte_sel == DQ_ALL) || (byte_sel == ALL)) begin
            case({pi_sel, rank_sel})
                {1'b0, RANK0} : begin
                    `CSR_WRF4(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_PI_0_M0_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_PI_0_M0_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                end
                {1'b1, RANK0} : begin
                    `CSR_WRF4(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_PI_1_M0_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_PI_1_M0_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                end
                {1'b0, RANK1} : begin
                    `CSR_WRF4(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_PI_0_M0_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_PI_0_M0_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                end
                {1'b1, RANK1} : begin
                    `CSR_WRF4(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_PI_1_M0_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_PI_1_M0_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                end
                {1'b1, RANK_ALL} : begin
                    `CSR_WRF4(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_PI_1_M0_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_PI_1_M0_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_PI_1_M0_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_PI_1_M0_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                end
                {1'b0, RANK_ALL} : begin
                    `CSR_WRF4(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_PI_0_M0_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_PI_0_M0_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_PI_0_M0_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_PI_0_M0_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                end
            endcase
        end
        if((byte_sel == CA) || (byte_sel == ALL)) begin
            case({pi_sel, rank_sel})
                {1'b0, RANK0} : begin
                    `CSR_WRF4(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_DDR_PI_0_M0_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_DDR_PI_0_M0_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                end
                {1'b1, RANK0} : begin
                    `CSR_WRF4(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_DDR_PI_1_M0_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_DDR_PI_1_M0_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                end
                {1'b0, RANK1} : begin
                    `CSR_WRF4(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_DDR_PI_0_M0_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_DDR_PI_0_M0_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                end
                {1'b1, RANK1} : begin
                    `CSR_WRF4(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_DDR_PI_1_M0_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_DDR_PI_1_M0_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                end
                {1'b1, RANK_ALL} : begin
                    `CSR_WRF4(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_DDR_PI_1_M0_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_DDR_PI_1_M0_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_DDR_PI_1_M0_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_DDR_PI_1_M0_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                end
                {1'b0, RANK_ALL} : begin
                    `CSR_WRF4(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_DDR_PI_0_M0_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_DDR_PI_0_M0_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_DDR_PI_0_M0_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_DDR_PI_0_M0_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                end
            endcase
        end
    end
endtask

task automatic set_tx_dq_sdr_rt_pi_cfg;
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
                    `CSR_WRF4(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_PI_RT_M0_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_PI_RT_M0_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                end
                {RANK1} : begin
                    `CSR_WRF4(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_PI_RT_M0_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_PI_RT_M0_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                end
                {RANK_ALL} : begin
                    `CSR_WRF4(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_PI_RT_M0_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_PI_RT_M0_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_PI_RT_M0_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_PI_RT_M0_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                end
            endcase
        end
        if((byte_sel == DQ1 ) || (byte_sel == DQ_ALL) || (byte_sel == ALL)) begin
            case({rank_sel})
                {RANK0} : begin
                    `CSR_WRF4(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_PI_RT_M0_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_PI_RT_M0_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                end
                {RANK1} : begin
                    `CSR_WRF4(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_PI_RT_M0_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_PI_RT_M0_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                end
                {RANK_ALL} : begin
                    `CSR_WRF4(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_PI_RT_M0_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_PI_RT_M0_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_PI_RT_M0_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_PI_RT_M0_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                end
            endcase
        end
        if((byte_sel == CA) || (byte_sel == ALL)) begin
            case({rank_sel})
                {RANK0} : begin
                    `CSR_WRF4(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_PI_RT_M0_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_PI_RT_M0_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                end
                {RANK1} : begin
                    `CSR_WRF4(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_PI_RT_M0_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_PI_RT_M0_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                end
                {RANK_ALL} : begin
                    `CSR_WRF4(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_PI_RT_M0_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_PI_RT_M0_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_PI_RT_M0_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_PI_RT_M0_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                end
            endcase
        end
    end
endtask

task automatic set_rx_ren_pi_cfg;
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
                    `CSR_WRF4(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_RX_REN_PI_M0_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_RX_REN_PI_M0_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                end
                {RANK1} : begin
                    `CSR_WRF4(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_RX_REN_PI_M0_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_RX_REN_PI_M0_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                end
                {RANK_ALL} : begin
                    `CSR_WRF4(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_RX_REN_PI_M0_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_RX_REN_PI_M0_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_RX_REN_PI_M0_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_RX_REN_PI_M0_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                end
            endcase
        end
        if((byte_sel == DQ1) || (byte_sel == DQ_ALL) || (byte_sel == ALL)) begin
            case({rank_sel})
                {RANK0} : begin
                    `CSR_WRF4(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_RX_REN_PI_M0_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_RX_REN_PI_M0_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                end
                {RANK1} : begin
                    `CSR_WRF4(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_RX_REN_PI_M0_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_RX_REN_PI_M0_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                end
                {RANK_ALL} : begin
                    `CSR_WRF4(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_RX_REN_PI_M0_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_RX_REN_PI_M0_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_RX_REN_PI_M0_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_RX_REN_PI_M0_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                end
            endcase
        end
        if((byte_sel == CA) || (byte_sel == ALL)) begin
            case({rank_sel})
                {RANK0} : begin
                    `CSR_WRF4(DDR_CH0_CA_OFFSET,DDR_CA_DQS_RX_REN_PI_M0_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_CA_OFFSET,DDR_CA_DQS_RX_REN_PI_M0_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                end
                {RANK1} : begin
                    `CSR_WRF4(DDR_CH0_CA_OFFSET,DDR_CA_DQS_RX_REN_PI_M0_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_CA_OFFSET,DDR_CA_DQS_RX_REN_PI_M0_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                end
                {RANK_ALL} : begin
                    `CSR_WRF4(DDR_CH0_CA_OFFSET,DDR_CA_DQS_RX_REN_PI_M0_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH0_CA_OFFSET,DDR_CA_DQS_RX_REN_PI_M0_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_CA_OFFSET,DDR_CA_DQS_RX_REN_PI_M0_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_CA_OFFSET,DDR_CA_DQS_RX_REN_PI_M0_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                end
            endcase
        end
    end
endtask

task automatic set_rx_rcs_pi_cfg;
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
                    `CSR_WRF4(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_RX_RCS_PI_M0_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_RX_RCS_PI_M0_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                end
                {RANK1} : begin
                    `CSR_WRF4(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_RX_RCS_PI_M0_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_RX_RCS_PI_M0_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                end
                {RANK_ALL} : begin
                    `CSR_WRF4(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_RX_RCS_PI_M0_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_RX_RCS_PI_M0_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_RX_RCS_PI_M0_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_RX_RCS_PI_M0_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                end
            endcase
        end
        if((byte_sel == DQ1) || (byte_sel == DQ_ALL) || (byte_sel == ALL)) begin
            case({rank_sel})
                {RANK0} : begin
                    `CSR_WRF4(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_RX_RCS_PI_M0_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_RX_RCS_PI_M0_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                end
                {RANK1} : begin
                    `CSR_WRF4(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_RX_RCS_PI_M0_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_RX_RCS_PI_M0_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                end
                {RANK_ALL} : begin
                    `CSR_WRF4(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_RX_RCS_PI_M0_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_RX_RCS_PI_M0_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_RX_RCS_PI_M0_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_RX_RCS_PI_M0_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                end
            endcase
        end
        if((byte_sel == CA) || (byte_sel == ALL)) begin
            case({rank_sel})
                {RANK0} : begin
                    `CSR_WRF4(DDR_CH0_CA_OFFSET,DDR_CA_DQS_RX_RCS_PI_M0_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_CA_OFFSET,DDR_CA_DQS_RX_RCS_PI_M0_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                end
                {RANK1} : begin
                    `CSR_WRF4(DDR_CH0_CA_OFFSET,DDR_CA_DQS_RX_RCS_PI_M0_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_CA_OFFSET,DDR_CA_DQS_RX_RCS_PI_M0_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                end
                {RANK_ALL} : begin
                    `CSR_WRF4(DDR_CH0_CA_OFFSET,DDR_CA_DQS_RX_RCS_PI_M0_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH0_CA_OFFSET,DDR_CA_DQS_RX_RCS_PI_M0_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_CA_OFFSET,DDR_CA_DQS_RX_RCS_PI_M0_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_CA_OFFSET,DDR_CA_DQS_RX_RCS_PI_M0_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                end
            endcase
        end
    end
endtask

task automatic set_rx_rdqs_pi_cfg;
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
                    `CSR_WRF4(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_RX_RDQS_PI_1_M0_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_RX_RDQS_PI_1_M0_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                end
                {1'b0, RANK0} : begin
                    `CSR_WRF4(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_RX_RDQS_PI_0_M0_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_RX_RDQS_PI_0_M0_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                end
                {1'b1, RANK1} : begin
                    `CSR_WRF4(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_RX_RDQS_PI_1_M0_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_RX_RDQS_PI_1_M0_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                end
                {1'b0, RANK1} : begin
                    `CSR_WRF4(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_RX_RDQS_PI_0_M0_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_RX_RDQS_PI_0_M0_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                end
                {1'b1, RANK_ALL} : begin
                    `CSR_WRF4(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_RX_RDQS_PI_1_M0_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_RX_RDQS_PI_1_M0_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_RX_RDQS_PI_1_M0_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_RX_RDQS_PI_1_M0_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                end
                {1'b0, RANK_ALL} : begin
                    `CSR_WRF4(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_RX_RDQS_PI_0_M0_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_RX_RDQS_PI_0_M0_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_RX_RDQS_PI_0_M0_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_RX_RDQS_PI_0_M0_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                end
            endcase
        end
        if((byte_sel == DQ1) || (byte_sel == DQ_ALL) || (byte_sel == ALL)) begin
            case({pi_sel, rank_sel})
                {1'b1, RANK0} : begin
                    `CSR_WRF4(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_RX_RDQS_PI_1_M0_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_RX_RDQS_PI_1_M0_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                end
                {1'b0, RANK0} : begin
                    `CSR_WRF4(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_RX_RDQS_PI_0_M0_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_RX_RDQS_PI_0_M0_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                end
                {1'b1, RANK1} : begin
                    `CSR_WRF4(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_RX_RDQS_PI_1_M0_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_RX_RDQS_PI_1_M0_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                end
                {1'b0, RANK1} : begin
                    `CSR_WRF4(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_RX_RDQS_PI_0_M0_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_RX_RDQS_PI_0_M0_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                end
                {1'b1, RANK_ALL} : begin
                    `CSR_WRF4(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_RX_RDQS_PI_1_M0_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_RX_RDQS_PI_1_M0_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_RX_RDQS_PI_1_M0_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_RX_RDQS_PI_1_M0_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                end
                {1'b0, RANK_ALL} : begin
                    `CSR_WRF4(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_RX_RDQS_PI_0_M0_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_RX_RDQS_PI_0_M0_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_RX_RDQS_PI_0_M0_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_RX_RDQS_PI_0_M0_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                end
            endcase
        end
        if((byte_sel == CA) || (byte_sel == ALL)) begin
            case({pi_sel, rank_sel})
                {1'b1, RANK0} : begin
                    `CSR_WRF4(DDR_CH0_CA_OFFSET,DDR_CA_DQS_RX_RDQS_PI_1_M0_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_CA_OFFSET,DDR_CA_DQS_RX_RDQS_PI_1_M0_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                end
                {1'b0, RANK0} : begin
                    `CSR_WRF4(DDR_CH0_CA_OFFSET,DDR_CA_DQS_RX_RDQS_PI_0_M0_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_CA_OFFSET,DDR_CA_DQS_RX_RDQS_PI_0_M0_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                end
                {1'b1, RANK1} : begin
                    `CSR_WRF4(DDR_CH0_CA_OFFSET,DDR_CA_DQS_RX_RDQS_PI_1_M0_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_CA_OFFSET,DDR_CA_DQS_RX_RDQS_PI_1_M0_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                end
                {1'b0, RANK1} : begin
                    `CSR_WRF4(DDR_CH0_CA_OFFSET,DDR_CA_DQS_RX_RDQS_PI_0_M0_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_CA_OFFSET,DDR_CA_DQS_RX_RDQS_PI_0_M0_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                end
                {1'b1, RANK_ALL} : begin
                    `CSR_WRF4(DDR_CH0_CA_OFFSET,DDR_CA_DQS_RX_RDQS_PI_1_M0_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH0_CA_OFFSET,DDR_CA_DQS_RX_RDQS_PI_1_M0_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_CA_OFFSET,DDR_CA_DQS_RX_RDQS_PI_1_M0_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_CA_OFFSET,DDR_CA_DQS_RX_RDQS_PI_1_M0_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                end
                {1'b0, RANK_ALL} : begin
                    `CSR_WRF4(DDR_CH0_CA_OFFSET,DDR_CA_DQS_RX_RDQS_PI_0_M0_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH0_CA_OFFSET,DDR_CA_DQS_RX_RDQS_PI_0_M0_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_CA_OFFSET,DDR_CA_DQS_RX_RDQS_PI_0_M0_R0_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                    `CSR_WRF4(DDR_CH1_CA_OFFSET,DDR_CA_DQS_RX_RDQS_PI_0_M0_R1_CFG,EN,CODE,GEAR,XCPL,en,code,gear,xcpl);
                end
            endcase
        end
    end
endtask

task automatic set_txdq_sdr_fc_dly;
    input byte_sel_t     byte_sel;
    input rank_sel_t     rank_sel;
    input logic    [7:0] dq;
    input logic   [31:0] fc_dly;
    begin
        if((byte_sel == DQ0) || (byte_sel == DQ_ALL) || (byte_sel == ALL)) begin
            case ({rank_sel,dq})
                {RANK0, 8'd0} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R0_CFG_0, fc_dly );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R0_CFG_0, fc_dly );
                end
                {RANK0, 8'd1} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R0_CFG_1, fc_dly );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R0_CFG_1, fc_dly );
                end
                {RANK0, 8'd2} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R0_CFG_2, fc_dly );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R0_CFG_2, fc_dly );
                end
                {RANK0, 8'd3} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R0_CFG_3, fc_dly );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R0_CFG_3, fc_dly );
                end
                {RANK0, 8'd4} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R0_CFG_4, fc_dly );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R0_CFG_4, fc_dly );
                end
                {RANK0, 8'd5} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R0_CFG_5, fc_dly );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R0_CFG_5, fc_dly );
                end
                {RANK0, 8'd6} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R0_CFG_6, fc_dly );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R0_CFG_6, fc_dly );
                end
                {RANK0, 8'd7} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R0_CFG_7, fc_dly );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R0_CFG_7, fc_dly );
                end
                {RANK0, 8'd8} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R0_CFG_8, fc_dly );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R0_CFG_8, fc_dly );
                end
                {RANK1, 8'd0} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R1_CFG_0, fc_dly );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R1_CFG_0, fc_dly );
                end
                {RANK1, 8'd1} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R1_CFG_1, fc_dly );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R1_CFG_1, fc_dly );
                end
                {RANK1, 8'd2} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R1_CFG_2, fc_dly );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R1_CFG_2, fc_dly );
                end
                {RANK1, 8'd3} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R1_CFG_3, fc_dly );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R1_CFG_3, fc_dly );
                end
                {RANK1, 8'd4} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R1_CFG_4, fc_dly );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R1_CFG_4, fc_dly );
                end
                {RANK1, 8'd5} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R1_CFG_5, fc_dly );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R1_CFG_5, fc_dly );
                end
                {RANK1, 8'd6} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R1_CFG_6, fc_dly );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R1_CFG_6, fc_dly );
                end
                {RANK1, 8'd7} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R1_CFG_7, fc_dly );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R1_CFG_7, fc_dly );
                end
                {RANK1, 8'd8} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R1_CFG_8, fc_dly );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R1_CFG_8, fc_dly );
                end
                default: begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R0_CFG_0, fc_dly );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R1_CFG_0, fc_dly );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R0_CFG_0, fc_dly );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R1_CFG_0, fc_dly );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R0_CFG_1, fc_dly );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R1_CFG_1, fc_dly );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R0_CFG_1, fc_dly );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R1_CFG_1, fc_dly );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R0_CFG_2, fc_dly );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R1_CFG_2, fc_dly );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R0_CFG_2, fc_dly );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R1_CFG_2, fc_dly );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R0_CFG_3, fc_dly );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R1_CFG_3, fc_dly );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R0_CFG_3, fc_dly );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R1_CFG_3, fc_dly );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R0_CFG_4, fc_dly );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R1_CFG_4, fc_dly );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R0_CFG_4, fc_dly );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R1_CFG_4, fc_dly );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R0_CFG_5, fc_dly );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R1_CFG_5, fc_dly );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R0_CFG_5, fc_dly );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R1_CFG_5, fc_dly );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R0_CFG_6, fc_dly );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R1_CFG_6, fc_dly );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R0_CFG_6, fc_dly );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R1_CFG_6, fc_dly );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R0_CFG_7, fc_dly );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R1_CFG_7, fc_dly );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R0_CFG_7, fc_dly );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R1_CFG_7, fc_dly );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R0_CFG_8, fc_dly );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R1_CFG_8, fc_dly );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R0_CFG_8, fc_dly );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R1_CFG_8, fc_dly );
                end
            endcase
        end
        if((byte_sel == DQ1) || (byte_sel == DQ_ALL) || (byte_sel == ALL)) begin
            case ({rank_sel,dq})
                {RANK0, 8'd0} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R0_CFG_0, fc_dly );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R0_CFG_0, fc_dly );
                end
                {RANK0, 8'd1} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R0_CFG_1, fc_dly );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R0_CFG_1, fc_dly );
                end
                {RANK0, 8'd2} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R0_CFG_2, fc_dly );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R0_CFG_2, fc_dly );
                end
                {RANK0, 8'd3} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R0_CFG_3, fc_dly );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R0_CFG_3, fc_dly );
                end
                {RANK0, 8'd4} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R0_CFG_4, fc_dly );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R0_CFG_4, fc_dly );
                end
                {RANK0, 8'd5} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R0_CFG_5, fc_dly );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R0_CFG_5, fc_dly );
                end
                {RANK0, 8'd6} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R0_CFG_6, fc_dly );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R0_CFG_6, fc_dly );
                end
                {RANK0, 8'd7} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R0_CFG_7, fc_dly );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R0_CFG_7, fc_dly );
                end
                {RANK0, 8'd8} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R0_CFG_8, fc_dly );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R0_CFG_8, fc_dly );
                end
                {RANK1, 8'd0} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R1_CFG_0, fc_dly );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R1_CFG_0, fc_dly );
                end
                {RANK1, 8'd1} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R1_CFG_1, fc_dly );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R1_CFG_1, fc_dly );
                end
                {RANK1, 8'd2} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R1_CFG_2, fc_dly );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R1_CFG_2, fc_dly );
                end
                {RANK1, 8'd3} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R1_CFG_3, fc_dly );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R1_CFG_3, fc_dly );
                end
                {RANK1, 8'd4} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R1_CFG_4, fc_dly );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R1_CFG_4, fc_dly );
                end
                {RANK1, 8'd5} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R1_CFG_5, fc_dly );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R1_CFG_5, fc_dly );
                end
                {RANK1, 8'd6} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R1_CFG_6, fc_dly );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R1_CFG_6, fc_dly );
                end
                {RANK1, 8'd7} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R1_CFG_7, fc_dly );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R1_CFG_7, fc_dly );
                end
                {RANK1, 8'd8} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R1_CFG_8, fc_dly );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R1_CFG_8, fc_dly );
                end
                default: begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R0_CFG_0, fc_dly );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R1_CFG_0, fc_dly );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R0_CFG_0, fc_dly );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R1_CFG_0, fc_dly );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R0_CFG_1, fc_dly );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R1_CFG_1, fc_dly );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R0_CFG_1, fc_dly );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R1_CFG_1, fc_dly );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R0_CFG_2, fc_dly );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R1_CFG_2, fc_dly );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R0_CFG_2, fc_dly );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R1_CFG_2, fc_dly );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R0_CFG_3, fc_dly );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R1_CFG_3, fc_dly );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R0_CFG_3, fc_dly );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R1_CFG_3, fc_dly );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R0_CFG_4, fc_dly );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R1_CFG_4, fc_dly );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R0_CFG_4, fc_dly );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R1_CFG_4, fc_dly );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R0_CFG_5, fc_dly );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R1_CFG_5, fc_dly );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R0_CFG_5, fc_dly );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R1_CFG_5, fc_dly );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R0_CFG_6, fc_dly );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R1_CFG_6, fc_dly );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R0_CFG_6, fc_dly );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R1_CFG_6, fc_dly );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R0_CFG_7, fc_dly );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R1_CFG_7, fc_dly );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R0_CFG_7, fc_dly );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R1_CFG_7, fc_dly );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R0_CFG_8, fc_dly );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R1_CFG_8, fc_dly );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R0_CFG_8, fc_dly );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_FC_DLY_M0_R1_CFG_8, fc_dly );
                end
            endcase
        end
        if((byte_sel == CA) || (byte_sel == ALL)) begin
            case ({rank_sel,dq})
                {RANK0, 8'd0} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_FC_DLY_M0_R0_CFG_0, fc_dly );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_FC_DLY_M0_R0_CFG_0, fc_dly );
                end
                {RANK0, 8'd1} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_FC_DLY_M0_R0_CFG_1, fc_dly );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_FC_DLY_M0_R0_CFG_1, fc_dly );
                end
                {RANK0, 8'd2} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_FC_DLY_M0_R0_CFG_2, fc_dly );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_FC_DLY_M0_R0_CFG_2, fc_dly );
                end
                {RANK0, 8'd3} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_FC_DLY_M0_R0_CFG_3, fc_dly );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_FC_DLY_M0_R0_CFG_3, fc_dly );
                end
                {RANK0, 8'd4} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_FC_DLY_M0_R0_CFG_4, fc_dly );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_FC_DLY_M0_R0_CFG_4, fc_dly );
                end
                {RANK0, 8'd5} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_FC_DLY_M0_R0_CFG_5, fc_dly );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_FC_DLY_M0_R0_CFG_5, fc_dly );
                end
                {RANK0, 8'd6} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_FC_DLY_M0_R0_CFG_6, fc_dly );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_FC_DLY_M0_R0_CFG_6, fc_dly );
                end
                {RANK0, 8'd7} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_FC_DLY_M0_R0_CFG_7, fc_dly );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_FC_DLY_M0_R0_CFG_7, fc_dly );
                end
                {RANK0, 8'd8} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_FC_DLY_M0_R0_CFG_8, fc_dly );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_FC_DLY_M0_R0_CFG_8, fc_dly );
                end
                {RANK0, 8'd9} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_FC_DLY_M0_R0_CFG_9, fc_dly );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_FC_DLY_M0_R0_CFG_9, fc_dly );
                end
                {RANK0, 8'd10} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_FC_DLY_M0_R0_CFG_10, fc_dly );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_FC_DLY_M0_R0_CFG_10, fc_dly );
                end
                {RANK1, 8'd0} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_FC_DLY_M0_R1_CFG_0, fc_dly );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_FC_DLY_M0_R1_CFG_0, fc_dly );
                end
                {RANK1, 8'd1} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_FC_DLY_M0_R1_CFG_1, fc_dly );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_FC_DLY_M0_R1_CFG_1, fc_dly );
                end
                {RANK1, 8'd2} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_FC_DLY_M0_R1_CFG_2, fc_dly );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_FC_DLY_M0_R1_CFG_2, fc_dly );
                end
                {RANK1, 8'd3} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_FC_DLY_M0_R1_CFG_3, fc_dly );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_FC_DLY_M0_R1_CFG_3, fc_dly );
                end
                {RANK1, 8'd4} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_FC_DLY_M0_R1_CFG_4, fc_dly );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_FC_DLY_M0_R1_CFG_4, fc_dly );
                end
                {RANK1, 8'd5} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_FC_DLY_M0_R1_CFG_5, fc_dly );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_FC_DLY_M0_R1_CFG_5, fc_dly );
                end
                {RANK1, 8'd6} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_FC_DLY_M0_R1_CFG_6, fc_dly );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_FC_DLY_M0_R1_CFG_6, fc_dly );
                end
                {RANK1, 8'd7} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_FC_DLY_M0_R1_CFG_7, fc_dly );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_FC_DLY_M0_R1_CFG_7, fc_dly );
                end
                {RANK1, 8'd8} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_FC_DLY_M0_R1_CFG_8, fc_dly );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_FC_DLY_M0_R1_CFG_8, fc_dly );
                end
                {RANK1, 8'd9} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_FC_DLY_M0_R1_CFG_9, fc_dly );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_FC_DLY_M0_R1_CFG_9, fc_dly );
                end
                {RANK1, 8'd10} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_FC_DLY_M0_R1_CFG_10, fc_dly );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_FC_DLY_M0_R1_CFG_10, fc_dly );
                end
                default: begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_FC_DLY_M0_R0_CFG_0, fc_dly );
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_FC_DLY_M0_R1_CFG_0, fc_dly );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_FC_DLY_M0_R0_CFG_0, fc_dly );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_FC_DLY_M0_R1_CFG_0, fc_dly );
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_FC_DLY_M0_R0_CFG_1, fc_dly );
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_FC_DLY_M0_R1_CFG_1, fc_dly );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_FC_DLY_M0_R0_CFG_1, fc_dly );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_FC_DLY_M0_R1_CFG_1, fc_dly );
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_FC_DLY_M0_R0_CFG_2, fc_dly );
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_FC_DLY_M0_R1_CFG_2, fc_dly );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_FC_DLY_M0_R0_CFG_2, fc_dly );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_FC_DLY_M0_R1_CFG_2, fc_dly );
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_FC_DLY_M0_R0_CFG_3, fc_dly );
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_FC_DLY_M0_R1_CFG_3, fc_dly );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_FC_DLY_M0_R0_CFG_3, fc_dly );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_FC_DLY_M0_R1_CFG_3, fc_dly );
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_FC_DLY_M0_R0_CFG_4, fc_dly );
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_FC_DLY_M0_R1_CFG_4, fc_dly );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_FC_DLY_M0_R0_CFG_4, fc_dly );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_FC_DLY_M0_R1_CFG_4, fc_dly );
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_FC_DLY_M0_R0_CFG_5, fc_dly );
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_FC_DLY_M0_R1_CFG_5, fc_dly );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_FC_DLY_M0_R0_CFG_5, fc_dly );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_FC_DLY_M0_R1_CFG_5, fc_dly );
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_FC_DLY_M0_R0_CFG_6, fc_dly );
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_FC_DLY_M0_R1_CFG_6, fc_dly );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_FC_DLY_M0_R0_CFG_6, fc_dly );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_FC_DLY_M0_R1_CFG_6, fc_dly );
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_FC_DLY_M0_R0_CFG_7, fc_dly );
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_FC_DLY_M0_R1_CFG_7, fc_dly );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_FC_DLY_M0_R0_CFG_7, fc_dly );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_FC_DLY_M0_R1_CFG_7, fc_dly );
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_FC_DLY_M0_R0_CFG_8, fc_dly );
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_FC_DLY_M0_R1_CFG_8, fc_dly );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_FC_DLY_M0_R0_CFG_8, fc_dly );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_FC_DLY_M0_R1_CFG_8, fc_dly );
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_FC_DLY_M0_R0_CFG_9, fc_dly );
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_FC_DLY_M0_R1_CFG_9, fc_dly );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_FC_DLY_M0_R0_CFG_9, fc_dly );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_FC_DLY_M0_R1_CFG_9, fc_dly );
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_FC_DLY_M0_R0_CFG_10, fc_dly );
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_FC_DLY_M0_R1_CFG_10, fc_dly );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_FC_DLY_M0_R0_CFG_10, fc_dly );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_FC_DLY_M0_R1_CFG_10, fc_dly );
                end
            endcase
        end
    end
endtask

task automatic set_txdq_rt_pipe_en;
    input byte_sel_t     byte_sel;
    input rank_sel_t     rank_sel;
    input logic   [31:0] pipe_en;
    begin
        if((byte_sel == DQ0) || (byte_sel == DQ_ALL) || (byte_sel == ALL)) begin
            case ({rank_sel})
                {RANK0} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_RT_M0_R0_CFG, pipe_en );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_RT_M0_R0_CFG, pipe_en );
                end
                {RANK1} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_RT_M0_R1_CFG, pipe_en );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_RT_M0_R1_CFG, pipe_en );
                end
                default: begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_RT_M0_R0_CFG, pipe_en );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_RT_M0_R1_CFG, pipe_en );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_RT_M0_R0_CFG, pipe_en );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_RT_M0_R1_CFG, pipe_en );
                end
            endcase
        end
        if((byte_sel == DQ1) || (byte_sel == DQ_ALL) || (byte_sel == ALL)) begin
            case ({rank_sel})
                {RANK0} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_RT_M0_R0_CFG, pipe_en );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_RT_M0_R0_CFG, pipe_en );
                end
                {RANK1} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_RT_M0_R1_CFG, pipe_en );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_RT_M0_R1_CFG, pipe_en );
                end
                default: begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_RT_M0_R0_CFG, pipe_en );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_RT_M0_R1_CFG, pipe_en );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_RT_M0_R0_CFG, pipe_en );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_RT_M0_R1_CFG, pipe_en );
                end
            endcase
        end
        if((byte_sel == CA) || (byte_sel == ALL)) begin
            case ({rank_sel})
                {RANK0} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_RT_M0_R0_CFG, pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_RT_M0_R0_CFG, pipe_en);
                end
                {RANK1} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_RT_M0_R1_CFG, pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_RT_M0_R1_CFG, pipe_en);
                end
                default: begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_RT_M0_R0_CFG, pipe_en );
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_RT_M0_R1_CFG, pipe_en );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_RT_M0_R0_CFG, pipe_en );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_RT_M0_R1_CFG, pipe_en );
                end
            endcase
        end
    end
endtask

task automatic set_txdq_sdr_x_sel;
    input byte_sel_t     byte_sel;
    input rank_sel_t     rank_sel;
    input logic    [7:0] dq;
    input logic   [31:0] x_sel;
    begin
        if((byte_sel == DQ0) || (byte_sel == DQ_ALL) || (byte_sel == ALL)) begin
            case ({rank_sel,dq})
                {RANK0, 8'd0} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M0_R0_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M0_R0_CFG_0 , x_sel  );
                end
                {RANK0, 8'd1} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M0_R0_CFG_1 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M0_R0_CFG_1 , x_sel  );
                end
                {RANK0, 8'd2} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M0_R0_CFG_2 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M0_R0_CFG_2 , x_sel  );
                end
                {RANK0, 8'd3} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M0_R0_CFG_3 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M0_R0_CFG_3 , x_sel  );
                end
                {RANK0, 8'd4} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M0_R0_CFG_4 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M0_R0_CFG_4 , x_sel  );
                end
                {RANK0, 8'd5} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M0_R0_CFG_5 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M0_R0_CFG_5 , x_sel  );
                end
                {RANK0, 8'd6} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M0_R0_CFG_6 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M0_R0_CFG_6 , x_sel  );
                end
                {RANK0, 8'd7} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M0_R0_CFG_7 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M0_R0_CFG_7 , x_sel  );
                end
                {RANK0, 8'd8} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M0_R0_CFG_8 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M0_R0_CFG_8 , x_sel  );
                end
                {RANK1, 8'd0} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M0_R1_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M0_R1_CFG_0 , x_sel  );
                end
                {RANK1, 8'd1} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M0_R1_CFG_1 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M0_R1_CFG_1 , x_sel  );
                end
                {RANK1, 8'd2} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M0_R1_CFG_2 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M0_R1_CFG_2 , x_sel  );
                end
                {RANK1, 8'd3} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M0_R1_CFG_3 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M0_R1_CFG_3 , x_sel  );
                end
                {RANK1, 8'd4} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M0_R1_CFG_4 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M0_R1_CFG_4 , x_sel  );
                end
                {RANK1, 8'd5} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M0_R1_CFG_5 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M0_R1_CFG_5 , x_sel  );
                end
                {RANK1, 8'd6} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M0_R1_CFG_6 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M0_R1_CFG_6 , x_sel  );
                end
                {RANK1, 8'd7} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M0_R1_CFG_7 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M0_R1_CFG_7 , x_sel  );
                end
                {RANK1, 8'd8} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M0_R1_CFG_8 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M0_R1_CFG_8 , x_sel  );
                end
                default: begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M0_R0_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M0_R1_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M0_R0_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M0_R1_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M0_R0_CFG_1 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M0_R1_CFG_1 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M0_R0_CFG_1 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M0_R1_CFG_1 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M0_R0_CFG_2 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M0_R1_CFG_2 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M0_R0_CFG_2 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M0_R1_CFG_2 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M0_R0_CFG_3 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M0_R1_CFG_3 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M0_R0_CFG_3 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M0_R1_CFG_3 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M0_R0_CFG_4 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M0_R1_CFG_4 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M0_R0_CFG_4 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M0_R1_CFG_4 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M0_R0_CFG_5 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M0_R1_CFG_5 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M0_R0_CFG_5 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M0_R1_CFG_5 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M0_R0_CFG_6 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M0_R1_CFG_6 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M0_R0_CFG_6 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M0_R1_CFG_6 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M0_R0_CFG_7 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M0_R1_CFG_7 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M0_R0_CFG_7 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M0_R1_CFG_7 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M0_R0_CFG_8 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M0_R1_CFG_8 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M0_R0_CFG_8 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M0_R1_CFG_8 , x_sel  );
                end
            endcase
        end
        if((byte_sel == DQ1) || (byte_sel == DQ_ALL) || (byte_sel == ALL)) begin
            case ({rank_sel,dq})
                {RANK0, 8'd0} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M0_R0_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M0_R0_CFG_0 , x_sel  );
                end
                {RANK0, 8'd1} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M0_R0_CFG_1 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M0_R0_CFG_1 , x_sel  );
                end
                {RANK0, 8'd2} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M0_R0_CFG_2 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M0_R0_CFG_2 , x_sel  );
                end
                {RANK0, 8'd3} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M0_R0_CFG_3 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M0_R0_CFG_3 , x_sel  );
                end
                {RANK0, 8'd4} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M0_R0_CFG_4 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M0_R0_CFG_4 , x_sel  );
                end
                {RANK0, 8'd5} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M0_R0_CFG_5 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M0_R0_CFG_5 , x_sel  );
                end
                {RANK0, 8'd6} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M0_R0_CFG_6 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M0_R0_CFG_6 , x_sel  );
                end
                {RANK0, 8'd7} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M0_R0_CFG_7 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M0_R0_CFG_7 , x_sel  );
                end
                {RANK0, 8'd8} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M0_R0_CFG_8 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M0_R0_CFG_8 , x_sel  );
                end
                {RANK1, 8'd0} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M0_R1_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M0_R1_CFG_0 , x_sel  );
                end
                {RANK1, 8'd1} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M0_R1_CFG_1 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M0_R1_CFG_1 , x_sel  );
                end
                {RANK1, 8'd2} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M0_R1_CFG_2 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M0_R1_CFG_2 , x_sel  );
                end
                {RANK1, 8'd3} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M0_R1_CFG_3 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M0_R1_CFG_3 , x_sel  );
                end
                {RANK1, 8'd4} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M0_R1_CFG_4 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M0_R1_CFG_4 , x_sel  );
                end
                {RANK1, 8'd5} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M0_R1_CFG_5 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M0_R1_CFG_5 , x_sel  );
                end
                {RANK1, 8'd6} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M0_R1_CFG_6 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M0_R1_CFG_6 , x_sel  );
                end
                {RANK1, 8'd7} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M0_R1_CFG_7 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M0_R1_CFG_7 , x_sel  );
                end
                {RANK1, 8'd8} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M0_R1_CFG_8 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M0_R1_CFG_8 , x_sel  );
                end
                default: begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M0_R0_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M0_R1_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M0_R0_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M0_R1_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M0_R0_CFG_1 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M0_R1_CFG_1 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M0_R0_CFG_1 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M0_R1_CFG_1 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M0_R0_CFG_2 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M0_R1_CFG_2 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M0_R0_CFG_2 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M0_R1_CFG_2 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M0_R0_CFG_3 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M0_R1_CFG_3 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M0_R0_CFG_3 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M0_R1_CFG_3 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M0_R0_CFG_4 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M0_R1_CFG_4 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M0_R0_CFG_4 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M0_R1_CFG_4 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M0_R0_CFG_5 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M0_R1_CFG_5 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M0_R0_CFG_5 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M0_R1_CFG_5 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M0_R0_CFG_6 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M0_R1_CFG_6 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M0_R0_CFG_6 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M0_R1_CFG_6 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M0_R0_CFG_7 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M0_R1_CFG_7 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M0_R0_CFG_7 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M0_R1_CFG_7 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M0_R0_CFG_8 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M0_R1_CFG_8 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M0_R0_CFG_8 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_X_SEL_M0_R1_CFG_8 , x_sel  );
                end
            endcase
        end
        if((byte_sel == CA) || (byte_sel == ALL)) begin
            case ({rank_sel,dq})
                {RANK0, 8'd0} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_X_SEL_M0_R0_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_X_SEL_M0_R0_CFG_0 , x_sel  );
                end
                {RANK0, 8'd1} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_X_SEL_M0_R0_CFG_1 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_X_SEL_M0_R0_CFG_1 , x_sel  );
                end
                {RANK0, 8'd2} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_X_SEL_M0_R0_CFG_2 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_X_SEL_M0_R0_CFG_2 , x_sel  );
                end
                {RANK0, 8'd3} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_X_SEL_M0_R0_CFG_3 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_X_SEL_M0_R0_CFG_3 , x_sel  );
                end
                {RANK0, 8'd4} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_X_SEL_M0_R0_CFG_4 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_X_SEL_M0_R0_CFG_4 , x_sel  );
                end
                {RANK0, 8'd5} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_X_SEL_M0_R0_CFG_5 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_X_SEL_M0_R0_CFG_5 , x_sel  );
                end
                {RANK0, 8'd6} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_X_SEL_M0_R0_CFG_6 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_X_SEL_M0_R0_CFG_6 , x_sel  );
                end
                {RANK0, 8'd7} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_X_SEL_M0_R0_CFG_7 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_X_SEL_M0_R0_CFG_7 , x_sel  );
                end
                {RANK0, 8'd8} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_X_SEL_M0_R0_CFG_8 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_X_SEL_M0_R0_CFG_8 , x_sel  );
                end
                {RANK0, 8'd9} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_X_SEL_M0_R0_CFG_9 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_X_SEL_M0_R0_CFG_9 , x_sel  );
                end
                {RANK0, 8'd10} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_X_SEL_M0_R0_CFG_10 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_X_SEL_M0_R0_CFG_10 , x_sel  );
                end
                {RANK1, 8'd0} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_X_SEL_M0_R1_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_X_SEL_M0_R1_CFG_0 , x_sel  );
                end
                {RANK1, 8'd1} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_X_SEL_M0_R1_CFG_1 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_X_SEL_M0_R1_CFG_1 , x_sel  );
                end
                {RANK1, 8'd2} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_X_SEL_M0_R1_CFG_2 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_X_SEL_M0_R1_CFG_2 , x_sel  );
                end
                {RANK1, 8'd3} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_X_SEL_M0_R1_CFG_3 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_X_SEL_M0_R1_CFG_3 , x_sel  );
                end
                {RANK1, 8'd4} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_X_SEL_M0_R1_CFG_4 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_X_SEL_M0_R1_CFG_4 , x_sel  );
                end
                {RANK1, 8'd5} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_X_SEL_M0_R1_CFG_5 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_X_SEL_M0_R1_CFG_5 , x_sel  );
                end
                {RANK1, 8'd6} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_X_SEL_M0_R1_CFG_6 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_X_SEL_M0_R1_CFG_6 , x_sel  );
                end
                {RANK1, 8'd7} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_X_SEL_M0_R1_CFG_7 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_X_SEL_M0_R1_CFG_7 , x_sel  );
                end
                {RANK1, 8'd8} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_X_SEL_M0_R1_CFG_8 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_X_SEL_M0_R1_CFG_8 , x_sel  );
                end
                {RANK1, 8'd9} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_X_SEL_M0_R1_CFG_9 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_X_SEL_M0_R1_CFG_9 , x_sel  );
                end
                {RANK1, 8'd10} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_X_SEL_M0_R1_CFG_10 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_X_SEL_M0_R1_CFG_10 , x_sel  );
                end
                default: begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_X_SEL_M0_R0_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_X_SEL_M0_R1_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_X_SEL_M0_R0_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_X_SEL_M0_R1_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_X_SEL_M0_R0_CFG_1 , x_sel  );
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_X_SEL_M0_R1_CFG_1 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_X_SEL_M0_R0_CFG_1 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_X_SEL_M0_R1_CFG_1 , x_sel  );
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_X_SEL_M0_R0_CFG_2 , x_sel  );
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_X_SEL_M0_R1_CFG_2 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_X_SEL_M0_R0_CFG_2 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_X_SEL_M0_R1_CFG_2 , x_sel  );
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_X_SEL_M0_R0_CFG_3 , x_sel  );
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_X_SEL_M0_R1_CFG_3 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_X_SEL_M0_R0_CFG_3 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_X_SEL_M0_R1_CFG_3 , x_sel  );
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_X_SEL_M0_R0_CFG_4 , x_sel  );
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_X_SEL_M0_R1_CFG_4 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_X_SEL_M0_R0_CFG_4 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_X_SEL_M0_R1_CFG_4 , x_sel  );
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_X_SEL_M0_R0_CFG_5 , x_sel  );
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_X_SEL_M0_R1_CFG_5 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_X_SEL_M0_R0_CFG_5 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_X_SEL_M0_R1_CFG_5 , x_sel  );
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_X_SEL_M0_R0_CFG_6 , x_sel  );
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_X_SEL_M0_R1_CFG_6 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_X_SEL_M0_R0_CFG_6 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_X_SEL_M0_R1_CFG_6 , x_sel  );
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_X_SEL_M0_R0_CFG_7 , x_sel  );
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_X_SEL_M0_R1_CFG_7 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_X_SEL_M0_R0_CFG_7 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_X_SEL_M0_R1_CFG_7 , x_sel  );
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_X_SEL_M0_R0_CFG_8 , x_sel  );
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_X_SEL_M0_R1_CFG_8 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_X_SEL_M0_R0_CFG_8 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_X_SEL_M0_R1_CFG_8 , x_sel  );
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_X_SEL_M0_R0_CFG_9 , x_sel  );
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_X_SEL_M0_R1_CFG_9 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_X_SEL_M0_R0_CFG_9 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_X_SEL_M0_R1_CFG_9 , x_sel  );
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_X_SEL_M0_R0_CFG_10 , x_sel  );
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_X_SEL_M0_R1_CFG_10 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_X_SEL_M0_R0_CFG_10 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_X_SEL_M0_R1_CFG_10 , x_sel  );
                end
            endcase
        end
    end
endtask

task automatic set_txdq_sdr_pipe_en ;
    input byte_sel_t     byte_sel;
    input rank_sel_t     rank_sel;
    input logic    [7:0] dq;
    input logic   [31:0] pipe_en;
    begin
        if((byte_sel == DQ0) || (byte_sel == DQ_ALL) || (byte_sel == ALL)) begin
            case ({rank_sel,dq})
                {RANK0, 8'd0} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_M0_R0_CFG_0       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_M0_R0_CFG_0       , pipe_en);
                end
                {RANK0, 8'd1} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_M0_R0_CFG_1       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_M0_R0_CFG_1       , pipe_en);
                end
                {RANK0, 8'd2} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_M0_R0_CFG_2       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_M0_R0_CFG_2       , pipe_en);
                end
                {RANK0, 8'd3} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_M0_R0_CFG_3       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_M0_R0_CFG_3       , pipe_en);
                end
                {RANK0, 8'd4} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_M0_R0_CFG_4       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_M0_R0_CFG_4       , pipe_en);
                end
                {RANK0, 8'd5} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_M0_R0_CFG_5       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_M0_R0_CFG_5       , pipe_en);
                end
                {RANK0, 8'd6} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_M0_R0_CFG_6       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_M0_R0_CFG_6       , pipe_en);
                end
                {RANK0, 8'd7} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_M0_R0_CFG_7       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_M0_R0_CFG_7       , pipe_en);
                end
                {RANK0, 8'd8} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_M0_R0_CFG_8       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_M0_R0_CFG_8       , pipe_en);
                end
                {RANK1, 8'd0} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_M0_R1_CFG_0       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_M0_R1_CFG_0       , pipe_en);
                end
                {RANK1, 8'd1} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_M0_R1_CFG_1       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_M0_R1_CFG_1       , pipe_en);
                end
                {RANK1, 8'd2} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_M0_R1_CFG_2       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_M0_R1_CFG_2       , pipe_en);
                end
                {RANK1, 8'd3} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_M0_R1_CFG_3       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_M0_R1_CFG_3       , pipe_en);
                end
                {RANK1, 8'd4} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_M0_R1_CFG_4       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_M0_R1_CFG_4       , pipe_en);
                end
                {RANK1, 8'd5} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_M0_R1_CFG_5       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_M0_R1_CFG_5       , pipe_en);
                end
                {RANK1, 8'd6} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_M0_R1_CFG_6       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_M0_R1_CFG_6       , pipe_en);
                end
                {RANK1, 8'd7} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_M0_R1_CFG_7       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_M0_R1_CFG_7       , pipe_en);
                end
                {RANK1, 8'd8} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_M0_R1_CFG_8       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_M0_R1_CFG_8       , pipe_en);
                end
                default: begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_M0_R0_CFG_0       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_M0_R0_CFG_0       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_M0_R0_CFG_1       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_M0_R0_CFG_1       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_M0_R0_CFG_2       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_M0_R0_CFG_2       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_M0_R0_CFG_3       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_M0_R0_CFG_3       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_M0_R0_CFG_4       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_M0_R0_CFG_4       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_M0_R0_CFG_5       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_M0_R0_CFG_5       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_M0_R0_CFG_6       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_M0_R0_CFG_6       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_M0_R0_CFG_7       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_M0_R0_CFG_7       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_M0_R0_CFG_8       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_M0_R0_CFG_8       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_M0_R1_CFG_0       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_M0_R1_CFG_0       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_M0_R1_CFG_1       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_M0_R1_CFG_1       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_M0_R1_CFG_2       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_M0_R1_CFG_2       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_M0_R1_CFG_3       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_M0_R1_CFG_3       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_M0_R1_CFG_4       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_M0_R1_CFG_4       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_M0_R1_CFG_5       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_M0_R1_CFG_5       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_M0_R1_CFG_6       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_M0_R1_CFG_6       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_M0_R1_CFG_7       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_M0_R1_CFG_7       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_M0_R1_CFG_8       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_SDR_M0_R1_CFG_8       , pipe_en);
                end
            endcase
        end
        if((byte_sel == DQ1) || (byte_sel == DQ_ALL) || (byte_sel == ALL)) begin
            case ({rank_sel,dq})
                {RANK0, 8'd0} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_M0_R0_CFG_0       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_M0_R0_CFG_0       , pipe_en);
                end
                {RANK0, 8'd1} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_M0_R0_CFG_1       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_M0_R0_CFG_1       , pipe_en);
                end
                {RANK0, 8'd2} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_M0_R0_CFG_2       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_M0_R0_CFG_2       , pipe_en);
                end
                {RANK0, 8'd3} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_M0_R0_CFG_3       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_M0_R0_CFG_3       , pipe_en);
                end
                {RANK0, 8'd4} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_M0_R0_CFG_4       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_M0_R0_CFG_4       , pipe_en);
                end
                {RANK0, 8'd5} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_M0_R0_CFG_5       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_M0_R0_CFG_5       , pipe_en);
                end
                {RANK0, 8'd6} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_M0_R0_CFG_6       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_M0_R0_CFG_6       , pipe_en);
                end
                {RANK0, 8'd7} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_M0_R0_CFG_7       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_M0_R0_CFG_7       , pipe_en);
                end
                {RANK0, 8'd8} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_M0_R0_CFG_8       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_M0_R0_CFG_8       , pipe_en);
                end
                {RANK1, 8'd0} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_M0_R1_CFG_0       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_M0_R1_CFG_0       , pipe_en);
                end
                {RANK1, 8'd1} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_M0_R1_CFG_1       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_M0_R1_CFG_1       , pipe_en);
                end
                {RANK1, 8'd2} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_M0_R1_CFG_2       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_M0_R1_CFG_2       , pipe_en);
                end
                {RANK1, 8'd3} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_M0_R1_CFG_3       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_M0_R1_CFG_3       , pipe_en);
                end
                {RANK1, 8'd4} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_M0_R1_CFG_4       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_M0_R1_CFG_4       , pipe_en);
                end
                {RANK1, 8'd5} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_M0_R1_CFG_5       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_M0_R1_CFG_5       , pipe_en);
                end
                {RANK1, 8'd6} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_M0_R1_CFG_6       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_M0_R1_CFG_6       , pipe_en);
                end
                {RANK1, 8'd7} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_M0_R1_CFG_7       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_M0_R1_CFG_7       , pipe_en);
                end
                {RANK1, 8'd8} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_M0_R1_CFG_8       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_M0_R1_CFG_8       , pipe_en);
                end
                default: begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_M0_R0_CFG_0       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_M0_R0_CFG_0       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_M0_R0_CFG_1       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_M0_R0_CFG_1       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_M0_R0_CFG_2       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_M0_R0_CFG_2       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_M0_R0_CFG_3       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_M0_R0_CFG_3       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_M0_R0_CFG_4       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_M0_R0_CFG_4       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_M0_R0_CFG_5       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_M0_R0_CFG_5       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_M0_R0_CFG_6       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_M0_R0_CFG_6       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_M0_R0_CFG_7       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_M0_R0_CFG_7       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_M0_R0_CFG_8       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_M0_R0_CFG_8       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_M0_R1_CFG_0       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_M0_R1_CFG_0       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_M0_R1_CFG_1       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_M0_R1_CFG_1       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_M0_R1_CFG_2       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_M0_R1_CFG_2       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_M0_R1_CFG_3       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_M0_R1_CFG_3       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_M0_R1_CFG_4       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_M0_R1_CFG_4       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_M0_R1_CFG_5       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_M0_R1_CFG_5       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_M0_R1_CFG_6       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_M0_R1_CFG_6       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_M0_R1_CFG_7       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_M0_R1_CFG_7       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_M0_R1_CFG_8       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_SDR_M0_R1_CFG_8       , pipe_en);
                end
            endcase
        end
        if((byte_sel == CA) || (byte_sel == ALL)) begin
            case ({rank_sel,dq})
                {RANK0, 8'd0} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_M0_R0_CFG_0       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_M0_R0_CFG_0       , pipe_en);
                end
                {RANK0, 8'd1} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_M0_R0_CFG_1       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_M0_R0_CFG_1       , pipe_en);
                end
                {RANK0, 8'd2} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_M0_R0_CFG_2       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_M0_R0_CFG_2       , pipe_en);
                end
                {RANK0, 8'd3} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_M0_R0_CFG_3       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_M0_R0_CFG_3       , pipe_en);
                end
                {RANK0, 8'd4} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_M0_R0_CFG_4       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_M0_R0_CFG_4       , pipe_en);
                end
                {RANK0, 8'd5} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_M0_R0_CFG_5       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_M0_R0_CFG_5       , pipe_en);
                end
                {RANK0, 8'd6} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_M0_R0_CFG_6       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_M0_R0_CFG_6       , pipe_en);
                end
                {RANK0, 8'd7} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_M0_R0_CFG_7       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_M0_R0_CFG_7       , pipe_en);
                end
                {RANK0, 8'd8} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_M0_R0_CFG_8       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_M0_R0_CFG_8       , pipe_en);
                end
                {RANK0, 8'd9} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_M0_R0_CFG_9       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_M0_R0_CFG_9       , pipe_en);
                end
                {RANK0, 8'd10} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_M0_R0_CFG_10       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_M0_R0_CFG_10       , pipe_en);
                end
                {RANK1, 8'd0} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_M0_R1_CFG_0       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_M0_R1_CFG_0       , pipe_en);
                end
                {RANK1, 8'd1} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_M0_R1_CFG_1       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_M0_R1_CFG_1       , pipe_en);
                end
                {RANK1, 8'd2} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_M0_R1_CFG_2       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_M0_R1_CFG_2       , pipe_en);
                end
                {RANK1, 8'd3} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_M0_R1_CFG_3       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_M0_R1_CFG_3       , pipe_en);
                end
                {RANK1, 8'd4} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_M0_R1_CFG_4       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_M0_R1_CFG_4       , pipe_en);
                end
                {RANK1, 8'd5} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_M0_R1_CFG_5       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_M0_R1_CFG_5       , pipe_en);
                end
                {RANK1, 8'd6} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_M0_R1_CFG_6       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_M0_R1_CFG_6       , pipe_en);
                end
                {RANK1, 8'd7} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_M0_R1_CFG_7       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_M0_R1_CFG_7       , pipe_en);
                end
                {RANK1, 8'd8} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_M0_R1_CFG_8       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_M0_R1_CFG_8       , pipe_en);
                end
                {RANK1, 8'd9} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_M0_R1_CFG_9       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_M0_R1_CFG_9       , pipe_en);
                end
                {RANK1, 8'd10} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_M0_R1_CFG_10       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_M0_R1_CFG_10       , pipe_en);
                end
                default: begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_M0_R0_CFG_0       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_M0_R0_CFG_0       , pipe_en);
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_M0_R0_CFG_1       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_M0_R0_CFG_1       , pipe_en);
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_M0_R0_CFG_2       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_M0_R0_CFG_2       , pipe_en);
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_M0_R0_CFG_3       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_M0_R0_CFG_3       , pipe_en);
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_M0_R0_CFG_4       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_M0_R0_CFG_4       , pipe_en);
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_M0_R0_CFG_5       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_M0_R0_CFG_5       , pipe_en);
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_M0_R0_CFG_6       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_M0_R0_CFG_6       , pipe_en);
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_M0_R0_CFG_7       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_M0_R0_CFG_7       , pipe_en);
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_M0_R0_CFG_8       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_M0_R0_CFG_8       , pipe_en);
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_M0_R0_CFG_9       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_M0_R0_CFG_9       , pipe_en);
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_M0_R0_CFG_10       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_M0_R0_CFG_10       , pipe_en);
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_M0_R1_CFG_0       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_M0_R1_CFG_0       , pipe_en);
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_M0_R1_CFG_1       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_M0_R1_CFG_1       , pipe_en);
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_M0_R1_CFG_2       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_M0_R1_CFG_2       , pipe_en);
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_M0_R1_CFG_3       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_M0_R1_CFG_3       , pipe_en);
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_M0_R1_CFG_4       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_M0_R1_CFG_4       , pipe_en);
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_M0_R1_CFG_5       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_M0_R1_CFG_5       , pipe_en);
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_M0_R1_CFG_6       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_M0_R1_CFG_6       , pipe_en);
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_M0_R1_CFG_7       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_M0_R1_CFG_7       , pipe_en);
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_M0_R1_CFG_8       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_M0_R1_CFG_8       , pipe_en);
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_M0_R1_CFG_9       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_M0_R1_CFG_9       , pipe_en);
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_SDR_M0_R1_CFG_10       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_SDR_M0_R1_CFG_10       , pipe_en);
                end
            endcase
        end
    end
endtask

task automatic set_txdq_ddr_x_sel;
    input byte_sel_t     byte_sel;
    input rank_sel_t     rank_sel;
    input logic    [7:0] dq;
    input logic   [31:0] x_sel;
    begin
        if((byte_sel == DQ0) || (byte_sel == DQ_ALL) || (byte_sel == ALL)) begin
            case ({rank_sel,dq})
                {RANK0, 8'd0} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M0_R0_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M0_R0_CFG_0 , x_sel  );
                end
                {RANK0, 8'd1} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M0_R0_CFG_1 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M0_R0_CFG_1 , x_sel  );
                end
                {RANK0, 8'd2} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M0_R0_CFG_2 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M0_R0_CFG_2 , x_sel  );
                end
                {RANK0, 8'd3} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M0_R0_CFG_3 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M0_R0_CFG_3 , x_sel  );
                end
                {RANK0, 8'd4} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M0_R0_CFG_4 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M0_R0_CFG_4 , x_sel  );
                end
                {RANK0, 8'd5} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M0_R0_CFG_5 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M0_R0_CFG_5 , x_sel  );
                end
                {RANK0, 8'd6} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M0_R0_CFG_6 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M0_R0_CFG_6 , x_sel  );
                end
                {RANK0, 8'd7} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M0_R0_CFG_7 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M0_R0_CFG_7 , x_sel  );
                end
                {RANK0, 8'd8} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M0_R0_CFG_8 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M0_R0_CFG_8 , x_sel  );
                end
                {RANK1, 8'd0} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M0_R1_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M0_R1_CFG_0 , x_sel  );
                end
                {RANK1, 8'd1} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M0_R1_CFG_1 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M0_R1_CFG_1 , x_sel  );
                end
                {RANK1, 8'd2} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M0_R1_CFG_2 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M0_R1_CFG_2 , x_sel  );
                end
                {RANK1, 8'd3} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M0_R1_CFG_3 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M0_R1_CFG_3 , x_sel  );
                end
                {RANK1, 8'd4} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M0_R1_CFG_4 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M0_R1_CFG_4 , x_sel  );
                end
                {RANK1, 8'd5} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M0_R1_CFG_5 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M0_R1_CFG_5 , x_sel  );
                end
                {RANK1, 8'd6} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M0_R1_CFG_6 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M0_R1_CFG_6 , x_sel  );
                end
                {RANK1, 8'd7} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M0_R1_CFG_7 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M0_R1_CFG_7 , x_sel  );
                end
                {RANK1, 8'd8} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M0_R1_CFG_8 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M0_R1_CFG_8 , x_sel  );
                end
                default: begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M0_R0_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M0_R1_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M0_R0_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M0_R1_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M0_R0_CFG_1 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M0_R1_CFG_1 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M0_R0_CFG_1 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M0_R1_CFG_1 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M0_R0_CFG_2 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M0_R1_CFG_2 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M0_R0_CFG_2 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M0_R1_CFG_2 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M0_R0_CFG_3 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M0_R1_CFG_3 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M0_R0_CFG_3 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M0_R1_CFG_3 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M0_R0_CFG_4 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M0_R1_CFG_4 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M0_R0_CFG_4 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M0_R1_CFG_4 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M0_R0_CFG_5 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M0_R1_CFG_5 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M0_R0_CFG_5 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M0_R1_CFG_5 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M0_R0_CFG_6 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M0_R1_CFG_6 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M0_R0_CFG_6 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M0_R1_CFG_6 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M0_R0_CFG_7 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M0_R1_CFG_7 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M0_R0_CFG_7 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M0_R1_CFG_7 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M0_R0_CFG_8 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M0_R1_CFG_8 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M0_R0_CFG_8 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M0_R1_CFG_8 , x_sel  );
                end
            endcase
        end
        if((byte_sel == DQ1) || (byte_sel == DQ_ALL) || (byte_sel == ALL)) begin
            case ({rank_sel,dq})
                {RANK0, 8'd0} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M0_R0_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M0_R0_CFG_0 , x_sel  );
                end
                {RANK0, 8'd1} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M0_R0_CFG_1 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M0_R0_CFG_1 , x_sel  );
                end
                {RANK0, 8'd2} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M0_R0_CFG_2 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M0_R0_CFG_2 , x_sel  );
                end
                {RANK0, 8'd3} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M0_R0_CFG_3 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M0_R0_CFG_3 , x_sel  );
                end
                {RANK0, 8'd4} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M0_R0_CFG_4 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M0_R0_CFG_4 , x_sel  );
                end
                {RANK0, 8'd5} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M0_R0_CFG_5 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M0_R0_CFG_5 , x_sel  );
                end
                {RANK0, 8'd6} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M0_R0_CFG_6 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M0_R0_CFG_6 , x_sel  );
                end
                {RANK0, 8'd7} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M0_R0_CFG_7 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M0_R0_CFG_7 , x_sel  );
                end
                {RANK0, 8'd8} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M0_R0_CFG_8 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M0_R0_CFG_8 , x_sel  );
                end
                {RANK1, 8'd0} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M0_R1_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M0_R1_CFG_0 , x_sel  );
                end
                {RANK1, 8'd1} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M0_R1_CFG_1 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M0_R1_CFG_1 , x_sel  );
                end
                {RANK1, 8'd2} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M0_R1_CFG_2 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M0_R1_CFG_2 , x_sel  );
                end
                {RANK1, 8'd3} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M0_R1_CFG_3 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M0_R1_CFG_3 , x_sel  );
                end
                {RANK1, 8'd4} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M0_R1_CFG_4 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M0_R1_CFG_4 , x_sel  );
                end
                {RANK1, 8'd5} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M0_R1_CFG_5 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M0_R1_CFG_5 , x_sel  );
                end
                {RANK1, 8'd6} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M0_R1_CFG_6 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M0_R1_CFG_6 , x_sel  );
                end
                {RANK1, 8'd7} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M0_R1_CFG_7 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M0_R1_CFG_7 , x_sel  );
                end
                {RANK1, 8'd8} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M0_R1_CFG_8 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M0_R1_CFG_8 , x_sel  );
                end
                default: begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M0_R0_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M0_R1_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M0_R0_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M0_R1_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M0_R0_CFG_1 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M0_R1_CFG_1 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M0_R0_CFG_1 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M0_R1_CFG_1 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M0_R0_CFG_2 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M0_R1_CFG_2 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M0_R0_CFG_2 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M0_R1_CFG_2 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M0_R0_CFG_3 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M0_R1_CFG_3 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M0_R0_CFG_3 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M0_R1_CFG_3 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M0_R0_CFG_4 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M0_R1_CFG_4 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M0_R0_CFG_4 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M0_R1_CFG_4 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M0_R0_CFG_5 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M0_R1_CFG_5 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M0_R0_CFG_5 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M0_R1_CFG_5 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M0_R0_CFG_6 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M0_R1_CFG_6 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M0_R0_CFG_6 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M0_R1_CFG_6 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M0_R0_CFG_7 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M0_R1_CFG_7 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M0_R0_CFG_7 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M0_R1_CFG_7 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M0_R0_CFG_8 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M0_R1_CFG_8 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M0_R0_CFG_8 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_X_SEL_M0_R1_CFG_8 , x_sel  );
                end
            endcase
        end
        if((byte_sel == CA) || (byte_sel == ALL)) begin
            case ({rank_sel,dq})
                {RANK0, 8'd0} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_DDR_X_SEL_M0_R0_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_DDR_X_SEL_M0_R0_CFG_0 , x_sel  );
                end
                {RANK0, 8'd1} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_DDR_X_SEL_M0_R0_CFG_1 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_DDR_X_SEL_M0_R0_CFG_1 , x_sel  );
                end
                {RANK0, 8'd2} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_DDR_X_SEL_M0_R0_CFG_2 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_DDR_X_SEL_M0_R0_CFG_2 , x_sel  );
                end
                {RANK0, 8'd3} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_DDR_X_SEL_M0_R0_CFG_3 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_DDR_X_SEL_M0_R0_CFG_3 , x_sel  );
                end
                {RANK0, 8'd4} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_DDR_X_SEL_M0_R0_CFG_4 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_DDR_X_SEL_M0_R0_CFG_4 , x_sel  );
                end
                {RANK0, 8'd5} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_DDR_X_SEL_M0_R0_CFG_5 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_DDR_X_SEL_M0_R0_CFG_5 , x_sel  );
                end
                {RANK0, 8'd6} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_DDR_X_SEL_M0_R0_CFG_6 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_DDR_X_SEL_M0_R0_CFG_6 , x_sel  );
                end
                {RANK0, 8'd7} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_DDR_X_SEL_M0_R0_CFG_7 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_DDR_X_SEL_M0_R0_CFG_7 , x_sel  );
                end
                {RANK0, 8'd8} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_DDR_X_SEL_M0_R0_CFG_8 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_DDR_X_SEL_M0_R0_CFG_8 , x_sel  );
                end
                {RANK0, 8'd9} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_DDR_X_SEL_M0_R0_CFG_9 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_DDR_X_SEL_M0_R0_CFG_9 , x_sel  );
                end
                {RANK0, 8'd10} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_DDR_X_SEL_M0_R0_CFG_10 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_DDR_X_SEL_M0_R0_CFG_10 , x_sel  );
                end
                {RANK1, 8'd0} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_DDR_X_SEL_M0_R1_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_DDR_X_SEL_M0_R1_CFG_0 , x_sel  );
                end
                {RANK1, 8'd1} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_DDR_X_SEL_M0_R1_CFG_1 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_DDR_X_SEL_M0_R1_CFG_1 , x_sel  );
                end
                {RANK1, 8'd2} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_DDR_X_SEL_M0_R1_CFG_2 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_DDR_X_SEL_M0_R1_CFG_2 , x_sel  );
                end
                {RANK1, 8'd3} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_DDR_X_SEL_M0_R1_CFG_3 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_DDR_X_SEL_M0_R1_CFG_3 , x_sel  );
                end
                {RANK1, 8'd4} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_DDR_X_SEL_M0_R1_CFG_4 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_DDR_X_SEL_M0_R1_CFG_4 , x_sel  );
                end
                {RANK1, 8'd5} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_DDR_X_SEL_M0_R1_CFG_5 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_DDR_X_SEL_M0_R1_CFG_5 , x_sel  );
                end
                {RANK1, 8'd6} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_DDR_X_SEL_M0_R1_CFG_6 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_DDR_X_SEL_M0_R1_CFG_6 , x_sel  );
                end
                {RANK1, 8'd7} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_DDR_X_SEL_M0_R1_CFG_7 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_DDR_X_SEL_M0_R1_CFG_7 , x_sel  );
                end
                {RANK1, 8'd8} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_DDR_X_SEL_M0_R1_CFG_8 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_DDR_X_SEL_M0_R1_CFG_8 , x_sel  );
                end
                {RANK1, 8'd9} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_DDR_X_SEL_M0_R1_CFG_9 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_DDR_X_SEL_M0_R1_CFG_9 , x_sel  );
                end
                {RANK1, 8'd10} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_DDR_X_SEL_M0_R1_CFG_10 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_DDR_X_SEL_M0_R1_CFG_10 , x_sel  );
                end
                default: begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_DDR_X_SEL_M0_R0_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_DDR_X_SEL_M0_R1_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_DDR_X_SEL_M0_R0_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_DDR_X_SEL_M0_R1_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_DDR_X_SEL_M0_R0_CFG_1 , x_sel  );
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_DDR_X_SEL_M0_R1_CFG_1 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_DDR_X_SEL_M0_R0_CFG_1 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_DDR_X_SEL_M0_R1_CFG_1 , x_sel  );
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_DDR_X_SEL_M0_R0_CFG_2 , x_sel  );
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_DDR_X_SEL_M0_R1_CFG_2 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_DDR_X_SEL_M0_R0_CFG_2 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_DDR_X_SEL_M0_R1_CFG_2 , x_sel  );
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_DDR_X_SEL_M0_R0_CFG_3 , x_sel  );
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_DDR_X_SEL_M0_R1_CFG_3 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_DDR_X_SEL_M0_R0_CFG_3 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_DDR_X_SEL_M0_R1_CFG_3 , x_sel  );
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_DDR_X_SEL_M0_R0_CFG_4 , x_sel  );
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_DDR_X_SEL_M0_R1_CFG_4 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_DDR_X_SEL_M0_R0_CFG_4 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_DDR_X_SEL_M0_R1_CFG_4 , x_sel  );
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_DDR_X_SEL_M0_R0_CFG_5 , x_sel  );
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_DDR_X_SEL_M0_R1_CFG_5 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_DDR_X_SEL_M0_R0_CFG_5 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_DDR_X_SEL_M0_R1_CFG_5 , x_sel  );
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_DDR_X_SEL_M0_R0_CFG_6 , x_sel  );
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_DDR_X_SEL_M0_R1_CFG_6 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_DDR_X_SEL_M0_R0_CFG_6 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_DDR_X_SEL_M0_R1_CFG_6 , x_sel  );
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_DDR_X_SEL_M0_R0_CFG_7 , x_sel  );
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_DDR_X_SEL_M0_R1_CFG_7 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_DDR_X_SEL_M0_R0_CFG_7 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_DDR_X_SEL_M0_R1_CFG_7 , x_sel  );
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_DDR_X_SEL_M0_R0_CFG_8 , x_sel  );
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_DDR_X_SEL_M0_R1_CFG_8 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_DDR_X_SEL_M0_R0_CFG_8 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_DDR_X_SEL_M0_R1_CFG_8 , x_sel  );
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_DDR_X_SEL_M0_R0_CFG_9 , x_sel  );
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_DDR_X_SEL_M0_R1_CFG_9 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_DDR_X_SEL_M0_R0_CFG_9 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_DDR_X_SEL_M0_R1_CFG_9 , x_sel  );
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_DDR_X_SEL_M0_R0_CFG_10 , x_sel  );
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_DDR_X_SEL_M0_R1_CFG_10 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_DDR_X_SEL_M0_R0_CFG_10 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_DDR_X_SEL_M0_R1_CFG_10 , x_sel  );
                end
            endcase
        end
    end
endtask

task automatic set_txdq_ddr_pipe_en ;
    input byte_sel_t     byte_sel;
    input rank_sel_t     rank_sel;
    input logic    [7:0] dq;
    input logic   [31:0] pipe_en;
    begin
        if((byte_sel == DQ0) || (byte_sel == DQ_ALL) || (byte_sel == ALL)) begin
            case ({rank_sel,dq})
                {RANK0, 8'd0} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_M0_R0_CFG_0       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_M0_R0_CFG_0       , pipe_en);
                end
                {RANK0, 8'd1} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_M0_R0_CFG_1       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_M0_R0_CFG_1       , pipe_en);
                end
                {RANK0, 8'd2} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_M0_R0_CFG_2       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_M0_R0_CFG_2       , pipe_en);
                end
                {RANK0, 8'd3} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_M0_R0_CFG_3       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_M0_R0_CFG_3       , pipe_en);
                end
                {RANK0, 8'd4} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_M0_R0_CFG_4       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_M0_R0_CFG_4       , pipe_en);
                end
                {RANK0, 8'd5} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_M0_R0_CFG_5       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_M0_R0_CFG_5       , pipe_en);
                end
                {RANK0, 8'd6} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_M0_R0_CFG_6       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_M0_R0_CFG_6       , pipe_en);
                end
                {RANK0, 8'd7} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_M0_R0_CFG_7       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_M0_R0_CFG_7       , pipe_en);
                end
                {RANK0, 8'd8} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_M0_R0_CFG_8       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_M0_R0_CFG_8       , pipe_en);
                end
                {RANK1, 8'd0} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_M0_R1_CFG_0       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_M0_R1_CFG_0       , pipe_en);
                end
                {RANK1, 8'd1} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_M0_R1_CFG_1       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_M0_R1_CFG_1       , pipe_en);
                end
                {RANK1, 8'd2} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_M0_R1_CFG_2       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_M0_R1_CFG_2       , pipe_en);
                end
                {RANK1, 8'd3} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_M0_R1_CFG_3       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_M0_R1_CFG_3       , pipe_en);
                end
                {RANK1, 8'd4} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_M0_R1_CFG_4       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_M0_R1_CFG_4       , pipe_en);
                end
                {RANK1, 8'd5} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_M0_R1_CFG_5       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_M0_R1_CFG_5       , pipe_en);
                end
                {RANK1, 8'd6} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_M0_R1_CFG_6       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_M0_R1_CFG_6       , pipe_en);
                end
                {RANK1, 8'd7} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_M0_R1_CFG_7       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_M0_R1_CFG_7       , pipe_en);
                end
                {RANK1, 8'd8} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_M0_R1_CFG_8       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_M0_R1_CFG_8       , pipe_en);
                end
                default: begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_M0_R0_CFG_0       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_M0_R0_CFG_0       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_M0_R0_CFG_1       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_M0_R0_CFG_1       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_M0_R0_CFG_2       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_M0_R0_CFG_2       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_M0_R0_CFG_3       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_M0_R0_CFG_3       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_M0_R0_CFG_4       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_M0_R0_CFG_4       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_M0_R0_CFG_5       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_M0_R0_CFG_5       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_M0_R0_CFG_6       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_M0_R0_CFG_6       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_M0_R0_CFG_7       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_M0_R0_CFG_7       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_M0_R0_CFG_8       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_M0_R0_CFG_8       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_M0_R1_CFG_0       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_M0_R1_CFG_0       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_M0_R1_CFG_1       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_M0_R1_CFG_1       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_M0_R1_CFG_2       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_M0_R1_CFG_2       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_M0_R1_CFG_3       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_M0_R1_CFG_3       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_M0_R1_CFG_4       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_M0_R1_CFG_4       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_M0_R1_CFG_5       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_M0_R1_CFG_5       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_M0_R1_CFG_6       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_M0_R1_CFG_6       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_M0_R1_CFG_7       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_M0_R1_CFG_7       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_M0_R1_CFG_8       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_DDR_M0_R1_CFG_8       , pipe_en);
                end
            endcase
        end
        if((byte_sel == DQ1) || (byte_sel == DQ_ALL) || (byte_sel == ALL)) begin
            case ({rank_sel,dq})
                {RANK0, 8'd0} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_M0_R0_CFG_0       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_M0_R0_CFG_0       , pipe_en);
                end
                {RANK0, 8'd1} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_M0_R0_CFG_1       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_M0_R0_CFG_1       , pipe_en);
                end
                {RANK0, 8'd2} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_M0_R0_CFG_2       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_M0_R0_CFG_2       , pipe_en);
                end
                {RANK0, 8'd3} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_M0_R0_CFG_3       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_M0_R0_CFG_3       , pipe_en);
                end
                {RANK0, 8'd4} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_M0_R0_CFG_4       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_M0_R0_CFG_4       , pipe_en);
                end
                {RANK0, 8'd5} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_M0_R0_CFG_5       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_M0_R0_CFG_5       , pipe_en);
                end
                {RANK0, 8'd6} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_M0_R0_CFG_6       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_M0_R0_CFG_6       , pipe_en);
                end
                {RANK0, 8'd7} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_M0_R0_CFG_7       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_M0_R0_CFG_7       , pipe_en);
                end
                {RANK0, 8'd8} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_M0_R0_CFG_8       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_M0_R0_CFG_8       , pipe_en);
                end
                {RANK1, 8'd0} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_M0_R1_CFG_0       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_M0_R1_CFG_0       , pipe_en);
                end
                {RANK1, 8'd1} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_M0_R1_CFG_1       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_M0_R1_CFG_1       , pipe_en);
                end
                {RANK1, 8'd2} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_M0_R1_CFG_2       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_M0_R1_CFG_2       , pipe_en);
                end
                {RANK1, 8'd3} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_M0_R1_CFG_3       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_M0_R1_CFG_3       , pipe_en);
                end
                {RANK1, 8'd4} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_M0_R1_CFG_4       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_M0_R1_CFG_4       , pipe_en);
                end
                {RANK1, 8'd5} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_M0_R1_CFG_5       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_M0_R1_CFG_5       , pipe_en);
                end
                {RANK1, 8'd6} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_M0_R1_CFG_6       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_M0_R1_CFG_6       , pipe_en);
                end
                {RANK1, 8'd7} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_M0_R1_CFG_7       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_M0_R1_CFG_7       , pipe_en);
                end
                {RANK1, 8'd8} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_M0_R1_CFG_8       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_M0_R1_CFG_8       , pipe_en);
                end
                default: begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_M0_R0_CFG_0       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_M0_R0_CFG_0       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_M0_R0_CFG_1       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_M0_R0_CFG_1       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_M0_R0_CFG_2       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_M0_R0_CFG_2       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_M0_R0_CFG_3       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_M0_R0_CFG_3       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_M0_R0_CFG_4       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_M0_R0_CFG_4       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_M0_R0_CFG_5       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_M0_R0_CFG_5       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_M0_R0_CFG_6       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_M0_R0_CFG_6       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_M0_R0_CFG_7       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_M0_R0_CFG_7       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_M0_R0_CFG_8       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_M0_R0_CFG_8       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_M0_R1_CFG_0       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_M0_R1_CFG_0       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_M0_R1_CFG_1       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_M0_R1_CFG_1       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_M0_R1_CFG_2       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_M0_R1_CFG_2       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_M0_R1_CFG_3       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_M0_R1_CFG_3       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_M0_R1_CFG_4       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_M0_R1_CFG_4       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_M0_R1_CFG_5       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_M0_R1_CFG_5       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_M0_R1_CFG_6       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_M0_R1_CFG_6       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_M0_R1_CFG_7       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_M0_R1_CFG_7       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_M0_R1_CFG_8       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_DDR_M0_R1_CFG_8       , pipe_en);
                end
            endcase
        end
        if((byte_sel == CA) || (byte_sel == ALL)) begin
            case ({rank_sel,dq})
                {RANK0, 8'd0} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_DDR_M0_R0_CFG_0       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_DDR_M0_R0_CFG_0       , pipe_en);
                end
                {RANK0, 8'd1} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_DDR_M0_R0_CFG_1       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_DDR_M0_R0_CFG_1       , pipe_en);
                end
                {RANK0, 8'd2} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_DDR_M0_R0_CFG_2       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_DDR_M0_R0_CFG_2       , pipe_en);
                end
                {RANK0, 8'd3} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_DDR_M0_R0_CFG_3       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_DDR_M0_R0_CFG_3       , pipe_en);
                end
                {RANK0, 8'd4} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_DDR_M0_R0_CFG_4       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_DDR_M0_R0_CFG_4       , pipe_en);
                end
                {RANK0, 8'd5} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_DDR_M0_R0_CFG_5       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_DDR_M0_R0_CFG_5       , pipe_en);
                end
                {RANK0, 8'd6} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_DDR_M0_R0_CFG_6       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_DDR_M0_R0_CFG_6       , pipe_en);
                end
                {RANK0, 8'd7} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_DDR_M0_R0_CFG_7       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_DDR_M0_R0_CFG_7       , pipe_en);
                end
                {RANK0, 8'd8} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_DDR_M0_R0_CFG_8       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_DDR_M0_R0_CFG_8       , pipe_en);
                end
                {RANK0, 8'd9} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_DDR_M0_R0_CFG_9       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_DDR_M0_R0_CFG_9       , pipe_en);
                end
                {RANK0, 8'd10} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_DDR_M0_R0_CFG_10       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_DDR_M0_R0_CFG_10       , pipe_en);
                end
                {RANK1, 8'd0} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_DDR_M0_R1_CFG_0       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_DDR_M0_R1_CFG_0       , pipe_en);
                end
                {RANK1, 8'd1} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_DDR_M0_R1_CFG_1       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_DDR_M0_R1_CFG_1       , pipe_en);
                end
                {RANK1, 8'd2} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_DDR_M0_R1_CFG_2       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_DDR_M0_R1_CFG_2       , pipe_en);
                end
                {RANK1, 8'd3} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_DDR_M0_R1_CFG_3       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_DDR_M0_R1_CFG_3       , pipe_en);
                end
                {RANK1, 8'd4} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_DDR_M0_R1_CFG_4       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_DDR_M0_R1_CFG_4       , pipe_en);
                end
                {RANK1, 8'd5} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_DDR_M0_R1_CFG_5       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_DDR_M0_R1_CFG_5       , pipe_en);
                end
                {RANK1, 8'd6} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_DDR_M0_R1_CFG_6       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_DDR_M0_R1_CFG_6       , pipe_en);
                end
                {RANK1, 8'd7} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_DDR_M0_R1_CFG_7       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_DDR_M0_R1_CFG_7       , pipe_en);
                end
                {RANK1, 8'd8} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_DDR_M0_R1_CFG_8       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_DDR_M0_R1_CFG_8       , pipe_en);
                end
                {RANK1, 8'd9} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_DDR_M0_R1_CFG_9       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_DDR_M0_R1_CFG_9       , pipe_en);
                end
                {RANK1, 8'd10} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_DDR_M0_R1_CFG_10       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_DDR_M0_R1_CFG_10       , pipe_en);
                end
                default: begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_DDR_M0_R0_CFG_0       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_DDR_M0_R0_CFG_0       , pipe_en);
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_DDR_M0_R0_CFG_1       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_DDR_M0_R0_CFG_1       , pipe_en);
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_DDR_M0_R0_CFG_2       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_DDR_M0_R0_CFG_2       , pipe_en);
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_DDR_M0_R0_CFG_3       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_DDR_M0_R0_CFG_3       , pipe_en);
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_DDR_M0_R0_CFG_4       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_DDR_M0_R0_CFG_4       , pipe_en);
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_DDR_M0_R0_CFG_5       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_DDR_M0_R0_CFG_5       , pipe_en);
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_DDR_M0_R0_CFG_6       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_DDR_M0_R0_CFG_6       , pipe_en);
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_DDR_M0_R0_CFG_7       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_DDR_M0_R0_CFG_7       , pipe_en);
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_DDR_M0_R0_CFG_8       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_DDR_M0_R0_CFG_8       , pipe_en);
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_DDR_M0_R0_CFG_9       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_DDR_M0_R0_CFG_9       , pipe_en);
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_DDR_M0_R0_CFG_10       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_DDR_M0_R0_CFG_10       , pipe_en);
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_DDR_M0_R1_CFG_0       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_DDR_M0_R1_CFG_0       , pipe_en);
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_DDR_M0_R1_CFG_1       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_DDR_M0_R1_CFG_1       , pipe_en);
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_DDR_M0_R1_CFG_2       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_DDR_M0_R1_CFG_2       , pipe_en);
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_DDR_M0_R1_CFG_3       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_DDR_M0_R1_CFG_3       , pipe_en);
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_DDR_M0_R1_CFG_4       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_DDR_M0_R1_CFG_4       , pipe_en);
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_DDR_M0_R1_CFG_5       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_DDR_M0_R1_CFG_5       , pipe_en);
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_DDR_M0_R1_CFG_6       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_DDR_M0_R1_CFG_6       , pipe_en);
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_DDR_M0_R1_CFG_7       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_DDR_M0_R1_CFG_7       , pipe_en);
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_DDR_M0_R1_CFG_8       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_DDR_M0_R1_CFG_8       , pipe_en);
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_DDR_M0_R1_CFG_9       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_DDR_M0_R1_CFG_9       , pipe_en);
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_DDR_M0_R1_CFG_10       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_DDR_M0_R1_CFG_10       , pipe_en);
                end
            endcase
        end
    end
endtask

task automatic set_txdq_qdr_x_sel;
    input byte_sel_t     byte_sel;
    input rank_sel_t     rank_sel;
    input logic    [7:0] dq;
    input logic   [31:0] x_sel;
    begin
        if((byte_sel == DQ0) || (byte_sel == DQ_ALL) || (byte_sel == ALL)) begin
            case ({rank_sel,dq})
                {RANK0, 8'd0} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M0_R0_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M0_R0_CFG_0 , x_sel  );
                end
                {RANK0, 8'd1} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M0_R0_CFG_1 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M0_R0_CFG_1 , x_sel  );
                end
                {RANK0, 8'd2} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M0_R0_CFG_2 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M0_R0_CFG_2 , x_sel  );
                end
                {RANK0, 8'd3} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M0_R0_CFG_3 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M0_R0_CFG_3 , x_sel  );
                end
                {RANK0, 8'd4} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M0_R0_CFG_4 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M0_R0_CFG_4 , x_sel  );
                end
                {RANK0, 8'd5} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M0_R0_CFG_5 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M0_R0_CFG_5 , x_sel  );
                end
                {RANK0, 8'd6} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M0_R0_CFG_6 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M0_R0_CFG_6 , x_sel  );
                end
                {RANK0, 8'd7} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M0_R0_CFG_7 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M0_R0_CFG_7 , x_sel  );
                end
                {RANK0, 8'd8} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M0_R0_CFG_8 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M0_R0_CFG_8 , x_sel  );
                end
                {RANK1, 8'd0} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M0_R1_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M0_R1_CFG_0 , x_sel  );
                end
                {RANK1, 8'd1} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M0_R1_CFG_1 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M0_R1_CFG_1 , x_sel  );
                end
                {RANK1, 8'd2} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M0_R1_CFG_2 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M0_R1_CFG_2 , x_sel  );
                end
                {RANK1, 8'd3} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M0_R1_CFG_3 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M0_R1_CFG_3 , x_sel  );
                end
                {RANK1, 8'd4} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M0_R1_CFG_4 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M0_R1_CFG_4 , x_sel  );
                end
                {RANK1, 8'd5} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M0_R1_CFG_5 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M0_R1_CFG_5 , x_sel  );
                end
                {RANK1, 8'd6} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M0_R1_CFG_6 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M0_R1_CFG_6 , x_sel  );
                end
                {RANK1, 8'd7} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M0_R1_CFG_7 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M0_R1_CFG_7 , x_sel  );
                end
                {RANK1, 8'd8} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M0_R1_CFG_8 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M0_R1_CFG_8 , x_sel  );
                end
                default: begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M0_R0_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M0_R1_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M0_R0_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M0_R1_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M0_R0_CFG_1 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M0_R1_CFG_1 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M0_R0_CFG_1 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M0_R1_CFG_1 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M0_R0_CFG_2 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M0_R1_CFG_2 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M0_R0_CFG_2 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M0_R1_CFG_2 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M0_R0_CFG_3 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M0_R1_CFG_3 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M0_R0_CFG_3 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M0_R1_CFG_3 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M0_R0_CFG_4 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M0_R1_CFG_4 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M0_R0_CFG_4 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M0_R1_CFG_4 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M0_R0_CFG_5 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M0_R1_CFG_5 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M0_R0_CFG_5 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M0_R1_CFG_5 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M0_R0_CFG_6 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M0_R1_CFG_6 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M0_R0_CFG_6 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M0_R1_CFG_6 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M0_R0_CFG_7 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M0_R1_CFG_7 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M0_R0_CFG_7 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M0_R1_CFG_7 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M0_R0_CFG_8 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M0_R1_CFG_8 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M0_R0_CFG_8 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M0_R1_CFG_8 , x_sel  );
                end
            endcase
        end
        if((byte_sel == DQ1) || (byte_sel == DQ_ALL) || (byte_sel == ALL)) begin
            case ({rank_sel,dq})
                {RANK0, 8'd0} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M0_R0_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M0_R0_CFG_0 , x_sel  );
                end
                {RANK0, 8'd1} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M0_R0_CFG_1 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M0_R0_CFG_1 , x_sel  );
                end
                {RANK0, 8'd2} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M0_R0_CFG_2 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M0_R0_CFG_2 , x_sel  );
                end
                {RANK0, 8'd3} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M0_R0_CFG_3 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M0_R0_CFG_3 , x_sel  );
                end
                {RANK0, 8'd4} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M0_R0_CFG_4 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M0_R0_CFG_4 , x_sel  );
                end
                {RANK0, 8'd5} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M0_R0_CFG_5 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M0_R0_CFG_5 , x_sel  );
                end
                {RANK0, 8'd6} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M0_R0_CFG_6 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M0_R0_CFG_6 , x_sel  );
                end
                {RANK0, 8'd7} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M0_R0_CFG_7 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M0_R0_CFG_7 , x_sel  );
                end
                {RANK0, 8'd8} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M0_R0_CFG_8 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M0_R0_CFG_8 , x_sel  );
                end
                {RANK1, 8'd0} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M0_R1_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M0_R1_CFG_0 , x_sel  );
                end
                {RANK1, 8'd1} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M0_R1_CFG_1 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M0_R1_CFG_1 , x_sel  );
                end
                {RANK1, 8'd2} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M0_R1_CFG_2 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M0_R1_CFG_2 , x_sel  );
                end
                {RANK1, 8'd3} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M0_R1_CFG_3 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M0_R1_CFG_3 , x_sel  );
                end
                {RANK1, 8'd4} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M0_R1_CFG_4 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M0_R1_CFG_4 , x_sel  );
                end
                {RANK1, 8'd5} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M0_R1_CFG_5 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M0_R1_CFG_5 , x_sel  );
                end
                {RANK1, 8'd6} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M0_R1_CFG_6 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M0_R1_CFG_6 , x_sel  );
                end
                {RANK1, 8'd7} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M0_R1_CFG_7 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M0_R1_CFG_7 , x_sel  );
                end
                {RANK1, 8'd8} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M0_R1_CFG_8 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M0_R1_CFG_8 , x_sel  );
                end
                default: begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M0_R0_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M0_R1_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M0_R0_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M0_R1_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M0_R0_CFG_1 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M0_R1_CFG_1 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M0_R0_CFG_1 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M0_R1_CFG_1 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M0_R0_CFG_2 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M0_R1_CFG_2 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M0_R0_CFG_2 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M0_R1_CFG_2 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M0_R0_CFG_3 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M0_R1_CFG_3 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M0_R0_CFG_3 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M0_R1_CFG_3 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M0_R0_CFG_4 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M0_R1_CFG_4 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M0_R0_CFG_4 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M0_R1_CFG_4 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M0_R0_CFG_5 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M0_R1_CFG_5 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M0_R0_CFG_5 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M0_R1_CFG_5 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M0_R0_CFG_6 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M0_R1_CFG_6 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M0_R0_CFG_6 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M0_R1_CFG_6 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M0_R0_CFG_7 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M0_R1_CFG_7 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M0_R0_CFG_7 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M0_R1_CFG_7 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M0_R0_CFG_8 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M0_R1_CFG_8 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M0_R0_CFG_8 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_X_SEL_M0_R1_CFG_8 , x_sel  );
                end
            endcase
        end
        if((byte_sel == CA) || (byte_sel == ALL)) begin
            case ({rank_sel,dq})
                {RANK0, 8'd0} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_QDR_X_SEL_M0_R0_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_QDR_X_SEL_M0_R0_CFG_0 , x_sel  );
                end
                {RANK0, 8'd1} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_QDR_X_SEL_M0_R0_CFG_1 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_QDR_X_SEL_M0_R0_CFG_1 , x_sel  );
                end
                {RANK0, 8'd2} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_QDR_X_SEL_M0_R0_CFG_2 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_QDR_X_SEL_M0_R0_CFG_2 , x_sel  );
                end
                {RANK0, 8'd3} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_QDR_X_SEL_M0_R0_CFG_3 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_QDR_X_SEL_M0_R0_CFG_3 , x_sel  );
                end
                {RANK0, 8'd4} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_QDR_X_SEL_M0_R0_CFG_4 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_QDR_X_SEL_M0_R0_CFG_4 , x_sel  );
                end
                {RANK0, 8'd5} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_QDR_X_SEL_M0_R0_CFG_5 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_QDR_X_SEL_M0_R0_CFG_5 , x_sel  );
                end
                {RANK0, 8'd6} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_QDR_X_SEL_M0_R0_CFG_6 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_QDR_X_SEL_M0_R0_CFG_6 , x_sel  );
                end
                {RANK0, 8'd7} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_QDR_X_SEL_M0_R0_CFG_7 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_QDR_X_SEL_M0_R0_CFG_7 , x_sel  );
                end
                {RANK0, 8'd8} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_QDR_X_SEL_M0_R0_CFG_8 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_QDR_X_SEL_M0_R0_CFG_8 , x_sel  );
                end
                {RANK0, 8'd9} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_QDR_X_SEL_M0_R0_CFG_9 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_QDR_X_SEL_M0_R0_CFG_9 , x_sel  );
                end
                {RANK0, 8'd10} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_QDR_X_SEL_M0_R0_CFG_10 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_QDR_X_SEL_M0_R0_CFG_10 , x_sel  );
                end
                {RANK1, 8'd0} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_QDR_X_SEL_M0_R1_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_QDR_X_SEL_M0_R1_CFG_0 , x_sel  );
                end
                {RANK1, 8'd1} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_QDR_X_SEL_M0_R1_CFG_1 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_QDR_X_SEL_M0_R1_CFG_1 , x_sel  );
                end
                {RANK1, 8'd2} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_QDR_X_SEL_M0_R1_CFG_2 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_QDR_X_SEL_M0_R1_CFG_2 , x_sel  );
                end
                {RANK1, 8'd3} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_QDR_X_SEL_M0_R1_CFG_3 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_QDR_X_SEL_M0_R1_CFG_3 , x_sel  );
                end
                {RANK1, 8'd4} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_QDR_X_SEL_M0_R1_CFG_4 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_QDR_X_SEL_M0_R1_CFG_4 , x_sel  );
                end
                {RANK1, 8'd5} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_QDR_X_SEL_M0_R1_CFG_5 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_QDR_X_SEL_M0_R1_CFG_5 , x_sel  );
                end
                {RANK1, 8'd6} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_QDR_X_SEL_M0_R1_CFG_6 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_QDR_X_SEL_M0_R1_CFG_6 , x_sel  );
                end
                {RANK1, 8'd7} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_QDR_X_SEL_M0_R1_CFG_7 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_QDR_X_SEL_M0_R1_CFG_7 , x_sel  );
                end
                {RANK1, 8'd8} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_QDR_X_SEL_M0_R1_CFG_8 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_QDR_X_SEL_M0_R1_CFG_8 , x_sel  );
                end
                {RANK1, 8'd9} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_QDR_X_SEL_M0_R1_CFG_9 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_QDR_X_SEL_M0_R1_CFG_9 , x_sel  );
                end
                {RANK1, 8'd10} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_QDR_X_SEL_M0_R1_CFG_10 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_QDR_X_SEL_M0_R1_CFG_10 , x_sel  );
                end
                default: begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_QDR_X_SEL_M0_R0_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_QDR_X_SEL_M0_R1_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_QDR_X_SEL_M0_R0_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_QDR_X_SEL_M0_R1_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_QDR_X_SEL_M0_R0_CFG_1 , x_sel  );
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_QDR_X_SEL_M0_R1_CFG_1 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_QDR_X_SEL_M0_R0_CFG_1 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_QDR_X_SEL_M0_R1_CFG_1 , x_sel  );
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_QDR_X_SEL_M0_R0_CFG_2 , x_sel  );
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_QDR_X_SEL_M0_R1_CFG_2 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_QDR_X_SEL_M0_R0_CFG_2 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_QDR_X_SEL_M0_R1_CFG_2 , x_sel  );
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_QDR_X_SEL_M0_R0_CFG_3 , x_sel  );
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_QDR_X_SEL_M0_R1_CFG_3 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_QDR_X_SEL_M0_R0_CFG_3 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_QDR_X_SEL_M0_R1_CFG_3 , x_sel  );
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_QDR_X_SEL_M0_R0_CFG_4 , x_sel  );
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_QDR_X_SEL_M0_R1_CFG_4 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_QDR_X_SEL_M0_R0_CFG_4 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_QDR_X_SEL_M0_R1_CFG_4 , x_sel  );
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_QDR_X_SEL_M0_R0_CFG_5 , x_sel  );
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_QDR_X_SEL_M0_R1_CFG_5 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_QDR_X_SEL_M0_R0_CFG_5 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_QDR_X_SEL_M0_R1_CFG_5 , x_sel  );
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_QDR_X_SEL_M0_R0_CFG_6 , x_sel  );
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_QDR_X_SEL_M0_R1_CFG_6 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_QDR_X_SEL_M0_R0_CFG_6 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_QDR_X_SEL_M0_R1_CFG_6 , x_sel  );
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_QDR_X_SEL_M0_R0_CFG_7 , x_sel  );
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_QDR_X_SEL_M0_R1_CFG_7 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_QDR_X_SEL_M0_R0_CFG_7 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_QDR_X_SEL_M0_R1_CFG_7 , x_sel  );
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_QDR_X_SEL_M0_R0_CFG_8 , x_sel  );
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_QDR_X_SEL_M0_R1_CFG_8 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_QDR_X_SEL_M0_R0_CFG_8 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_QDR_X_SEL_M0_R1_CFG_8 , x_sel  );
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_QDR_X_SEL_M0_R0_CFG_9 , x_sel  );
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_QDR_X_SEL_M0_R1_CFG_9 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_QDR_X_SEL_M0_R0_CFG_9 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_QDR_X_SEL_M0_R1_CFG_9 , x_sel  );
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_QDR_X_SEL_M0_R0_CFG_10 , x_sel  );
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_QDR_X_SEL_M0_R1_CFG_10 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_QDR_X_SEL_M0_R0_CFG_10 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_QDR_X_SEL_M0_R1_CFG_10 , x_sel  );
                end
            endcase
        end
    end
endtask

task automatic set_txdq_qdr_pipe_en ;
    input byte_sel_t     byte_sel;
    input rank_sel_t     rank_sel;
    input logic    [7:0] dq;
    input logic   [31:0] pipe_en;
    begin
        if((byte_sel == DQ0) || (byte_sel == DQ_ALL) || (byte_sel == ALL)) begin
            case ({rank_sel,dq})
                {RANK0, 8'd0} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_M0_R0_CFG_0       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_M0_R0_CFG_0       , pipe_en);
                end
                {RANK0, 8'd1} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_M0_R0_CFG_1       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_M0_R0_CFG_1       , pipe_en);
                end
                {RANK0, 8'd2} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_M0_R0_CFG_2       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_M0_R0_CFG_2       , pipe_en);
                end
                {RANK0, 8'd3} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_M0_R0_CFG_3       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_M0_R0_CFG_3       , pipe_en);
                end
                {RANK0, 8'd4} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_M0_R0_CFG_4       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_M0_R0_CFG_4       , pipe_en);
                end
                {RANK0, 8'd5} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_M0_R0_CFG_5       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_M0_R0_CFG_5       , pipe_en);
                end
                {RANK0, 8'd6} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_M0_R0_CFG_6       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_M0_R0_CFG_6       , pipe_en);
                end
                {RANK0, 8'd7} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_M0_R0_CFG_7       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_M0_R0_CFG_7       , pipe_en);
                end
                {RANK0, 8'd8} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_M0_R0_CFG_8       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_M0_R0_CFG_8       , pipe_en);
                end
                {RANK1, 8'd0} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_M0_R1_CFG_0       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_M0_R1_CFG_0       , pipe_en);
                end
                {RANK1, 8'd1} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_M0_R1_CFG_1       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_M0_R1_CFG_1       , pipe_en);
                end
                {RANK1, 8'd2} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_M0_R1_CFG_2       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_M0_R1_CFG_2       , pipe_en);
                end
                {RANK1, 8'd3} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_M0_R1_CFG_3       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_M0_R1_CFG_3       , pipe_en);
                end
                {RANK1, 8'd4} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_M0_R1_CFG_4       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_M0_R1_CFG_4       , pipe_en);
                end
                {RANK1, 8'd5} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_M0_R1_CFG_5       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_M0_R1_CFG_5       , pipe_en);
                end
                {RANK1, 8'd6} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_M0_R1_CFG_6       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_M0_R1_CFG_6       , pipe_en);
                end
                {RANK1, 8'd7} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_M0_R1_CFG_7       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_M0_R1_CFG_7       , pipe_en);
                end
                {RANK1, 8'd8} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_M0_R1_CFG_8       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_M0_R1_CFG_8       , pipe_en);
                end
                default: begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_M0_R0_CFG_0       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_M0_R0_CFG_0       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_M0_R0_CFG_1       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_M0_R0_CFG_1       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_M0_R0_CFG_2       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_M0_R0_CFG_2       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_M0_R0_CFG_3       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_M0_R0_CFG_3       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_M0_R0_CFG_4       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_M0_R0_CFG_4       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_M0_R0_CFG_5       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_M0_R0_CFG_5       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_M0_R0_CFG_6       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_M0_R0_CFG_6       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_M0_R0_CFG_7       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_M0_R0_CFG_7       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_M0_R0_CFG_8       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_M0_R0_CFG_8       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_M0_R1_CFG_0       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_M0_R1_CFG_0       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_M0_R1_CFG_1       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_M0_R1_CFG_1       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_M0_R1_CFG_2       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_M0_R1_CFG_2       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_M0_R1_CFG_3       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_M0_R1_CFG_3       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_M0_R1_CFG_4       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_M0_R1_CFG_4       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_M0_R1_CFG_5       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_M0_R1_CFG_5       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_M0_R1_CFG_6       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_M0_R1_CFG_6       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_M0_R1_CFG_7       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_M0_R1_CFG_7       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_M0_R1_CFG_8       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_TX_QDR_M0_R1_CFG_8       , pipe_en);
                end
            endcase
        end
        if((byte_sel == DQ1) || (byte_sel == DQ_ALL) || (byte_sel == ALL)) begin
            case ({rank_sel,dq})
                {RANK0, 8'd0} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_M0_R0_CFG_0       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_M0_R0_CFG_0       , pipe_en);
                end
                {RANK0, 8'd1} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_M0_R0_CFG_1       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_M0_R0_CFG_1       , pipe_en);
                end
                {RANK0, 8'd2} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_M0_R0_CFG_2       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_M0_R0_CFG_2       , pipe_en);
                end
                {RANK0, 8'd3} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_M0_R0_CFG_3       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_M0_R0_CFG_3       , pipe_en);
                end
                {RANK0, 8'd4} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_M0_R0_CFG_4       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_M0_R0_CFG_4       , pipe_en);
                end
                {RANK0, 8'd5} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_M0_R0_CFG_5       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_M0_R0_CFG_5       , pipe_en);
                end
                {RANK0, 8'd6} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_M0_R0_CFG_6       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_M0_R0_CFG_6       , pipe_en);
                end
                {RANK0, 8'd7} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_M0_R0_CFG_7       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_M0_R0_CFG_7       , pipe_en);
                end
                {RANK0, 8'd8} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_M0_R0_CFG_8       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_M0_R0_CFG_8       , pipe_en);
                end
                {RANK1, 8'd0} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_M0_R1_CFG_0       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_M0_R1_CFG_0       , pipe_en);
                end
                {RANK1, 8'd1} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_M0_R1_CFG_1       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_M0_R1_CFG_1       , pipe_en);
                end
                {RANK1, 8'd2} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_M0_R1_CFG_2       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_M0_R1_CFG_2       , pipe_en);
                end
                {RANK1, 8'd3} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_M0_R1_CFG_3       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_M0_R1_CFG_3       , pipe_en);
                end
                {RANK1, 8'd4} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_M0_R1_CFG_4       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_M0_R1_CFG_4       , pipe_en);
                end
                {RANK1, 8'd5} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_M0_R1_CFG_5       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_M0_R1_CFG_5       , pipe_en);
                end
                {RANK1, 8'd6} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_M0_R1_CFG_6       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_M0_R1_CFG_6       , pipe_en);
                end
                {RANK1, 8'd7} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_M0_R1_CFG_7       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_M0_R1_CFG_7       , pipe_en);
                end
                {RANK1, 8'd8} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_M0_R1_CFG_8       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_M0_R1_CFG_8       , pipe_en);
                end
                default: begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_M0_R0_CFG_0       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_M0_R0_CFG_0       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_M0_R0_CFG_1       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_M0_R0_CFG_1       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_M0_R0_CFG_2       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_M0_R0_CFG_2       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_M0_R0_CFG_3       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_M0_R0_CFG_3       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_M0_R0_CFG_4       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_M0_R0_CFG_4       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_M0_R0_CFG_5       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_M0_R0_CFG_5       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_M0_R0_CFG_6       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_M0_R0_CFG_6       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_M0_R0_CFG_7       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_M0_R0_CFG_7       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_M0_R0_CFG_8       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_M0_R0_CFG_8       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_M0_R1_CFG_0       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_M0_R1_CFG_0       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_M0_R1_CFG_1       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_M0_R1_CFG_1       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_M0_R1_CFG_2       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_M0_R1_CFG_2       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_M0_R1_CFG_3       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_M0_R1_CFG_3       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_M0_R1_CFG_4       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_M0_R1_CFG_4       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_M0_R1_CFG_5       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_M0_R1_CFG_5       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_M0_R1_CFG_6       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_M0_R1_CFG_6       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_M0_R1_CFG_7       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_M0_R1_CFG_7       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_M0_R1_CFG_8       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_TX_QDR_M0_R1_CFG_8       , pipe_en);
                end
            endcase
        end
        if((byte_sel == CA) || (byte_sel == ALL)) begin
            case ({rank_sel,dq})
                {RANK0, 8'd0} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_QDR_M0_R0_CFG_0       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_QDR_M0_R0_CFG_0       , pipe_en);
                end
                {RANK0, 8'd1} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_QDR_M0_R0_CFG_1       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_QDR_M0_R0_CFG_1       , pipe_en);
                end
                {RANK0, 8'd2} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_QDR_M0_R0_CFG_2       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_QDR_M0_R0_CFG_2       , pipe_en);
                end
                {RANK0, 8'd3} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_QDR_M0_R0_CFG_3       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_QDR_M0_R0_CFG_3       , pipe_en);
                end
                {RANK0, 8'd4} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_QDR_M0_R0_CFG_4       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_QDR_M0_R0_CFG_4       , pipe_en);
                end
                {RANK0, 8'd5} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_QDR_M0_R0_CFG_5       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_QDR_M0_R0_CFG_5       , pipe_en);
                end
                {RANK0, 8'd6} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_QDR_M0_R0_CFG_6       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_QDR_M0_R0_CFG_6       , pipe_en);
                end
                {RANK0, 8'd7} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_QDR_M0_R0_CFG_7       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_QDR_M0_R0_CFG_7       , pipe_en);
                end
                {RANK0, 8'd8} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_QDR_M0_R0_CFG_8       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_QDR_M0_R0_CFG_8       , pipe_en);
                end
                {RANK0, 8'd9} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_QDR_M0_R0_CFG_9       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_QDR_M0_R0_CFG_9       , pipe_en);
                end
                {RANK0, 8'd10} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_QDR_M0_R0_CFG_10       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_QDR_M0_R0_CFG_10       , pipe_en);
                end
                {RANK1, 8'd0} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_QDR_M0_R1_CFG_0       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_QDR_M0_R1_CFG_0       , pipe_en);
                end
                {RANK1, 8'd1} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_QDR_M0_R1_CFG_1       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_QDR_M0_R1_CFG_1       , pipe_en);
                end
                {RANK1, 8'd2} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_QDR_M0_R1_CFG_2       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_QDR_M0_R1_CFG_2       , pipe_en);
                end
                {RANK1, 8'd3} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_QDR_M0_R1_CFG_3       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_QDR_M0_R1_CFG_3       , pipe_en);
                end
                {RANK1, 8'd4} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_QDR_M0_R1_CFG_4       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_QDR_M0_R1_CFG_4       , pipe_en);
                end
                {RANK1, 8'd5} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_QDR_M0_R1_CFG_5       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_QDR_M0_R1_CFG_5       , pipe_en);
                end
                {RANK1, 8'd6} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_QDR_M0_R1_CFG_6       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_QDR_M0_R1_CFG_6       , pipe_en);
                end
                {RANK1, 8'd7} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_QDR_M0_R1_CFG_7       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_QDR_M0_R1_CFG_7       , pipe_en);
                end
                {RANK1, 8'd8} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_QDR_M0_R1_CFG_8       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_QDR_M0_R1_CFG_8       , pipe_en);
                end
                {RANK1, 8'd9} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_QDR_M0_R1_CFG_9       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_QDR_M0_R1_CFG_9       , pipe_en);
                end
                {RANK1, 8'd10} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_QDR_M0_R1_CFG_10       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_QDR_M0_R1_CFG_10       , pipe_en);
                end
                default: begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_QDR_M0_R0_CFG_0       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_QDR_M0_R0_CFG_0       , pipe_en);
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_QDR_M0_R0_CFG_1       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_QDR_M0_R0_CFG_1       , pipe_en);
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_QDR_M0_R0_CFG_2       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_QDR_M0_R0_CFG_2       , pipe_en);
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_QDR_M0_R0_CFG_3       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_QDR_M0_R0_CFG_3       , pipe_en);
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_QDR_M0_R0_CFG_4       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_QDR_M0_R0_CFG_4       , pipe_en);
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_QDR_M0_R0_CFG_5       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_QDR_M0_R0_CFG_5       , pipe_en);
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_QDR_M0_R0_CFG_6       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_QDR_M0_R0_CFG_6       , pipe_en);
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_QDR_M0_R0_CFG_7       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_QDR_M0_R0_CFG_7       , pipe_en);
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_QDR_M0_R0_CFG_8       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_QDR_M0_R0_CFG_8       , pipe_en);
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_QDR_M0_R0_CFG_9       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_QDR_M0_R0_CFG_9       , pipe_en);
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_QDR_M0_R0_CFG_10       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_QDR_M0_R0_CFG_10       , pipe_en);
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_QDR_M0_R1_CFG_0       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_QDR_M0_R1_CFG_0       , pipe_en);
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_QDR_M0_R1_CFG_1       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_QDR_M0_R1_CFG_1       , pipe_en);
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_QDR_M0_R1_CFG_2       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_QDR_M0_R1_CFG_2       , pipe_en);
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_QDR_M0_R1_CFG_3       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_QDR_M0_R1_CFG_3       , pipe_en);
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_QDR_M0_R1_CFG_4       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_QDR_M0_R1_CFG_4       , pipe_en);
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_QDR_M0_R1_CFG_5       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_QDR_M0_R1_CFG_5       , pipe_en);
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_QDR_M0_R1_CFG_6       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_QDR_M0_R1_CFG_6       , pipe_en);
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_QDR_M0_R1_CFG_7       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_QDR_M0_R1_CFG_7       , pipe_en);
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_QDR_M0_R1_CFG_8       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_QDR_M0_R1_CFG_8       , pipe_en);
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_QDR_M0_R1_CFG_9       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_QDR_M0_R1_CFG_9       , pipe_en);
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQ_TX_QDR_M0_R1_CFG_10       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQ_TX_QDR_M0_R1_CFG_10       , pipe_en);
                end
            endcase
        end
    end
endtask

task automatic set_txdqs_sdr_fc_dly;
    input byte_sel_t     byte_sel;
    input rank_sel_t     rank_sel;
    input logic    [7:0] dqs;
    input logic   [31:0] fc_dly;
    begin
        if((byte_sel == DQ0) || (byte_sel == DQ_ALL) || (byte_sel == ALL)) begin
            case ({rank_sel,dqs})
                {RANK0, 8'd0} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R0_CFG_0, fc_dly );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R0_CFG_0, fc_dly );
                end
                {RANK0, 8'd1} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R0_CFG_1, fc_dly );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R0_CFG_1, fc_dly );
                end
                {RANK0, 8'd2} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R0_CFG_2, fc_dly );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R0_CFG_2, fc_dly );
                end
                {RANK0, 8'd3} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R0_CFG_3, fc_dly );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R0_CFG_3, fc_dly );
                end
                {RANK0, 8'd4} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R0_CFG_4, fc_dly );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R0_CFG_4, fc_dly );
                end
                {RANK0, 8'd5} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R0_CFG_5, fc_dly );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R0_CFG_5, fc_dly );
                end
                {RANK0, 8'd6} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R0_CFG_6, fc_dly );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R0_CFG_6, fc_dly );
                end
                {RANK0, 8'd7} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R0_CFG_7, fc_dly );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R0_CFG_7, fc_dly );
                end
                {RANK0, 8'd8} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R0_CFG_8, fc_dly );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R0_CFG_8, fc_dly );
                end
                {RANK1, 8'd0} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R1_CFG_0, fc_dly );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R1_CFG_0, fc_dly );
                end
                {RANK1, 8'd1} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R1_CFG_1, fc_dly );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R1_CFG_1, fc_dly );
                end
                {RANK1, 8'd2} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R1_CFG_2, fc_dly );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R1_CFG_2, fc_dly );
                end
                {RANK1, 8'd3} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R1_CFG_3, fc_dly );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R1_CFG_3, fc_dly );
                end
                {RANK1, 8'd4} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R1_CFG_4, fc_dly );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R1_CFG_4, fc_dly );
                end
                {RANK1, 8'd5} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R1_CFG_5, fc_dly );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R1_CFG_5, fc_dly );
                end
                {RANK1, 8'd6} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R1_CFG_6, fc_dly );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R1_CFG_6, fc_dly );
                end
                {RANK1, 8'd7} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R1_CFG_7, fc_dly );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R1_CFG_7, fc_dly );
                end
                {RANK1, 8'd8} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R1_CFG_8, fc_dly );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R1_CFG_8, fc_dly );
                end
                {RANK_ALL, 8'd0} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R0_CFG_0, fc_dly );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R0_CFG_0, fc_dly );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R1_CFG_0, fc_dly );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R1_CFG_0, fc_dly );
                end
                {RANK_ALL, 8'd1} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R0_CFG_1, fc_dly );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R0_CFG_1, fc_dly );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R1_CFG_1, fc_dly );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R1_CFG_1, fc_dly );
                end
                {RANK_ALL, 8'd2} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R0_CFG_2, fc_dly );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R0_CFG_2, fc_dly );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R1_CFG_2, fc_dly );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R1_CFG_2, fc_dly );
                end
                {RANK_ALL, 8'd3} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R0_CFG_3, fc_dly );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R0_CFG_3, fc_dly );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R1_CFG_3, fc_dly );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R1_CFG_3, fc_dly );
                end
                {RANK_ALL, 8'd4} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R0_CFG_4, fc_dly );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R0_CFG_4, fc_dly );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R1_CFG_4, fc_dly );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R1_CFG_4, fc_dly );
                end
                {RANK_ALL, 8'd5} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R0_CFG_5, fc_dly );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R0_CFG_5, fc_dly );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R1_CFG_5, fc_dly );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R1_CFG_5, fc_dly );
                end
                {RANK_ALL, 8'd6} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R0_CFG_6, fc_dly );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R0_CFG_6, fc_dly );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R1_CFG_6, fc_dly );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R1_CFG_6, fc_dly );
                end
                {RANK_ALL, 8'd7} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R0_CFG_7, fc_dly );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R0_CFG_7, fc_dly );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R1_CFG_7, fc_dly );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R1_CFG_7, fc_dly );
                end
                {RANK_ALL, 8'd8} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R0_CFG_8, fc_dly );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R0_CFG_8, fc_dly );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R1_CFG_8, fc_dly );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R1_CFG_8, fc_dly );
                end
                default: begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R0_CFG_0, fc_dly );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R0_CFG_0, fc_dly );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R0_CFG_1, fc_dly );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R0_CFG_1, fc_dly );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R0_CFG_2, fc_dly );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R0_CFG_2, fc_dly );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R0_CFG_3, fc_dly );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R0_CFG_3, fc_dly );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R0_CFG_4, fc_dly );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R0_CFG_4, fc_dly );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R0_CFG_5, fc_dly );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R0_CFG_5, fc_dly );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R0_CFG_6, fc_dly );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R0_CFG_6, fc_dly );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R0_CFG_7, fc_dly );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R0_CFG_7, fc_dly );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R0_CFG_8, fc_dly );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R0_CFG_8, fc_dly );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R1_CFG_0, fc_dly );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R1_CFG_0, fc_dly );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R1_CFG_1, fc_dly );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R1_CFG_1, fc_dly );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R1_CFG_2, fc_dly );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R1_CFG_2, fc_dly );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R1_CFG_3, fc_dly );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R1_CFG_3, fc_dly );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R1_CFG_4, fc_dly );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R1_CFG_4, fc_dly );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R1_CFG_5, fc_dly );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R1_CFG_5, fc_dly );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R1_CFG_6, fc_dly );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R1_CFG_6, fc_dly );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R1_CFG_7, fc_dly );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R1_CFG_7, fc_dly );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R1_CFG_8, fc_dly );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R1_CFG_8, fc_dly );
                end
            endcase
        end
        if((byte_sel == DQ1) || (byte_sel == DQ_ALL) || (byte_sel == ALL)) begin
            case ({rank_sel,dqs})
                {RANK0, 8'd0} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R0_CFG_0, fc_dly );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R0_CFG_0, fc_dly );
                end
                {RANK0, 8'd1} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R0_CFG_1, fc_dly );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R0_CFG_1, fc_dly );
                end
                {RANK0, 8'd2} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R0_CFG_2, fc_dly );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R0_CFG_2, fc_dly );
                end
                {RANK0, 8'd3} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R0_CFG_3, fc_dly );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R0_CFG_3, fc_dly );
                end
                {RANK0, 8'd4} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R0_CFG_4, fc_dly );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R0_CFG_4, fc_dly );
                end
                {RANK0, 8'd5} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R0_CFG_5, fc_dly );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R0_CFG_5, fc_dly );
                end
                {RANK0, 8'd6} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R0_CFG_6, fc_dly );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R0_CFG_6, fc_dly );
                end
                {RANK0, 8'd7} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R0_CFG_7, fc_dly );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R0_CFG_7, fc_dly );
                end
                {RANK0, 8'd8} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R0_CFG_8, fc_dly );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R0_CFG_8, fc_dly );
                end
                {RANK1, 8'd0} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R1_CFG_0, fc_dly );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R1_CFG_0, fc_dly );
                end
                {RANK1, 8'd1} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R1_CFG_1, fc_dly );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R1_CFG_1, fc_dly );
                end
                {RANK1, 8'd2} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R1_CFG_2, fc_dly );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R1_CFG_2, fc_dly );
                end
                {RANK1, 8'd3} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R1_CFG_3, fc_dly );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R1_CFG_3, fc_dly );
                end
                {RANK1, 8'd4} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R1_CFG_4, fc_dly );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R1_CFG_4, fc_dly );
                end
                {RANK1, 8'd5} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R1_CFG_5, fc_dly );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R1_CFG_5, fc_dly );
                end
                {RANK1, 8'd6} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R1_CFG_6, fc_dly );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R1_CFG_6, fc_dly );
                end
                {RANK1, 8'd7} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R1_CFG_7, fc_dly );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R1_CFG_7, fc_dly );
                end
                {RANK1, 8'd8} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R1_CFG_8, fc_dly );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R1_CFG_8, fc_dly );
                end
                {RANK_ALL, 8'd0} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R0_CFG_0, fc_dly );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R0_CFG_0, fc_dly );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R1_CFG_0, fc_dly );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R1_CFG_0, fc_dly );
                end
                {RANK_ALL, 8'd1} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R0_CFG_1, fc_dly );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R0_CFG_1, fc_dly );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R1_CFG_1, fc_dly );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R1_CFG_1, fc_dly );
                end
                {RANK_ALL, 8'd2} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R0_CFG_2, fc_dly );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R0_CFG_2, fc_dly );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R1_CFG_2, fc_dly );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R1_CFG_2, fc_dly );
                end
                {RANK_ALL, 8'd3} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R0_CFG_3, fc_dly );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R0_CFG_3, fc_dly );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R1_CFG_3, fc_dly );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R1_CFG_3, fc_dly );
                end
                {RANK_ALL, 8'd4} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R0_CFG_4, fc_dly );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R0_CFG_4, fc_dly );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R1_CFG_4, fc_dly );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R1_CFG_4, fc_dly );
                end
                {RANK_ALL, 8'd5} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R0_CFG_5, fc_dly );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R0_CFG_5, fc_dly );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R1_CFG_5, fc_dly );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R1_CFG_5, fc_dly );
                end
                {RANK_ALL, 8'd6} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R0_CFG_6, fc_dly );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R0_CFG_6, fc_dly );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R1_CFG_6, fc_dly );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R1_CFG_6, fc_dly );
                end
                {RANK_ALL, 8'd7} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R0_CFG_7, fc_dly );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R0_CFG_7, fc_dly );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R1_CFG_7, fc_dly );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R1_CFG_7, fc_dly );
                end
                {RANK_ALL, 8'd8} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R0_CFG_8, fc_dly );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R0_CFG_8, fc_dly );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R1_CFG_8, fc_dly );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R1_CFG_8, fc_dly );
                end
                default: begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R0_CFG_0, fc_dly );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R0_CFG_0, fc_dly );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R0_CFG_1, fc_dly );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R0_CFG_1, fc_dly );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R0_CFG_2, fc_dly );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R0_CFG_2, fc_dly );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R0_CFG_3, fc_dly );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R0_CFG_3, fc_dly );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R0_CFG_4, fc_dly );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R0_CFG_4, fc_dly );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R0_CFG_5, fc_dly );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R0_CFG_5, fc_dly );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R0_CFG_6, fc_dly );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R0_CFG_6, fc_dly );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R0_CFG_7, fc_dly );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R0_CFG_7, fc_dly );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R0_CFG_8, fc_dly );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R0_CFG_8, fc_dly );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R1_CFG_0, fc_dly );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R1_CFG_0, fc_dly );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R1_CFG_1, fc_dly );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R1_CFG_1, fc_dly );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R1_CFG_2, fc_dly );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R1_CFG_2, fc_dly );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R1_CFG_3, fc_dly );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R1_CFG_3, fc_dly );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R1_CFG_4, fc_dly );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R1_CFG_4, fc_dly );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R1_CFG_5, fc_dly );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R1_CFG_5, fc_dly );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R1_CFG_6, fc_dly );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R1_CFG_6, fc_dly );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R1_CFG_7, fc_dly );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R1_CFG_7, fc_dly );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R1_CFG_8, fc_dly );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_FC_DLY_M0_R1_CFG_8, fc_dly );
                end
            endcase
        end
        if((byte_sel == CA) || (byte_sel == ALL)) begin
            case ({rank_sel,dqs})
                {RANK0, 8'd0} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQS_TX_SDR_FC_DLY_M0_R0_CFG_0, fc_dly );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQS_TX_SDR_FC_DLY_M0_R0_CFG_0, fc_dly );
                end
                {RANK1, 8'd0} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQS_TX_SDR_FC_DLY_M0_R1_CFG_0, fc_dly );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQS_TX_SDR_FC_DLY_M0_R1_CFG_0, fc_dly );
                end
                {RANK_ALL, 8'd0} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQS_TX_SDR_FC_DLY_M0_R0_CFG_0, fc_dly );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQS_TX_SDR_FC_DLY_M0_R0_CFG_0, fc_dly );
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQS_TX_SDR_FC_DLY_M0_R1_CFG_0, fc_dly );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQS_TX_SDR_FC_DLY_M0_R1_CFG_0, fc_dly );
                end
                default: begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQS_TX_SDR_FC_DLY_M0_R0_CFG_0, fc_dly );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQS_TX_SDR_FC_DLY_M0_R0_CFG_0, fc_dly );
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQS_TX_SDR_FC_DLY_M0_R1_CFG_0, fc_dly );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQS_TX_SDR_FC_DLY_M0_R1_CFG_0, fc_dly );
                end
            endcase
        end
    end
endtask

task automatic set_txdqs_rt_pipe_en;
    input byte_sel_t     byte_sel;
    input rank_sel_t     rank_sel;
    input logic   [31:0] pipe_en;
    begin
        if((byte_sel == DQ0) || (byte_sel == DQ_ALL) || (byte_sel == ALL)) begin
            case ({rank_sel})
                {RANK0} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_RT_M0_R0_CFG, pipe_en );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_RT_M0_R0_CFG, pipe_en );
                end
                {RANK1} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_RT_M0_R1_CFG, pipe_en );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_RT_M0_R1_CFG, pipe_en );
                end
                default: begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_RT_M0_R0_CFG, pipe_en );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_RT_M0_R1_CFG, pipe_en );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_RT_M0_R0_CFG, pipe_en );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_RT_M0_R1_CFG, pipe_en );
                end
            endcase
        end
        if((byte_sel == DQ1) || (byte_sel == DQ_ALL) || (byte_sel == ALL)) begin
            case ({rank_sel})
                {RANK0} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_RT_M0_R0_CFG, pipe_en );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_RT_M0_R0_CFG, pipe_en );
                end
                {RANK1} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_RT_M0_R1_CFG, pipe_en );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_RT_M0_R1_CFG, pipe_en );
                end
                default: begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_RT_M0_R0_CFG, pipe_en );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_RT_M0_R1_CFG, pipe_en );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_RT_M0_R0_CFG, pipe_en );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_RT_M0_R1_CFG, pipe_en );
                end
            endcase
        end
        if((byte_sel == CA) || (byte_sel == ALL)) begin
            case ({rank_sel})
                {RANK0} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQS_TX_RT_M0_R0_CFG, pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQS_TX_RT_M0_R0_CFG, pipe_en);
                end
                {RANK1} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQS_TX_RT_M0_R1_CFG, pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQS_TX_RT_M0_R1_CFG, pipe_en);
                end
                default: begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQS_TX_RT_M0_R0_CFG, pipe_en );
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQS_TX_RT_M0_R1_CFG, pipe_en );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQS_TX_RT_M0_R0_CFG, pipe_en );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQS_TX_RT_M0_R1_CFG, pipe_en );
                end
            endcase
        end
    end
endtask

task automatic set_txdqs_sdr_x_sel;
    input byte_sel_t     byte_sel;
    input rank_sel_t     rank_sel;
    input logic    [7:0] dqs;
    input logic   [31:0] x_sel;
    begin
        if((byte_sel == DQ0) || (byte_sel == DQ_ALL) || (byte_sel == ALL)) begin
            case ({rank_sel,dqs})
                {RANK0, 8'd0} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R0_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R0_CFG_0 , x_sel  );
                end
                {RANK0, 8'd1} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R0_CFG_1 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R0_CFG_1 , x_sel  );
                end
                {RANK0, 8'd2} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R0_CFG_2 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R0_CFG_2 , x_sel  );
                end
                {RANK0, 8'd3} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R0_CFG_3 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R0_CFG_3 , x_sel  );
                end
                {RANK0, 8'd4} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R0_CFG_4 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R0_CFG_4 , x_sel  );
                end
                {RANK0, 8'd5} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R0_CFG_5 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R0_CFG_5 , x_sel  );
                end
                {RANK0, 8'd6} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R0_CFG_6 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R0_CFG_6 , x_sel  );
                end
                {RANK0, 8'd7} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R0_CFG_7 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R0_CFG_7 , x_sel  );
                end
                {RANK0, 8'd8} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R0_CFG_8 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R0_CFG_8 , x_sel  );
                end
                {RANK1, 8'd0} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R1_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R1_CFG_0 , x_sel  );
                end
                {RANK1, 8'd1} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R1_CFG_1 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R1_CFG_1 , x_sel  );
                end
                {RANK1, 8'd2} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R1_CFG_2 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R1_CFG_2 , x_sel  );
                end
                {RANK1, 8'd3} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R1_CFG_3 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R1_CFG_3 , x_sel  );
                end
                {RANK1, 8'd4} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R1_CFG_4 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R1_CFG_4 , x_sel  );
                end
                {RANK1, 8'd5} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R1_CFG_5 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R1_CFG_5 , x_sel  );
                end
                {RANK1, 8'd6} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R1_CFG_6 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R1_CFG_6 , x_sel  );
                end
                {RANK1, 8'd7} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R1_CFG_7 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R1_CFG_7 , x_sel  );
                end
                {RANK1, 8'd8} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R1_CFG_8 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R1_CFG_8 , x_sel  );
                end
                {RANK_ALL, 8'd0} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R0_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R0_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R1_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R1_CFG_0 , x_sel  );
                end
                {RANK_ALL, 8'd1} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R0_CFG_1 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R0_CFG_1 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R1_CFG_1 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R1_CFG_1 , x_sel  );
                end
                {RANK_ALL, 8'd2} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R0_CFG_2 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R0_CFG_2 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R1_CFG_2 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R1_CFG_2 , x_sel  );
                end
                {RANK_ALL, 8'd3} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R0_CFG_3 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R0_CFG_3 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R1_CFG_3 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R1_CFG_3 , x_sel  );
                end
                {RANK_ALL, 8'd4} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R0_CFG_4 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R0_CFG_4 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R1_CFG_4 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R1_CFG_4 , x_sel  );
                end
                {RANK_ALL, 8'd5} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R0_CFG_5 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R0_CFG_5 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R1_CFG_5 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R1_CFG_5 , x_sel  );
                end
                {RANK_ALL, 8'd6} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R0_CFG_6 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R0_CFG_6 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R1_CFG_6 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R1_CFG_6 , x_sel  );
                end
                {RANK_ALL, 8'd7} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R0_CFG_7 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R0_CFG_7 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R1_CFG_7 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R1_CFG_7 , x_sel  );
                end
                {RANK_ALL, 8'd8} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R0_CFG_8 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R0_CFG_8 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R1_CFG_8 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R1_CFG_8 , x_sel  );
                end
                default: begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R0_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R0_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R0_CFG_1 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R0_CFG_1 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R0_CFG_2 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R0_CFG_2 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R0_CFG_3 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R0_CFG_3 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R0_CFG_4 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R0_CFG_4 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R0_CFG_5 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R0_CFG_5 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R0_CFG_6 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R0_CFG_6 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R0_CFG_7 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R0_CFG_7 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R0_CFG_8 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R0_CFG_8 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R1_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R1_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R1_CFG_1 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R1_CFG_1 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R1_CFG_2 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R1_CFG_2 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R1_CFG_3 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R1_CFG_3 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R1_CFG_4 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R1_CFG_4 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R1_CFG_5 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R1_CFG_5 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R1_CFG_6 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R1_CFG_6 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R1_CFG_7 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R1_CFG_7 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R1_CFG_8 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R1_CFG_8 , x_sel  );
                end
            endcase
        end
        if((byte_sel == DQ1) || (byte_sel == DQ_ALL) || (byte_sel == ALL)) begin
            case ({rank_sel,dqs})
                {RANK0, 8'd0} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R0_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R0_CFG_0 , x_sel  );
                end
                {RANK0, 8'd1} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R0_CFG_1 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R0_CFG_1 , x_sel  );
                end
                {RANK0, 8'd2} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R0_CFG_2 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R0_CFG_2 , x_sel  );
                end
                {RANK0, 8'd3} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R0_CFG_3 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R0_CFG_3 , x_sel  );
                end
                {RANK0, 8'd4} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R0_CFG_4 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R0_CFG_4 , x_sel  );
                end
                {RANK0, 8'd5} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R0_CFG_5 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R0_CFG_5 , x_sel  );
                end
                {RANK0, 8'd6} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R0_CFG_6 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R0_CFG_6 , x_sel  );
                end
                {RANK0, 8'd7} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R0_CFG_7 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R0_CFG_7 , x_sel  );
                end
                {RANK0, 8'd8} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R0_CFG_8 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R0_CFG_8 , x_sel  );
                end
                {RANK1, 8'd0} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R1_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R1_CFG_0 , x_sel  );
                end
                {RANK1, 8'd1} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R1_CFG_1 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R1_CFG_1 , x_sel  );
                end
                {RANK1, 8'd2} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R1_CFG_2 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R1_CFG_2 , x_sel  );
                end
                {RANK1, 8'd3} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R1_CFG_3 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R1_CFG_3 , x_sel  );
                end
                {RANK1, 8'd4} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R1_CFG_4 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R1_CFG_4 , x_sel  );
                end
                {RANK1, 8'd5} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R1_CFG_5 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R1_CFG_5 , x_sel  );
                end
                {RANK1, 8'd6} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R1_CFG_6 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R1_CFG_6 , x_sel  );
                end
                {RANK1, 8'd7} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R1_CFG_7 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R1_CFG_7 , x_sel  );
                end
                {RANK1, 8'd8} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R1_CFG_8 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R1_CFG_8 , x_sel  );
                end
                {RANK_ALL, 8'd0} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R0_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R0_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R1_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R1_CFG_0 , x_sel  );
                end
                {RANK_ALL, 8'd1} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R0_CFG_1 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R0_CFG_1 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R1_CFG_1 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R1_CFG_1 , x_sel  );
                end
                {RANK_ALL, 8'd2} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R0_CFG_2 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R0_CFG_2 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R1_CFG_2 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R1_CFG_2 , x_sel  );
                end
                {RANK_ALL, 8'd3} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R0_CFG_3 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R0_CFG_3 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R1_CFG_3 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R1_CFG_3 , x_sel  );
                end
                {RANK_ALL, 8'd4} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R0_CFG_4 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R0_CFG_4 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R1_CFG_4 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R1_CFG_4 , x_sel  );
                end
                {RANK_ALL, 8'd5} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R0_CFG_5 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R0_CFG_5 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R1_CFG_5 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R1_CFG_5 , x_sel  );
                end
                {RANK_ALL, 8'd6} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R0_CFG_6 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R0_CFG_6 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R1_CFG_6 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R1_CFG_6 , x_sel  );
                end
                {RANK_ALL, 8'd7} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R0_CFG_7 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R0_CFG_7 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R1_CFG_7 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R1_CFG_7 , x_sel  );
                end
                {RANK_ALL, 8'd8} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R0_CFG_8 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R0_CFG_8 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R1_CFG_8 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R1_CFG_8 , x_sel  );
                end
                default: begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R0_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R0_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R0_CFG_1 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R0_CFG_1 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R0_CFG_2 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R0_CFG_2 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R0_CFG_3 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R0_CFG_3 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R0_CFG_4 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R0_CFG_4 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R0_CFG_5 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R0_CFG_5 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R0_CFG_6 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R0_CFG_6 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R0_CFG_7 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R0_CFG_7 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R0_CFG_8 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R0_CFG_8 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R1_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R1_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R1_CFG_1 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R1_CFG_1 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R1_CFG_2 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R1_CFG_2 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R1_CFG_3 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R1_CFG_3 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R1_CFG_4 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R1_CFG_4 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R1_CFG_5 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R1_CFG_5 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R1_CFG_6 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R1_CFG_6 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R1_CFG_7 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R1_CFG_7 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R1_CFG_8 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_X_SEL_M0_R1_CFG_8 , x_sel  );
                end
            endcase
        end
        if((byte_sel == CA) || (byte_sel == ALL)) begin
            case ({rank_sel,dqs})
                {RANK0, 8'd0} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQS_TX_SDR_X_SEL_M0_R0_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQS_TX_SDR_X_SEL_M0_R0_CFG_0 , x_sel  );
                end
                {RANK1, 8'd0} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQS_TX_SDR_X_SEL_M0_R1_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQS_TX_SDR_X_SEL_M0_R1_CFG_0 , x_sel  );
                end
                {RANK_ALL, 8'd0} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQS_TX_SDR_X_SEL_M0_R0_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQS_TX_SDR_X_SEL_M0_R0_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQS_TX_SDR_X_SEL_M0_R1_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQS_TX_SDR_X_SEL_M0_R1_CFG_0 , x_sel  );
                end
                default: begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQS_TX_SDR_X_SEL_M0_R0_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQS_TX_SDR_X_SEL_M0_R0_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQS_TX_SDR_X_SEL_M0_R1_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQS_TX_SDR_X_SEL_M0_R1_CFG_0 , x_sel  );
                end
            endcase
        end
    end
endtask

task automatic set_txdqs_sdr_pipe_en ;
    input byte_sel_t     byte_sel;
    input rank_sel_t     rank_sel;
    input logic    [7:0] dqs;
    input logic   [31:0] pipe_en;
    begin
        if((byte_sel == DQ0) || (byte_sel == DQ_ALL) || (byte_sel == ALL)) begin
            case ({rank_sel,dqs})
                {RANK0, 8'd0} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_M0_R0_CFG_0       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_M0_R0_CFG_0       , pipe_en);
                end
                {RANK0, 8'd1} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_M0_R0_CFG_1       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_M0_R0_CFG_1       , pipe_en);
                end
                {RANK0, 8'd2} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_M0_R0_CFG_2       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_M0_R0_CFG_2       , pipe_en);
                end
                {RANK0, 8'd3} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_M0_R0_CFG_3       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_M0_R0_CFG_3       , pipe_en);
                end
                {RANK0, 8'd4} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_M0_R0_CFG_4       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_M0_R0_CFG_4       , pipe_en);
                end
                {RANK0, 8'd5} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_M0_R0_CFG_5       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_M0_R0_CFG_5       , pipe_en);
                end
                {RANK0, 8'd6} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_M0_R0_CFG_6       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_M0_R0_CFG_6       , pipe_en);
                end
                {RANK0, 8'd7} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_M0_R0_CFG_7       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_M0_R0_CFG_7       , pipe_en);
                end
                {RANK0, 8'd8} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_M0_R0_CFG_8       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_M0_R0_CFG_8       , pipe_en);
                end
                {RANK1, 8'd0} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_M0_R1_CFG_0       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_M0_R1_CFG_0       , pipe_en);
                end
                {RANK1, 8'd1} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_M0_R1_CFG_1       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_M0_R1_CFG_1       , pipe_en);
                end
                {RANK1, 8'd2} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_M0_R1_CFG_2       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_M0_R1_CFG_2       , pipe_en);
                end
                {RANK1, 8'd3} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_M0_R1_CFG_3       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_M0_R1_CFG_3       , pipe_en);
                end
                {RANK1, 8'd4} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_M0_R1_CFG_4       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_M0_R1_CFG_4       , pipe_en);
                end
                {RANK1, 8'd5} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_M0_R1_CFG_5       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_M0_R1_CFG_5       , pipe_en);
                end
                {RANK1, 8'd6} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_M0_R1_CFG_6       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_M0_R1_CFG_6       , pipe_en);
                end
                {RANK1, 8'd7} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_M0_R1_CFG_7       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_M0_R1_CFG_7       , pipe_en);
                end
                {RANK1, 8'd8} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_M0_R1_CFG_8       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_M0_R1_CFG_8       , pipe_en);
                end
                default: begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_M0_R0_CFG_0       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_M0_R0_CFG_0       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_M0_R0_CFG_1       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_M0_R0_CFG_1       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_M0_R0_CFG_2       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_M0_R0_CFG_2       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_M0_R0_CFG_3       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_M0_R0_CFG_3       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_M0_R0_CFG_4       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_M0_R0_CFG_4       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_M0_R0_CFG_5       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_M0_R0_CFG_5       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_M0_R0_CFG_6       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_M0_R0_CFG_6       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_M0_R0_CFG_7       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_M0_R0_CFG_7       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_M0_R0_CFG_8       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_M0_R0_CFG_8       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_M0_R1_CFG_0       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_M0_R1_CFG_0       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_M0_R1_CFG_1       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_M0_R1_CFG_1       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_M0_R1_CFG_2       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_M0_R1_CFG_2       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_M0_R1_CFG_3       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_M0_R1_CFG_3       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_M0_R1_CFG_4       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_M0_R1_CFG_4       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_M0_R1_CFG_5       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_M0_R1_CFG_5       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_M0_R1_CFG_6       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_M0_R1_CFG_6       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_M0_R1_CFG_7       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_M0_R1_CFG_7       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_M0_R1_CFG_8       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_SDR_M0_R1_CFG_8       , pipe_en);
                end
            endcase
        end
        if((byte_sel == DQ1) || (byte_sel == DQ_ALL) || (byte_sel == ALL)) begin
            case ({rank_sel,dqs})
                {RANK0, 8'd0} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_M0_R0_CFG_0       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_M0_R0_CFG_0       , pipe_en);
                end
                {RANK0, 8'd1} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_M0_R0_CFG_1       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_M0_R0_CFG_1       , pipe_en);
                end
                {RANK0, 8'd2} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_M0_R0_CFG_2       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_M0_R0_CFG_2       , pipe_en);
                end
                {RANK0, 8'd3} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_M0_R0_CFG_3       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_M0_R0_CFG_3       , pipe_en);
                end
                {RANK0, 8'd4} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_M0_R0_CFG_4       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_M0_R0_CFG_4       , pipe_en);
                end
                {RANK0, 8'd5} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_M0_R0_CFG_5       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_M0_R0_CFG_5       , pipe_en);
                end
                {RANK0, 8'd6} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_M0_R0_CFG_6       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_M0_R0_CFG_6       , pipe_en);
                end
                {RANK0, 8'd7} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_M0_R0_CFG_7       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_M0_R0_CFG_7       , pipe_en);
                end
                {RANK0, 8'd8} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_M0_R0_CFG_8       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_M0_R0_CFG_8       , pipe_en);
                end
                {RANK1, 8'd0} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_M0_R1_CFG_0       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_M0_R1_CFG_0       , pipe_en);
                end
                {RANK1, 8'd1} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_M0_R1_CFG_1       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_M0_R1_CFG_1       , pipe_en);
                end
                {RANK1, 8'd2} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_M0_R1_CFG_2       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_M0_R1_CFG_2       , pipe_en);
                end
                {RANK1, 8'd3} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_M0_R1_CFG_3       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_M0_R1_CFG_3       , pipe_en);
                end
                {RANK1, 8'd4} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_M0_R1_CFG_4       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_M0_R1_CFG_4       , pipe_en);
                end
                {RANK1, 8'd5} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_M0_R1_CFG_5       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_M0_R1_CFG_5       , pipe_en);
                end
                {RANK1, 8'd6} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_M0_R1_CFG_6       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_M0_R1_CFG_6       , pipe_en);
                end
                {RANK1, 8'd7} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_M0_R1_CFG_7       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_M0_R1_CFG_7       , pipe_en);
                end
                {RANK1, 8'd8} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_M0_R1_CFG_8       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_M0_R1_CFG_8       , pipe_en);
                end
                default: begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_M0_R0_CFG_0       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_M0_R0_CFG_0       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_M0_R0_CFG_1       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_M0_R0_CFG_1       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_M0_R0_CFG_2       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_M0_R0_CFG_2       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_M0_R0_CFG_3       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_M0_R0_CFG_3       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_M0_R0_CFG_4       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_M0_R0_CFG_4       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_M0_R0_CFG_5       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_M0_R0_CFG_5       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_M0_R0_CFG_6       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_M0_R0_CFG_6       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_M0_R0_CFG_7       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_M0_R0_CFG_7       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_M0_R0_CFG_8       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_M0_R0_CFG_8       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_M0_R1_CFG_0       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_M0_R1_CFG_0       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_M0_R1_CFG_1       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_M0_R1_CFG_1       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_M0_R1_CFG_2       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_M0_R1_CFG_2       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_M0_R1_CFG_3       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_M0_R1_CFG_3       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_M0_R1_CFG_4       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_M0_R1_CFG_4       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_M0_R1_CFG_5       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_M0_R1_CFG_5       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_M0_R1_CFG_6       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_M0_R1_CFG_6       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_M0_R1_CFG_7       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_M0_R1_CFG_7       , pipe_en);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_M0_R1_CFG_8       , pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_SDR_M0_R1_CFG_8       , pipe_en);
                end
            endcase
        end
        if((byte_sel == CA) || (byte_sel == ALL)) begin
            case ({rank_sel,dqs})
                {RANK0, 8'd0} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQS_TX_SDR_M0_R0_CFG_0       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQS_TX_SDR_M0_R0_CFG_0       , pipe_en);
                end
                {RANK1, 8'd0} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQS_TX_SDR_M0_R1_CFG_0       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQS_TX_SDR_M0_R1_CFG_0       , pipe_en);
                end
                default: begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQS_TX_SDR_M0_R0_CFG_0       , pipe_en);
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQS_TX_SDR_M0_R1_CFG_0       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQS_TX_SDR_M0_R0_CFG_0       , pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQS_TX_SDR_M0_R1_CFG_0       , pipe_en);
                end
            endcase
        end
    end
endtask

task automatic set_txdqs_ddr_x_sel;
    input byte_sel_t     byte_sel;
    input rank_sel_t     rank_sel;
    input logic    [7:0] dqs;
    input logic   [31:0] x_sel;
    begin
        if((byte_sel == DQ0) || (byte_sel == DQ_ALL) || (byte_sel == ALL)) begin
            case ({rank_sel,dqs})
                {RANK0, 8'd0} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M0_R0_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M0_R0_CFG_0 , x_sel  );
                end
                {RANK0, 8'd1} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M0_R0_CFG_1 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M0_R0_CFG_1 , x_sel  );
                end
                {RANK0, 8'd2} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M0_R0_CFG_2 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M0_R0_CFG_2 , x_sel  );
                end
                {RANK0, 8'd3} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M0_R0_CFG_3 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M0_R0_CFG_3 , x_sel  );
                end
                {RANK0, 8'd4} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M0_R0_CFG_4 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M0_R0_CFG_4 , x_sel  );
                end
                {RANK0, 8'd5} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M0_R0_CFG_5 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M0_R0_CFG_5 , x_sel  );
                end
                {RANK0, 8'd6} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M0_R0_CFG_6 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M0_R0_CFG_6 , x_sel  );
                end
                {RANK0, 8'd7} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M0_R0_CFG_7 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M0_R0_CFG_7 , x_sel  );
                end
                {RANK0, 8'd8} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M0_R0_CFG_8 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M0_R0_CFG_8 , x_sel  );
                end
                {RANK1, 8'd0} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M0_R1_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M0_R1_CFG_0 , x_sel  );
                end
                {RANK1, 8'd1} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M0_R1_CFG_1 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M0_R1_CFG_1 , x_sel  );
                end
                {RANK1, 8'd2} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M0_R1_CFG_2 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M0_R1_CFG_2 , x_sel  );
                end
                {RANK1, 8'd3} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M0_R1_CFG_3 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M0_R1_CFG_3 , x_sel  );
                end
                {RANK1, 8'd4} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M0_R1_CFG_4 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M0_R1_CFG_4 , x_sel  );
                end
                {RANK1, 8'd5} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M0_R1_CFG_5 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M0_R1_CFG_5 , x_sel  );
                end
                {RANK1, 8'd6} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M0_R1_CFG_6 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M0_R1_CFG_6 , x_sel  );
                end
                {RANK1, 8'd7} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M0_R1_CFG_7 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M0_R1_CFG_7 , x_sel  );
                end
                {RANK1, 8'd8} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M0_R1_CFG_8 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M0_R1_CFG_8 , x_sel  );
                end
                default: begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M0_R0_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M0_R0_CFG_1 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M0_R0_CFG_2 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M0_R0_CFG_3 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M0_R0_CFG_4 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M0_R0_CFG_5 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M0_R0_CFG_6 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M0_R0_CFG_7 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M0_R0_CFG_8 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M0_R1_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M0_R1_CFG_1 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M0_R1_CFG_2 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M0_R1_CFG_3 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M0_R1_CFG_4 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M0_R1_CFG_5 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M0_R1_CFG_6 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M0_R1_CFG_7 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M0_R1_CFG_8 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M0_R0_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M0_R0_CFG_1 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M0_R0_CFG_2 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M0_R0_CFG_3 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M0_R0_CFG_4 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M0_R0_CFG_5 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M0_R0_CFG_6 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M0_R0_CFG_7 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M0_R0_CFG_8 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M0_R1_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M0_R1_CFG_1 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M0_R1_CFG_2 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M0_R1_CFG_3 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M0_R1_CFG_4 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M0_R1_CFG_5 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M0_R1_CFG_6 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M0_R1_CFG_7 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M0_R1_CFG_8 , x_sel  );
                end
            endcase
        end
        if((byte_sel == DQ1) || (byte_sel == DQ_ALL) || (byte_sel == ALL)) begin
            case ({rank_sel,dqs})
                {RANK0, 8'd0} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M0_R0_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M0_R0_CFG_0 , x_sel  );
                end
                {RANK0, 8'd1} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M0_R0_CFG_1 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M0_R0_CFG_1 , x_sel  );
                end
                {RANK0, 8'd2} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M0_R0_CFG_2 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M0_R0_CFG_2 , x_sel  );
                end
                {RANK0, 8'd3} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M0_R0_CFG_3 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M0_R0_CFG_3 , x_sel  );
                end
                {RANK0, 8'd4} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M0_R0_CFG_4 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M0_R0_CFG_4 , x_sel  );
                end
                {RANK0, 8'd5} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M0_R0_CFG_5 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M0_R0_CFG_5 , x_sel  );
                end
                {RANK0, 8'd6} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M0_R0_CFG_6 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M0_R0_CFG_6 , x_sel  );
                end
                {RANK0, 8'd7} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M0_R0_CFG_7 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M0_R0_CFG_7 , x_sel  );
                end
                {RANK0, 8'd8} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M0_R0_CFG_8 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M0_R0_CFG_8 , x_sel  );
                end
                {RANK1, 8'd0} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M0_R1_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M0_R1_CFG_0 , x_sel  );
                end
                {RANK1, 8'd1} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M0_R1_CFG_1 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M0_R1_CFG_1 , x_sel  );
                end
                {RANK1, 8'd2} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M0_R1_CFG_2 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M0_R1_CFG_2 , x_sel  );
                end
                {RANK1, 8'd3} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M0_R1_CFG_3 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M0_R1_CFG_3 , x_sel  );
                end
                {RANK1, 8'd4} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M0_R1_CFG_4 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M0_R1_CFG_4 , x_sel  );
                end
                {RANK1, 8'd5} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M0_R1_CFG_5 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M0_R1_CFG_5 , x_sel  );
                end
                {RANK1, 8'd6} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M0_R1_CFG_6 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M0_R1_CFG_6 , x_sel  );
                end
                {RANK1, 8'd7} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M0_R1_CFG_7 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M0_R1_CFG_7 , x_sel  );
                end
                {RANK1, 8'd8} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M0_R1_CFG_8 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M0_R1_CFG_8 , x_sel  );
                end
                default: begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M0_R0_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M0_R0_CFG_1 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M0_R0_CFG_2 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M0_R0_CFG_3 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M0_R0_CFG_4 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M0_R0_CFG_5 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M0_R0_CFG_6 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M0_R0_CFG_7 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M0_R0_CFG_8 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M0_R1_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M0_R1_CFG_1 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M0_R1_CFG_2 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M0_R1_CFG_3 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M0_R1_CFG_4 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M0_R1_CFG_5 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M0_R1_CFG_6 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M0_R1_CFG_7 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M0_R1_CFG_8 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M0_R0_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M0_R0_CFG_1 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M0_R0_CFG_2 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M0_R0_CFG_3 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M0_R0_CFG_4 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M0_R0_CFG_5 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M0_R0_CFG_6 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M0_R0_CFG_7 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M0_R0_CFG_8 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M0_R1_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M0_R1_CFG_1 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M0_R1_CFG_2 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M0_R1_CFG_3 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M0_R1_CFG_4 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M0_R1_CFG_5 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M0_R1_CFG_6 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M0_R1_CFG_7 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_DDR_X_SEL_M0_R1_CFG_8 , x_sel  );
                end
            endcase
        end
        if((byte_sel == CA) || (byte_sel == ALL)) begin
            case ({rank_sel,dqs})
                {RANK0, 8'd0} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQS_TX_DDR_X_SEL_M0_R0_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQS_TX_DDR_X_SEL_M0_R0_CFG_0 , x_sel  );
                end
                {RANK1, 8'd0} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQS_TX_DDR_X_SEL_M0_R1_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQS_TX_DDR_X_SEL_M0_R1_CFG_0 , x_sel  );
                end
                default: begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQS_TX_DDR_X_SEL_M0_R0_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQS_TX_DDR_X_SEL_M0_R1_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQS_TX_DDR_X_SEL_M0_R0_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQS_TX_DDR_X_SEL_M0_R1_CFG_0 , x_sel  );
                end
            endcase
        end
    end
endtask

task automatic set_txdqs_ddr_pipe_en;
    input byte_sel_t     byte_sel;
    input rank_sel_t     rank_sel;
    input logic    [7:0] dqs;
    input logic  [31:0]  pipe_en;
    begin
        if((byte_sel == DQ0) || (byte_sel == DQ_ALL) || (byte_sel == ALL)) begin
            case ({rank_sel,dqs})
                {RANK0, 8'd0} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET, DDR_DQ_DQS_TX_DDR_M0_R0_CFG_0, pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET, DDR_DQ_DQS_TX_DDR_M0_R0_CFG_0, pipe_en);
                end
                {RANK0, 8'd1} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET, DDR_DQ_DQS_TX_DDR_M0_R0_CFG_1, pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET, DDR_DQ_DQS_TX_DDR_M0_R0_CFG_1, pipe_en);
                end
                {RANK0, 8'd2} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET, DDR_DQ_DQS_TX_DDR_M0_R0_CFG_2, pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET, DDR_DQ_DQS_TX_DDR_M0_R0_CFG_2, pipe_en);
                end
                {RANK0, 8'd3} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET, DDR_DQ_DQS_TX_DDR_M0_R0_CFG_3, pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET, DDR_DQ_DQS_TX_DDR_M0_R0_CFG_3, pipe_en);
                end
                {RANK0, 8'd4} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET, DDR_DQ_DQS_TX_DDR_M0_R0_CFG_4, pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET, DDR_DQ_DQS_TX_DDR_M0_R0_CFG_4, pipe_en);
                end
                {RANK0, 8'd5} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET, DDR_DQ_DQS_TX_DDR_M0_R0_CFG_5, pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET, DDR_DQ_DQS_TX_DDR_M0_R0_CFG_5, pipe_en);
                end
                {RANK0, 8'd6} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET, DDR_DQ_DQS_TX_DDR_M0_R0_CFG_6, pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET, DDR_DQ_DQS_TX_DDR_M0_R0_CFG_6, pipe_en);
                end
                {RANK0, 8'd7} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET, DDR_DQ_DQS_TX_DDR_M0_R0_CFG_7, pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET, DDR_DQ_DQS_TX_DDR_M0_R0_CFG_7, pipe_en);
                end
                {RANK0, 8'd8} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET, DDR_DQ_DQS_TX_DDR_M0_R0_CFG_8, pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET, DDR_DQ_DQS_TX_DDR_M0_R0_CFG_8, pipe_en);
                end
                {RANK1, 8'd0} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET, DDR_DQ_DQS_TX_DDR_M0_R1_CFG_0, pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET, DDR_DQ_DQS_TX_DDR_M0_R1_CFG_0, pipe_en);
                end
                {RANK1, 8'd1} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET, DDR_DQ_DQS_TX_DDR_M0_R1_CFG_1, pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET, DDR_DQ_DQS_TX_DDR_M0_R1_CFG_1, pipe_en);
                end
                {RANK1, 8'd2} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET, DDR_DQ_DQS_TX_DDR_M0_R1_CFG_2, pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET, DDR_DQ_DQS_TX_DDR_M0_R1_CFG_2, pipe_en);
                end
                {RANK1, 8'd3} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET, DDR_DQ_DQS_TX_DDR_M0_R1_CFG_3, pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET, DDR_DQ_DQS_TX_DDR_M0_R1_CFG_3, pipe_en);
                end
                {RANK1, 8'd4} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET, DDR_DQ_DQS_TX_DDR_M0_R1_CFG_4, pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET, DDR_DQ_DQS_TX_DDR_M0_R1_CFG_4, pipe_en);
                end
                {RANK1, 8'd5} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET, DDR_DQ_DQS_TX_DDR_M0_R1_CFG_5, pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET, DDR_DQ_DQS_TX_DDR_M0_R1_CFG_5, pipe_en);
                end
                {RANK1, 8'd6} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET, DDR_DQ_DQS_TX_DDR_M0_R1_CFG_6, pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET, DDR_DQ_DQS_TX_DDR_M0_R1_CFG_6, pipe_en);
                end
                {RANK1, 8'd7} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET, DDR_DQ_DQS_TX_DDR_M0_R1_CFG_7, pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET, DDR_DQ_DQS_TX_DDR_M0_R1_CFG_7, pipe_en);
                end
                {RANK1, 8'd8} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET, DDR_DQ_DQS_TX_DDR_M0_R1_CFG_8, pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET, DDR_DQ_DQS_TX_DDR_M0_R1_CFG_8, pipe_en);
                end
                default: begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET, DDR_DQ_DQS_TX_DDR_M0_R0_CFG_0, pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET, DDR_DQ_DQS_TX_DDR_M0_R0_CFG_0, pipe_en);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET, DDR_DQ_DQS_TX_DDR_M0_R0_CFG_1, pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET, DDR_DQ_DQS_TX_DDR_M0_R0_CFG_1, pipe_en);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET, DDR_DQ_DQS_TX_DDR_M0_R0_CFG_2, pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET, DDR_DQ_DQS_TX_DDR_M0_R0_CFG_2, pipe_en);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET, DDR_DQ_DQS_TX_DDR_M0_R0_CFG_3, pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET, DDR_DQ_DQS_TX_DDR_M0_R0_CFG_3, pipe_en);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET, DDR_DQ_DQS_TX_DDR_M0_R0_CFG_4, pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET, DDR_DQ_DQS_TX_DDR_M0_R0_CFG_4, pipe_en);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET, DDR_DQ_DQS_TX_DDR_M0_R0_CFG_5, pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET, DDR_DQ_DQS_TX_DDR_M0_R0_CFG_5, pipe_en);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET, DDR_DQ_DQS_TX_DDR_M0_R0_CFG_6, pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET, DDR_DQ_DQS_TX_DDR_M0_R0_CFG_6, pipe_en);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET, DDR_DQ_DQS_TX_DDR_M0_R0_CFG_7, pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET, DDR_DQ_DQS_TX_DDR_M0_R0_CFG_7, pipe_en);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET, DDR_DQ_DQS_TX_DDR_M0_R0_CFG_8, pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET, DDR_DQ_DQS_TX_DDR_M0_R0_CFG_8, pipe_en);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET, DDR_DQ_DQS_TX_DDR_M0_R1_CFG_0, pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET, DDR_DQ_DQS_TX_DDR_M0_R1_CFG_0, pipe_en);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET, DDR_DQ_DQS_TX_DDR_M0_R1_CFG_1, pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET, DDR_DQ_DQS_TX_DDR_M0_R1_CFG_1, pipe_en);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET, DDR_DQ_DQS_TX_DDR_M0_R1_CFG_2, pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET, DDR_DQ_DQS_TX_DDR_M0_R1_CFG_2, pipe_en);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET, DDR_DQ_DQS_TX_DDR_M0_R1_CFG_3, pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET, DDR_DQ_DQS_TX_DDR_M0_R1_CFG_3, pipe_en);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET, DDR_DQ_DQS_TX_DDR_M0_R1_CFG_4, pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET, DDR_DQ_DQS_TX_DDR_M0_R1_CFG_4, pipe_en);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET, DDR_DQ_DQS_TX_DDR_M0_R1_CFG_5, pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET, DDR_DQ_DQS_TX_DDR_M0_R1_CFG_5, pipe_en);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET, DDR_DQ_DQS_TX_DDR_M0_R1_CFG_6, pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET, DDR_DQ_DQS_TX_DDR_M0_R1_CFG_6, pipe_en);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET, DDR_DQ_DQS_TX_DDR_M0_R1_CFG_7, pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET, DDR_DQ_DQS_TX_DDR_M0_R1_CFG_7, pipe_en);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET, DDR_DQ_DQS_TX_DDR_M0_R1_CFG_8, pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET, DDR_DQ_DQS_TX_DDR_M0_R1_CFG_8, pipe_en);
                end
            endcase
        end
        if((byte_sel == DQ1) || (byte_sel == DQ_ALL) || (byte_sel == ALL)) begin
            case ({rank_sel,dqs})
                {RANK0, 8'd0} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET, DDR_DQ_DQS_TX_DDR_M0_R0_CFG_0, pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET, DDR_DQ_DQS_TX_DDR_M0_R0_CFG_0, pipe_en);
                end
                {RANK0, 8'd1} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET, DDR_DQ_DQS_TX_DDR_M0_R0_CFG_1, pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET, DDR_DQ_DQS_TX_DDR_M0_R0_CFG_1, pipe_en);
                end
                {RANK0, 8'd2} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET, DDR_DQ_DQS_TX_DDR_M0_R0_CFG_2, pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET, DDR_DQ_DQS_TX_DDR_M0_R0_CFG_2, pipe_en);
                end
                {RANK0, 8'd3} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET, DDR_DQ_DQS_TX_DDR_M0_R0_CFG_3, pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET, DDR_DQ_DQS_TX_DDR_M0_R0_CFG_3, pipe_en);
                end
                {RANK0, 8'd4} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET, DDR_DQ_DQS_TX_DDR_M0_R0_CFG_4, pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET, DDR_DQ_DQS_TX_DDR_M0_R0_CFG_4, pipe_en);
                end
                {RANK0, 8'd5} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET, DDR_DQ_DQS_TX_DDR_M0_R0_CFG_5, pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET, DDR_DQ_DQS_TX_DDR_M0_R0_CFG_5, pipe_en);
                end
                {RANK0, 8'd6} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET, DDR_DQ_DQS_TX_DDR_M0_R0_CFG_6, pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET, DDR_DQ_DQS_TX_DDR_M0_R0_CFG_6, pipe_en);
                end
                {RANK0, 8'd7} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET, DDR_DQ_DQS_TX_DDR_M0_R0_CFG_7, pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET, DDR_DQ_DQS_TX_DDR_M0_R0_CFG_7, pipe_en);
                end
                {RANK0, 8'd8} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET, DDR_DQ_DQS_TX_DDR_M0_R0_CFG_8, pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET, DDR_DQ_DQS_TX_DDR_M0_R0_CFG_8, pipe_en);
                end
                {RANK1, 8'd0} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET, DDR_DQ_DQS_TX_DDR_M0_R1_CFG_0, pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET, DDR_DQ_DQS_TX_DDR_M0_R1_CFG_0, pipe_en);
                end
                {RANK1, 8'd1} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET, DDR_DQ_DQS_TX_DDR_M0_R1_CFG_1, pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET, DDR_DQ_DQS_TX_DDR_M0_R1_CFG_1, pipe_en);
                end
                {RANK1, 8'd2} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET, DDR_DQ_DQS_TX_DDR_M0_R1_CFG_2, pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET, DDR_DQ_DQS_TX_DDR_M0_R1_CFG_2, pipe_en);
                end
                {RANK1, 8'd3} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET, DDR_DQ_DQS_TX_DDR_M0_R1_CFG_3, pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET, DDR_DQ_DQS_TX_DDR_M0_R1_CFG_3, pipe_en);
                end
                {RANK1, 8'd4} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET, DDR_DQ_DQS_TX_DDR_M0_R1_CFG_4, pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET, DDR_DQ_DQS_TX_DDR_M0_R1_CFG_4, pipe_en);
                end
                {RANK1, 8'd5} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET, DDR_DQ_DQS_TX_DDR_M0_R1_CFG_5, pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET, DDR_DQ_DQS_TX_DDR_M0_R1_CFG_5, pipe_en);
                end
                {RANK1, 8'd6} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET, DDR_DQ_DQS_TX_DDR_M0_R1_CFG_6, pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET, DDR_DQ_DQS_TX_DDR_M0_R1_CFG_6, pipe_en);
                end
                {RANK1, 8'd7} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET, DDR_DQ_DQS_TX_DDR_M0_R1_CFG_7, pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET, DDR_DQ_DQS_TX_DDR_M0_R1_CFG_7, pipe_en);
                end
                {RANK1, 8'd8} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET, DDR_DQ_DQS_TX_DDR_M0_R1_CFG_8, pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET, DDR_DQ_DQS_TX_DDR_M0_R1_CFG_8, pipe_en);
                end
                default: begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET, DDR_DQ_DQS_TX_DDR_M0_R0_CFG_0, pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET, DDR_DQ_DQS_TX_DDR_M0_R0_CFG_0, pipe_en);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET, DDR_DQ_DQS_TX_DDR_M0_R0_CFG_1, pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET, DDR_DQ_DQS_TX_DDR_M0_R0_CFG_1, pipe_en);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET, DDR_DQ_DQS_TX_DDR_M0_R0_CFG_2, pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET, DDR_DQ_DQS_TX_DDR_M0_R0_CFG_2, pipe_en);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET, DDR_DQ_DQS_TX_DDR_M0_R0_CFG_3, pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET, DDR_DQ_DQS_TX_DDR_M0_R0_CFG_3, pipe_en);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET, DDR_DQ_DQS_TX_DDR_M0_R0_CFG_4, pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET, DDR_DQ_DQS_TX_DDR_M0_R0_CFG_4, pipe_en);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET, DDR_DQ_DQS_TX_DDR_M0_R0_CFG_5, pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET, DDR_DQ_DQS_TX_DDR_M0_R0_CFG_5, pipe_en);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET, DDR_DQ_DQS_TX_DDR_M0_R0_CFG_6, pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET, DDR_DQ_DQS_TX_DDR_M0_R0_CFG_6, pipe_en);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET, DDR_DQ_DQS_TX_DDR_M0_R0_CFG_7, pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET, DDR_DQ_DQS_TX_DDR_M0_R0_CFG_7, pipe_en);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET, DDR_DQ_DQS_TX_DDR_M0_R0_CFG_8, pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET, DDR_DQ_DQS_TX_DDR_M0_R0_CFG_8, pipe_en);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET, DDR_DQ_DQS_TX_DDR_M0_R1_CFG_0, pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET, DDR_DQ_DQS_TX_DDR_M0_R1_CFG_0, pipe_en);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET, DDR_DQ_DQS_TX_DDR_M0_R1_CFG_1, pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET, DDR_DQ_DQS_TX_DDR_M0_R1_CFG_1, pipe_en);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET, DDR_DQ_DQS_TX_DDR_M0_R1_CFG_2, pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET, DDR_DQ_DQS_TX_DDR_M0_R1_CFG_2, pipe_en);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET, DDR_DQ_DQS_TX_DDR_M0_R1_CFG_3, pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET, DDR_DQ_DQS_TX_DDR_M0_R1_CFG_3, pipe_en);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET, DDR_DQ_DQS_TX_DDR_M0_R1_CFG_4, pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET, DDR_DQ_DQS_TX_DDR_M0_R1_CFG_4, pipe_en);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET, DDR_DQ_DQS_TX_DDR_M0_R1_CFG_5, pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET, DDR_DQ_DQS_TX_DDR_M0_R1_CFG_5, pipe_en);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET, DDR_DQ_DQS_TX_DDR_M0_R1_CFG_6, pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET, DDR_DQ_DQS_TX_DDR_M0_R1_CFG_6, pipe_en);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET, DDR_DQ_DQS_TX_DDR_M0_R1_CFG_7, pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET, DDR_DQ_DQS_TX_DDR_M0_R1_CFG_7, pipe_en);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET, DDR_DQ_DQS_TX_DDR_M0_R1_CFG_8, pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET, DDR_DQ_DQS_TX_DDR_M0_R1_CFG_8, pipe_en);
                end
            endcase
        end
        if((byte_sel == CA) || (byte_sel == ALL)) begin
            case ({rank_sel,dqs})
                {RANK0, 8'd0} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET, DDR_CA_DQS_TX_DDR_M0_R0_CFG_0, pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET, DDR_CA_DQS_TX_DDR_M0_R0_CFG_0, pipe_en);
                end
                {RANK1, 8'd0} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET, DDR_CA_DQS_TX_DDR_M0_R1_CFG_0, pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET, DDR_CA_DQS_TX_DDR_M0_R1_CFG_0, pipe_en);
                end
                default: begin
                    `CSR_WR(DDR_CH0_CA_OFFSET, DDR_CA_DQS_TX_DDR_M0_R0_CFG_0, pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET, DDR_CA_DQS_TX_DDR_M0_R0_CFG_0, pipe_en);
                    `CSR_WR(DDR_CH0_CA_OFFSET, DDR_CA_DQS_TX_DDR_M0_R1_CFG_0, pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET, DDR_CA_DQS_TX_DDR_M0_R1_CFG_0, pipe_en);
                end
            endcase
        end
    end
endtask

task automatic set_txdqs_qdr_x_sel;
    input byte_sel_t     byte_sel;
    input rank_sel_t     rank_sel;
    input logic    [7:0] dqs;
    input logic   [31:0] x_sel;
    begin
        if((byte_sel == DQ0) || (byte_sel == DQ_ALL) || (byte_sel == ALL)) begin
            case ({rank_sel,dqs})
                {RANK0, 8'd0} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M0_R0_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M0_R0_CFG_0 , x_sel  );
                end
                {RANK0, 8'd1} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M0_R0_CFG_1 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M0_R0_CFG_1 , x_sel  );
                end
                {RANK0, 8'd2} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M0_R0_CFG_2 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M0_R0_CFG_2 , x_sel  );
                end
                {RANK0, 8'd3} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M0_R0_CFG_3 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M0_R0_CFG_3 , x_sel  );
                end
                {RANK0, 8'd4} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M0_R0_CFG_4 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M0_R0_CFG_4 , x_sel  );
                end
                {RANK0, 8'd5} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M0_R0_CFG_5 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M0_R0_CFG_5 , x_sel  );
                end
                {RANK0, 8'd6} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M0_R0_CFG_6 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M0_R0_CFG_6 , x_sel  );
                end
                {RANK0, 8'd7} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M0_R0_CFG_7 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M0_R0_CFG_7 , x_sel  );
                end
                {RANK0, 8'd8} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M0_R0_CFG_8 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M0_R0_CFG_8 , x_sel  );
                end
                {RANK1, 8'd0} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M0_R1_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M0_R1_CFG_0 , x_sel  );
                end
                {RANK1, 8'd1} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M0_R1_CFG_1 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M0_R1_CFG_1 , x_sel  );
                end
                {RANK1, 8'd2} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M0_R1_CFG_2 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M0_R1_CFG_2 , x_sel  );
                end
                {RANK1, 8'd3} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M0_R1_CFG_3 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M0_R1_CFG_3 , x_sel  );
                end
                {RANK1, 8'd4} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M0_R1_CFG_4 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M0_R1_CFG_4 , x_sel  );
                end
                {RANK1, 8'd5} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M0_R1_CFG_5 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M0_R1_CFG_5 , x_sel  );
                end
                {RANK1, 8'd6} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M0_R1_CFG_6 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M0_R1_CFG_6 , x_sel  );
                end
                {RANK1, 8'd7} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M0_R1_CFG_7 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M0_R1_CFG_7 , x_sel  );
                end
                {RANK1, 8'd8} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M0_R1_CFG_8 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M0_R1_CFG_8 , x_sel  );
                end
                default: begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M0_R0_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M0_R0_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M0_R0_CFG_1 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M0_R0_CFG_1 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M0_R0_CFG_2 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M0_R0_CFG_2 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M0_R0_CFG_3 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M0_R0_CFG_3 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M0_R0_CFG_4 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M0_R0_CFG_4 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M0_R0_CFG_5 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M0_R0_CFG_5 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M0_R0_CFG_6 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M0_R0_CFG_6 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M0_R0_CFG_7 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M0_R0_CFG_7 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M0_R0_CFG_8 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M0_R0_CFG_8 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M0_R1_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M0_R1_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M0_R1_CFG_1 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M0_R1_CFG_1 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M0_R1_CFG_2 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M0_R1_CFG_2 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M0_R1_CFG_3 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M0_R1_CFG_3 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M0_R1_CFG_4 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M0_R1_CFG_4 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M0_R1_CFG_5 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M0_R1_CFG_5 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M0_R1_CFG_6 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M0_R1_CFG_6 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M0_R1_CFG_7 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M0_R1_CFG_7 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M0_R1_CFG_8 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M0_R1_CFG_8 , x_sel  );
                end
            endcase
        end
        if((byte_sel == DQ1) || (byte_sel == DQ_ALL) || (byte_sel == ALL)) begin
            case ({rank_sel,dqs})
                {RANK0, 8'd0} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M0_R0_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M0_R0_CFG_0 , x_sel  );
                end
                {RANK0, 8'd1} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M0_R0_CFG_1 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M0_R0_CFG_1 , x_sel  );
                end
                {RANK0, 8'd2} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M0_R0_CFG_2 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M0_R0_CFG_2 , x_sel  );
                end
                {RANK0, 8'd3} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M0_R0_CFG_3 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M0_R0_CFG_3 , x_sel  );
                end
                {RANK0, 8'd4} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M0_R0_CFG_4 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M0_R0_CFG_4 , x_sel  );
                end
                {RANK0, 8'd5} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M0_R0_CFG_5 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M0_R0_CFG_5 , x_sel  );
                end
                {RANK0, 8'd6} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M0_R0_CFG_6 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M0_R0_CFG_6 , x_sel  );
                end
                {RANK0, 8'd7} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M0_R0_CFG_7 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M0_R0_CFG_7 , x_sel  );
                end
                {RANK0, 8'd8} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M0_R0_CFG_8 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M0_R0_CFG_8 , x_sel  );
                end
                {RANK1, 8'd0} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M0_R1_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M0_R1_CFG_0 , x_sel  );
                end
                {RANK1, 8'd1} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M0_R1_CFG_1 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M0_R1_CFG_1 , x_sel  );
                end
                {RANK1, 8'd2} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M0_R1_CFG_2 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M0_R1_CFG_2 , x_sel  );
                end
                {RANK1, 8'd3} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M0_R1_CFG_3 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M0_R1_CFG_3 , x_sel  );
                end
                {RANK1, 8'd4} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M0_R1_CFG_4 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M0_R1_CFG_4 , x_sel  );
                end
                {RANK1, 8'd5} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M0_R1_CFG_5 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M0_R1_CFG_5 , x_sel  );
                end
                {RANK1, 8'd6} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M0_R1_CFG_6 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M0_R1_CFG_6 , x_sel  );
                end
                {RANK1, 8'd7} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M0_R1_CFG_7 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M0_R1_CFG_7 , x_sel  );
                end
                {RANK1, 8'd8} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M0_R1_CFG_8 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M0_R1_CFG_8 , x_sel  );
                end
                default: begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M0_R0_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M0_R0_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M0_R0_CFG_1 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M0_R0_CFG_1 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M0_R0_CFG_2 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M0_R0_CFG_2 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M0_R0_CFG_3 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M0_R0_CFG_3 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M0_R0_CFG_4 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M0_R0_CFG_4 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M0_R0_CFG_5 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M0_R0_CFG_5 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M0_R0_CFG_6 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M0_R0_CFG_6 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M0_R0_CFG_7 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M0_R0_CFG_7 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M0_R0_CFG_8 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M0_R0_CFG_8 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M0_R1_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M0_R1_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M0_R1_CFG_1 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M0_R1_CFG_1 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M0_R1_CFG_2 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M0_R1_CFG_2 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M0_R1_CFG_3 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M0_R1_CFG_3 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M0_R1_CFG_4 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M0_R1_CFG_4 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M0_R1_CFG_5 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M0_R1_CFG_5 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M0_R1_CFG_6 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M0_R1_CFG_6 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M0_R1_CFG_7 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M0_R1_CFG_7 , x_sel  );
                    `CSR_WR(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M0_R1_CFG_8 , x_sel  );
                    `CSR_WR(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQS_TX_QDR_X_SEL_M0_R1_CFG_8 , x_sel  );
                end
            endcase
        end
        if((byte_sel == CA) || (byte_sel == ALL)) begin
            case ({rank_sel,dqs})
                {RANK0, 8'd0} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQS_TX_QDR_X_SEL_M0_R0_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQS_TX_QDR_X_SEL_M0_R0_CFG_0 , x_sel  );
                end
                {RANK1, 8'd0} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQS_TX_QDR_X_SEL_M0_R1_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQS_TX_QDR_X_SEL_M0_R1_CFG_0 , x_sel  );
                end
                default: begin
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQS_TX_QDR_X_SEL_M0_R0_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQS_TX_QDR_X_SEL_M0_R0_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH0_CA_OFFSET,DDR_CA_DQS_TX_QDR_X_SEL_M0_R1_CFG_0 , x_sel  );
                    `CSR_WR(DDR_CH1_CA_OFFSET,DDR_CA_DQS_TX_QDR_X_SEL_M0_R1_CFG_0 , x_sel  );
                end
            endcase
        end
    end
endtask

task automatic set_txdqs_qdr_pipe_en;
    input byte_sel_t     byte_sel;
    input rank_sel_t     rank_sel;
    input logic    [7:0] dqs;
    input logic   [31:0] pipe_en;
    begin
        if((byte_sel == DQ0) || (byte_sel == DQ_ALL) || (byte_sel == ALL)) begin
            case ({rank_sel,dqs})
                {RANK0, 8'd0} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET, DDR_DQ_DQS_TX_QDR_M0_R0_CFG_0, pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET, DDR_DQ_DQS_TX_QDR_M0_R0_CFG_0, pipe_en);
                end
                {RANK0, 8'd1} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET, DDR_DQ_DQS_TX_QDR_M0_R0_CFG_1, pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET, DDR_DQ_DQS_TX_QDR_M0_R0_CFG_1, pipe_en);
                end
                {RANK0, 8'd2} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET, DDR_DQ_DQS_TX_QDR_M0_R0_CFG_2, pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET, DDR_DQ_DQS_TX_QDR_M0_R0_CFG_2, pipe_en);
                end
                {RANK0, 8'd3} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET, DDR_DQ_DQS_TX_QDR_M0_R0_CFG_3, pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET, DDR_DQ_DQS_TX_QDR_M0_R0_CFG_3, pipe_en);
                end
                {RANK0, 8'd4} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET, DDR_DQ_DQS_TX_QDR_M0_R0_CFG_4, pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET, DDR_DQ_DQS_TX_QDR_M0_R0_CFG_4, pipe_en);
                end
                {RANK0, 8'd5} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET, DDR_DQ_DQS_TX_QDR_M0_R0_CFG_5, pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET, DDR_DQ_DQS_TX_QDR_M0_R0_CFG_5, pipe_en);
                end
                {RANK0, 8'd6} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET, DDR_DQ_DQS_TX_QDR_M0_R0_CFG_6, pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET, DDR_DQ_DQS_TX_QDR_M0_R0_CFG_6, pipe_en);
                end
                {RANK0, 8'd7} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET, DDR_DQ_DQS_TX_QDR_M0_R0_CFG_7, pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET, DDR_DQ_DQS_TX_QDR_M0_R0_CFG_7, pipe_en);
                end
                {RANK0, 8'd8} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET, DDR_DQ_DQS_TX_QDR_M0_R0_CFG_8, pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET, DDR_DQ_DQS_TX_QDR_M0_R0_CFG_8, pipe_en);
                end
                {RANK1, 8'd0} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET, DDR_DQ_DQS_TX_QDR_M0_R1_CFG_0, pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET, DDR_DQ_DQS_TX_QDR_M0_R1_CFG_0, pipe_en);
                end
                {RANK1, 8'd1} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET, DDR_DQ_DQS_TX_QDR_M0_R1_CFG_1, pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET, DDR_DQ_DQS_TX_QDR_M0_R1_CFG_1, pipe_en);
                end
                {RANK1, 8'd2} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET, DDR_DQ_DQS_TX_QDR_M0_R1_CFG_2, pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET, DDR_DQ_DQS_TX_QDR_M0_R1_CFG_2, pipe_en);
                end
                {RANK1, 8'd3} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET, DDR_DQ_DQS_TX_QDR_M0_R1_CFG_3, pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET, DDR_DQ_DQS_TX_QDR_M0_R1_CFG_3, pipe_en);
                end
                {RANK1, 8'd4} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET, DDR_DQ_DQS_TX_QDR_M0_R1_CFG_4, pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET, DDR_DQ_DQS_TX_QDR_M0_R1_CFG_4, pipe_en);
                end
                {RANK1, 8'd5} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET, DDR_DQ_DQS_TX_QDR_M0_R1_CFG_5, pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET, DDR_DQ_DQS_TX_QDR_M0_R1_CFG_5, pipe_en);
                end
                {RANK1, 8'd6} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET, DDR_DQ_DQS_TX_QDR_M0_R1_CFG_6, pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET, DDR_DQ_DQS_TX_QDR_M0_R1_CFG_6, pipe_en);
                end
                {RANK1, 8'd7} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET, DDR_DQ_DQS_TX_QDR_M0_R1_CFG_7, pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET, DDR_DQ_DQS_TX_QDR_M0_R1_CFG_7, pipe_en);
                end
                {RANK1, 8'd8} : begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET, DDR_DQ_DQS_TX_QDR_M0_R1_CFG_8, pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET, DDR_DQ_DQS_TX_QDR_M0_R1_CFG_8, pipe_en);
                end
                default: begin
                    `CSR_WR(DDR_CH0_DQ0_OFFSET, DDR_DQ_DQS_TX_QDR_M0_R0_CFG_0, pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET, DDR_DQ_DQS_TX_QDR_M0_R0_CFG_0, pipe_en);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET, DDR_DQ_DQS_TX_QDR_M0_R0_CFG_1, pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET, DDR_DQ_DQS_TX_QDR_M0_R0_CFG_1, pipe_en);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET, DDR_DQ_DQS_TX_QDR_M0_R0_CFG_2, pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET, DDR_DQ_DQS_TX_QDR_M0_R0_CFG_2, pipe_en);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET, DDR_DQ_DQS_TX_QDR_M0_R0_CFG_3, pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET, DDR_DQ_DQS_TX_QDR_M0_R0_CFG_3, pipe_en);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET, DDR_DQ_DQS_TX_QDR_M0_R0_CFG_4, pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET, DDR_DQ_DQS_TX_QDR_M0_R0_CFG_4, pipe_en);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET, DDR_DQ_DQS_TX_QDR_M0_R0_CFG_5, pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET, DDR_DQ_DQS_TX_QDR_M0_R0_CFG_5, pipe_en);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET, DDR_DQ_DQS_TX_QDR_M0_R0_CFG_6, pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET, DDR_DQ_DQS_TX_QDR_M0_R0_CFG_6, pipe_en);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET, DDR_DQ_DQS_TX_QDR_M0_R0_CFG_7, pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET, DDR_DQ_DQS_TX_QDR_M0_R0_CFG_7, pipe_en);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET, DDR_DQ_DQS_TX_QDR_M0_R0_CFG_8, pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET, DDR_DQ_DQS_TX_QDR_M0_R0_CFG_8, pipe_en);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET, DDR_DQ_DQS_TX_QDR_M0_R1_CFG_0, pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET, DDR_DQ_DQS_TX_QDR_M0_R1_CFG_0, pipe_en);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET, DDR_DQ_DQS_TX_QDR_M0_R1_CFG_1, pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET, DDR_DQ_DQS_TX_QDR_M0_R1_CFG_1, pipe_en);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET, DDR_DQ_DQS_TX_QDR_M0_R1_CFG_2, pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET, DDR_DQ_DQS_TX_QDR_M0_R1_CFG_2, pipe_en);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET, DDR_DQ_DQS_TX_QDR_M0_R1_CFG_3, pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET, DDR_DQ_DQS_TX_QDR_M0_R1_CFG_3, pipe_en);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET, DDR_DQ_DQS_TX_QDR_M0_R1_CFG_4, pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET, DDR_DQ_DQS_TX_QDR_M0_R1_CFG_4, pipe_en);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET, DDR_DQ_DQS_TX_QDR_M0_R1_CFG_5, pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET, DDR_DQ_DQS_TX_QDR_M0_R1_CFG_5, pipe_en);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET, DDR_DQ_DQS_TX_QDR_M0_R1_CFG_6, pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET, DDR_DQ_DQS_TX_QDR_M0_R1_CFG_6, pipe_en);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET, DDR_DQ_DQS_TX_QDR_M0_R1_CFG_7, pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET, DDR_DQ_DQS_TX_QDR_M0_R1_CFG_7, pipe_en);
                    `CSR_WR(DDR_CH0_DQ0_OFFSET, DDR_DQ_DQS_TX_QDR_M0_R1_CFG_8, pipe_en);
                    `CSR_WR(DDR_CH1_DQ0_OFFSET, DDR_DQ_DQS_TX_QDR_M0_R1_CFG_8, pipe_en);
                end
            endcase
        end
        if((byte_sel == DQ1) || (byte_sel == DQ_ALL) || (byte_sel == ALL)) begin
            case ({rank_sel,dqs})
                {RANK0, 8'd0} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET, DDR_DQ_DQS_TX_QDR_M0_R0_CFG_0, pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET, DDR_DQ_DQS_TX_QDR_M0_R0_CFG_0, pipe_en);
                end
                {RANK0, 8'd1} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET, DDR_DQ_DQS_TX_QDR_M0_R0_CFG_1, pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET, DDR_DQ_DQS_TX_QDR_M0_R0_CFG_1, pipe_en);
                end
                {RANK0, 8'd2} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET, DDR_DQ_DQS_TX_QDR_M0_R0_CFG_2, pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET, DDR_DQ_DQS_TX_QDR_M0_R0_CFG_2, pipe_en);
                end
                {RANK0, 8'd3} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET, DDR_DQ_DQS_TX_QDR_M0_R0_CFG_3, pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET, DDR_DQ_DQS_TX_QDR_M0_R0_CFG_3, pipe_en);
                end
                {RANK0, 8'd4} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET, DDR_DQ_DQS_TX_QDR_M0_R0_CFG_4, pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET, DDR_DQ_DQS_TX_QDR_M0_R0_CFG_4, pipe_en);
                end
                {RANK0, 8'd5} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET, DDR_DQ_DQS_TX_QDR_M0_R0_CFG_5, pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET, DDR_DQ_DQS_TX_QDR_M0_R0_CFG_5, pipe_en);
                end
                {RANK0, 8'd6} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET, DDR_DQ_DQS_TX_QDR_M0_R0_CFG_6, pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET, DDR_DQ_DQS_TX_QDR_M0_R0_CFG_6, pipe_en);
                end
                {RANK0, 8'd7} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET, DDR_DQ_DQS_TX_QDR_M0_R0_CFG_7, pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET, DDR_DQ_DQS_TX_QDR_M0_R0_CFG_7, pipe_en);
                end
                {RANK0, 8'd8} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET, DDR_DQ_DQS_TX_QDR_M0_R0_CFG_8, pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET, DDR_DQ_DQS_TX_QDR_M0_R0_CFG_8, pipe_en);
                end
                {RANK1, 8'd0} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET, DDR_DQ_DQS_TX_QDR_M0_R1_CFG_0, pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET, DDR_DQ_DQS_TX_QDR_M0_R1_CFG_0, pipe_en);
                end
                {RANK1, 8'd1} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET, DDR_DQ_DQS_TX_QDR_M0_R1_CFG_1, pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET, DDR_DQ_DQS_TX_QDR_M0_R1_CFG_1, pipe_en);
                end
                {RANK1, 8'd2} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET, DDR_DQ_DQS_TX_QDR_M0_R1_CFG_2, pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET, DDR_DQ_DQS_TX_QDR_M0_R1_CFG_2, pipe_en);
                end
                {RANK1, 8'd3} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET, DDR_DQ_DQS_TX_QDR_M0_R1_CFG_3, pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET, DDR_DQ_DQS_TX_QDR_M0_R1_CFG_3, pipe_en);
                end
                {RANK1, 8'd4} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET, DDR_DQ_DQS_TX_QDR_M0_R1_CFG_4, pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET, DDR_DQ_DQS_TX_QDR_M0_R1_CFG_4, pipe_en);
                end
                {RANK1, 8'd5} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET, DDR_DQ_DQS_TX_QDR_M0_R1_CFG_5, pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET, DDR_DQ_DQS_TX_QDR_M0_R1_CFG_5, pipe_en);
                end
                {RANK1, 8'd6} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET, DDR_DQ_DQS_TX_QDR_M0_R1_CFG_6, pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET, DDR_DQ_DQS_TX_QDR_M0_R1_CFG_6, pipe_en);
                end
                {RANK1, 8'd7} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET, DDR_DQ_DQS_TX_QDR_M0_R1_CFG_7, pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET, DDR_DQ_DQS_TX_QDR_M0_R1_CFG_7, pipe_en);
                end
                {RANK1, 8'd8} : begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET, DDR_DQ_DQS_TX_QDR_M0_R1_CFG_8, pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET, DDR_DQ_DQS_TX_QDR_M0_R1_CFG_8, pipe_en);
                end
                default: begin
                    `CSR_WR(DDR_CH0_DQ1_OFFSET, DDR_DQ_DQS_TX_QDR_M0_R0_CFG_0, pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET, DDR_DQ_DQS_TX_QDR_M0_R0_CFG_0, pipe_en);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET, DDR_DQ_DQS_TX_QDR_M0_R0_CFG_1, pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET, DDR_DQ_DQS_TX_QDR_M0_R0_CFG_1, pipe_en);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET, DDR_DQ_DQS_TX_QDR_M0_R0_CFG_2, pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET, DDR_DQ_DQS_TX_QDR_M0_R0_CFG_2, pipe_en);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET, DDR_DQ_DQS_TX_QDR_M0_R0_CFG_3, pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET, DDR_DQ_DQS_TX_QDR_M0_R0_CFG_3, pipe_en);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET, DDR_DQ_DQS_TX_QDR_M0_R0_CFG_4, pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET, DDR_DQ_DQS_TX_QDR_M0_R0_CFG_4, pipe_en);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET, DDR_DQ_DQS_TX_QDR_M0_R0_CFG_5, pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET, DDR_DQ_DQS_TX_QDR_M0_R0_CFG_5, pipe_en);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET, DDR_DQ_DQS_TX_QDR_M0_R0_CFG_6, pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET, DDR_DQ_DQS_TX_QDR_M0_R0_CFG_6, pipe_en);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET, DDR_DQ_DQS_TX_QDR_M0_R0_CFG_7, pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET, DDR_DQ_DQS_TX_QDR_M0_R0_CFG_7, pipe_en);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET, DDR_DQ_DQS_TX_QDR_M0_R0_CFG_8, pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET, DDR_DQ_DQS_TX_QDR_M0_R0_CFG_8, pipe_en);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET, DDR_DQ_DQS_TX_QDR_M0_R1_CFG_0, pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET, DDR_DQ_DQS_TX_QDR_M0_R1_CFG_0, pipe_en);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET, DDR_DQ_DQS_TX_QDR_M0_R1_CFG_1, pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET, DDR_DQ_DQS_TX_QDR_M0_R1_CFG_1, pipe_en);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET, DDR_DQ_DQS_TX_QDR_M0_R1_CFG_2, pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET, DDR_DQ_DQS_TX_QDR_M0_R1_CFG_2, pipe_en);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET, DDR_DQ_DQS_TX_QDR_M0_R1_CFG_3, pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET, DDR_DQ_DQS_TX_QDR_M0_R1_CFG_3, pipe_en);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET, DDR_DQ_DQS_TX_QDR_M0_R1_CFG_4, pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET, DDR_DQ_DQS_TX_QDR_M0_R1_CFG_4, pipe_en);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET, DDR_DQ_DQS_TX_QDR_M0_R1_CFG_5, pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET, DDR_DQ_DQS_TX_QDR_M0_R1_CFG_5, pipe_en);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET, DDR_DQ_DQS_TX_QDR_M0_R1_CFG_6, pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET, DDR_DQ_DQS_TX_QDR_M0_R1_CFG_6, pipe_en);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET, DDR_DQ_DQS_TX_QDR_M0_R1_CFG_7, pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET, DDR_DQ_DQS_TX_QDR_M0_R1_CFG_7, pipe_en);
                    `CSR_WR(DDR_CH0_DQ1_OFFSET, DDR_DQ_DQS_TX_QDR_M0_R1_CFG_8, pipe_en);
                    `CSR_WR(DDR_CH1_DQ1_OFFSET, DDR_DQ_DQS_TX_QDR_M0_R1_CFG_8, pipe_en);
                end
            endcase
        end
        if((byte_sel == CA) || (byte_sel == ALL)) begin
            case ({rank_sel,dqs})
                {RANK0, 8'd0} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET, DDR_CA_DQS_TX_QDR_M0_R0_CFG_0, pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET, DDR_CA_DQS_TX_QDR_M0_R0_CFG_0, pipe_en);
                end
                {RANK1, 8'd0} : begin
                    `CSR_WR(DDR_CH0_CA_OFFSET, DDR_CA_DQS_TX_QDR_M0_R1_CFG_0, pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET, DDR_CA_DQS_TX_QDR_M0_R1_CFG_0, pipe_en);
                end
                default: begin
                    `CSR_WR(DDR_CH0_CA_OFFSET, DDR_CA_DQS_TX_QDR_M0_R0_CFG_0, pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET, DDR_CA_DQS_TX_QDR_M0_R0_CFG_0, pipe_en);
                    `CSR_WR(DDR_CH0_CA_OFFSET, DDR_CA_DQS_TX_QDR_M0_R1_CFG_0, pipe_en);
                    `CSR_WR(DDR_CH1_CA_OFFSET, DDR_CA_DQS_TX_QDR_M0_R1_CFG_0, pipe_en);
                end
            endcase
        end
    end
endtask

//-----------------------------------------------------------------------
// DQ DP APIs - End
//-----------------------------------------------------------------------

//-----------------------------------------------------------------------
// DFI APIs - Begin
//-----------------------------------------------------------------------
localparam       N                            = 12;  // DFI buffer Transactions

localparam       NUM_DPACKETS                 = 9;
localparam       NUM_CAPACKETS                = 9;
localparam BL                                 = 128;
//localparam [(BL*8)+32-1:0] DATA               = 288'h123452789ABCDEFCFED2BA987654321B123456789ABCDEF0FEDCBA9876543210;  //P0
//localparam [(BL*8)+32-1:0] CMND               = 288'h123452789ABCDEFCFED2BA987654321B123456789ABCDEF0FEDCBA9876543210;  //P0
`ifndef DUMP_SPICE_VCD
localparam [(BL*9)-1:0] DATA                  = {
                                                 256'h12345278_9ABCDEFC_FED2BA98_7654321B_12345678_9ABCDEF0_FEDCBA98_76543210,
                                                 256'h12345278_9ABCDEFC_FED2BA98_7654321B_12345678_9ABCDEF0_FEDCBA98_76543210,
                                                 256'h12345278_9ABCDEFC_FED2BA98_7654321B_12345678_9ABCDEF0_FEDCBA98_76543210,
                                                 256'h12345278_9ABCDEFC_FED2BA98_7654321B_12345678_9ABCDEF0_FEDCBA98_76543210,
                                                 256'h12345278_9ABCDEFC_FED2BA98_7654321B_12345678_9ABCDEF0_FEDCBA98_76543210
                                                }; // 1056'h

`else
localparam [(BL*9)-1:0] DATA                  = {
                                                 256'hFF00FF00_FF00FF00_FF00FF00_FF00FF00_00FF00FF_00FF00FF_00FF00FF_00FF00FF,
                                                 256'hFF00FF00_FF00FF00_FF00FF00_FF00FF00_00FF00FF_00FF00FF_00FF00FF_00FF00FF,
                                                 256'hFF00FF00_FF00FF00_FF00FF00_FF00FF00_00FF00FF_00FF00FF_00FF00FF_00FF00FF,
                                                 256'hFF00FF00_FF00FF00_FF00FF00_FF00FF00_00FF00FF_00FF00FF_00FF00FF_00FF00FF,
                                                 256'hFF00FF00_FF00FF00_FF00FF00_FF00FF00_00FF00FF_00FF00FF_00FF00FF_00FF00FF
                                                }; // 1056'h
`endif

`ifndef DUMP_SPICE_VCD
localparam [(BL*9)-1:0] CMND                  = {
                                                 256'h12345278_9ABCDEFC_FED2BA98_7654321B_12345678_9ABCDEF0_FEDCBA98_76543210,
                                                 256'h12345278_9ABCDEFC_FED2BA98_7654321B_12345678_9ABCDEF0_FEDCBA98_76543210,
                                                 256'h12345278_9ABCDEFC_FED2BA98_7654321B_12345678_9ABCDEF0_FEDCBA98_76543210,
                                                 256'h12345278_9ABCDEFC_FED2BA98_7654321B_12345678_9ABCDEF0_FEDCBA98_76543210,
                                                 256'h12345278_9ABCDEFC_FED2BA98_7654321B_12345678_9ABCDEF0_FEDCBA98_76543210
                                                }; // 1056'h
`else
localparam [(BL*9)-1:0] CMND                  = {
                                                 256'hFF00FF00_FF00FF00_FF00FF00_FF00FF00_00FF00FF_00FF00FF_00FF00FF_00FF00FF,
                                                 256'hFF00FF00_FF00FF00_FF00FF00_FF00FF00_00FF00FF_00FF00FF_00FF00FF_00FF00FF,
                                                 256'hFF00FF00_FF00FF00_FF00FF00_FF00FF00_00FF00FF_00FF00FF_00FF00FF_00FF00FF,
                                                 256'hFF00FF00_FF00FF00_FF00FF00_FF00FF00_00FF00FF_00FF00FF_00FF00FF_00FF00FF,
                                                 256'hFF00FF00_FF00FF00_FF00FF00_FF00FF00_00FF00FF_00FF00FF_00FF00FF_00FF00FF
                                                }; // 1056'h
`endif

localparam [NUM_DFI_WPH*TWIDTH-1:0] WCKT_SL = {NUM_DFI_WPH*TWIDTH{WCK_STATIC_LOW}}  ;
localparam [NUM_DFI_WPH*TWIDTH-1:0] WCKT_SH = {NUM_DFI_WPH*TWIDTH{WCK_STATIC_HIGH}} ;
localparam [NUM_DFI_WPH*TWIDTH-1:0] WCKT_T  = {NUM_DFI_WPH*TWIDTH{WCK_TOGGLE}}      ;
localparam [NUM_DFI_WPH*TWIDTH-1:0] WCKT_FT = {NUM_DFI_WPH*TWIDTH{WCK_FAST_TOGGLE}} ;

task automatic gen_dfi_data_packet;
    //input  logic [7:0] tphy_cmdlat   ;   // max 3 cycle supported.  // DFI Cycles between "wr command" to "dfi_wrdata_en"
    input  logic [7:0] tphy_wrlat   ;   // max 3 cycle supported.  // DFI Cycles between "wr command" to "dfi_wrdata_en"
    input  logic [7:0] tphy_wrcslat   ; // max 3 cycle supported.  // DFI Cycles between "wr cs" to "wr command"
    input  logic [7:0] tphy_wrdata  ;   // max 3 cycle supported.  // DFI Cycles between "dfi_wrdata_en" and "dfi_wrdata"
    input  logic [1:0] rank_sel ;
    input  integer cadce_pnum ;
    input  integer cacs_pnum ;
    input  integer cacke_pnum ;
    input  integer caaddr_pnum ;
    input  integer wckcs_pnum ;
    input  integer wcken_pnum ;
    input  integer wckt_pnum ;
    input  integer wren_pnum ;
    input  integer par_pnum ;
    input  integer wrcs_pnum ;
    input  integer rden_pnum ;
    input  integer wr_pnum ;
    //input  wckt_sl_cycles ;
    //input  wckt_sh_cycles ;
    //input  wckt_t_cycles ;
    //input  wckt_ft_cycles ;
    input  integer bl ;
    input  logic [TSWIDTH-1:0] ts_offset ;
    output logic [IG_WIDTH-1:0] wrd_packet[N:0] ;
    output logic [EG_WIDTH-1:0] rd_exp_packet[N-1:0];

    int i, j, k, beat_cnt;

    logic [TSWIDTH-1:0] ts;
    logic [SWIDTH-1:0]  dq0_wrdata_p0;
    logic [MWIDTH-1:0]  dq0_wrdata_mask_p0;
    logic [SWIDTH-1:0]  dq1_wrdata_p0;
    logic [MWIDTH-1:0]  dq1_wrdata_mask_p0;
    logic [SWIDTH-1:0]  dq2_wrdata_p0;
    logic [MWIDTH-1:0]  dq2_wrdata_mask_p0;
    logic [SWIDTH-1:0]  dq3_wrdata_p0;
    logic [MWIDTH-1:0]  dq3_wrdata_mask_p0;
    logic               parity_in_p0;
    logic [1:0]         wrdata_cs_p0;
    logic               wrdata_en_p0;
    logic [1:0]         wck_cs_p0;
    logic               wck_en_p0;
    logic [TWIDTH-1:0]  wck_toggle_p0;
    logic [1:0]         rddata_cs_p0;
    logic               rddata_en_p0;
    logic [SWIDTH-1:0]  dq0_wrdata_p1;
    logic [MWIDTH-1:0]  dq0_wrdata_mask_p1;
    logic [SWIDTH-1:0]  dq1_wrdata_p1;
    logic [MWIDTH-1:0]  dq1_wrdata_mask_p1;
    logic [SWIDTH-1:0]  dq2_wrdata_p1;
    logic [MWIDTH-1:0]  dq2_wrdata_mask_p1;
    logic [SWIDTH-1:0]  dq3_wrdata_p1;
    logic [MWIDTH-1:0]  dq3_wrdata_mask_p1;
    logic               parity_in_p1;
    logic [1:0]         wrdata_cs_p1;
    logic               wrdata_en_p1;
    logic [1:0]         wck_cs_p1;
    logic               wck_en_p1;
    logic [TWIDTH-1:0]  wck_toggle_p1;
    logic [1:0]         rddata_cs_p1;
    logic               rddata_en_p1;
    logic [SWIDTH-1:0]  dq0_wrdata_p2;
    logic [MWIDTH-1:0]  dq0_wrdata_mask_p2;
    logic [SWIDTH-1:0]  dq1_wrdata_p2;
    logic [MWIDTH-1:0]  dq1_wrdata_mask_p2;
    logic [SWIDTH-1:0]  dq2_wrdata_p2;
    logic [MWIDTH-1:0]  dq2_wrdata_mask_p2;
    logic [SWIDTH-1:0]  dq3_wrdata_p2;
    logic [MWIDTH-1:0]  dq3_wrdata_mask_p2;
    logic               parity_in_p2;
    logic [1:0]         wrdata_cs_p2;
    logic               wrdata_en_p2;
    logic [1:0]         wck_cs_p2;
    logic               wck_en_p2;
    logic [TWIDTH-1:0]  wck_toggle_p2;
    logic [1:0]         rddata_cs_p2;
    logic               rddata_en_p2;
    logic [SWIDTH-1:0]  dq0_wrdata_p3;
    logic [MWIDTH-1:0]  dq0_wrdata_mask_p3;
    logic [SWIDTH-1:0]  dq1_wrdata_p3;
    logic [MWIDTH-1:0]  dq1_wrdata_mask_p3;
    logic [SWIDTH-1:0]  dq2_wrdata_p3;
    logic [MWIDTH-1:0]  dq2_wrdata_mask_p3;
    logic [SWIDTH-1:0]  dq3_wrdata_p3;
    logic [MWIDTH-1:0]  dq3_wrdata_mask_p3;
    logic               parity_in_p3;
    logic [1:0]         wrdata_cs_p3;
    logic               wrdata_en_p3;
    logic [1:0]         wck_cs_p3;
    logic               wck_en_p3;
    logic [TWIDTH-1:0]  wck_toggle_p3;
    logic [1:0]         rddata_cs_p3;
    logic               rddata_en_p3;
    logic [SWIDTH-1:0]  dq0_wrdata_p4;
    logic [MWIDTH-1:0]  dq0_wrdata_mask_p4;
    logic [SWIDTH-1:0]  dq1_wrdata_p4;
    logic [MWIDTH-1:0]  dq1_wrdata_mask_p4;
    logic [SWIDTH-1:0]  dq2_wrdata_p4;
    logic [MWIDTH-1:0]  dq2_wrdata_mask_p4;
    logic [SWIDTH-1:0]  dq3_wrdata_p4;
    logic [MWIDTH-1:0]  dq3_wrdata_mask_p4;
    logic               parity_in_p4;
    logic [1:0]         wrdata_cs_p4;
    logic               wrdata_en_p4;
    logic [1:0]         wck_cs_p4;
    logic               wck_en_p4;
    logic [TWIDTH-1:0]  wck_toggle_p4;
    logic [1:0]         rddata_cs_p4;
    logic               rddata_en_p4;
    logic [SWIDTH-1:0]  dq0_wrdata_p5;
    logic [MWIDTH-1:0]  dq0_wrdata_mask_p5;
    logic [SWIDTH-1:0]  dq1_wrdata_p5;
    logic [MWIDTH-1:0]  dq1_wrdata_mask_p5;
    logic [SWIDTH-1:0]  dq2_wrdata_p5;
    logic [MWIDTH-1:0]  dq2_wrdata_mask_p5;
    logic [SWIDTH-1:0]  dq3_wrdata_p5;
    logic [MWIDTH-1:0]  dq3_wrdata_mask_p5;
    logic               parity_in_p5;
    logic [1:0]         wrdata_cs_p5;
    logic               wrdata_en_p5;
    logic [1:0]         wck_cs_p5;
    logic               wck_en_p5;
    logic [TWIDTH-1:0]  wck_toggle_p5;
    logic [1:0]         rddata_cs_p5;
    logic               rddata_en_p5;
    logic [SWIDTH-1:0]  dq0_wrdata_p6;
    logic [MWIDTH-1:0]  dq0_wrdata_mask_p6;
    logic [SWIDTH-1:0]  dq1_wrdata_p6;
    logic [MWIDTH-1:0]  dq1_wrdata_mask_p6;
    logic [SWIDTH-1:0]  dq2_wrdata_p6;
    logic [MWIDTH-1:0]  dq2_wrdata_mask_p6;
    logic [SWIDTH-1:0]  dq3_wrdata_p6;
    logic [MWIDTH-1:0]  dq3_wrdata_mask_p6;
    logic               parity_in_p6;
    logic [1:0]         wrdata_cs_p6;
    logic               wrdata_en_p6;
    logic [1:0]         wck_cs_p6;
    logic               wck_en_p6;
    logic [TWIDTH-1:0]  wck_toggle_p6;
    logic [1:0]         rddata_cs_p6;
    logic               rddata_en_p6;
    logic [SWIDTH-1:0]  dq0_wrdata_p7;
    logic [MWIDTH-1:0]  dq0_wrdata_mask_p7;
    logic [SWIDTH-1:0]  dq1_wrdata_p7;
    logic [MWIDTH-1:0]  dq1_wrdata_mask_p7;
    logic [SWIDTH-1:0]  dq2_wrdata_p7;
    logic [MWIDTH-1:0]  dq2_wrdata_mask_p7;
    logic [SWIDTH-1:0]  dq3_wrdata_p7;
    logic [MWIDTH-1:0]  dq3_wrdata_mask_p7;
    logic               parity_in_p7;
    logic [1:0]         wrdata_cs_p7;
    logic               wrdata_en_p7;
    logic [1:0]         wck_cs_p7;
    logic               wck_en_p7;
    logic [TWIDTH-1:0]  wck_toggle_p7;
    logic [1:0]         rddata_cs_p7;
    logic               rddata_en_p7;

    logic               dce_p0;
    logic [AWIDTH-1:0]  address_p0;
    logic [1:0]         cke_p0;
    logic [1:0]         cs_p0;
    logic               dce_p1;
    logic [AWIDTH-1:0]  address_p1;
    logic [1:0]         cke_p1;
    logic [1:0]         cs_p1;
    logic               dce_p2;
    logic [AWIDTH-1:0]  address_p2;
    logic [1:0]         cke_p2;
    logic [1:0]         cs_p2;
    logic               dce_p3;
    logic [AWIDTH-1:0]  address_p3;
    logic [1:0]         cke_p3;
    logic [1:0]         cs_p3;
    logic               dce_p4;
    logic [AWIDTH-1:0]  address_p4;
    logic [1:0]         cke_p4;
    logic [1:0]         cs_p4;
    logic               dce_p5;
    logic [AWIDTH-1:0]  address_p5;
    logic [1:0]         cke_p5;
    logic [1:0]         cs_p5;
    logic               dce_p6;
    logic [AWIDTH-1:0]  address_p6;
    logic [1:0]         cke_p6;
    logic [1:0]         cs_p6;
    logic               dce_p7;
    logic [AWIDTH-1:0]  address_p7;
    logic [1:0]         cke_p7;
    logic [1:0]         cs_p7;
    logic [127:0]  ca_dce;
    logic [255:0]  ca_cs;
    logic [255:0]  ca_cke;
    logic [895:0]  ca_addr;
    logic [1023:0] data;
    logic [127:0]   wr_en;
    logic [7:0]    tphy_cmdlat_int   ;
    logic [7:0]    tphy_wrlat_int   ;
    logic [7:0]    tphy_wrcslat_int ;
    logic [7:0]    tphy_wrdata_int  ;
    begin
        data = '0;
        wr_en = '0;
        ca_addr = '0;
        ca_dce  = '0;
        ca_cs   = '0;
        ca_cke  = '0;

        //tphy_wrcslat_int = tphy_wrcslat + 3 ;
        //tphy_wrlat_int   = tphy_wrcslat + tphy_wrlat + 3;
        //tphy_wrdata_int  = tphy_wrlat_int + tphy_wrdata + 3;
        tphy_cmdlat_int  = tphy_wrlat ;   // FIXME: should be independent control and not tied to wrlat.
        tphy_wrcslat_int = tphy_wrcslat ;
        tphy_wrlat_int   = tphy_wrlat  ;
        tphy_wrdata_int  = tphy_wrdata + tphy_wrlat ;

        if (bl==128) begin
          ca_cke  = '1 << (cacke_pnum*2 ) ; ;
          ca_cs   = {128{rank_sel}}  << (cacs_pnum*2  + tphy_cmdlat_int*NUM_DFI_WPH*2) ;
          wr_en   = {128{1'b1}} << (wren_pnum + tphy_wrlat_int*NUM_DFI_WPH);
          data    = DATA[128*SWIDTH-1:0] << (wr_pnum*SWIDTH + tphy_wrdata_int*NUM_DFI_WPH*SWIDTH);
        end else if(bl==64) begin
          ca_cke  = '1 << (cacke_pnum*2 ) ; ;
          ca_cs   = {64{rank_sel}}  << (cacs_pnum*2  + tphy_cmdlat_int*NUM_DFI_WPH*2) ;
          wr_en   = {64{1'b1}} << (wren_pnum + tphy_wrlat_int*NUM_DFI_WPH);
          data    = DATA[64*SWIDTH-1:0] << (wr_pnum*SWIDTH + tphy_wrdata_int*NUM_DFI_WPH*SWIDTH);
        end else if(bl==32) begin
            ca_cke  = '1 << (cacke_pnum*2 ) ; ;
            ca_cs   = {32{rank_sel}}  << (cacs_pnum*2  + tphy_cmdlat_int*NUM_DFI_WPH*2) ;
            wr_en   = {32{1'b1}} << (wren_pnum + tphy_wrlat_int*NUM_DFI_WPH);
            data    = DATA[32*SWIDTH-1:0] << (wr_pnum*SWIDTH + tphy_wrdata_int*NUM_DFI_WPH*SWIDTH);
        end else begin //if (bl==16)
            ca_cke  = '1 << (cacke_pnum*2 ) ;
            ca_cs   = {16{rank_sel}} << (cacs_pnum*2 + tphy_cmdlat_int*NUM_DFI_WPH*2 ) ;
            wr_en   = {16{1'b1}} << (wren_pnum + tphy_wrlat_int*NUM_DFI_WPH);
            data    = DATA[16*SWIDTH-1:0] << (wr_pnum*SWIDTH + tphy_wrdata_int*NUM_DFI_WPH*SWIDTH);
        end

        //Initialize all signals to 0
        dce_p0             = '0 ;
        address_p0         = '0 ;
        cke_p0             = '0 ;
        cs_p0              = '0 ;
        dce_p1             = '0 ;
        address_p1         = '0 ;
        cke_p1             = '0 ;
        cs_p1              = '0 ;
        dce_p2             = '0 ;
        address_p2         = '0 ;
        cke_p2             = '0 ;
        cs_p2              = '0 ;
        dce_p3             = '0 ;
        address_p3         = '0 ;
        cke_p3             = '0 ;
        cs_p3              = '0 ;
        dce_p4             = '0 ;
        address_p4         = '0 ;
        cke_p4             = '0 ;
        cs_p4              = '0 ;
        dce_p5             = '0 ;
        address_p5         = '0 ;
        cke_p5             = '0 ;
        cs_p5              = '0 ;
        dce_p6             = '0 ;
        address_p6         = '0 ;
        cke_p6             = '0 ;
        cs_p6              = '0 ;
        dce_p7             = '0 ;
        address_p7         = '0 ;
        cke_p7             = '0 ;
        cs_p7              = '0 ;
        dq0_wrdata_p0      = '0;
        dq0_wrdata_mask_p0 = '0;
        dq1_wrdata_p0      = '0;
        dq1_wrdata_mask_p0 = '0;
        dq2_wrdata_p0      = '0;
        dq2_wrdata_mask_p0 = '0;
        dq3_wrdata_p0      = '0;
        dq3_wrdata_mask_p0 = '0;
        parity_in_p0       = '0;
        wrdata_cs_p0       = '0;
        wrdata_en_p0       = '0;
        wck_cs_p0          = '0;
        wck_en_p0          = '0;
        wck_toggle_p0      = '0;
        rddata_cs_p0       = '0;
        rddata_en_p0       = '0;
        dq0_wrdata_p1      = '0;
        dq0_wrdata_mask_p1 = '0;
        dq1_wrdata_p1      = '0;
        dq1_wrdata_mask_p1 = '0;
        dq2_wrdata_p1      = '0;
        dq2_wrdata_mask_p1 = '0;
        dq3_wrdata_p1      = '0;
        dq3_wrdata_mask_p1 = '0;
        parity_in_p1       = '0;
        wrdata_cs_p1       = '0;
        wrdata_en_p1       = '0;
        wck_cs_p1          = '0;
        wck_en_p1          = '0;
        wck_toggle_p1      = '0;
        rddata_cs_p1       = '0;
        rddata_en_p1       = '0;
        dq0_wrdata_p2      = '0;
        dq0_wrdata_mask_p2 = '0;
        dq1_wrdata_p2      = '0;
        dq1_wrdata_mask_p2 = '0;
        dq2_wrdata_p2      = '0;
        dq2_wrdata_mask_p2 = '0;
        dq3_wrdata_p2      = '0;
        dq3_wrdata_mask_p2 = '0;
        parity_in_p2       = '0;
        wrdata_cs_p2       = '0;
        wrdata_en_p2       = '0;
        wck_cs_p2          = '0;
        wck_en_p2          = '0;
        wck_toggle_p2      = '0;
        rddata_cs_p2       = '0;
        rddata_en_p2       = '0;
        dq0_wrdata_p3      = '0;
        dq0_wrdata_mask_p3 = '0;
        dq1_wrdata_p3      = '0;
        dq1_wrdata_mask_p3 = '0;
        dq2_wrdata_p3      = '0;
        dq2_wrdata_mask_p3 = '0;
        dq3_wrdata_p3      = '0;
        dq3_wrdata_mask_p3 = '0;
        parity_in_p3       = '0;
        wrdata_cs_p3       = '0;
        wrdata_en_p3       = '0;
        wck_cs_p3          = '0;
        wck_en_p3          = '0;
        wck_toggle_p3      = '0;
        rddata_cs_p3       = '0;
        rddata_en_p3       = '0;
        dq0_wrdata_p4      = '0;
        dq0_wrdata_mask_p4 = '0;
        dq1_wrdata_p4      = '0;
        dq1_wrdata_mask_p4 = '0;
        dq2_wrdata_p4      = '0;
        dq2_wrdata_mask_p4 = '0;
        dq3_wrdata_p4      = '0;
        dq3_wrdata_mask_p4 = '0;
        parity_in_p4       = '0;
        wrdata_cs_p4       = '0;
        wrdata_en_p4       = '0;
        wck_cs_p4          = '0;
        wck_en_p4          = '0;
        wck_toggle_p4      = '0;
        rddata_cs_p4       = '0;
        rddata_en_p4       = '0;
        dq0_wrdata_p5      = '0;
        dq0_wrdata_mask_p5 = '0;
        dq1_wrdata_p5      = '0;
        dq1_wrdata_mask_p5 = '0;
        dq2_wrdata_p5      = '0;
        dq2_wrdata_mask_p5 = '0;
        dq3_wrdata_p5      = '0;
        dq3_wrdata_mask_p5 = '0;
        parity_in_p5       = '0;
        wrdata_cs_p5       = '0;
        wrdata_en_p5       = '0;
        wck_cs_p5          = '0;
        wck_en_p5          = '0;
        wck_toggle_p5      = '0;
        rddata_cs_p5       = '0;
        rddata_en_p5       = '0;
        dq0_wrdata_p6      = '0;
        dq0_wrdata_mask_p6 = '0;
        dq1_wrdata_p6      = '0;
        dq1_wrdata_mask_p6 = '0;
        dq2_wrdata_p6      = '0;
        dq2_wrdata_mask_p6 = '0;
        dq3_wrdata_p6      = '0;
        dq3_wrdata_mask_p6 = '0;
        parity_in_p6       = '0;
        wrdata_cs_p6       = '0;
        wrdata_en_p6       = '0;
        wck_cs_p6          = '0;
        wck_en_p6          = '0;
        wck_toggle_p6      = '0;
        rddata_cs_p6       = '0;
        rddata_en_p6       = '0;
        dq0_wrdata_p7      = '0;
        dq0_wrdata_mask_p7 = '0;
        dq1_wrdata_p7      = '0;
        dq1_wrdata_mask_p7 = '0;
        dq2_wrdata_p7      = '0;
        dq2_wrdata_mask_p7 = '0;
        dq3_wrdata_p7      = '0;
        dq3_wrdata_mask_p7 = '0;
        parity_in_p7       = '0;
        wrdata_cs_p7       = '0;
        wrdata_en_p7       = '0;
        wck_cs_p7          = '0;
        wck_en_p7          = '0;
        wck_toggle_p7      = '0;
        rddata_cs_p7       = '0;
        rddata_en_p7       = '0;

        ts   = ts_offset;
        i    = 0;
        beat_cnt = (bl+ tphy_wrdata_int*NUM_DFI_WPH + wr_pnum);
        //$display ("ts = %d, IG_WIDTH = %d, EG_WIDTH = %d bl = %d beat_cnt = %d data = %x tphy_wrdata_int=%d wr_pnum=%d", ts, IG_WIDTH, EG_WIDTH, bl, beat_cnt, data, tphy_wrdata + tphy_wrlat, wr_pnum);

        for(j=0; j < beat_cnt; j=j+NUM_DFI_WPH)
        begin
            if( j < tphy_wrdata_int*NUM_DFI_WPH ) begin
                {
                    wrdata_en_p7,
                    wrdata_en_p6,
                    wrdata_en_p5,
                    wrdata_en_p4,
                    wrdata_en_p3,
                    wrdata_en_p2,
                    wrdata_en_p1,
                wrdata_en_p0 } = wr_en[j+:NUM_DFI_WPH] ;
                {
                    rddata_en_p7,
                    rddata_en_p6,
                    rddata_en_p5,
                    rddata_en_p4,
                    rddata_en_p3,
                    rddata_en_p2,
                    rddata_en_p1,
                rddata_en_p0 } = wr_en[j+:NUM_DFI_WPH] ;
                {
                    dce_p7,
                    dce_p6,
                    dce_p5,
                    dce_p4,
                    dce_p3,
                    dce_p2,
                    dce_p1,
                dce_p0 } = ca_dce[j+:NUM_DFI_WPH] ;
                {
                    cs_p7,
                    cs_p6,
                    cs_p5,
                    cs_p4,
                    cs_p3,
                    cs_p2,
                    cs_p1,
                cs_p0 } = ca_cs[(j*2) +: (NUM_DFI_WPH*2)] ;

                {
                    cke_p7,
                    cke_p6,
                    cke_p5,
                    cke_p4,
                    cke_p3,
                    cke_p2,
                    cke_p1,
                cke_p0 } = ca_cke[(j*2) +: (NUM_DFI_WPH*2)] ;
                {
                    address_p7,
                    address_p6,
                    address_p5,
                    address_p4,
                    address_p3,
                    address_p2,
                    address_p1,
                address_p0 } = ca_addr[(j*AWIDTH) +: (NUM_DFI_WPH*AWIDTH)] ;

                wrd_packet[i] =   {
                    ts
                    //,dce_p`i
                    //,cs_p`i
                    //,cke_p`i
                    //,address_p`i
                    ,wrdata_en_p0
                    ,cs_p0
                    ,cke_p0
                    ,dq0_wrdata_p0[AWIDTH-1:0]
                    //,dce_p`i
                    //,cs_p`i
                    //,cke_p`i
                    //,address_p`i
                    ,wrdata_en_p1
                    ,cs_p1
                    ,cke_p1
                    ,dq0_wrdata_p1[AWIDTH-1:0]
                    //,dce_p`i
                    //,cs_p`i
                    //,cke_p`i
                    //,address_p`i
                    ,wrdata_en_p2
                    ,cs_p2
                    ,cke_p2
                    ,dq0_wrdata_p2[AWIDTH-1:0]
                    //,dce_p`i
                    //,cs_p`i
                    //,cke_p`i
                    //,address_p`i
                    ,wrdata_en_p3
                    ,cs_p3
                    ,cke_p3
                    ,dq0_wrdata_p3[AWIDTH-1:0]
                    //,dce_p`i
                    //,cs_p`i
                    //,cke_p`i
                    //,address_p`i
                    ,wrdata_en_p4
                    ,cs_p4
                    ,cke_p4
                    ,dq0_wrdata_p4[AWIDTH-1:0]
                    //,dce_p`i
                    //,cs_p`i
                    //,cke_p`i
                    //,address_p`i
                    ,wrdata_en_p5
                    ,cs_p5
                    ,cke_p5
                    ,dq0_wrdata_p5[AWIDTH-1:0]
                    //,dce_p`i
                    //,cs_p`i
                    //,cke_p`i
                    //,address_p`i
                    ,wrdata_en_p6
                    ,cs_p6
                    ,cke_p6
                    ,dq0_wrdata_p6[AWIDTH-1:0]
                    //,dce_p`i
                    //,cs_p`i
                    //,cke_p`i
                    //,address_p`i
                    ,wrdata_en_p7
                    ,cs_p7
                    ,cke_p7
                    ,dq0_wrdata_p7[AWIDTH-1:0]
                    ,rddata_en_p0
                    ,rddata_cs_p0
                    ,wck_toggle_p0
                    ,wck_en_p0
                    ,wck_cs_p0
                    ,wrdata_en_p0
                    ,parity_in_p0
                    ,wrdata_cs_p0
                    ,dq0_wrdata_mask_p0
                    ,dq0_wrdata_p0
                    ,dq1_wrdata_mask_p0
                    ,dq1_wrdata_p0
                    ,dq2_wrdata_mask_p0
                    ,dq2_wrdata_p0
                    ,dq3_wrdata_mask_p0
                    ,dq3_wrdata_p0
                    ,rddata_en_p1
                    ,rddata_cs_p1
                    ,wck_toggle_p1
                    ,wck_en_p1
                    ,wck_cs_p1
                    ,wrdata_en_p1
                    ,parity_in_p1
                    ,wrdata_cs_p1
                    ,dq0_wrdata_mask_p1
                    ,dq0_wrdata_p1
                    ,dq1_wrdata_mask_p1
                    ,dq1_wrdata_p1
                    ,dq2_wrdata_mask_p1
                    ,dq2_wrdata_p1
                    ,dq3_wrdata_mask_p1
                    ,dq3_wrdata_p1
                    ,rddata_en_p2
                    ,rddata_cs_p2
                    ,wck_toggle_p2
                    ,wck_en_p2
                    ,wck_cs_p2
                    ,wrdata_en_p2
                    ,parity_in_p2
                    ,wrdata_cs_p2
                    ,dq0_wrdata_mask_p2
                    ,dq0_wrdata_p2
                    ,dq1_wrdata_mask_p2
                    ,dq1_wrdata_p2
                    ,dq2_wrdata_mask_p2
                    ,dq2_wrdata_p2
                    ,dq3_wrdata_mask_p2
                    ,dq3_wrdata_p2
                    ,rddata_en_p3
                    ,rddata_cs_p3
                    ,wck_toggle_p3
                    ,wck_en_p3
                    ,wck_cs_p3
                    ,wrdata_en_p3
                    ,parity_in_p3
                    ,wrdata_cs_p3
                    ,dq0_wrdata_mask_p3
                    ,dq0_wrdata_p3
                    ,dq1_wrdata_mask_p3
                    ,dq1_wrdata_p3
                    ,dq2_wrdata_mask_p3
                    ,dq2_wrdata_p3
                    ,dq3_wrdata_mask_p3
                    ,dq3_wrdata_p3
                    ,rddata_en_p4
                    ,rddata_cs_p4
                    ,wck_toggle_p4
                    ,wck_en_p4
                    ,wck_cs_p4
                    ,wrdata_en_p4
                    ,parity_in_p4
                    ,wrdata_cs_p4
                    ,dq0_wrdata_mask_p4
                    ,dq0_wrdata_p4
                    ,dq1_wrdata_mask_p4
                    ,dq1_wrdata_p4
                    ,dq2_wrdata_mask_p4
                    ,dq2_wrdata_p4
                    ,dq3_wrdata_mask_p4
                    ,dq3_wrdata_p4
                    ,rddata_en_p5
                    ,rddata_cs_p5
                    ,wck_toggle_p5
                    ,wck_en_p5
                    ,wck_cs_p5
                    ,wrdata_en_p5
                    ,parity_in_p5
                    ,wrdata_cs_p5
                    ,dq0_wrdata_mask_p5
                    ,dq0_wrdata_p5
                    ,dq1_wrdata_mask_p5
                    ,dq1_wrdata_p5
                    ,dq2_wrdata_mask_p5
                    ,dq2_wrdata_p5
                    ,dq3_wrdata_mask_p5
                    ,dq3_wrdata_p5
                    ,rddata_en_p6
                    ,rddata_cs_p6
                    ,wck_toggle_p6
                    ,wck_en_p6
                    ,wck_cs_p6
                    ,wrdata_en_p6
                    ,parity_in_p6
                    ,wrdata_cs_p6
                    ,dq0_wrdata_mask_p6
                    ,dq0_wrdata_p6
                    ,dq1_wrdata_mask_p6
                    ,dq1_wrdata_p6
                    ,dq2_wrdata_mask_p6
                    ,dq2_wrdata_p6
                    ,dq3_wrdata_mask_p6
                    ,dq3_wrdata_p6
                    ,rddata_en_p7
                    ,rddata_cs_p7
                    ,wck_toggle_p7
                    ,wck_en_p7
                    ,wck_cs_p7
                    ,wrdata_en_p7
                    ,parity_in_p7
                    ,wrdata_cs_p7
                    ,dq0_wrdata_mask_p7
                    ,dq0_wrdata_p7
                    ,dq1_wrdata_mask_p7
                    ,dq1_wrdata_p7
                    ,dq2_wrdata_mask_p7
                    ,dq2_wrdata_p7
                    ,dq3_wrdata_mask_p7
                    ,dq3_wrdata_p7
                };
                //$display ("INFO: GEN_DFI_PACKET -early wr_data_en -  [%d] %d : DQ0{ p3 p2 p1 p0 } = { %x %x %x %x }  DQ1{ p3 p2 p1 p0 } = { %x %x %x %x }", i, j, dq0_wrdata_p3, dq0_wrdata_p2, dq0_wrdata_p1, dq0_wrdata_p0, dq1_wrdata_p3, dq1_wrdata_p2, dq1_wrdata_p1, dq1_wrdata_p0  );
                ts           = ts + 4'd1;
                i = i+1;
            end
            //send first data beat tphy_wrdata DFI cycles after wrdata_en high
            else if(j == (tphy_wrdata_int*NUM_DFI_WPH) ) begin
                {
                    parity_in_p7,
                    parity_in_p6,
                    parity_in_p5,
                    parity_in_p4,
                    parity_in_p3,
                    parity_in_p2,
                    parity_in_p1,
                parity_in_p0 } = {NUM_DFI_WPH{1'b1}} << (par_pnum) ;

                {
                    wrdata_cs_p7,
                    wrdata_cs_p6,
                    wrdata_cs_p5,
                    wrdata_cs_p4,
                    wrdata_cs_p3,
                    wrdata_cs_p2,
                    wrdata_cs_p1,
                wrdata_cs_p0 } = {NUM_DFI_WPH{rank_sel}} << (wrcs_pnum*2) ;

                {
                    wck_cs_p7,
                    wck_cs_p6,
                    wck_cs_p5,
                    wck_cs_p4,
                    wck_cs_p3,
                    wck_cs_p2,
                    wck_cs_p1,
                wck_cs_p0 } =  {NUM_DFI_WPH{rank_sel}} << (wckcs_pnum*2) ;

                {
                    wck_en_p7,
                    wck_en_p6,
                    wck_en_p5,
                    wck_en_p4,
                    wck_en_p3,
                    wck_en_p2,
                    wck_en_p1,
                wck_en_p0 } = {NUM_DFI_WPH{1'b1}} << (wcken_pnum) ;

                {
                    wrdata_en_p7,
                    wrdata_en_p6,
                    wrdata_en_p5,
                    wrdata_en_p4,
                    wrdata_en_p3,
                    wrdata_en_p2,
                    wrdata_en_p1,
                wrdata_en_p0 } = wr_en[j+:NUM_DFI_WPH] ;

                {
                    rddata_en_p7,
                    rddata_en_p6,
                    rddata_en_p5,
                    rddata_en_p4,
                    rddata_en_p3,
                    rddata_en_p2,
                    rddata_en_p1,
                rddata_en_p0 } = wr_en[j+:NUM_DFI_WPH] ;

                {
                    wck_toggle_p7,
                    wck_toggle_p6,
                    wck_toggle_p5,
                    wck_toggle_p4,
                    wck_toggle_p3,
                    wck_toggle_p2,
                    wck_toggle_p1,
                wck_toggle_p0 } = WCKT_FT << (wckt_pnum*TWIDTH) ;

                {
                    rddata_cs_p7,
                    rddata_cs_p6,
                    rddata_cs_p5,
                    rddata_cs_p4,
                    rddata_cs_p3,
                    rddata_cs_p2,
                    rddata_cs_p1,
                rddata_cs_p0 } = {NUM_DFI_WPH{rank_sel}} << (wrcs_pnum*2) ;

                {
                    dq0_wrdata_p7,
                    dq0_wrdata_p6,
                    dq0_wrdata_p5,
                    dq0_wrdata_p4,
                    dq0_wrdata_p3,
                    dq0_wrdata_p2,
                    dq0_wrdata_p1,
                    //dq`j::_wrdata_p0 }   = data[(NUM_DFI_WPH*SWIDTH)-1:0] << (wr_pnum*SWIDTH) ;
                dq0_wrdata_p0 }   = data[(SWIDTH*j)+:(NUM_DFI_WPH*SWIDTH)] ;
                {
                    dq1_wrdata_p7,
                    dq1_wrdata_p6,
                    dq1_wrdata_p5,
                    dq1_wrdata_p4,
                    dq1_wrdata_p3,
                    dq1_wrdata_p2,
                    dq1_wrdata_p1,
                    //dq`j::_wrdata_p0 }   = data[(NUM_DFI_WPH*SWIDTH)-1:0] << (wr_pnum*SWIDTH) ;
                dq1_wrdata_p0 }   = data[(SWIDTH*j)+:(NUM_DFI_WPH*SWIDTH)] ;
                {
                    dq2_wrdata_p7,
                    dq2_wrdata_p6,
                    dq2_wrdata_p5,
                    dq2_wrdata_p4,
                    dq2_wrdata_p3,
                    dq2_wrdata_p2,
                    dq2_wrdata_p1,
                    //dq`j::_wrdata_p0 }   = data[(NUM_DFI_WPH*SWIDTH)-1:0] << (wr_pnum*SWIDTH) ;
                dq2_wrdata_p0 }   = data[(SWIDTH*j)+:(NUM_DFI_WPH*SWIDTH)] ;
                {
                    dq3_wrdata_p7,
                    dq3_wrdata_p6,
                    dq3_wrdata_p5,
                    dq3_wrdata_p4,
                    dq3_wrdata_p3,
                    dq3_wrdata_p2,
                    dq3_wrdata_p1,
                    //dq`j::_wrdata_p0 }   = data[(NUM_DFI_WPH*SWIDTH)-1:0] << (wr_pnum*SWIDTH) ;
                dq3_wrdata_p0 }   = data[(SWIDTH*j)+:(NUM_DFI_WPH*SWIDTH)] ;

                {
                    dce_p7,
                    dce_p6,
                    dce_p5,
                    dce_p4,
                    dce_p3,
                    dce_p2,
                    dce_p1,
                dce_p0 } = ca_dce[j+:NUM_DFI_WPH] ;
                {
                    cke_p7,
                    cke_p6,
                    cke_p5,
                    cke_p4,
                    cke_p3,
                    cke_p2,
                    cke_p1,
                cke_p0 } = ca_cke[(j*2) +: (NUM_DFI_WPH*2)];
                {
                    cs_p7,
                    cs_p6,
                    cs_p5,
                    cs_p4,
                    cs_p3,
                    cs_p2,
                    cs_p1,
                cs_p0 } = ca_cs[(j*2) +: (NUM_DFI_WPH*2)] ;

                {
                    address_p7,
                    address_p6,
                    address_p5,
                    address_p4,
                    address_p3,
                    address_p2,
                    address_p1,
                address_p0 } = ca_addr[(j*AWIDTH) +: (NUM_DFI_WPH*AWIDTH)] ;

                wrd_packet[i] =   {
                    ts
                    //,dce_p`i
                    //,cs_p`i
                    //,cke_p`i
                    //,address_p`i
                    ,wrdata_en_p0
                    ,cs_p0
                    ,cke_p0
                    ,dq0_wrdata_p0[AWIDTH-1:0]
                    //,dce_p`i
                    //,cs_p`i
                    //,cke_p`i
                    //,address_p`i
                    ,wrdata_en_p1
                    ,cs_p1
                    ,cke_p1
                    ,dq0_wrdata_p1[AWIDTH-1:0]
                    //,dce_p`i
                    //,cs_p`i
                    //,cke_p`i
                    //,address_p`i
                    ,wrdata_en_p2
                    ,cs_p2
                    ,cke_p2
                    ,dq0_wrdata_p2[AWIDTH-1:0]
                    //,dce_p`i
                    //,cs_p`i
                    //,cke_p`i
                    //,address_p`i
                    ,wrdata_en_p3
                    ,cs_p3
                    ,cke_p3
                    ,dq0_wrdata_p3[AWIDTH-1:0]
                    //,dce_p`i
                    //,cs_p`i
                    //,cke_p`i
                    //,address_p`i
                    ,wrdata_en_p4
                    ,cs_p4
                    ,cke_p4
                    ,dq0_wrdata_p4[AWIDTH-1:0]
                    //,dce_p`i
                    //,cs_p`i
                    //,cke_p`i
                    //,address_p`i
                    ,wrdata_en_p5
                    ,cs_p5
                    ,cke_p5
                    ,dq0_wrdata_p5[AWIDTH-1:0]
                    //,dce_p`i
                    //,cs_p`i
                    //,cke_p`i
                    //,address_p`i
                    ,wrdata_en_p6
                    ,cs_p6
                    ,cke_p6
                    ,dq0_wrdata_p6[AWIDTH-1:0]
                    //,dce_p`i
                    //,cs_p`i
                    //,cke_p`i
                    //,address_p`i
                    ,wrdata_en_p7
                    ,cs_p7
                    ,cke_p7
                    ,dq0_wrdata_p7[AWIDTH-1:0]
                    ,rddata_en_p0
                    ,rddata_cs_p0
                    ,wck_toggle_p0
                    ,wck_en_p0
                    ,wck_cs_p0
                    ,wrdata_en_p0
                    ,parity_in_p0
                    ,wrdata_cs_p0
                    ,dq0_wrdata_mask_p0
                    ,dq0_wrdata_p0
                    ,dq1_wrdata_mask_p0
                    ,dq1_wrdata_p0
                    ,dq2_wrdata_mask_p0
                    ,dq2_wrdata_p0
                    ,dq3_wrdata_mask_p0
                    ,dq3_wrdata_p0
                    ,rddata_en_p1
                    ,rddata_cs_p1
                    ,wck_toggle_p1
                    ,wck_en_p1
                    ,wck_cs_p1
                    ,wrdata_en_p1
                    ,parity_in_p1
                    ,wrdata_cs_p1
                    ,dq0_wrdata_mask_p1
                    ,dq0_wrdata_p1
                    ,dq1_wrdata_mask_p1
                    ,dq1_wrdata_p1
                    ,dq2_wrdata_mask_p1
                    ,dq2_wrdata_p1
                    ,dq3_wrdata_mask_p1
                    ,dq3_wrdata_p1
                    ,rddata_en_p2
                    ,rddata_cs_p2
                    ,wck_toggle_p2
                    ,wck_en_p2
                    ,wck_cs_p2
                    ,wrdata_en_p2
                    ,parity_in_p2
                    ,wrdata_cs_p2
                    ,dq0_wrdata_mask_p2
                    ,dq0_wrdata_p2
                    ,dq1_wrdata_mask_p2
                    ,dq1_wrdata_p2
                    ,dq2_wrdata_mask_p2
                    ,dq2_wrdata_p2
                    ,dq3_wrdata_mask_p2
                    ,dq3_wrdata_p2
                    ,rddata_en_p3
                    ,rddata_cs_p3
                    ,wck_toggle_p3
                    ,wck_en_p3
                    ,wck_cs_p3
                    ,wrdata_en_p3
                    ,parity_in_p3
                    ,wrdata_cs_p3
                    ,dq0_wrdata_mask_p3
                    ,dq0_wrdata_p3
                    ,dq1_wrdata_mask_p3
                    ,dq1_wrdata_p3
                    ,dq2_wrdata_mask_p3
                    ,dq2_wrdata_p3
                    ,dq3_wrdata_mask_p3
                    ,dq3_wrdata_p3
                    ,rddata_en_p4
                    ,rddata_cs_p4
                    ,wck_toggle_p4
                    ,wck_en_p4
                    ,wck_cs_p4
                    ,wrdata_en_p4
                    ,parity_in_p4
                    ,wrdata_cs_p4
                    ,dq0_wrdata_mask_p4
                    ,dq0_wrdata_p4
                    ,dq1_wrdata_mask_p4
                    ,dq1_wrdata_p4
                    ,dq2_wrdata_mask_p4
                    ,dq2_wrdata_p4
                    ,dq3_wrdata_mask_p4
                    ,dq3_wrdata_p4
                    ,rddata_en_p5
                    ,rddata_cs_p5
                    ,wck_toggle_p5
                    ,wck_en_p5
                    ,wck_cs_p5
                    ,wrdata_en_p5
                    ,parity_in_p5
                    ,wrdata_cs_p5
                    ,dq0_wrdata_mask_p5
                    ,dq0_wrdata_p5
                    ,dq1_wrdata_mask_p5
                    ,dq1_wrdata_p5
                    ,dq2_wrdata_mask_p5
                    ,dq2_wrdata_p5
                    ,dq3_wrdata_mask_p5
                    ,dq3_wrdata_p5
                    ,rddata_en_p6
                    ,rddata_cs_p6
                    ,wck_toggle_p6
                    ,wck_en_p6
                    ,wck_cs_p6
                    ,wrdata_en_p6
                    ,parity_in_p6
                    ,wrdata_cs_p6
                    ,dq0_wrdata_mask_p6
                    ,dq0_wrdata_p6
                    ,dq1_wrdata_mask_p6
                    ,dq1_wrdata_p6
                    ,dq2_wrdata_mask_p6
                    ,dq2_wrdata_p6
                    ,dq3_wrdata_mask_p6
                    ,dq3_wrdata_p6
                    ,rddata_en_p7
                    ,rddata_cs_p7
                    ,wck_toggle_p7
                    ,wck_en_p7
                    ,wck_cs_p7
                    ,wrdata_en_p7
                    ,parity_in_p7
                    ,wrdata_cs_p7
                    ,dq0_wrdata_mask_p7
                    ,dq0_wrdata_p7
                    ,dq1_wrdata_mask_p7
                    ,dq1_wrdata_p7
                    ,dq2_wrdata_mask_p7
                    ,dq2_wrdata_p7
                    ,dq3_wrdata_mask_p7
                    ,dq3_wrdata_p7
                };
                //$display ("INFO: GEN_DFI_PACKET [%d] %d : DQ0{ p3 p2 p1 p0 } = { %x %x %x %x }  DQ1{ p3 p2 p1 p0 } = { %x %x %x %x }", i, j, dq0_wrdata_p3, dq0_wrdata_p2, dq0_wrdata_p1, dq0_wrdata_p0, dq1_wrdata_p3, dq1_wrdata_p2, dq1_wrdata_p1, dq1_wrdata_p0  );
                ts           = ts + 4'd1;
                //j = j+NUM_DFI_WPH;
                i=i+1;
            end
            // If transaction ends in this DFI buffer entry
            else if (j+NUM_DFI_WPH > beat_cnt && j <= beat_cnt)
            begin
                {
                    parity_in_p7,
                    parity_in_p6,
                    parity_in_p5,
                    parity_in_p4,
                    parity_in_p3,
                    parity_in_p2,
                    parity_in_p1,
                parity_in_p0 } = {NUM_DFI_WPH{1'b1}} >> ( NUM_DFI_WPH - (beat_cnt-j-(wr_pnum-par_pnum))) ;

                {
                    wrdata_cs_p7,
                    wrdata_cs_p6,
                    wrdata_cs_p5,
                    wrdata_cs_p4,
                    wrdata_cs_p3,
                    wrdata_cs_p2,
                    wrdata_cs_p1,
                wrdata_cs_p0 } = {NUM_DFI_WPH{rank_sel}} >> ( (NUM_DFI_WPH - (beat_cnt-j-(wr_pnum-wrcs_pnum)))*2 ) ;

                {
                    wck_cs_p7,
                    wck_cs_p6,
                    wck_cs_p5,
                    wck_cs_p4,
                    wck_cs_p3,
                    wck_cs_p2,
                    wck_cs_p1,
                wck_cs_p0 } = {NUM_DFI_WPH{rank_sel}} >> ( (NUM_DFI_WPH - (beat_cnt-j-(wr_pnum-wckcs_pnum)))*2 ) ;

                {
                    wck_en_p7,
                    wck_en_p6,
                    wck_en_p5,
                    wck_en_p4,
                    wck_en_p3,
                    wck_en_p2,
                    wck_en_p1,
                wck_en_p0 } = {NUM_DFI_WPH{1'b1}} >> ( NUM_DFI_WPH -(beat_cnt-j-(wr_pnum-wcken_pnum)) ) ;

                {
                    wrdata_en_p7,
                    wrdata_en_p6,
                    wrdata_en_p5,
                    wrdata_en_p4,
                    wrdata_en_p3,
                    wrdata_en_p2,
                    wrdata_en_p1,
                    //wrdata_en_p0 } = {NUM_DFI_WPH{1'b1}} >> ( NUM_DFI_WPH - (beat_cnt-j-(wr_pnum-wren_pnum)) ) ;
                wrdata_en_p0 } = wr_en [j +: NUM_DFI_WPH ];

                {
                    rddata_en_p7,
                    rddata_en_p6,
                    rddata_en_p5,
                    rddata_en_p4,
                    rddata_en_p3,
                    rddata_en_p2,
                    rddata_en_p1,
                    // rddata_en_p0 } = {NUM_DFI_WPH{1'b1}} >> ( NUM_DFI_WPH - (beat_cnt-j-(wr_pnum-rden_pnum))) ;
                rddata_en_p0 } = wr_en [j +: NUM_DFI_WPH ];

                {
                    wck_toggle_p7,
                    wck_toggle_p6,
                    wck_toggle_p5,
                    wck_toggle_p4,
                    wck_toggle_p3,
                    wck_toggle_p2,
                    wck_toggle_p1,
                wck_toggle_p0 } = WCKT_FT >> ( NUM_DFI_WPH*TWIDTH - ((beat_cnt-j-(wr_pnum-wckt_pnum))*TWIDTH) ) ;

                {
                    rddata_cs_p7,
                    rddata_cs_p6,
                    rddata_cs_p5,
                    rddata_cs_p4,
                    rddata_cs_p3,
                    rddata_cs_p2,
                    rddata_cs_p1,
                rddata_cs_p0 } = {NUM_DFI_WPH{rank_sel}} >> ( (NUM_DFI_WPH - (beat_cnt-j-(wr_pnum-wrcs_pnum)))*2 ) ;

                {
                    dq0_wrdata_p7,
                    dq0_wrdata_p6,
                    dq0_wrdata_p5,
                    dq0_wrdata_p4,
                    dq0_wrdata_p3,
                    dq0_wrdata_p2,
                    dq0_wrdata_p1,
                    //dq`j::_wrdata_p0 }   = data[(j*SWIDTH) +: (NUM_DFI_WPH*SWIDTH)] && (32'hFFFFFFFF >> (NUM_DFI_WPH*SWIDTH - ((beat_cnt-j)*SWIDTH))) ;
                dq0_wrdata_p0 }   = data[(j*SWIDTH) +: (NUM_DFI_WPH*SWIDTH)] ;
                {
                    dq1_wrdata_p7,
                    dq1_wrdata_p6,
                    dq1_wrdata_p5,
                    dq1_wrdata_p4,
                    dq1_wrdata_p3,
                    dq1_wrdata_p2,
                    dq1_wrdata_p1,
                    //dq`j::_wrdata_p0 }   = data[(j*SWIDTH) +: (NUM_DFI_WPH*SWIDTH)] && (32'hFFFFFFFF >> (NUM_DFI_WPH*SWIDTH - ((beat_cnt-j)*SWIDTH))) ;
                dq1_wrdata_p0 }   = data[(j*SWIDTH) +: (NUM_DFI_WPH*SWIDTH)] ;
                {
                    dq2_wrdata_p7,
                    dq2_wrdata_p6,
                    dq2_wrdata_p5,
                    dq2_wrdata_p4,
                    dq2_wrdata_p3,
                    dq2_wrdata_p2,
                    dq2_wrdata_p1,
                    //dq`j::_wrdata_p0 }   = data[(j*SWIDTH) +: (NUM_DFI_WPH*SWIDTH)] && (32'hFFFFFFFF >> (NUM_DFI_WPH*SWIDTH - ((beat_cnt-j)*SWIDTH))) ;
                dq2_wrdata_p0 }   = data[(j*SWIDTH) +: (NUM_DFI_WPH*SWIDTH)] ;
                {
                    dq3_wrdata_p7,
                    dq3_wrdata_p6,
                    dq3_wrdata_p5,
                    dq3_wrdata_p4,
                    dq3_wrdata_p3,
                    dq3_wrdata_p2,
                    dq3_wrdata_p1,
                    //dq`j::_wrdata_p0 }   = data[(j*SWIDTH) +: (NUM_DFI_WPH*SWIDTH)] && (32'hFFFFFFFF >> (NUM_DFI_WPH*SWIDTH - ((beat_cnt-j)*SWIDTH))) ;
                dq3_wrdata_p0 }   = data[(j*SWIDTH) +: (NUM_DFI_WPH*SWIDTH)] ;

                {
                    dce_p7,
                    dce_p6,
                    dce_p5,
                    dce_p4,
                    dce_p3,
                    dce_p2,
                    dce_p1,
                dce_p0 } = ca_dce[j+:NUM_DFI_WPH] ;
                {
                    cke_p7,
                    cke_p6,
                    cke_p5,
                    cke_p4,
                    cke_p3,
                    cke_p2,
                    cke_p1,
                cke_p0 } = ca_cke[(j*2) +: (NUM_DFI_WPH*2)]; //{NUM_DFI_WPH{2'h3}} >> 2*( NUM_DFI_WPH -(beat_cnt-j-(wr_pnum-cacke_pnum)) ) ;
                {
                    cs_p7,
                    cs_p6,
                    cs_p5,
                    cs_p4,
                    cs_p3,
                    cs_p2,
                    cs_p1,
                cs_p0 } = ca_cs[(j*2) +: (NUM_DFI_WPH*2)] ;

                {
                    address_p7,
                    address_p6,
                    address_p5,
                    address_p4,
                    address_p3,
                    address_p2,
                    address_p1,
                address_p0 } = ca_addr[(j*AWIDTH) +: (NUM_DFI_WPH*AWIDTH)] ;

                wrd_packet[i] =   {
                    ts
                    //,dce_p`i
                    //,cs_p`i
                    //,cke_p`i
                    //,address_p`i
                    ,wrdata_en_p0
                    ,cs_p0
                    ,cke_p0
                    ,dq0_wrdata_p0[AWIDTH-1:0]
                    //,dce_p`i
                    //,cs_p`i
                    //,cke_p`i
                    //,address_p`i
                    ,wrdata_en_p1
                    ,cs_p1
                    ,cke_p1
                    ,dq0_wrdata_p1[AWIDTH-1:0]
                    //,dce_p`i
                    //,cs_p`i
                    //,cke_p`i
                    //,address_p`i
                    ,wrdata_en_p2
                    ,cs_p2
                    ,cke_p2
                    ,dq0_wrdata_p2[AWIDTH-1:0]
                    //,dce_p`i
                    //,cs_p`i
                    //,cke_p`i
                    //,address_p`i
                    ,wrdata_en_p3
                    ,cs_p3
                    ,cke_p3
                    ,dq0_wrdata_p3[AWIDTH-1:0]
                    //,dce_p`i
                    //,cs_p`i
                    //,cke_p`i
                    //,address_p`i
                    ,wrdata_en_p4
                    ,cs_p4
                    ,cke_p4
                    ,dq0_wrdata_p4[AWIDTH-1:0]
                    //,dce_p`i
                    //,cs_p`i
                    //,cke_p`i
                    //,address_p`i
                    ,wrdata_en_p5
                    ,cs_p5
                    ,cke_p5
                    ,dq0_wrdata_p5[AWIDTH-1:0]
                    //,dce_p`i
                    //,cs_p`i
                    //,cke_p`i
                    //,address_p`i
                    ,wrdata_en_p6
                    ,cs_p6
                    ,cke_p6
                    ,dq0_wrdata_p6[AWIDTH-1:0]
                    //,dce_p`i
                    //,cs_p`i
                    //,cke_p`i
                    //,address_p`i
                    ,wrdata_en_p7
                    ,cs_p7
                    ,cke_p7
                    ,dq0_wrdata_p7[AWIDTH-1:0]
                    ,rddata_en_p0
                    ,rddata_cs_p0
                    ,wck_toggle_p0
                    ,wck_en_p0
                    ,wck_cs_p0
                    ,wrdata_en_p0
                    ,parity_in_p0
                    ,wrdata_cs_p0
                    ,dq0_wrdata_mask_p0
                    ,dq0_wrdata_p0
                    ,dq1_wrdata_mask_p0
                    ,dq1_wrdata_p0
                    ,dq2_wrdata_mask_p0
                    ,dq2_wrdata_p0
                    ,dq3_wrdata_mask_p0
                    ,dq3_wrdata_p0
                    ,rddata_en_p1
                    ,rddata_cs_p1
                    ,wck_toggle_p1
                    ,wck_en_p1
                    ,wck_cs_p1
                    ,wrdata_en_p1
                    ,parity_in_p1
                    ,wrdata_cs_p1
                    ,dq0_wrdata_mask_p1
                    ,dq0_wrdata_p1
                    ,dq1_wrdata_mask_p1
                    ,dq1_wrdata_p1
                    ,dq2_wrdata_mask_p1
                    ,dq2_wrdata_p1
                    ,dq3_wrdata_mask_p1
                    ,dq3_wrdata_p1
                    ,rddata_en_p2
                    ,rddata_cs_p2
                    ,wck_toggle_p2
                    ,wck_en_p2
                    ,wck_cs_p2
                    ,wrdata_en_p2
                    ,parity_in_p2
                    ,wrdata_cs_p2
                    ,dq0_wrdata_mask_p2
                    ,dq0_wrdata_p2
                    ,dq1_wrdata_mask_p2
                    ,dq1_wrdata_p2
                    ,dq2_wrdata_mask_p2
                    ,dq2_wrdata_p2
                    ,dq3_wrdata_mask_p2
                    ,dq3_wrdata_p2
                    ,rddata_en_p3
                    ,rddata_cs_p3
                    ,wck_toggle_p3
                    ,wck_en_p3
                    ,wck_cs_p3
                    ,wrdata_en_p3
                    ,parity_in_p3
                    ,wrdata_cs_p3
                    ,dq0_wrdata_mask_p3
                    ,dq0_wrdata_p3
                    ,dq1_wrdata_mask_p3
                    ,dq1_wrdata_p3
                    ,dq2_wrdata_mask_p3
                    ,dq2_wrdata_p3
                    ,dq3_wrdata_mask_p3
                    ,dq3_wrdata_p3
                    ,rddata_en_p4
                    ,rddata_cs_p4
                    ,wck_toggle_p4
                    ,wck_en_p4
                    ,wck_cs_p4
                    ,wrdata_en_p4
                    ,parity_in_p4
                    ,wrdata_cs_p4
                    ,dq0_wrdata_mask_p4
                    ,dq0_wrdata_p4
                    ,dq1_wrdata_mask_p4
                    ,dq1_wrdata_p4
                    ,dq2_wrdata_mask_p4
                    ,dq2_wrdata_p4
                    ,dq3_wrdata_mask_p4
                    ,dq3_wrdata_p4
                    ,rddata_en_p5
                    ,rddata_cs_p5
                    ,wck_toggle_p5
                    ,wck_en_p5
                    ,wck_cs_p5
                    ,wrdata_en_p5
                    ,parity_in_p5
                    ,wrdata_cs_p5
                    ,dq0_wrdata_mask_p5
                    ,dq0_wrdata_p5
                    ,dq1_wrdata_mask_p5
                    ,dq1_wrdata_p5
                    ,dq2_wrdata_mask_p5
                    ,dq2_wrdata_p5
                    ,dq3_wrdata_mask_p5
                    ,dq3_wrdata_p5
                    ,rddata_en_p6
                    ,rddata_cs_p6
                    ,wck_toggle_p6
                    ,wck_en_p6
                    ,wck_cs_p6
                    ,wrdata_en_p6
                    ,parity_in_p6
                    ,wrdata_cs_p6
                    ,dq0_wrdata_mask_p6
                    ,dq0_wrdata_p6
                    ,dq1_wrdata_mask_p6
                    ,dq1_wrdata_p6
                    ,dq2_wrdata_mask_p6
                    ,dq2_wrdata_p6
                    ,dq3_wrdata_mask_p6
                    ,dq3_wrdata_p6
                    ,rddata_en_p7
                    ,rddata_cs_p7
                    ,wck_toggle_p7
                    ,wck_en_p7
                    ,wck_cs_p7
                    ,wrdata_en_p7
                    ,parity_in_p7
                    ,wrdata_cs_p7
                    ,dq0_wrdata_mask_p7
                    ,dq0_wrdata_p7
                    ,dq1_wrdata_mask_p7
                    ,dq1_wrdata_p7
                    ,dq2_wrdata_mask_p7
                    ,dq2_wrdata_p7
                    ,dq3_wrdata_mask_p7
                    ,dq3_wrdata_p7
                };
                //$display ("INFO: GEN_DFI_PACKET [%d] %d : DQ0{ p3 p2 p1 p0 } = { %x %x %x %x }  DQ1{ p3 p2 p1 p0 } = { %x %x %x %x }", i, j, dq0_wrdata_p3, dq0_wrdata_p2, dq0_wrdata_p1, dq0_wrdata_p0, dq1_wrdata_p3, dq1_wrdata_p2, dq1_wrdata_p1, dq1_wrdata_p0  );
                i=i+1;
                ts = ts + 1;
            end
            // If transaction is not complete in this DFI buf entry
            else begin
                {
                    parity_in_p7,
                    parity_in_p6,
                    parity_in_p5,
                    parity_in_p4,
                    parity_in_p3,
                    parity_in_p2,
                    parity_in_p1,
                parity_in_p0 } = {NUM_DFI_WPH{1'b1}}  ;

                {
                    wrdata_cs_p7,
                    wrdata_cs_p6,
                    wrdata_cs_p5,
                    wrdata_cs_p4,
                    wrdata_cs_p3,
                    wrdata_cs_p2,
                    wrdata_cs_p1,
                wrdata_cs_p0 } = {NUM_DFI_WPH{rank_sel}}  ;

                {
                    wck_cs_p7,
                    wck_cs_p6,
                    wck_cs_p5,
                    wck_cs_p4,
                    wck_cs_p3,
                    wck_cs_p2,
                    wck_cs_p1,
                wck_cs_p0 } = {NUM_DFI_WPH{rank_sel}} ;

                {
                    wck_en_p7,
                    wck_en_p6,
                    wck_en_p5,
                    wck_en_p4,
                    wck_en_p3,
                    wck_en_p2,
                    wck_en_p1,
                wck_en_p0 } = {NUM_DFI_WPH{1'b1}}  ;

                {
                    wrdata_en_p7,
                    wrdata_en_p6,
                    wrdata_en_p5,
                    wrdata_en_p4,
                    wrdata_en_p3,
                    wrdata_en_p2,
                    wrdata_en_p1,
                    //wrdata_en_p0 } = {NUM_DFI_WPH{1'b1}}  ;
                wrdata_en_p0 } = wr_en[j+:NUM_DFI_WPH]  ;

                {
                    rddata_en_p7,
                    rddata_en_p6,
                    rddata_en_p5,
                    rddata_en_p4,
                    rddata_en_p3,
                    rddata_en_p2,
                    rddata_en_p1,
                rddata_en_p0 } = wr_en[j+:NUM_DFI_WPH]  ;

                {
                    wck_toggle_p7,
                    wck_toggle_p6,
                    wck_toggle_p5,
                    wck_toggle_p4,
                    wck_toggle_p3,
                    wck_toggle_p2,
                    wck_toggle_p1,
                wck_toggle_p0 } = WCKT_FT  ;

                {
                    rddata_cs_p7,
                    rddata_cs_p6,
                    rddata_cs_p5,
                    rddata_cs_p4,
                    rddata_cs_p3,
                    rddata_cs_p2,
                    rddata_cs_p1,
                rddata_cs_p0 } = {NUM_DFI_WPH{rank_sel}}  ;

                {
                    dq0_wrdata_p7,
                    dq0_wrdata_p6,
                    dq0_wrdata_p5,
                    dq0_wrdata_p4,
                    dq0_wrdata_p3,
                    dq0_wrdata_p2,
                    dq0_wrdata_p1,
                dq0_wrdata_p0 }   = data[(j*SWIDTH) +: (NUM_DFI_WPH*SWIDTH)] ;
                {
                    dq1_wrdata_p7,
                    dq1_wrdata_p6,
                    dq1_wrdata_p5,
                    dq1_wrdata_p4,
                    dq1_wrdata_p3,
                    dq1_wrdata_p2,
                    dq1_wrdata_p1,
                dq1_wrdata_p0 }   = data[(j*SWIDTH) +: (NUM_DFI_WPH*SWIDTH)] ;
                {
                    dq2_wrdata_p7,
                    dq2_wrdata_p6,
                    dq2_wrdata_p5,
                    dq2_wrdata_p4,
                    dq2_wrdata_p3,
                    dq2_wrdata_p2,
                    dq2_wrdata_p1,
                dq2_wrdata_p0 }   = data[(j*SWIDTH) +: (NUM_DFI_WPH*SWIDTH)] ;
                {
                    dq3_wrdata_p7,
                    dq3_wrdata_p6,
                    dq3_wrdata_p5,
                    dq3_wrdata_p4,
                    dq3_wrdata_p3,
                    dq3_wrdata_p2,
                    dq3_wrdata_p1,
                dq3_wrdata_p0 }   = data[(j*SWIDTH) +: (NUM_DFI_WPH*SWIDTH)] ;

                {
                    dce_p7,
                    dce_p6,
                    dce_p5,
                    dce_p4,
                    dce_p3,
                    dce_p2,
                    dce_p1,
                dce_p0 } = ca_dce[j+:NUM_DFI_WPH] ;
                {
                    cke_p7,
                    cke_p6,
                    cke_p5,
                    cke_p4,
                    cke_p3,
                    cke_p2,
                    cke_p1,
                cke_p0 } = ca_cke[(j*2) +: (NUM_DFI_WPH*2)] ;
                {
                    cs_p7,
                    cs_p6,
                    cs_p5,
                    cs_p4,
                    cs_p3,
                    cs_p2,
                    cs_p1,
                cs_p0 } = ca_cs[(j*2) +: (NUM_DFI_WPH*2)] ;

                {
                    address_p7,
                    address_p6,
                    address_p5,
                    address_p4,
                    address_p3,
                    address_p2,
                    address_p1,
                address_p0 } = ca_addr[(j*AWIDTH) +: (NUM_DFI_WPH*AWIDTH)] ;

                wrd_packet[i] =   {
                    ts
                    //,dce_p`i
                    //,cs_p`i
                    //,cke_p`i
                    //,address_p`i
                    ,wrdata_en_p0
                    ,cs_p0
                    ,cke_p0
                    ,dq0_wrdata_p0[AWIDTH-1:0]
                    //,dce_p`i
                    //,cs_p`i
                    //,cke_p`i
                    //,address_p`i
                    ,wrdata_en_p1
                    ,cs_p1
                    ,cke_p1
                    ,dq0_wrdata_p1[AWIDTH-1:0]
                    //,dce_p`i
                    //,cs_p`i
                    //,cke_p`i
                    //,address_p`i
                    ,wrdata_en_p2
                    ,cs_p2
                    ,cke_p2
                    ,dq0_wrdata_p2[AWIDTH-1:0]
                    //,dce_p`i
                    //,cs_p`i
                    //,cke_p`i
                    //,address_p`i
                    ,wrdata_en_p3
                    ,cs_p3
                    ,cke_p3
                    ,dq0_wrdata_p3[AWIDTH-1:0]
                    //,dce_p`i
                    //,cs_p`i
                    //,cke_p`i
                    //,address_p`i
                    ,wrdata_en_p4
                    ,cs_p4
                    ,cke_p4
                    ,dq0_wrdata_p4[AWIDTH-1:0]
                    //,dce_p`i
                    //,cs_p`i
                    //,cke_p`i
                    //,address_p`i
                    ,wrdata_en_p5
                    ,cs_p5
                    ,cke_p5
                    ,dq0_wrdata_p5[AWIDTH-1:0]
                    //,dce_p`i
                    //,cs_p`i
                    //,cke_p`i
                    //,address_p`i
                    ,wrdata_en_p6
                    ,cs_p6
                    ,cke_p6
                    ,dq0_wrdata_p6[AWIDTH-1:0]
                    //,dce_p`i
                    //,cs_p`i
                    //,cke_p`i
                    //,address_p`i
                    ,wrdata_en_p7
                    ,cs_p7
                    ,cke_p7
                    ,dq0_wrdata_p7[AWIDTH-1:0]
                    ,rddata_en_p0
                    ,rddata_cs_p0
                    ,wck_toggle_p0
                    ,wck_en_p0
                    ,wck_cs_p0
                    ,wrdata_en_p0
                    ,parity_in_p0
                    ,wrdata_cs_p0
                    ,dq0_wrdata_mask_p0
                    ,dq0_wrdata_p0
                    ,dq1_wrdata_mask_p0
                    ,dq1_wrdata_p0
                    ,dq2_wrdata_mask_p0
                    ,dq2_wrdata_p0
                    ,dq3_wrdata_mask_p0
                    ,dq3_wrdata_p0
                    ,rddata_en_p1
                    ,rddata_cs_p1
                    ,wck_toggle_p1
                    ,wck_en_p1
                    ,wck_cs_p1
                    ,wrdata_en_p1
                    ,parity_in_p1
                    ,wrdata_cs_p1
                    ,dq0_wrdata_mask_p1
                    ,dq0_wrdata_p1
                    ,dq1_wrdata_mask_p1
                    ,dq1_wrdata_p1
                    ,dq2_wrdata_mask_p1
                    ,dq2_wrdata_p1
                    ,dq3_wrdata_mask_p1
                    ,dq3_wrdata_p1
                    ,rddata_en_p2
                    ,rddata_cs_p2
                    ,wck_toggle_p2
                    ,wck_en_p2
                    ,wck_cs_p2
                    ,wrdata_en_p2
                    ,parity_in_p2
                    ,wrdata_cs_p2
                    ,dq0_wrdata_mask_p2
                    ,dq0_wrdata_p2
                    ,dq1_wrdata_mask_p2
                    ,dq1_wrdata_p2
                    ,dq2_wrdata_mask_p2
                    ,dq2_wrdata_p2
                    ,dq3_wrdata_mask_p2
                    ,dq3_wrdata_p2
                    ,rddata_en_p3
                    ,rddata_cs_p3
                    ,wck_toggle_p3
                    ,wck_en_p3
                    ,wck_cs_p3
                    ,wrdata_en_p3
                    ,parity_in_p3
                    ,wrdata_cs_p3
                    ,dq0_wrdata_mask_p3
                    ,dq0_wrdata_p3
                    ,dq1_wrdata_mask_p3
                    ,dq1_wrdata_p3
                    ,dq2_wrdata_mask_p3
                    ,dq2_wrdata_p3
                    ,dq3_wrdata_mask_p3
                    ,dq3_wrdata_p3
                    ,rddata_en_p4
                    ,rddata_cs_p4
                    ,wck_toggle_p4
                    ,wck_en_p4
                    ,wck_cs_p4
                    ,wrdata_en_p4
                    ,parity_in_p4
                    ,wrdata_cs_p4
                    ,dq0_wrdata_mask_p4
                    ,dq0_wrdata_p4
                    ,dq1_wrdata_mask_p4
                    ,dq1_wrdata_p4
                    ,dq2_wrdata_mask_p4
                    ,dq2_wrdata_p4
                    ,dq3_wrdata_mask_p4
                    ,dq3_wrdata_p4
                    ,rddata_en_p5
                    ,rddata_cs_p5
                    ,wck_toggle_p5
                    ,wck_en_p5
                    ,wck_cs_p5
                    ,wrdata_en_p5
                    ,parity_in_p5
                    ,wrdata_cs_p5
                    ,dq0_wrdata_mask_p5
                    ,dq0_wrdata_p5
                    ,dq1_wrdata_mask_p5
                    ,dq1_wrdata_p5
                    ,dq2_wrdata_mask_p5
                    ,dq2_wrdata_p5
                    ,dq3_wrdata_mask_p5
                    ,dq3_wrdata_p5
                    ,rddata_en_p6
                    ,rddata_cs_p6
                    ,wck_toggle_p6
                    ,wck_en_p6
                    ,wck_cs_p6
                    ,wrdata_en_p6
                    ,parity_in_p6
                    ,wrdata_cs_p6
                    ,dq0_wrdata_mask_p6
                    ,dq0_wrdata_p6
                    ,dq1_wrdata_mask_p6
                    ,dq1_wrdata_p6
                    ,dq2_wrdata_mask_p6
                    ,dq2_wrdata_p6
                    ,dq3_wrdata_mask_p6
                    ,dq3_wrdata_p6
                    ,rddata_en_p7
                    ,rddata_cs_p7
                    ,wck_toggle_p7
                    ,wck_en_p7
                    ,wck_cs_p7
                    ,wrdata_en_p7
                    ,parity_in_p7
                    ,wrdata_cs_p7
                    ,dq0_wrdata_mask_p7
                    ,dq0_wrdata_p7
                    ,dq1_wrdata_mask_p7
                    ,dq1_wrdata_p7
                    ,dq2_wrdata_mask_p7
                    ,dq2_wrdata_p7
                    ,dq3_wrdata_mask_p7
                    ,dq3_wrdata_p7
                };
                //$display ("INFO: GEN_DFI_PACKET [%d] %d : DQ0{ p3 p2 p1 p0 } = { %x %x %x %x }  DQ1{ p3 p2 p1 p0 } = { %x %x %x %x }", i, j, dq0_wrdata_p3, dq0_wrdata_p2, dq0_wrdata_p1, dq0_wrdata_p0, dq1_wrdata_p3, dq1_wrdata_p2, dq1_wrdata_p1, dq1_wrdata_p0  );
                i=i+1;
                ts = ts + 1;
            end
        end

        if (i <= N) begin
            dce_p0             = '0 ;
            address_p0         = '0 ;
            cke_p0             = '0 ;
            cs_p0              = '0 ;
            dce_p1             = '0 ;
            address_p1         = '0 ;
            cke_p1             = '0 ;
            cs_p1              = '0 ;
            dce_p2             = '0 ;
            address_p2         = '0 ;
            cke_p2             = '0 ;
            cs_p2              = '0 ;
            dce_p3             = '0 ;
            address_p3         = '0 ;
            cke_p3             = '0 ;
            cs_p3              = '0 ;
            dce_p4             = '0 ;
            address_p4         = '0 ;
            cke_p4             = '0 ;
            cs_p4              = '0 ;
            dce_p5             = '0 ;
            address_p5         = '0 ;
            cke_p5             = '0 ;
            cs_p5              = '0 ;
            dce_p6             = '0 ;
            address_p6         = '0 ;
            cke_p6             = '0 ;
            cs_p6              = '0 ;
            dce_p7             = '0 ;
            address_p7         = '0 ;
            cke_p7             = '0 ;
            cs_p7              = '0 ;
            dq0_wrdata_p0      = '0;
            dq0_wrdata_mask_p0 = '0;
            dq1_wrdata_p0      = '0;
            dq1_wrdata_mask_p0 = '0;
            dq2_wrdata_p0      = '0;
            dq2_wrdata_mask_p0 = '0;
            dq3_wrdata_p0      = '0;
            dq3_wrdata_mask_p0 = '0;
            parity_in_p0       = '0;
            wrdata_cs_p0       = '0;
            wrdata_en_p0       = '0;
            wck_cs_p0          = '0;
            wck_en_p0          = '0;
            wck_toggle_p0      = '0;
            rddata_cs_p0       = '0;
            rddata_en_p0       = '0;
            dq0_wrdata_p1      = '0;
            dq0_wrdata_mask_p1 = '0;
            dq1_wrdata_p1      = '0;
            dq1_wrdata_mask_p1 = '0;
            dq2_wrdata_p1      = '0;
            dq2_wrdata_mask_p1 = '0;
            dq3_wrdata_p1      = '0;
            dq3_wrdata_mask_p1 = '0;
            parity_in_p1       = '0;
            wrdata_cs_p1       = '0;
            wrdata_en_p1       = '0;
            wck_cs_p1          = '0;
            wck_en_p1          = '0;
            wck_toggle_p1      = '0;
            rddata_cs_p1       = '0;
            rddata_en_p1       = '0;
            dq0_wrdata_p2      = '0;
            dq0_wrdata_mask_p2 = '0;
            dq1_wrdata_p2      = '0;
            dq1_wrdata_mask_p2 = '0;
            dq2_wrdata_p2      = '0;
            dq2_wrdata_mask_p2 = '0;
            dq3_wrdata_p2      = '0;
            dq3_wrdata_mask_p2 = '0;
            parity_in_p2       = '0;
            wrdata_cs_p2       = '0;
            wrdata_en_p2       = '0;
            wck_cs_p2          = '0;
            wck_en_p2          = '0;
            wck_toggle_p2      = '0;
            rddata_cs_p2       = '0;
            rddata_en_p2       = '0;
            dq0_wrdata_p3      = '0;
            dq0_wrdata_mask_p3 = '0;
            dq1_wrdata_p3      = '0;
            dq1_wrdata_mask_p3 = '0;
            dq2_wrdata_p3      = '0;
            dq2_wrdata_mask_p3 = '0;
            dq3_wrdata_p3      = '0;
            dq3_wrdata_mask_p3 = '0;
            parity_in_p3       = '0;
            wrdata_cs_p3       = '0;
            wrdata_en_p3       = '0;
            wck_cs_p3          = '0;
            wck_en_p3          = '0;
            wck_toggle_p3      = '0;
            rddata_cs_p3       = '0;
            rddata_en_p3       = '0;
            dq0_wrdata_p4      = '0;
            dq0_wrdata_mask_p4 = '0;
            dq1_wrdata_p4      = '0;
            dq1_wrdata_mask_p4 = '0;
            dq2_wrdata_p4      = '0;
            dq2_wrdata_mask_p4 = '0;
            dq3_wrdata_p4      = '0;
            dq3_wrdata_mask_p4 = '0;
            parity_in_p4       = '0;
            wrdata_cs_p4       = '0;
            wrdata_en_p4       = '0;
            wck_cs_p4          = '0;
            wck_en_p4          = '0;
            wck_toggle_p4      = '0;
            rddata_cs_p4       = '0;
            rddata_en_p4       = '0;
            dq0_wrdata_p5      = '0;
            dq0_wrdata_mask_p5 = '0;
            dq1_wrdata_p5      = '0;
            dq1_wrdata_mask_p5 = '0;
            dq2_wrdata_p5      = '0;
            dq2_wrdata_mask_p5 = '0;
            dq3_wrdata_p5      = '0;
            dq3_wrdata_mask_p5 = '0;
            parity_in_p5       = '0;
            wrdata_cs_p5       = '0;
            wrdata_en_p5       = '0;
            wck_cs_p5          = '0;
            wck_en_p5          = '0;
            wck_toggle_p5      = '0;
            rddata_cs_p5       = '0;
            rddata_en_p5       = '0;
            dq0_wrdata_p6      = '0;
            dq0_wrdata_mask_p6 = '0;
            dq1_wrdata_p6      = '0;
            dq1_wrdata_mask_p6 = '0;
            dq2_wrdata_p6      = '0;
            dq2_wrdata_mask_p6 = '0;
            dq3_wrdata_p6      = '0;
            dq3_wrdata_mask_p6 = '0;
            parity_in_p6       = '0;
            wrdata_cs_p6       = '0;
            wrdata_en_p6       = '0;
            wck_cs_p6          = '0;
            wck_en_p6          = '0;
            wck_toggle_p6      = '0;
            rddata_cs_p6       = '0;
            rddata_en_p6       = '0;
            dq0_wrdata_p7      = '0;
            dq0_wrdata_mask_p7 = '0;
            dq1_wrdata_p7      = '0;
            dq1_wrdata_mask_p7 = '0;
            dq2_wrdata_p7      = '0;
            dq2_wrdata_mask_p7 = '0;
            dq3_wrdata_p7      = '0;
            dq3_wrdata_mask_p7 = '0;
            parity_in_p7       = '0;
            wrdata_cs_p7       = '0;
            wrdata_en_p7       = '0;
            wck_cs_p7          = '0;
            wck_en_p7          = '0;
            wck_toggle_p7      = '0;
            rddata_cs_p7       = '0;
            rddata_en_p7       = '0;
            for (j=i; j <= N; j=j+1) begin

                wrd_packet[j] =   {
                    ts
                    //,dce_p`i
                    //,cs_p`i
                    //,cke_p`i
                    //,address_p`i
                    ,wrdata_en_p0
                    ,cs_p0
                    ,cke_p0
                    ,dq0_wrdata_p0[AWIDTH-1:0]
                    //,dce_p`i
                    //,cs_p`i
                    //,cke_p`i
                    //,address_p`i
                    ,wrdata_en_p1
                    ,cs_p1
                    ,cke_p1
                    ,dq0_wrdata_p1[AWIDTH-1:0]
                    //,dce_p`i
                    //,cs_p`i
                    //,cke_p`i
                    //,address_p`i
                    ,wrdata_en_p2
                    ,cs_p2
                    ,cke_p2
                    ,dq0_wrdata_p2[AWIDTH-1:0]
                    //,dce_p`i
                    //,cs_p`i
                    //,cke_p`i
                    //,address_p`i
                    ,wrdata_en_p3
                    ,cs_p3
                    ,cke_p3
                    ,dq0_wrdata_p3[AWIDTH-1:0]
                    //,dce_p`i
                    //,cs_p`i
                    //,cke_p`i
                    //,address_p`i
                    ,wrdata_en_p4
                    ,cs_p4
                    ,cke_p4
                    ,dq0_wrdata_p4[AWIDTH-1:0]
                    //,dce_p`i
                    //,cs_p`i
                    //,cke_p`i
                    //,address_p`i
                    ,wrdata_en_p5
                    ,cs_p5
                    ,cke_p5
                    ,dq0_wrdata_p5[AWIDTH-1:0]
                    //,dce_p`i
                    //,cs_p`i
                    //,cke_p`i
                    //,address_p`i
                    ,wrdata_en_p6
                    ,cs_p6
                    ,cke_p6
                    ,dq0_wrdata_p6[AWIDTH-1:0]
                    //,dce_p`i
                    //,cs_p`i
                    //,cke_p`i
                    //,address_p`i
                    ,wrdata_en_p7
                    ,cs_p7
                    ,cke_p7
                    ,dq0_wrdata_p7[AWIDTH-1:0]
                    ,rddata_en_p0
                    ,rddata_cs_p0
                    ,wck_toggle_p0
                    ,wck_en_p0
                    ,wck_cs_p0
                    ,wrdata_en_p0
                    ,parity_in_p0
                    ,wrdata_cs_p0
                    ,dq0_wrdata_mask_p0
                    ,dq0_wrdata_p0
                    ,dq1_wrdata_mask_p0
                    ,dq1_wrdata_p0
                    ,dq2_wrdata_mask_p0
                    ,dq2_wrdata_p0
                    ,dq3_wrdata_mask_p0
                    ,dq3_wrdata_p0
                    ,rddata_en_p1
                    ,rddata_cs_p1
                    ,wck_toggle_p1
                    ,wck_en_p1
                    ,wck_cs_p1
                    ,wrdata_en_p1
                    ,parity_in_p1
                    ,wrdata_cs_p1
                    ,dq0_wrdata_mask_p1
                    ,dq0_wrdata_p1
                    ,dq1_wrdata_mask_p1
                    ,dq1_wrdata_p1
                    ,dq2_wrdata_mask_p1
                    ,dq2_wrdata_p1
                    ,dq3_wrdata_mask_p1
                    ,dq3_wrdata_p1
                    ,rddata_en_p2
                    ,rddata_cs_p2
                    ,wck_toggle_p2
                    ,wck_en_p2
                    ,wck_cs_p2
                    ,wrdata_en_p2
                    ,parity_in_p2
                    ,wrdata_cs_p2
                    ,dq0_wrdata_mask_p2
                    ,dq0_wrdata_p2
                    ,dq1_wrdata_mask_p2
                    ,dq1_wrdata_p2
                    ,dq2_wrdata_mask_p2
                    ,dq2_wrdata_p2
                    ,dq3_wrdata_mask_p2
                    ,dq3_wrdata_p2
                    ,rddata_en_p3
                    ,rddata_cs_p3
                    ,wck_toggle_p3
                    ,wck_en_p3
                    ,wck_cs_p3
                    ,wrdata_en_p3
                    ,parity_in_p3
                    ,wrdata_cs_p3
                    ,dq0_wrdata_mask_p3
                    ,dq0_wrdata_p3
                    ,dq1_wrdata_mask_p3
                    ,dq1_wrdata_p3
                    ,dq2_wrdata_mask_p3
                    ,dq2_wrdata_p3
                    ,dq3_wrdata_mask_p3
                    ,dq3_wrdata_p3
                    ,rddata_en_p4
                    ,rddata_cs_p4
                    ,wck_toggle_p4
                    ,wck_en_p4
                    ,wck_cs_p4
                    ,wrdata_en_p4
                    ,parity_in_p4
                    ,wrdata_cs_p4
                    ,dq0_wrdata_mask_p4
                    ,dq0_wrdata_p4
                    ,dq1_wrdata_mask_p4
                    ,dq1_wrdata_p4
                    ,dq2_wrdata_mask_p4
                    ,dq2_wrdata_p4
                    ,dq3_wrdata_mask_p4
                    ,dq3_wrdata_p4
                    ,rddata_en_p5
                    ,rddata_cs_p5
                    ,wck_toggle_p5
                    ,wck_en_p5
                    ,wck_cs_p5
                    ,wrdata_en_p5
                    ,parity_in_p5
                    ,wrdata_cs_p5
                    ,dq0_wrdata_mask_p5
                    ,dq0_wrdata_p5
                    ,dq1_wrdata_mask_p5
                    ,dq1_wrdata_p5
                    ,dq2_wrdata_mask_p5
                    ,dq2_wrdata_p5
                    ,dq3_wrdata_mask_p5
                    ,dq3_wrdata_p5
                    ,rddata_en_p6
                    ,rddata_cs_p6
                    ,wck_toggle_p6
                    ,wck_en_p6
                    ,wck_cs_p6
                    ,wrdata_en_p6
                    ,parity_in_p6
                    ,wrdata_cs_p6
                    ,dq0_wrdata_mask_p6
                    ,dq0_wrdata_p6
                    ,dq1_wrdata_mask_p6
                    ,dq1_wrdata_p6
                    ,dq2_wrdata_mask_p6
                    ,dq2_wrdata_p6
                    ,dq3_wrdata_mask_p6
                    ,dq3_wrdata_p6
                    ,rddata_en_p7
                    ,rddata_cs_p7
                    ,wck_toggle_p7
                    ,wck_en_p7
                    ,wck_cs_p7
                    ,wrdata_en_p7
                    ,parity_in_p7
                    ,wrdata_cs_p7
                    ,dq0_wrdata_mask_p7
                    ,dq0_wrdata_p7
                    ,dq1_wrdata_mask_p7
                    ,dq1_wrdata_p7
                    ,dq2_wrdata_mask_p7
                    ,dq2_wrdata_p7
                    ,dq3_wrdata_mask_p7
                    ,dq3_wrdata_p7
                };
                //$display ("INFO: GEN_DFI_PACKET EMPTY [%d] : DQ0{ p3 p2 p1 p0 } = { %x %x %x %x }  DQ1{ p3 p2 p1 p0 } = { %x %x %x %x }", j, dq0_wrdata_p3, dq0_wrdata_p2, dq0_wrdata_p1, dq0_wrdata_p0, dq1_wrdata_p3, dq1_wrdata_p2, dq1_wrdata_p1, dq1_wrdata_p0  );
                ts = ts + 1;
            end
        end

        // data = '0;
        // wr_en = '0;
        // ca_addr = '0;
        // ca_dce  = '0;
        // ca_cs   = '0;
        // ca_cke  = '0;

        // dphy_wrcslat_int = tphy_wrcslat ;
        // tphy_wrlat_int   = tphy_wrcslat + tphy_wrlat ;
        // tphy_wrdata_int  = tphy_wrlat_int + tphy_wrdata ;

        // if(bl==32) begin
        //   ca_cke  = {32*{2'h3}} << (cacke_pnum*2) ;
        //   ca_cs   = {32*{rank_sel}} << (cacs_pnum*2) ;
        //   ca_addr = CA[4*AWIDTH-1:0] << (caaddr_pnum*AWIDTH + tphy_wrcslat_int*NUM_DFI_WPH*AWIDTH) ;
        //   wr_en   = {32{1'b1}} << (wren_pnum + tphy_wrdata_int*NUM_DFI_WPH);
        //   data    = DATA[32*SWIDTH-1:0] << (wr_pnum*SWIDTH + tphy_wrdata_int*NUM_DFI_WPH*SWIDTH);
        // end else begin //if (bl==16)
        //   ca_cke  = {16*{2'h3}} << (cacke_pnum*2) ;
        //   ca_cs   = {16*{rank_sel}} << (cacs_pnum*2) ;
        //   ca_addr = CA[4*AWIDTH-1:0] << (caaddr_pnum*AWIDTH + tphy_wrcslat_int*NUM_DFI_WPH*AWIDTH) ;
        //   wr_en   = {16{1'b1}} << (wren_pnum + tphy_wrdata_int*NUM_DFI_WPH);
        //   data    = DATA[16*SWIDTH-1:0] << (wr_pnum*SWIDTH + tphy_wrdata_int*NUM_DFI_WPH*SWIDTH);
        // end

        //beat_cnt = (bl+tphy_wrdata_int*NUM_DFI_WPH+wr_pnum);

        for(j=0; j < bl; j=j+NUM_DFI_RPH)
        begin
            k = j/NUM_DFI_RPH ;
            rd_exp_packet[k] = {
                {TSWIDTH{1'h0}}
                ,rank_sel
                ,2'h3
                ,DATA[(SWIDTH*(j+0)) +: AWIDTH]
                // ,ca_cs[2*(j+`i) +: 2]
                // ,ca_cke[2*(j+`i) +: 2]
                // ,ca_addr[AWIDTH*(j+`i) +: AWIDTH]
                ,rank_sel
                ,2'h3
                ,DATA[(SWIDTH*(j+1)) +: AWIDTH]
                // ,ca_cs[2*(j+`i) +: 2]
                // ,ca_cke[2*(j+`i) +: 2]
                // ,ca_addr[AWIDTH*(j+`i) +: AWIDTH]
                ,rank_sel
                ,2'h3
                ,DATA[(SWIDTH*(j+2)) +: AWIDTH]
                // ,ca_cs[2*(j+`i) +: 2]
                // ,ca_cke[2*(j+`i) +: 2]
                // ,ca_addr[AWIDTH*(j+`i) +: AWIDTH]
                ,rank_sel
                ,2'h3
                ,DATA[(SWIDTH*(j+3)) +: AWIDTH]
                // ,ca_cs[2*(j+`i) +: 2]
                // ,ca_cke[2*(j+`i) +: 2]
                // ,ca_addr[AWIDTH*(j+`i) +: AWIDTH]
                ,rank_sel
                ,2'h3
                ,DATA[(SWIDTH*(j+4)) +: AWIDTH]
                // ,ca_cs[2*(j+`i) +: 2]
                // ,ca_cke[2*(j+`i) +: 2]
                // ,ca_addr[AWIDTH*(j+`i) +: AWIDTH]
                ,rank_sel
                ,2'h3
                ,DATA[(SWIDTH*(j+5)) +: AWIDTH]
                // ,ca_cs[2*(j+`i) +: 2]
                // ,ca_cke[2*(j+`i) +: 2]
                // ,ca_addr[AWIDTH*(j+`i) +: AWIDTH]
                ,rank_sel
                ,2'h3
                ,DATA[(SWIDTH*(j+6)) +: AWIDTH]
                // ,ca_cs[2*(j+`i) +: 2]
                // ,ca_cke[2*(j+`i) +: 2]
                // ,ca_addr[AWIDTH*(j+`i) +: AWIDTH]
                ,rank_sel
                ,2'h3
                ,DATA[(SWIDTH*(j+7)) +: AWIDTH]
                // ,ca_cs[2*(j+`i) +: 2]
                // ,ca_cke[2*(j+`i) +: 2]
                // ,ca_addr[AWIDTH*(j+`i) +: AWIDTH]
                ,1'b1
                ,{MWIDTH{1'b0}}
                ,DATA[(SWIDTH*(j+0))+:SWIDTH]
                //,wr_en[(j+`i) +: 1]
                //,{MWIDTH{1'b0}}
                //,data[(SWIDTH*(j+`i))+:SWIDTH]
                ,1'b1
                ,{MWIDTH{1'b0}}
                ,DATA[(SWIDTH*(j+1))+:SWIDTH]
                //,wr_en[(j+`i) +: 1]
                //,{MWIDTH{1'b0}}
                //,data[(SWIDTH*(j+`i))+:SWIDTH]
                ,1'b1
                ,{MWIDTH{1'b0}}
                ,DATA[(SWIDTH*(j+2))+:SWIDTH]
                //,wr_en[(j+`i) +: 1]
                //,{MWIDTH{1'b0}}
                //,data[(SWIDTH*(j+`i))+:SWIDTH]
                ,1'b1
                ,{MWIDTH{1'b0}}
                ,DATA[(SWIDTH*(j+3))+:SWIDTH]
                //,wr_en[(j+`i) +: 1]
                //,{MWIDTH{1'b0}}
                //,data[(SWIDTH*(j+`i))+:SWIDTH]
                ,1'b1
                ,{MWIDTH{1'b0}}
                ,DATA[(SWIDTH*(j+4))+:SWIDTH]
                //,wr_en[(j+`i) +: 1]
                //,{MWIDTH{1'b0}}
                //,data[(SWIDTH*(j+`i))+:SWIDTH]
                ,1'b1
                ,{MWIDTH{1'b0}}
                ,DATA[(SWIDTH*(j+5))+:SWIDTH]
                //,wr_en[(j+`i) +: 1]
                //,{MWIDTH{1'b0}}
                //,data[(SWIDTH*(j+`i))+:SWIDTH]
                ,1'b1
                ,{MWIDTH{1'b0}}
                ,DATA[(SWIDTH*(j+6))+:SWIDTH]
                //,wr_en[(j+`i) +: 1]
                //,{MWIDTH{1'b0}}
                //,data[(SWIDTH*(j+`i))+:SWIDTH]
                ,1'b1
                ,{MWIDTH{1'b0}}
                ,DATA[(SWIDTH*(j+7))+:SWIDTH]
                //,wr_en[(j+`i) +: 1]
                //,{MWIDTH{1'b0}}
                //,data[(SWIDTH*(j+`i))+:SWIDTH]
                ,1'b1
                ,{MWIDTH{1'b0}}
                ,DATA[(SWIDTH*(j+0))+:SWIDTH]
                //,wr_en[(j+`i) +: 1]
                //,{MWIDTH{1'b0}}
                //,data[(SWIDTH*(j+`i))+:SWIDTH]
                ,1'b1
                ,{MWIDTH{1'b0}}
                ,DATA[(SWIDTH*(j+1))+:SWIDTH]
                //,wr_en[(j+`i) +: 1]
                //,{MWIDTH{1'b0}}
                //,data[(SWIDTH*(j+`i))+:SWIDTH]
                ,1'b1
                ,{MWIDTH{1'b0}}
                ,DATA[(SWIDTH*(j+2))+:SWIDTH]
                //,wr_en[(j+`i) +: 1]
                //,{MWIDTH{1'b0}}
                //,data[(SWIDTH*(j+`i))+:SWIDTH]
                ,1'b1
                ,{MWIDTH{1'b0}}
                ,DATA[(SWIDTH*(j+3))+:SWIDTH]
                //,wr_en[(j+`i) +: 1]
                //,{MWIDTH{1'b0}}
                //,data[(SWIDTH*(j+`i))+:SWIDTH]
                ,1'b1
                ,{MWIDTH{1'b0}}
                ,DATA[(SWIDTH*(j+4))+:SWIDTH]
                //,wr_en[(j+`i) +: 1]
                //,{MWIDTH{1'b0}}
                //,data[(SWIDTH*(j+`i))+:SWIDTH]
                ,1'b1
                ,{MWIDTH{1'b0}}
                ,DATA[(SWIDTH*(j+5))+:SWIDTH]
                //,wr_en[(j+`i) +: 1]
                //,{MWIDTH{1'b0}}
                //,data[(SWIDTH*(j+`i))+:SWIDTH]
                ,1'b1
                ,{MWIDTH{1'b0}}
                ,DATA[(SWIDTH*(j+6))+:SWIDTH]
                //,wr_en[(j+`i) +: 1]
                //,{MWIDTH{1'b0}}
                //,data[(SWIDTH*(j+`i))+:SWIDTH]
                ,1'b1
                ,{MWIDTH{1'b0}}
                ,DATA[(SWIDTH*(j+7))+:SWIDTH]
                //,wr_en[(j+`i) +: 1]
                //,{MWIDTH{1'b0}}
                //,data[(SWIDTH*(j+`i))+:SWIDTH]
                ,1'b1
                ,{MWIDTH{1'b0}}
                ,DATA[(SWIDTH*(j+0))+:SWIDTH]
                //,wr_en[(j+`i) +: 1]
                //,{MWIDTH{1'b0}}
                //,data[(SWIDTH*(j+`i))+:SWIDTH]
                ,1'b1
                ,{MWIDTH{1'b0}}
                ,DATA[(SWIDTH*(j+1))+:SWIDTH]
                //,wr_en[(j+`i) +: 1]
                //,{MWIDTH{1'b0}}
                //,data[(SWIDTH*(j+`i))+:SWIDTH]
                ,1'b1
                ,{MWIDTH{1'b0}}
                ,DATA[(SWIDTH*(j+2))+:SWIDTH]
                //,wr_en[(j+`i) +: 1]
                //,{MWIDTH{1'b0}}
                //,data[(SWIDTH*(j+`i))+:SWIDTH]
                ,1'b1
                ,{MWIDTH{1'b0}}
                ,DATA[(SWIDTH*(j+3))+:SWIDTH]
                //,wr_en[(j+`i) +: 1]
                //,{MWIDTH{1'b0}}
                //,data[(SWIDTH*(j+`i))+:SWIDTH]
                ,1'b1
                ,{MWIDTH{1'b0}}
                ,DATA[(SWIDTH*(j+4))+:SWIDTH]
                //,wr_en[(j+`i) +: 1]
                //,{MWIDTH{1'b0}}
                //,data[(SWIDTH*(j+`i))+:SWIDTH]
                ,1'b1
                ,{MWIDTH{1'b0}}
                ,DATA[(SWIDTH*(j+5))+:SWIDTH]
                //,wr_en[(j+`i) +: 1]
                //,{MWIDTH{1'b0}}
                //,data[(SWIDTH*(j+`i))+:SWIDTH]
                ,1'b1
                ,{MWIDTH{1'b0}}
                ,DATA[(SWIDTH*(j+6))+:SWIDTH]
                //,wr_en[(j+`i) +: 1]
                //,{MWIDTH{1'b0}}
                //,data[(SWIDTH*(j+`i))+:SWIDTH]
                ,1'b1
                ,{MWIDTH{1'b0}}
                ,DATA[(SWIDTH*(j+7))+:SWIDTH]
                //,wr_en[(j+`i) +: 1]
                //,{MWIDTH{1'b0}}
                //,data[(SWIDTH*(j+`i))+:SWIDTH]
                ,1'b1
                ,{MWIDTH{1'b0}}
                ,DATA[(SWIDTH*(j+0))+:SWIDTH]
                //,wr_en[(j+`i) +: 1]
                //,{MWIDTH{1'b0}}
                //,data[(SWIDTH*(j+`i))+:SWIDTH]
                ,1'b1
                ,{MWIDTH{1'b0}}
                ,DATA[(SWIDTH*(j+1))+:SWIDTH]
                //,wr_en[(j+`i) +: 1]
                //,{MWIDTH{1'b0}}
                //,data[(SWIDTH*(j+`i))+:SWIDTH]
                ,1'b1
                ,{MWIDTH{1'b0}}
                ,DATA[(SWIDTH*(j+2))+:SWIDTH]
                //,wr_en[(j+`i) +: 1]
                //,{MWIDTH{1'b0}}
                //,data[(SWIDTH*(j+`i))+:SWIDTH]
                ,1'b1
                ,{MWIDTH{1'b0}}
                ,DATA[(SWIDTH*(j+3))+:SWIDTH]
                //,wr_en[(j+`i) +: 1]
                //,{MWIDTH{1'b0}}
                //,data[(SWIDTH*(j+`i))+:SWIDTH]
                ,1'b1
                ,{MWIDTH{1'b0}}
                ,DATA[(SWIDTH*(j+4))+:SWIDTH]
                //,wr_en[(j+`i) +: 1]
                //,{MWIDTH{1'b0}}
                //,data[(SWIDTH*(j+`i))+:SWIDTH]
                ,1'b1
                ,{MWIDTH{1'b0}}
                ,DATA[(SWIDTH*(j+5))+:SWIDTH]
                //,wr_en[(j+`i) +: 1]
                //,{MWIDTH{1'b0}}
                //,data[(SWIDTH*(j+`i))+:SWIDTH]
                ,1'b1
                ,{MWIDTH{1'b0}}
                ,DATA[(SWIDTH*(j+6))+:SWIDTH]
                //,wr_en[(j+`i) +: 1]
                //,{MWIDTH{1'b0}}
                //,data[(SWIDTH*(j+`i))+:SWIDTH]
                ,1'b1
                ,{MWIDTH{1'b0}}
                ,DATA[(SWIDTH*(j+7))+:SWIDTH]
                //,wr_en[(j+`i) +: 1]
                //,{MWIDTH{1'b0}}
                //,data[(SWIDTH*(j+`i))+:SWIDTH]
            } ;
        end
    end
endtask

task automatic set_dfi_paden_pext_cfg;
    input logic [7:0] wrd_oe_cycles;
    input logic [7:0] wrd_en_cycles;
    input logic [7:0] wck_oe_cycles;
    input logic [7:0] ie_cycles;
    input logic [7:0] re_cycles;
    input logic [7:0] ren_cycles;
    input logic [7:0] rcs_cycles;
    begin
        `CSR_WRF2(DDR_DFICH0_OFFSET,DDR_DFICH_CTRL5_M0_CFG   , IE_PHASE_EXT, RE_PHASE_EXT, ie_cycles, re_cycles);
        `CSR_WRF1(DDR_DFICH0_OFFSET,DDR_DFICH_CTRL3_M0_CFG   , WRD_OE_PHASE_EXT, wrd_oe_cycles);
        `CSR_WRF1(DDR_DFICH0_OFFSET,DDR_DFICH_CTRL4_M0_CFG   , WCK_OE_PHASE_EXT, wck_oe_cycles);
        `CSR_WRF1(DDR_DFICH0_OFFSET,DDR_DFICH_CTRL3_M0_CFG   , WRD_EN_PHASE_EXT, wrd_en_cycles);
        `CSR_WRF2(DDR_DFICH0_OFFSET,DDR_DFICH_CTRL5_M0_CFG   , REN_PHASE_EXT, RCS_PHASE_EXT, ren_cycles, rcs_cycles);
    end
endtask

task automatic set_dfi_clken_pext_cfg;
    input logic [3:0] wr_clken_cycles;
    input logic [3:0] rd_clken_cycles;
    input logic [3:0] ca_clken_cycles;
    begin
        `CSR_WRF3(DDR_DFICH0_OFFSET,DDR_DFICH_CTRL2_M0_CFG, DQ_WRCLK_EN_PULSE_EXT, DQS_WRCLK_EN_PULSE_EXT, RDCLK_EN_PULSE_EXT,wr_clken_cycles,wr_clken_cycles,rd_clken_cycles );
        `CSR_WRF2(DDR_DFICH0_OFFSET,DDR_DFICH_CTRL2_M0_CFG, CA_CLK_EN_PULSE_EXT, CK_CLK_EN_PULSE_EXT , ca_clken_cycles, ca_clken_cycles );
    end
endtask

task automatic set_dfi_traffic_ovr_cfg;
    input logic  sw_en ;
    input logic  sw_mode ;
    begin
        `CSR_WRF2(DDR_DFICH0_OFFSET,DDR_DFICH_CTRL1_M0_CFG, DQ_WRTRAFFIC_OVR,      CA_TRAFFIC_OVR,     sw_en , sw_en );
        `CSR_WRF2(DDR_DFICH0_OFFSET,DDR_DFICH_CTRL1_M0_CFG, DQS_WRTRAFFIC_OVR,     CK_TRAFFIC_OVR,     sw_en , sw_en );
        `CSR_WRF2(DDR_DFICH0_OFFSET,DDR_DFICH_CTRL1_M0_CFG, DQ_WRTRAFFIC_OVR_SEL,  CA_TRAFFIC_OVR_SEL, sw_mode , sw_mode );
        `CSR_WRF2(DDR_DFICH0_OFFSET,DDR_DFICH_CTRL1_M0_CFG, DQS_WRTRAFFIC_OVR_SEL, CK_TRAFFIC_OVR_SEL, sw_mode , sw_mode );
        `CSR_WRF2(DDR_DFICH0_OFFSET,DDR_DFICH_CTRL1_M1_CFG, DQ_WRTRAFFIC_OVR,      CA_TRAFFIC_OVR,     sw_en , sw_en );
        `CSR_WRF2(DDR_DFICH0_OFFSET,DDR_DFICH_CTRL1_M1_CFG, DQS_WRTRAFFIC_OVR,     CK_TRAFFIC_OVR,     sw_en , sw_en );
        `CSR_WRF2(DDR_DFICH0_OFFSET,DDR_DFICH_CTRL1_M1_CFG, DQ_WRTRAFFIC_OVR_SEL,  CA_TRAFFIC_OVR_SEL, sw_mode , sw_mode );
        `CSR_WRF2(DDR_DFICH0_OFFSET,DDR_DFICH_CTRL1_M1_CFG, DQS_WRTRAFFIC_OVR_SEL, CK_TRAFFIC_OVR_SEL, sw_mode , sw_mode );
    end
endtask

task automatic set_dfi_ca_rddata_en ;
    input logic en;
    begin
        `CSR_WRF1(DDR_DFICH0_OFFSET,DDR_DFICH_TOP_1_CFG, CA_RDDATA_EN , en );
    end
endtask

task automatic set_dfiwctrl_wdp_cfg;
    input dwgb_t       gb_mode;
    input logic [2:0]  gb_pipe_dly;
    input logic        pre_gb_pipe_en;
    begin
        `CSR_WRF3(DDR_DFICH0_OFFSET,DDR_DFICH_WCTRL_M0_CFG  ,POST_GB_FC_DLY, GB_MODE, PIPE_EN, gb_pipe_dly, gb_mode, pre_gb_pipe_en);
    end
endtask

task automatic set_dfiwenctrl_wdp_cfg;
    input dwgb_t       gb_mode;
    input logic [2:0]  gb_pipe_dly;
    input logic        pre_gb_pipe_en;
    begin
        `CSR_WRF3(DDR_DFICH0_OFFSET,DDR_DFICH_WENCTRL_M0_CFG  ,POST_GB_FC_DLY, GB_MODE, PIPE_EN, gb_pipe_dly, gb_mode, pre_gb_pipe_en);
    end
endtask

task automatic set_dfiwckctrl_wdp_cfg;
    input dwgb_t       gb_mode;
    input logic [2:0]  gb_pipe_dly;
    input logic        pre_gb_pipe_en;
    begin
        `CSR_WRF3(DDR_DFICH0_OFFSET,DDR_DFICH_WCKCTRL_M0_CFG,POST_GB_FC_DLY, GB_MODE, PIPE_EN, gb_pipe_dly, gb_mode, pre_gb_pipe_en);
    end
endtask

task automatic set_dfirctrl_wdp_cfg;
    input dwgb_t       gb_mode;
    input logic [2:0]  gb_pipe_dly;
    input logic        pre_gb_pipe_en;
    begin
        `CSR_WRF3(DDR_DFICH0_OFFSET,DDR_DFICH_RCTRL_M0_CFG  ,POST_GB_FC_DLY, GB_MODE, PIPE_EN, gb_pipe_dly, gb_mode, pre_gb_pipe_en);
    end
endtask

task automatic set_dfiwrcctrl_wdp_cfg;

    input dwgb_t  gb_mode;
    input logic [2:0]  gb_pipe_dly;
    input logic   pre_gb_pipe_en;
    begin
        `CSR_WRF3(DDR_DFICH0_OFFSET,DDR_DFICH_WRCCTRL_M0_CFG    ,POST_GB_FC_DLY, GB_MODE, PIPE_EN, gb_pipe_dly, gb_mode, pre_gb_pipe_en);
    end
endtask

task automatic set_dfickctrl_wdp_cfg;

    input dwgb_t  gb_mode;
    input logic [2:0]  gb_pipe_dly;
    input logic   pre_gb_pipe_en;
    begin
        `CSR_WRF3(DDR_DFICH0_OFFSET,DDR_DFICH_CKCTRL_M0_CFG    ,POST_GB_FC_DLY, GB_MODE, PIPE_EN, gb_pipe_dly, gb_mode, pre_gb_pipe_en);
    end
endtask

task automatic set_dfiwrd_wdp_cfg;

    input dwgb_t  gb_mode;
    input logic [2:0]  gb_pipe_dly;
    input logic   pre_gb_pipe_en;
    begin
        `CSR_WRF3(DDR_DFICH0_OFFSET,DDR_DFICH_WRD_M0_CFG    ,POST_GB_FC_DLY, GB_MODE, PIPE_EN, gb_pipe_dly, gb_mode, pre_gb_pipe_en);
        `CSR_WRF3(DDR_DFICH0_OFFSET,DDR_DFICH_WRC_M0_CFG    ,POST_GB_FC_DLY, GB_MODE, PIPE_EN, gb_pipe_dly, gb_mode, pre_gb_pipe_en);
    end
endtask

task automatic set_dfi_wck_mode;
    input logic mode;
    begin
        // 1: LP4/DDR/HBM mode, 0: LP5/GDDR mode
        `CSR_WRF1(DDR_DFICH0_OFFSET,DDR_DFICH_TOP_1_CFG,WCK_MODE,mode);
    end
endtask

task automatic set_dfi_rdata_clr;
    begin
        `CSR_WRF1(DDR_DFICH0_OFFSET,DDR_DFICH_TOP_1_CFG,RDATA_CLR,1'b1);
        `CSR_WRF1(DDR_DFICH0_OFFSET,DDR_DFICH_TOP_1_CFG,RDATA_CLR,1'b0);
    end
endtask

task automatic set_dfi_wdata_clr;
    begin
        `CSR_WRF1(DDR_DFICH0_OFFSET,DDR_DFICH_TOP_1_CFG,WDATA_CLR, 1'b1);
        `CSR_WRF1(DDR_DFICH0_OFFSET,DDR_DFICH_TOP_1_CFG,WDATA_CLR, 1'b0);
    end
endtask

task automatic set_dfi_buf_mode;
    input logic en;
    begin
        `CSR_WRF1(DDR_DFICH0_OFFSET,DDR_DFICH_TOP_1_CFG,BUF_MODE,en);
    end
endtask

task automatic set_dfi_buf_clken;
    input logic en;
    begin
        `CSR_WRF1(DDR_DFICH0_OFFSET,DDR_DFICH_TOP_1_CFG,BUF_CLK_EN,en);
    end
endtask

task automatic set_dfi_rdout_mode;
    input logic sel;
    input logic en;
    begin
        `CSR_WRF1(DDR_DFICH0_OFFSET,DDR_DFICH_TOP_1_CFG,RDOUT_EN_OVR_SEL,sel);
        `CSR_WRF1(DDR_DFICH0_OFFSET,DDR_DFICH_TOP_1_CFG,RDOUT_EN_OVR,en);
    end
endtask

task automatic set_dfi_rdgb_mode;
    input drgb_t gbmode;
    begin
        `CSR_WRF1(DDR_DFICH0_OFFSET,DDR_DFICH_RDD_M0_CFG,GB_MODE, gbmode);
    end
endtask

task automatic set_dfi_status_req;
    input ovr;
    input val;
    begin
        `CSR_WRF1(DDR_DFI_OFFSET,DDR_DFI_STATUS_IF_CFG, SW_REQ_OVR, ovr);
        `CSR_WRF1(DDR_DFI_OFFSET,DDR_DFI_STATUS_IF_CFG, SW_REQ_VAL, val);
    end
endtask

task automatic get_dfi_status_req;
    output logic val;
    begin
        `CSR_RDF1(DDR_DFI_OFFSET,DDR_DFI_STATUS_IF_STA, REQ, val);
    end
endtask

task automatic set_dfi_status_ack;
    input ovr;
    input val;
    begin
        `CSR_WRF1(DDR_DFI_OFFSET,DDR_DFI_STATUS_IF_CFG, SW_ACK_OVR, ovr);
        `CSR_WRF1(DDR_DFI_OFFSET,DDR_DFI_STATUS_IF_CFG, SW_ACK_VAL, val);
    end
endtask

task automatic get_dfi_status_ack;
    output logic val;
    begin
        `CSR_RDF1(DDR_DFI_OFFSET,DDR_DFI_STATUS_IF_STA, ACK, val);
    end
endtask

task automatic get_cmn_switch_done;
    output logic val;
    begin
        `CSR_RDF1(DDR_FSW_OFFSET,DDR_FSW_CTRL_STA, SWITCH_DONE, val);
    end
endtask

task automatic set_dfi_event_0;
    input ovr;
    input val;
    begin
        `CSR_WRF1(DDR_DFI_OFFSET,DDR_DFI_STATUS_IF_CFG, SW_EVENT_0_OVR, ovr);
        `CSR_WRF1(DDR_DFI_OFFSET,DDR_DFI_STATUS_IF_CFG, SW_EVENT_0_VAL, val);
    end
endtask

task automatic set_dfi_event_1;
    input ovr;
    input val;
    begin
        `CSR_WRF1(DDR_DFI_OFFSET,DDR_DFI_STATUS_IF_CFG, SW_EVENT_1_OVR, ovr);
        `CSR_WRF1(DDR_DFI_OFFSET,DDR_DFI_STATUS_IF_CFG, SW_EVENT_1_VAL, val);
    end
endtask

task automatic set_dfi_event_0_cnt;
    input cnt;
    begin
        `CSR_WRF1(DDR_DFI_OFFSET,DDR_DFI_STATUS_IF_EVENT_0_CFG, SW_EVENT_CNT, cnt);
    end
endtask

task automatic set_dfi_event_1_cnt;
    input cnt;
    begin
        `CSR_WRF1(DDR_DFI_OFFSET,DDR_DFI_STATUS_IF_EVENT_1_CFG, SW_EVENT_CNT, cnt);
    end
endtask

task automatic wait_dfibuf_ig_empty;
    logic [1:0] val;
    begin
        do begin
            `CSR_RDF1(DDR_DFICH0_OFFSET,DDR_DFICH_TOP_STA,IG_STATE, val);
        end while (val[0] != 1'b1 );
    end
endtask

task automatic wait_dfibuf_eg_not_empty;
    logic [1:0] val;
    begin
        do begin
            `CSR_RDF1(DDR_DFICH0_OFFSET,DDR_DFICH_TOP_STA,EG_STATE,val);
        end while (val[0] == 1'b1) ;
    end
endtask

task automatic toggle_dfibuf_ig_wdata_en ;
    logic [AHB_DWIDTH-1:0] data;
    begin
        `CSR_RD(DDR_DFICH0_OFFSET,DDR_DFICH_TOP_1_CFG,data);
        data[`DDR_DFICH_TOP_1_CFG_WDATA_ENABLE_FIELD] = ~data[`DDR_DFICH_TOP_1_CFG_WDATA_ENABLE_FIELD];
        `CSR_WR(DDR_DFICH0_OFFSET,DDR_DFICH_TOP_1_CFG,data);
    end
endtask

task automatic toggle_dfibuf_ig_wdata_upd ;
    logic [AHB_DWIDTH-1:0] data;
    begin
        `CSR_RD(DDR_DFICH0_OFFSET,DDR_DFICH_TOP_1_CFG, data);
        data[`DDR_DFICH_TOP_1_CFG_WDATA_UPDATE_FIELD] = ~data[`DDR_DFICH_TOP_1_CFG_WDATA_UPDATE_FIELD];
        `CSR_WR(DDR_DFICH0_OFFSET,DDR_DFICH_TOP_1_CFG, data);
    end
endtask

task automatic set_dfibuf_ts_cfg ;
    input logic en;
    input logic rst;
    begin
        `CSR_WRF2(DDR_DFICH0_OFFSET,DDR_DFICH_TOP_1_CFG,TS_ENABLE,TS_RESET,en, rst);
    end
endtask

task automatic toggle_dfibuf_eg_rdata_en ;
    logic [AHB_DWIDTH-1:0] data;
    begin
        `CSR_RD(DDR_DFICH0_OFFSET,DDR_DFICH_TOP_1_CFG, data);
        data[`DDR_DFICH_TOP_1_CFG_RDATA_ENABLE_FIELD] = ~data[`DDR_DFICH_TOP_1_CFG_RDATA_ENABLE_FIELD];
        `CSR_WR(DDR_DFICH0_OFFSET,DDR_DFICH_TOP_1_CFG, data);
    end
endtask

task automatic toggle_dfibuf_eg_rdata_upd ;
    logic [AHB_DWIDTH-1:0] data;
    begin
        `CSR_RD(DDR_DFICH0_OFFSET,DDR_DFICH_TOP_1_CFG, data);
        data[`DDR_DFICH_TOP_1_CFG_RDATA_UPDATE_FIELD] = ~data[`DDR_DFICH_TOP_1_CFG_RDATA_UPDATE_FIELD];
        `CSR_WR(DDR_DFICH0_OFFSET,DDR_DFICH_TOP_1_CFG, data);
    end
endtask

task automatic push_dfi_ig_buf ;
    input logic [IG_WIDTH-1:0] load_data;
    int i;
    localparam LOOP_CNT = IG_WIDTH/AHB_DWIDTH + ((IG_WIDTH%AHB_DWIDTH != 0) ? 1 : 0) ;
    localparam IG_LOAD_DWIDTH = LOOP_CNT*AHB_DWIDTH ;
    logic [IG_LOAD_DWIDTH-1:0] data = '0;
    begin

        data = load_data ;
        //$display("INFO: push ig buf: IG_LOAD_DATA = %x.\n IG_WIDTH = %d \n IG_LOAD_DWIDTH = %d \n loop_cnt = %d  \n/", data, IG_WIDTH, IG_LOAD_DWIDTH, LOOP_CNT );
        for (i=0; i < LOOP_CNT; i=i+1) begin
            wait_hclk(1);
            //$display("INFO: push ig buf: DATA[%d] = %x.\n /", i, data[IG_LOAD_DWIDTH-1:IG_LOAD_DWIDTH-AHB_DWIDTH] );
            `CSR_WR(DDR_DFICH0_OFFSET,DDR_DFICH_IG_DATA_CFG, data[IG_LOAD_DWIDTH-1:IG_LOAD_DWIDTH-AHB_DWIDTH]);
            data      = data << AHB_DWIDTH ;
            toggle_dfibuf_ig_wdata_en ;
        end
        toggle_dfibuf_ig_wdata_upd ;
    end
endtask

task automatic pop_dfi_eg_buf ;
    output logic [EG_WIDTH-1:0] o_rdata;

    localparam LOOP_CNT = EG_WIDTH/AHB_DWIDTH + ((EG_WIDTH%AHB_DWIDTH != 0) ? 1 : 0) ;
    localparam EG_RD_DWIDTH = LOOP_CNT*AHB_DWIDTH ;
    int i;
    logic  [EG_RD_DWIDTH-1:0] rdata;
    logic  [AHB_DWIDTH-1:0] eg_rdata;
    logic   val;

    begin
        rdata = '0;
        toggle_dfibuf_eg_rdata_upd ;
        `CSR_RDF1(DDR_DFICH0_OFFSET,DDR_DFICH_TOP_1_CFG, RDATA_UPDATE, val); // Added to prvide extra clock cycles before reading data.
        `CSR_RDF1(DDR_DFICH0_OFFSET,DDR_DFICH_TOP_1_CFG, RDATA_UPDATE, val); // Added to prvide extra clock cycles before reading data.
        `CSR_RDF1(DDR_DFICH0_OFFSET,DDR_DFICH_TOP_1_CFG, RDATA_UPDATE, val); // Added to prvide extra clock cycles before reading data.
        for (i=0; i < LOOP_CNT ; i=i+1) begin
            `CSR_RD(DDR_DFICH0_OFFSET,DDR_DFICH_EG_DATA_STA, eg_rdata); //// Added to prvide extra clock cycles before reading data
            `CSR_RD(DDR_DFICH0_OFFSET,DDR_DFICH_EG_DATA_STA, eg_rdata); //// Added to prvide extra clock cycles before reading data
            `CSR_RD(DDR_DFICH0_OFFSET,DDR_DFICH_EG_DATA_STA, eg_rdata);
            //$display("INFO: %d, POP : RDATA = %x \n/", i , eg_rdata);
            rdata = {eg_rdata, rdata[EG_RD_DWIDTH-1:AHB_DWIDTH]};
            toggle_dfibuf_eg_rdata_en ;
        end
        o_rdata = rdata[EG_WIDTH-1:0];
    end
endtask

task automatic check_dfibuf_eg_data ;
    input byte_sel_t    byte_sel;
    input logic [EG_WIDTH-1:0] rdata ;
    input logic [EG_WIDTH-1:0] rdata_expected ;
    output int err_cnt;
    input mode_t mode ;

    localparam EWIDTH = (1+MWIDTH+SWIDTH);
    localparam NWIDTH = NUM_DFI_RPH * (1+MWIDTH+SWIDTH);
    int i;
    logic data_match;

    logic [TSWIDTH-1:0] timestamp;
    logic [TSWIDTH-1:0] exp_timestamp;
    logic [AWIDTH-1:0]        dfi_address_w0;
    logic [1:0]               dfi_cke_w0;
    logic [1:0]               dfi_cs_w0;
    logic [AWIDTH-1:0]        exp_dfi_address_w0;
    logic [1:0]               exp_dfi_cke_w0;
    logic [1:0]               exp_dfi_cs_w0;
    logic [AWIDTH-1:0]        dfi_address_w1;
    logic [1:0]               dfi_cke_w1;
    logic [1:0]               dfi_cs_w1;
    logic [AWIDTH-1:0]        exp_dfi_address_w1;
    logic [1:0]               exp_dfi_cke_w1;
    logic [1:0]               exp_dfi_cs_w1;
    logic [AWIDTH-1:0]        dfi_address_w2;
    logic [1:0]               dfi_cke_w2;
    logic [1:0]               dfi_cs_w2;
    logic [AWIDTH-1:0]        exp_dfi_address_w2;
    logic [1:0]               exp_dfi_cke_w2;
    logic [1:0]               exp_dfi_cs_w2;
    logic [AWIDTH-1:0]        dfi_address_w3;
    logic [1:0]               dfi_cke_w3;
    logic [1:0]               dfi_cs_w3;
    logic [AWIDTH-1:0]        exp_dfi_address_w3;
    logic [1:0]               exp_dfi_cke_w3;
    logic [1:0]               exp_dfi_cs_w3;
    logic [AWIDTH-1:0]        dfi_address_w4;
    logic [1:0]               dfi_cke_w4;
    logic [1:0]               dfi_cs_w4;
    logic [AWIDTH-1:0]        exp_dfi_address_w4;
    logic [1:0]               exp_dfi_cke_w4;
    logic [1:0]               exp_dfi_cs_w4;
    logic [AWIDTH-1:0]        dfi_address_w5;
    logic [1:0]               dfi_cke_w5;
    logic [1:0]               dfi_cs_w5;
    logic [AWIDTH-1:0]        exp_dfi_address_w5;
    logic [1:0]               exp_dfi_cke_w5;
    logic [1:0]               exp_dfi_cs_w5;
    logic [AWIDTH-1:0]        dfi_address_w6;
    logic [1:0]               dfi_cke_w6;
    logic [1:0]               dfi_cs_w6;
    logic [AWIDTH-1:0]        exp_dfi_address_w6;
    logic [1:0]               exp_dfi_cke_w6;
    logic [1:0]               exp_dfi_cs_w6;
    logic [AWIDTH-1:0]        dfi_address_w7;
    logic [1:0]               dfi_cke_w7;
    logic [1:0]               dfi_cs_w7;
    logic [AWIDTH-1:0]        exp_dfi_address_w7;
    logic [1:0]               exp_dfi_cke_w7;
    logic [1:0]               exp_dfi_cs_w7;

    // Read Data
    logic [SWIDTH-1:0]        dq0_dfi_rddata_w0;
    logic [MWIDTH-1:0]        dq0_dfi_rddata_dbi_w0;
    logic                     dq0_dfi_rddata_valid_w0;
    logic [SWIDTH-1:0]        exp_dq0_dfi_rddata_w0;
    logic [MWIDTH-1:0]        exp_dq0_dfi_rddata_dbi_w0;
    logic                     exp_dq0_dfi_rddata_valid_w0;
    logic [SWIDTH-1:0]        dq0_dfi_rddata_w1;
    logic [MWIDTH-1:0]        dq0_dfi_rddata_dbi_w1;
    logic                     dq0_dfi_rddata_valid_w1;
    logic [SWIDTH-1:0]        exp_dq0_dfi_rddata_w1;
    logic [MWIDTH-1:0]        exp_dq0_dfi_rddata_dbi_w1;
    logic                     exp_dq0_dfi_rddata_valid_w1;
    logic [SWIDTH-1:0]        dq0_dfi_rddata_w2;
    logic [MWIDTH-1:0]        dq0_dfi_rddata_dbi_w2;
    logic                     dq0_dfi_rddata_valid_w2;
    logic [SWIDTH-1:0]        exp_dq0_dfi_rddata_w2;
    logic [MWIDTH-1:0]        exp_dq0_dfi_rddata_dbi_w2;
    logic                     exp_dq0_dfi_rddata_valid_w2;
    logic [SWIDTH-1:0]        dq0_dfi_rddata_w3;
    logic [MWIDTH-1:0]        dq0_dfi_rddata_dbi_w3;
    logic                     dq0_dfi_rddata_valid_w3;
    logic [SWIDTH-1:0]        exp_dq0_dfi_rddata_w3;
    logic [MWIDTH-1:0]        exp_dq0_dfi_rddata_dbi_w3;
    logic                     exp_dq0_dfi_rddata_valid_w3;
    logic [SWIDTH-1:0]        dq0_dfi_rddata_w4;
    logic [MWIDTH-1:0]        dq0_dfi_rddata_dbi_w4;
    logic                     dq0_dfi_rddata_valid_w4;
    logic [SWIDTH-1:0]        exp_dq0_dfi_rddata_w4;
    logic [MWIDTH-1:0]        exp_dq0_dfi_rddata_dbi_w4;
    logic                     exp_dq0_dfi_rddata_valid_w4;
    logic [SWIDTH-1:0]        dq0_dfi_rddata_w5;
    logic [MWIDTH-1:0]        dq0_dfi_rddata_dbi_w5;
    logic                     dq0_dfi_rddata_valid_w5;
    logic [SWIDTH-1:0]        exp_dq0_dfi_rddata_w5;
    logic [MWIDTH-1:0]        exp_dq0_dfi_rddata_dbi_w5;
    logic                     exp_dq0_dfi_rddata_valid_w5;
    logic [SWIDTH-1:0]        dq0_dfi_rddata_w6;
    logic [MWIDTH-1:0]        dq0_dfi_rddata_dbi_w6;
    logic                     dq0_dfi_rddata_valid_w6;
    logic [SWIDTH-1:0]        exp_dq0_dfi_rddata_w6;
    logic [MWIDTH-1:0]        exp_dq0_dfi_rddata_dbi_w6;
    logic                     exp_dq0_dfi_rddata_valid_w6;
    logic [SWIDTH-1:0]        dq0_dfi_rddata_w7;
    logic [MWIDTH-1:0]        dq0_dfi_rddata_dbi_w7;
    logic                     dq0_dfi_rddata_valid_w7;
    logic [SWIDTH-1:0]        exp_dq0_dfi_rddata_w7;
    logic [MWIDTH-1:0]        exp_dq0_dfi_rddata_dbi_w7;
    logic                     exp_dq0_dfi_rddata_valid_w7;
    logic [SWIDTH-1:0]        dq1_dfi_rddata_w0;
    logic [MWIDTH-1:0]        dq1_dfi_rddata_dbi_w0;
    logic                     dq1_dfi_rddata_valid_w0;
    logic [SWIDTH-1:0]        exp_dq1_dfi_rddata_w0;
    logic [MWIDTH-1:0]        exp_dq1_dfi_rddata_dbi_w0;
    logic                     exp_dq1_dfi_rddata_valid_w0;
    logic [SWIDTH-1:0]        dq1_dfi_rddata_w1;
    logic [MWIDTH-1:0]        dq1_dfi_rddata_dbi_w1;
    logic                     dq1_dfi_rddata_valid_w1;
    logic [SWIDTH-1:0]        exp_dq1_dfi_rddata_w1;
    logic [MWIDTH-1:0]        exp_dq1_dfi_rddata_dbi_w1;
    logic                     exp_dq1_dfi_rddata_valid_w1;
    logic [SWIDTH-1:0]        dq1_dfi_rddata_w2;
    logic [MWIDTH-1:0]        dq1_dfi_rddata_dbi_w2;
    logic                     dq1_dfi_rddata_valid_w2;
    logic [SWIDTH-1:0]        exp_dq1_dfi_rddata_w2;
    logic [MWIDTH-1:0]        exp_dq1_dfi_rddata_dbi_w2;
    logic                     exp_dq1_dfi_rddata_valid_w2;
    logic [SWIDTH-1:0]        dq1_dfi_rddata_w3;
    logic [MWIDTH-1:0]        dq1_dfi_rddata_dbi_w3;
    logic                     dq1_dfi_rddata_valid_w3;
    logic [SWIDTH-1:0]        exp_dq1_dfi_rddata_w3;
    logic [MWIDTH-1:0]        exp_dq1_dfi_rddata_dbi_w3;
    logic                     exp_dq1_dfi_rddata_valid_w3;
    logic [SWIDTH-1:0]        dq1_dfi_rddata_w4;
    logic [MWIDTH-1:0]        dq1_dfi_rddata_dbi_w4;
    logic                     dq1_dfi_rddata_valid_w4;
    logic [SWIDTH-1:0]        exp_dq1_dfi_rddata_w4;
    logic [MWIDTH-1:0]        exp_dq1_dfi_rddata_dbi_w4;
    logic                     exp_dq1_dfi_rddata_valid_w4;
    logic [SWIDTH-1:0]        dq1_dfi_rddata_w5;
    logic [MWIDTH-1:0]        dq1_dfi_rddata_dbi_w5;
    logic                     dq1_dfi_rddata_valid_w5;
    logic [SWIDTH-1:0]        exp_dq1_dfi_rddata_w5;
    logic [MWIDTH-1:0]        exp_dq1_dfi_rddata_dbi_w5;
    logic                     exp_dq1_dfi_rddata_valid_w5;
    logic [SWIDTH-1:0]        dq1_dfi_rddata_w6;
    logic [MWIDTH-1:0]        dq1_dfi_rddata_dbi_w6;
    logic                     dq1_dfi_rddata_valid_w6;
    logic [SWIDTH-1:0]        exp_dq1_dfi_rddata_w6;
    logic [MWIDTH-1:0]        exp_dq1_dfi_rddata_dbi_w6;
    logic                     exp_dq1_dfi_rddata_valid_w6;
    logic [SWIDTH-1:0]        dq1_dfi_rddata_w7;
    logic [MWIDTH-1:0]        dq1_dfi_rddata_dbi_w7;
    logic                     dq1_dfi_rddata_valid_w7;
    logic [SWIDTH-1:0]        exp_dq1_dfi_rddata_w7;
    logic [MWIDTH-1:0]        exp_dq1_dfi_rddata_dbi_w7;
    logic                     exp_dq1_dfi_rddata_valid_w7;
    logic [SWIDTH-1:0]        dq2_dfi_rddata_w0;
    logic [MWIDTH-1:0]        dq2_dfi_rddata_dbi_w0;
    logic                     dq2_dfi_rddata_valid_w0;
    logic [SWIDTH-1:0]        exp_dq2_dfi_rddata_w0;
    logic [MWIDTH-1:0]        exp_dq2_dfi_rddata_dbi_w0;
    logic                     exp_dq2_dfi_rddata_valid_w0;
    logic [SWIDTH-1:0]        dq2_dfi_rddata_w1;
    logic [MWIDTH-1:0]        dq2_dfi_rddata_dbi_w1;
    logic                     dq2_dfi_rddata_valid_w1;
    logic [SWIDTH-1:0]        exp_dq2_dfi_rddata_w1;
    logic [MWIDTH-1:0]        exp_dq2_dfi_rddata_dbi_w1;
    logic                     exp_dq2_dfi_rddata_valid_w1;
    logic [SWIDTH-1:0]        dq2_dfi_rddata_w2;
    logic [MWIDTH-1:0]        dq2_dfi_rddata_dbi_w2;
    logic                     dq2_dfi_rddata_valid_w2;
    logic [SWIDTH-1:0]        exp_dq2_dfi_rddata_w2;
    logic [MWIDTH-1:0]        exp_dq2_dfi_rddata_dbi_w2;
    logic                     exp_dq2_dfi_rddata_valid_w2;
    logic [SWIDTH-1:0]        dq2_dfi_rddata_w3;
    logic [MWIDTH-1:0]        dq2_dfi_rddata_dbi_w3;
    logic                     dq2_dfi_rddata_valid_w3;
    logic [SWIDTH-1:0]        exp_dq2_dfi_rddata_w3;
    logic [MWIDTH-1:0]        exp_dq2_dfi_rddata_dbi_w3;
    logic                     exp_dq2_dfi_rddata_valid_w3;
    logic [SWIDTH-1:0]        dq2_dfi_rddata_w4;
    logic [MWIDTH-1:0]        dq2_dfi_rddata_dbi_w4;
    logic                     dq2_dfi_rddata_valid_w4;
    logic [SWIDTH-1:0]        exp_dq2_dfi_rddata_w4;
    logic [MWIDTH-1:0]        exp_dq2_dfi_rddata_dbi_w4;
    logic                     exp_dq2_dfi_rddata_valid_w4;
    logic [SWIDTH-1:0]        dq2_dfi_rddata_w5;
    logic [MWIDTH-1:0]        dq2_dfi_rddata_dbi_w5;
    logic                     dq2_dfi_rddata_valid_w5;
    logic [SWIDTH-1:0]        exp_dq2_dfi_rddata_w5;
    logic [MWIDTH-1:0]        exp_dq2_dfi_rddata_dbi_w5;
    logic                     exp_dq2_dfi_rddata_valid_w5;
    logic [SWIDTH-1:0]        dq2_dfi_rddata_w6;
    logic [MWIDTH-1:0]        dq2_dfi_rddata_dbi_w6;
    logic                     dq2_dfi_rddata_valid_w6;
    logic [SWIDTH-1:0]        exp_dq2_dfi_rddata_w6;
    logic [MWIDTH-1:0]        exp_dq2_dfi_rddata_dbi_w6;
    logic                     exp_dq2_dfi_rddata_valid_w6;
    logic [SWIDTH-1:0]        dq2_dfi_rddata_w7;
    logic [MWIDTH-1:0]        dq2_dfi_rddata_dbi_w7;
    logic                     dq2_dfi_rddata_valid_w7;
    logic [SWIDTH-1:0]        exp_dq2_dfi_rddata_w7;
    logic [MWIDTH-1:0]        exp_dq2_dfi_rddata_dbi_w7;
    logic                     exp_dq2_dfi_rddata_valid_w7;
    logic [SWIDTH-1:0]        dq3_dfi_rddata_w0;
    logic [MWIDTH-1:0]        dq3_dfi_rddata_dbi_w0;
    logic                     dq3_dfi_rddata_valid_w0;
    logic [SWIDTH-1:0]        exp_dq3_dfi_rddata_w0;
    logic [MWIDTH-1:0]        exp_dq3_dfi_rddata_dbi_w0;
    logic                     exp_dq3_dfi_rddata_valid_w0;
    logic [SWIDTH-1:0]        dq3_dfi_rddata_w1;
    logic [MWIDTH-1:0]        dq3_dfi_rddata_dbi_w1;
    logic                     dq3_dfi_rddata_valid_w1;
    logic [SWIDTH-1:0]        exp_dq3_dfi_rddata_w1;
    logic [MWIDTH-1:0]        exp_dq3_dfi_rddata_dbi_w1;
    logic                     exp_dq3_dfi_rddata_valid_w1;
    logic [SWIDTH-1:0]        dq3_dfi_rddata_w2;
    logic [MWIDTH-1:0]        dq3_dfi_rddata_dbi_w2;
    logic                     dq3_dfi_rddata_valid_w2;
    logic [SWIDTH-1:0]        exp_dq3_dfi_rddata_w2;
    logic [MWIDTH-1:0]        exp_dq3_dfi_rddata_dbi_w2;
    logic                     exp_dq3_dfi_rddata_valid_w2;
    logic [SWIDTH-1:0]        dq3_dfi_rddata_w3;
    logic [MWIDTH-1:0]        dq3_dfi_rddata_dbi_w3;
    logic                     dq3_dfi_rddata_valid_w3;
    logic [SWIDTH-1:0]        exp_dq3_dfi_rddata_w3;
    logic [MWIDTH-1:0]        exp_dq3_dfi_rddata_dbi_w3;
    logic                     exp_dq3_dfi_rddata_valid_w3;
    logic [SWIDTH-1:0]        dq3_dfi_rddata_w4;
    logic [MWIDTH-1:0]        dq3_dfi_rddata_dbi_w4;
    logic                     dq3_dfi_rddata_valid_w4;
    logic [SWIDTH-1:0]        exp_dq3_dfi_rddata_w4;
    logic [MWIDTH-1:0]        exp_dq3_dfi_rddata_dbi_w4;
    logic                     exp_dq3_dfi_rddata_valid_w4;
    logic [SWIDTH-1:0]        dq3_dfi_rddata_w5;
    logic [MWIDTH-1:0]        dq3_dfi_rddata_dbi_w5;
    logic                     dq3_dfi_rddata_valid_w5;
    logic [SWIDTH-1:0]        exp_dq3_dfi_rddata_w5;
    logic [MWIDTH-1:0]        exp_dq3_dfi_rddata_dbi_w5;
    logic                     exp_dq3_dfi_rddata_valid_w5;
    logic [SWIDTH-1:0]        dq3_dfi_rddata_w6;
    logic [MWIDTH-1:0]        dq3_dfi_rddata_dbi_w6;
    logic                     dq3_dfi_rddata_valid_w6;
    logic [SWIDTH-1:0]        exp_dq3_dfi_rddata_w6;
    logic [MWIDTH-1:0]        exp_dq3_dfi_rddata_dbi_w6;
    logic                     exp_dq3_dfi_rddata_valid_w6;
    logic [SWIDTH-1:0]        dq3_dfi_rddata_w7;
    logic [MWIDTH-1:0]        dq3_dfi_rddata_dbi_w7;
    logic                     dq3_dfi_rddata_valid_w7;
    logic [SWIDTH-1:0]        exp_dq3_dfi_rddata_w7;
    logic [MWIDTH-1:0]        exp_dq3_dfi_rddata_dbi_w7;
    logic                     exp_dq3_dfi_rddata_valid_w7;
    begin
        {
            timestamp
            ,dfi_cs_w0
            ,dfi_cke_w0
            ,dfi_address_w0
            ,dfi_cs_w1
            ,dfi_cke_w1
            ,dfi_address_w1
            ,dfi_cs_w2
            ,dfi_cke_w2
            ,dfi_address_w2
            ,dfi_cs_w3
            ,dfi_cke_w3
            ,dfi_address_w3
            ,dfi_cs_w4
            ,dfi_cke_w4
            ,dfi_address_w4
            ,dfi_cs_w5
            ,dfi_cke_w5
            ,dfi_address_w5
            ,dfi_cs_w6
            ,dfi_cke_w6
            ,dfi_address_w6
            ,dfi_cs_w7
            ,dfi_cke_w7
            ,dfi_address_w7
            ,dq0_dfi_rddata_valid_w0
            ,dq0_dfi_rddata_dbi_w0
            ,dq0_dfi_rddata_w0
            ,dq0_dfi_rddata_valid_w1
            ,dq0_dfi_rddata_dbi_w1
            ,dq0_dfi_rddata_w1
            ,dq0_dfi_rddata_valid_w2
            ,dq0_dfi_rddata_dbi_w2
            ,dq0_dfi_rddata_w2
            ,dq0_dfi_rddata_valid_w3
            ,dq0_dfi_rddata_dbi_w3
            ,dq0_dfi_rddata_w3
            ,dq0_dfi_rddata_valid_w4
            ,dq0_dfi_rddata_dbi_w4
            ,dq0_dfi_rddata_w4
            ,dq0_dfi_rddata_valid_w5
            ,dq0_dfi_rddata_dbi_w5
            ,dq0_dfi_rddata_w5
            ,dq0_dfi_rddata_valid_w6
            ,dq0_dfi_rddata_dbi_w6
            ,dq0_dfi_rddata_w6
            ,dq0_dfi_rddata_valid_w7
            ,dq0_dfi_rddata_dbi_w7
            ,dq0_dfi_rddata_w7
            ,dq1_dfi_rddata_valid_w0
            ,dq1_dfi_rddata_dbi_w0
            ,dq1_dfi_rddata_w0
            ,dq1_dfi_rddata_valid_w1
            ,dq1_dfi_rddata_dbi_w1
            ,dq1_dfi_rddata_w1
            ,dq1_dfi_rddata_valid_w2
            ,dq1_dfi_rddata_dbi_w2
            ,dq1_dfi_rddata_w2
            ,dq1_dfi_rddata_valid_w3
            ,dq1_dfi_rddata_dbi_w3
            ,dq1_dfi_rddata_w3
            ,dq1_dfi_rddata_valid_w4
            ,dq1_dfi_rddata_dbi_w4
            ,dq1_dfi_rddata_w4
            ,dq1_dfi_rddata_valid_w5
            ,dq1_dfi_rddata_dbi_w5
            ,dq1_dfi_rddata_w5
            ,dq1_dfi_rddata_valid_w6
            ,dq1_dfi_rddata_dbi_w6
            ,dq1_dfi_rddata_w6
            ,dq1_dfi_rddata_valid_w7
            ,dq1_dfi_rddata_dbi_w7
            ,dq1_dfi_rddata_w7
            ,dq2_dfi_rddata_valid_w0
            ,dq2_dfi_rddata_dbi_w0
            ,dq2_dfi_rddata_w0
            ,dq2_dfi_rddata_valid_w1
            ,dq2_dfi_rddata_dbi_w1
            ,dq2_dfi_rddata_w1
            ,dq2_dfi_rddata_valid_w2
            ,dq2_dfi_rddata_dbi_w2
            ,dq2_dfi_rddata_w2
            ,dq2_dfi_rddata_valid_w3
            ,dq2_dfi_rddata_dbi_w3
            ,dq2_dfi_rddata_w3
            ,dq2_dfi_rddata_valid_w4
            ,dq2_dfi_rddata_dbi_w4
            ,dq2_dfi_rddata_w4
            ,dq2_dfi_rddata_valid_w5
            ,dq2_dfi_rddata_dbi_w5
            ,dq2_dfi_rddata_w5
            ,dq2_dfi_rddata_valid_w6
            ,dq2_dfi_rddata_dbi_w6
            ,dq2_dfi_rddata_w6
            ,dq2_dfi_rddata_valid_w7
            ,dq2_dfi_rddata_dbi_w7
            ,dq2_dfi_rddata_w7
            ,dq3_dfi_rddata_valid_w0
            ,dq3_dfi_rddata_dbi_w0
            ,dq3_dfi_rddata_w0
            ,dq3_dfi_rddata_valid_w1
            ,dq3_dfi_rddata_dbi_w1
            ,dq3_dfi_rddata_w1
            ,dq3_dfi_rddata_valid_w2
            ,dq3_dfi_rddata_dbi_w2
            ,dq3_dfi_rddata_w2
            ,dq3_dfi_rddata_valid_w3
            ,dq3_dfi_rddata_dbi_w3
            ,dq3_dfi_rddata_w3
            ,dq3_dfi_rddata_valid_w4
            ,dq3_dfi_rddata_dbi_w4
            ,dq3_dfi_rddata_w4
            ,dq3_dfi_rddata_valid_w5
            ,dq3_dfi_rddata_dbi_w5
            ,dq3_dfi_rddata_w5
            ,dq3_dfi_rddata_valid_w6
            ,dq3_dfi_rddata_dbi_w6
            ,dq3_dfi_rddata_w6
            ,dq3_dfi_rddata_valid_w7
            ,dq3_dfi_rddata_dbi_w7
            ,dq3_dfi_rddata_w7
        } = rdata ;

        {
            exp_timestamp
            ,exp_dfi_cs_w0
            ,exp_dfi_cke_w0
            ,exp_dfi_address_w0
            ,exp_dfi_cs_w1
            ,exp_dfi_cke_w1
            ,exp_dfi_address_w1
            ,exp_dfi_cs_w2
            ,exp_dfi_cke_w2
            ,exp_dfi_address_w2
            ,exp_dfi_cs_w3
            ,exp_dfi_cke_w3
            ,exp_dfi_address_w3
            ,exp_dfi_cs_w4
            ,exp_dfi_cke_w4
            ,exp_dfi_address_w4
            ,exp_dfi_cs_w5
            ,exp_dfi_cke_w5
            ,exp_dfi_address_w5
            ,exp_dfi_cs_w6
            ,exp_dfi_cke_w6
            ,exp_dfi_address_w6
            ,exp_dfi_cs_w7
            ,exp_dfi_cke_w7
            ,exp_dfi_address_w7
            ,exp_dq0_dfi_rddata_valid_w0
            ,exp_dq0_dfi_rddata_dbi_w0
            ,exp_dq0_dfi_rddata_w0
            ,exp_dq0_dfi_rddata_valid_w1
            ,exp_dq0_dfi_rddata_dbi_w1
            ,exp_dq0_dfi_rddata_w1
            ,exp_dq0_dfi_rddata_valid_w2
            ,exp_dq0_dfi_rddata_dbi_w2
            ,exp_dq0_dfi_rddata_w2
            ,exp_dq0_dfi_rddata_valid_w3
            ,exp_dq0_dfi_rddata_dbi_w3
            ,exp_dq0_dfi_rddata_w3
            ,exp_dq0_dfi_rddata_valid_w4
            ,exp_dq0_dfi_rddata_dbi_w4
            ,exp_dq0_dfi_rddata_w4
            ,exp_dq0_dfi_rddata_valid_w5
            ,exp_dq0_dfi_rddata_dbi_w5
            ,exp_dq0_dfi_rddata_w5
            ,exp_dq0_dfi_rddata_valid_w6
            ,exp_dq0_dfi_rddata_dbi_w6
            ,exp_dq0_dfi_rddata_w6
            ,exp_dq0_dfi_rddata_valid_w7
            ,exp_dq0_dfi_rddata_dbi_w7
            ,exp_dq0_dfi_rddata_w7
            ,exp_dq1_dfi_rddata_valid_w0
            ,exp_dq1_dfi_rddata_dbi_w0
            ,exp_dq1_dfi_rddata_w0
            ,exp_dq1_dfi_rddata_valid_w1
            ,exp_dq1_dfi_rddata_dbi_w1
            ,exp_dq1_dfi_rddata_w1
            ,exp_dq1_dfi_rddata_valid_w2
            ,exp_dq1_dfi_rddata_dbi_w2
            ,exp_dq1_dfi_rddata_w2
            ,exp_dq1_dfi_rddata_valid_w3
            ,exp_dq1_dfi_rddata_dbi_w3
            ,exp_dq1_dfi_rddata_w3
            ,exp_dq1_dfi_rddata_valid_w4
            ,exp_dq1_dfi_rddata_dbi_w4
            ,exp_dq1_dfi_rddata_w4
            ,exp_dq1_dfi_rddata_valid_w5
            ,exp_dq1_dfi_rddata_dbi_w5
            ,exp_dq1_dfi_rddata_w5
            ,exp_dq1_dfi_rddata_valid_w6
            ,exp_dq1_dfi_rddata_dbi_w6
            ,exp_dq1_dfi_rddata_w6
            ,exp_dq1_dfi_rddata_valid_w7
            ,exp_dq1_dfi_rddata_dbi_w7
            ,exp_dq1_dfi_rddata_w7
            ,exp_dq2_dfi_rddata_valid_w0
            ,exp_dq2_dfi_rddata_dbi_w0
            ,exp_dq2_dfi_rddata_w0
            ,exp_dq2_dfi_rddata_valid_w1
            ,exp_dq2_dfi_rddata_dbi_w1
            ,exp_dq2_dfi_rddata_w1
            ,exp_dq2_dfi_rddata_valid_w2
            ,exp_dq2_dfi_rddata_dbi_w2
            ,exp_dq2_dfi_rddata_w2
            ,exp_dq2_dfi_rddata_valid_w3
            ,exp_dq2_dfi_rddata_dbi_w3
            ,exp_dq2_dfi_rddata_w3
            ,exp_dq2_dfi_rddata_valid_w4
            ,exp_dq2_dfi_rddata_dbi_w4
            ,exp_dq2_dfi_rddata_w4
            ,exp_dq2_dfi_rddata_valid_w5
            ,exp_dq2_dfi_rddata_dbi_w5
            ,exp_dq2_dfi_rddata_w5
            ,exp_dq2_dfi_rddata_valid_w6
            ,exp_dq2_dfi_rddata_dbi_w6
            ,exp_dq2_dfi_rddata_w6
            ,exp_dq2_dfi_rddata_valid_w7
            ,exp_dq2_dfi_rddata_dbi_w7
            ,exp_dq2_dfi_rddata_w7
            ,exp_dq3_dfi_rddata_valid_w0
            ,exp_dq3_dfi_rddata_dbi_w0
            ,exp_dq3_dfi_rddata_w0
            ,exp_dq3_dfi_rddata_valid_w1
            ,exp_dq3_dfi_rddata_dbi_w1
            ,exp_dq3_dfi_rddata_w1
            ,exp_dq3_dfi_rddata_valid_w2
            ,exp_dq3_dfi_rddata_dbi_w2
            ,exp_dq3_dfi_rddata_w2
            ,exp_dq3_dfi_rddata_valid_w3
            ,exp_dq3_dfi_rddata_dbi_w3
            ,exp_dq3_dfi_rddata_w3
            ,exp_dq3_dfi_rddata_valid_w4
            ,exp_dq3_dfi_rddata_dbi_w4
            ,exp_dq3_dfi_rddata_w4
            ,exp_dq3_dfi_rddata_valid_w5
            ,exp_dq3_dfi_rddata_dbi_w5
            ,exp_dq3_dfi_rddata_w5
            ,exp_dq3_dfi_rddata_valid_w6
            ,exp_dq3_dfi_rddata_dbi_w6
            ,exp_dq3_dfi_rddata_w6
            ,exp_dq3_dfi_rddata_valid_w7
            ,exp_dq3_dfi_rddata_dbi_w7
            ,exp_dq3_dfi_rddata_w7
        } = rdata_expected ;

        err_cnt = 0;
        case ({byte_sel, mode})
            {DQ_ALL, DDR_2}  : begin
                data_match = 1'b1
                & (exp_dq3_dfi_rddata_w1 === dq3_dfi_rddata_w1)
                & (exp_dq3_dfi_rddata_w0 === dq3_dfi_rddata_w0)
                & (exp_dq2_dfi_rddata_w1 === dq2_dfi_rddata_w1)
                & (exp_dq2_dfi_rddata_w0 === dq2_dfi_rddata_w0)
                & (exp_dq1_dfi_rddata_w1 === dq1_dfi_rddata_w1)
                & (exp_dq1_dfi_rddata_w0 === dq1_dfi_rddata_w0)
                & (exp_dq0_dfi_rddata_w1 === dq0_dfi_rddata_w1)
                & (exp_dq0_dfi_rddata_w0 === dq0_dfi_rddata_w0)
                & 1'b1;

                if (data_match != 1'b1) begin
                    $display ("Error: RDATA MISMATCH DQ0 or DQ1 :  {DQ1_w1, DQ1_w0, DQ0_w1, DQ0_w0} Rcvd = %x %x %x %x Exp = %x %x %x %x", dq1_dfi_rddata_w1, dq1_dfi_rddata_w0, dq0_dfi_rddata_w1 , dq0_dfi_rddata_w0, exp_dq1_dfi_rddata_w1, exp_dq1_dfi_rddata_w0, exp_dq0_dfi_rddata_w1 , exp_dq0_dfi_rddata_w0 );
                    err_cnt = err_cnt + 1;
                end
                else begin
                    $display ("Info: RDATA MATCH DQ0 or DQ1 :  {DQ1_w1, DQ1_w0, DQ0_w1, DQ0_w0} Rcvd = %x %x %x %x Exp = %x %x %x %x", dq1_dfi_rddata_w1, dq1_dfi_rddata_w0, dq0_dfi_rddata_w1 , dq0_dfi_rddata_w0, exp_dq1_dfi_rddata_w1, exp_dq1_dfi_rddata_w0, exp_dq0_dfi_rddata_w1 , exp_dq0_dfi_rddata_w0 );
                end
            end

            {DQ_ALL, DDR_4}  : begin
                data_match = 1'b1
                & (exp_dq3_dfi_rddata_w3 === dq3_dfi_rddata_w3)
                & (exp_dq3_dfi_rddata_w2 === dq3_dfi_rddata_w2)
                & (exp_dq3_dfi_rddata_w1 === dq3_dfi_rddata_w1)
                & (exp_dq3_dfi_rddata_w0 === dq3_dfi_rddata_w0)
                & (exp_dq2_dfi_rddata_w3 === dq2_dfi_rddata_w3)
                & (exp_dq2_dfi_rddata_w2 === dq2_dfi_rddata_w2)
                & (exp_dq2_dfi_rddata_w1 === dq2_dfi_rddata_w1)
                & (exp_dq2_dfi_rddata_w0 === dq2_dfi_rddata_w0)
                & (exp_dq1_dfi_rddata_w3 === dq1_dfi_rddata_w3)
                & (exp_dq1_dfi_rddata_w2 === dq1_dfi_rddata_w2)
                & (exp_dq1_dfi_rddata_w1 === dq1_dfi_rddata_w1)
                & (exp_dq1_dfi_rddata_w0 === dq1_dfi_rddata_w0)
                & (exp_dq0_dfi_rddata_w3 === dq0_dfi_rddata_w3)
                & (exp_dq0_dfi_rddata_w2 === dq0_dfi_rddata_w2)
                & (exp_dq0_dfi_rddata_w1 === dq0_dfi_rddata_w1)
                & (exp_dq0_dfi_rddata_w0 === dq0_dfi_rddata_w0)
                & 1'b1;

                if (data_match != 1'b1) begin
                    $display ("Error: RDATA MISMATCH DQ0 or DQ1 :  {DQ1_w3, DQ1_w2, DQ1_w1, DQ1_w0, DQ0_w3, DQ0_w2, DQ0_w1, DQ0_w0} Rcvd = %x %x %x %x %x %x %x %x Exp = %x %x %x %x %x %x %x %x", dq1_dfi_rddata_w3, dq1_dfi_rddata_w2, dq1_dfi_rddata_w1, dq0_dfi_rddata_w3, dq0_dfi_rddata_w2, dq1_dfi_rddata_w0, dq0_dfi_rddata_w1 , dq0_dfi_rddata_w0, exp_dq1_dfi_rddata_w3, exp_dq1_dfi_rddata_w2, exp_dq1_dfi_rddata_w1, exp_dq1_dfi_rddata_w0, exp_dq0_dfi_rddata_w3 , exp_dq0_dfi_rddata_w2, exp_dq0_dfi_rddata_w1 , exp_dq0_dfi_rddata_w0 );
                    err_cnt = err_cnt + 1;
                end
                else begin
                    $display ("Info: RDATA MATCH DQ0 or DQ1 :  {DQ1_w3, DQ1_w2, DQ1_w1, DQ1_w0, DQ0_w3, DQ0_w2, DQ0_w1, DQ0_w0} Rcvd = %x %x %x %x %x %x %x %x Exp = %x %x %x %x %x %x %x %x", dq1_dfi_rddata_w3, dq1_dfi_rddata_w2, dq1_dfi_rddata_w1, dq0_dfi_rddata_w3, dq0_dfi_rddata_w2, dq1_dfi_rddata_w0, dq0_dfi_rddata_w1 , dq0_dfi_rddata_w0, exp_dq1_dfi_rddata_w3, exp_dq1_dfi_rddata_w2, exp_dq1_dfi_rddata_w1, exp_dq1_dfi_rddata_w0, exp_dq0_dfi_rddata_w3 , exp_dq0_dfi_rddata_w2, exp_dq0_dfi_rddata_w1 , exp_dq0_dfi_rddata_w0 );
                end
            end
            {DQ_ALL, DDR_ALL} : begin
                data_match = 1'b1
                & (exp_dq3_dfi_rddata_w7 === dq3_dfi_rddata_w7)
                & (exp_dq3_dfi_rddata_w6 === dq3_dfi_rddata_w6)
                & (exp_dq3_dfi_rddata_w5 === dq3_dfi_rddata_w5)
                & (exp_dq3_dfi_rddata_w4 === dq3_dfi_rddata_w4)
                & (exp_dq3_dfi_rddata_w3 === dq3_dfi_rddata_w3)
                & (exp_dq3_dfi_rddata_w2 === dq3_dfi_rddata_w2)
                & (exp_dq3_dfi_rddata_w1 === dq3_dfi_rddata_w1)
                & (exp_dq3_dfi_rddata_w0 === dq3_dfi_rddata_w0)
                & (exp_dq2_dfi_rddata_w7 === dq2_dfi_rddata_w7)
                & (exp_dq2_dfi_rddata_w6 === dq2_dfi_rddata_w6)
                & (exp_dq2_dfi_rddata_w5 === dq2_dfi_rddata_w5)
                & (exp_dq2_dfi_rddata_w4 === dq2_dfi_rddata_w4)
                & (exp_dq2_dfi_rddata_w3 === dq2_dfi_rddata_w3)
                & (exp_dq2_dfi_rddata_w2 === dq2_dfi_rddata_w2)
                & (exp_dq2_dfi_rddata_w1 === dq2_dfi_rddata_w1)
                & (exp_dq2_dfi_rddata_w0 === dq2_dfi_rddata_w0)
                & (exp_dq1_dfi_rddata_w7 === dq1_dfi_rddata_w7)
                & (exp_dq1_dfi_rddata_w6 === dq1_dfi_rddata_w6)
                & (exp_dq1_dfi_rddata_w5 === dq1_dfi_rddata_w5)
                & (exp_dq1_dfi_rddata_w4 === dq1_dfi_rddata_w4)
                & (exp_dq1_dfi_rddata_w3 === dq1_dfi_rddata_w3)
                & (exp_dq1_dfi_rddata_w2 === dq1_dfi_rddata_w2)
                & (exp_dq1_dfi_rddata_w1 === dq1_dfi_rddata_w1)
                & (exp_dq1_dfi_rddata_w0 === dq1_dfi_rddata_w0)
                & (exp_dq0_dfi_rddata_w7 === dq0_dfi_rddata_w7)
                & (exp_dq0_dfi_rddata_w6 === dq0_dfi_rddata_w6)
                & (exp_dq0_dfi_rddata_w5 === dq0_dfi_rddata_w5)
                & (exp_dq0_dfi_rddata_w4 === dq0_dfi_rddata_w4)
                & (exp_dq0_dfi_rddata_w3 === dq0_dfi_rddata_w3)
                & (exp_dq0_dfi_rddata_w2 === dq0_dfi_rddata_w2)
                & (exp_dq0_dfi_rddata_w1 === dq0_dfi_rddata_w1)
                & (exp_dq0_dfi_rddata_w0 === dq0_dfi_rddata_w0)
                & 1'b1;
                if (data_match != 1'b1) begin
                    $display ("Error: RDATA MISMATCH DQ0 or DQ1 : {DQ1_w3, DQ1_w2, DQ1_w1, DQ1_w0, DQ0_w3, DQ0_w2, DQ0_w1, DQ0_w0} Rcvd = %x %x %x %x %x %x %x %x Exp = %x %x %x %x %x %x %x %x", dq1_dfi_rddata_w3, dq1_dfi_rddata_w2, dq1_dfi_rddata_w1, dq0_dfi_rddata_w3, dq0_dfi_rddata_w2, dq1_dfi_rddata_w0, dq0_dfi_rddata_w1 , dq0_dfi_rddata_w0, exp_dq1_dfi_rddata_w3, exp_dq1_dfi_rddata_w2, exp_dq1_dfi_rddata_w1, exp_dq1_dfi_rddata_w0, exp_dq0_dfi_rddata_w3 , exp_dq0_dfi_rddata_w2, exp_dq0_dfi_rddata_w1 , exp_dq0_dfi_rddata_w0 );
                    err_cnt = err_cnt + 1;
                end
                else begin
                    $display ("Info: RDATA MATCH DQ0 or DQ1 :  {DQ1_w3, DQ1_w2, DQ1_w1, DQ1_w0, DQ0_w3, DQ0_w2, DQ0_w1, DQ0_w0} Rcvd = %x %x %x %x %x %x %x %x Exp = %x %x %x %x %x %x %x %x", dq1_dfi_rddata_w3, dq1_dfi_rddata_w2, dq1_dfi_rddata_w1, dq0_dfi_rddata_w3, dq0_dfi_rddata_w2, dq1_dfi_rddata_w0, dq0_dfi_rddata_w1 , dq0_dfi_rddata_w0, exp_dq1_dfi_rddata_w3, exp_dq1_dfi_rddata_w2, exp_dq1_dfi_rddata_w1, exp_dq1_dfi_rddata_w0, exp_dq0_dfi_rddata_w3 , exp_dq0_dfi_rddata_w2, exp_dq0_dfi_rddata_w1 , exp_dq0_dfi_rddata_w0 );
                end
            end
            {DQ_ALL,SDR_1} : begin
                data_match = 1'b1
                & (exp_dq3_dfi_rddata_w0 === dq3_dfi_rddata_w0)
                & (exp_dq2_dfi_rddata_w0 === dq2_dfi_rddata_w0)
                & (exp_dq1_dfi_rddata_w0 === dq1_dfi_rddata_w0)
                & (exp_dq0_dfi_rddata_w0 === dq0_dfi_rddata_w0)
                & 1'b1;

                if (data_match != 1'b1) begin
                    $display ("Error: RDATA MISMATCH DQ0 or DQ1 :  { DQ1_w0, DQ0_w0} Rcvd = %x %x Exp = %x %x", dq1_dfi_rddata_w0, dq0_dfi_rddata_w0, exp_dq1_dfi_rddata_w0, exp_dq0_dfi_rddata_w0 );
                    err_cnt = err_cnt + 1;
                end
                else begin
                    $display ("Info: RDATA MATCH DQ0 or DQ1 :  { DQ1_w0, DQ0_w0} Rcvd = %x %x Exp = %x %x", dq1_dfi_rddata_w0, dq0_dfi_rddata_w0, exp_dq1_dfi_rddata_w0, exp_dq0_dfi_rddata_w0 );
                end
            end
            {CA,SDR_1} : begin
                data_match = 1'b1
                & (exp_dfi_address_w0 === dfi_address_w0)
                & (exp_dfi_cke_w0 === dfi_cke_w0)
                & (exp_dfi_cs_w0 === dfi_cs_w0)
                & 1'b1;

                if (data_match != 1'b1) begin
                    $display ("Error: RDATA MISMATCH CA :  { CA_w0, CS_w0 CKE_w0} Rcvd = %x %x %x Exp = %x %x %x", dfi_address_w0, dfi_cs_w0, dfi_cke_w0, exp_dfi_address_w0, exp_dfi_cs_w0, exp_dfi_cke_w0 );
                    err_cnt = err_cnt + 1;
                end
                else begin
                    $display ("Info: RDATA MATCH CA :  { CA_w0, CS_w0 CKE_w0} Rcvd = %x %x %x Exp = %x %x %x", dfi_address_w0, dfi_cs_w0, dfi_cke_w0, exp_dfi_address_w0, exp_dfi_cs_w0, exp_dfi_cke_w0 );
                end
            end
            {CA,DDR_2} : begin
                data_match = 1'b1
                & (exp_dfi_address_w1 === dfi_address_w1)
                & (exp_dfi_cke_w1 === dfi_cke_w1)
                & (exp_dfi_cs_w1 === dfi_cs_w1)
                & (exp_dfi_address_w0 === dfi_address_w0)
                & (exp_dfi_cke_w0 === dfi_cke_w0)
                & (exp_dfi_cs_w0 === dfi_cs_w0)
                & 1'b1;

                if (data_match != 1'b1) begin
                    $display ("Error: RDATA MISMATCH CA :  { CA_w1, CS_w1 CKE_w1, CA_w0, CS_w0 CKE_w0} Rcvd = %x %x %x %x %x %x Exp = %x %x %x %x %x %x", dfi_address_w1, dfi_cs_w1, dfi_cke_w1, dfi_address_w0, dfi_cs_w0, dfi_cke_w0, exp_dfi_address_w1, exp_dfi_cs_w1, exp_dfi_cke_w1, exp_dfi_address_w0, exp_dfi_cs_w0, exp_dfi_cke_w0 );
                    err_cnt = err_cnt + 1;
                end
            end
            {CA,DDR_ALL} : begin
                data_match = 1'b1
                & (exp_dfi_address_w7 === dfi_address_w7)
                & (exp_dfi_cke_w7 === dfi_cke_w7)
                & (exp_dfi_cs_w7 === dfi_cs_w7)
                & (exp_dfi_address_w6 === dfi_address_w6)
                & (exp_dfi_cke_w6 === dfi_cke_w6)
                & (exp_dfi_cs_w6 === dfi_cs_w6)
                & (exp_dfi_address_w5 === dfi_address_w5)
                & (exp_dfi_cke_w5 === dfi_cke_w5)
                & (exp_dfi_cs_w5 === dfi_cs_w5)
                & (exp_dfi_address_w4 === dfi_address_w4)
                & (exp_dfi_cke_w4 === dfi_cke_w4)
                & (exp_dfi_cs_w4 === dfi_cs_w4)
                & (exp_dfi_address_w3 === dfi_address_w3)
                & (exp_dfi_cke_w3 === dfi_cke_w3)
                & (exp_dfi_cs_w3 === dfi_cs_w3)
                & (exp_dfi_address_w2 === dfi_address_w2)
                & (exp_dfi_cke_w2 === dfi_cke_w2)
                & (exp_dfi_cs_w2 === dfi_cs_w2)
                & (exp_dfi_address_w1 === dfi_address_w1)
                & (exp_dfi_cke_w1 === dfi_cke_w1)
                & (exp_dfi_cs_w1 === dfi_cs_w1)
                & (exp_dfi_address_w0 === dfi_address_w0)
                & (exp_dfi_cke_w0 === dfi_cke_w0)
                & (exp_dfi_cs_w0 === dfi_cs_w0)
                & 1'b1;
                if (data_match != 1'b1) begin
                    $display ("Error: RDATA MISMATCH CA :  { CA_w3, CS_w3, CKE_w3, CA_w2, CS_w2, CKE_w2, CA_w1, CS_w1, CKE_w1, CA_w0, CS_w0, CKE_w0} Rcvd = %x %x %x %x %x %x %x %x %x %x %x %x Exp = %x %x %x %x %x %x %x %x %x %x %x %x", dfi_address_w3, dfi_cs_w3, dfi_cke_w3, dfi_address_w2, dfi_cs_w2, dfi_cke_w2, dfi_address_w1, dfi_cs_w1, dfi_cke_w1, dfi_address_w0, dfi_cs_w0, dfi_cke_w0, exp_dfi_address_w3, exp_dfi_cs_w3, exp_dfi_cke_w3, exp_dfi_address_w2, exp_dfi_cs_w2, exp_dfi_cke_w2, exp_dfi_address_w1, exp_dfi_cs_w1, exp_dfi_cke_w1, exp_dfi_address_w0, exp_dfi_cs_w0, exp_dfi_cke_w0 );
                    err_cnt = err_cnt + 1;
                end
            end
            default: begin
                $display ("ERROR: Incorrect mode specified for data check. Data checker is OFF. byte_sel = %x. \n", byte_sel);
                err_cnt = err_cnt+1;
            end
        endcase

    end
endtask

task automatic set_phy_ch1_disable ;
    begin
        //Disable  CH1 DQ0, DQ1
        `CSR_WRF1(DDR_CH1_DQ0_OFFSET,DDR_DQ_TOP_CFG,TRAINING_MODE, 1'b1 );
        `CSR_WRF1(DDR_CH1_DQ1_OFFSET,DDR_DQ_TOP_CFG,TRAINING_MODE, 1'b1 );
        `CSR_WRF1(DDR_CH1_CA_OFFSET ,DDR_CA_TOP_CFG,TRAINING_MODE, 1'b1 );
        `CSR_WRF1(DDR_DFICH0_OFFSET ,DDR_DFICH_TOP_1_CFG,DQBYTE_RDVALID_MASK, 4'hC );
        `CSR_WRF1(DDR_DFI_OFFSET    ,DDR_DFI_TOP_0_CFG,CA_LPBK_SEL, 1'b0 );
    end
endtask

task automatic set_phy_ch0_disable ;
    begin
        //Disable  CH1 DQ0, DQ1
        `CSR_WRF1(DDR_CH0_DQ0_OFFSET,DDR_DQ_TOP_CFG,TRAINING_MODE, 1'b1 );
        `CSR_WRF1(DDR_CH0_DQ1_OFFSET,DDR_DQ_TOP_CFG,TRAINING_MODE, 1'b1 );
        `CSR_WRF1(DDR_CH0_CA_OFFSET ,DDR_CA_TOP_CFG,TRAINING_MODE, 1'b1 );
        `CSR_WRF1(DDR_DFICH0_OFFSET ,DDR_DFICH_TOP_1_CFG,DQBYTE_RDVALID_MASK, 4'h3 );
        `CSR_WRF1(DDR_DFI_OFFSET    ,DDR_DFI_TOP_0_CFG,CA_LPBK_SEL, 1'b1 );
    end
endtask

task automatic set_phy_ch0_ch1_enable ;
    begin
        //Disable  CH1 DQ0, DQ1
        `CSR_WRF1(DDR_CH0_DQ0_OFFSET,DDR_DQ_TOP_CFG,TRAINING_MODE, 1'b0 );
        `CSR_WRF1(DDR_CH0_DQ1_OFFSET,DDR_DQ_TOP_CFG,TRAINING_MODE, 1'b0 );
        `CSR_WRF1(DDR_CH0_CA_OFFSET ,DDR_CA_TOP_CFG,TRAINING_MODE, 1'b0 );
        `CSR_WRF1(DDR_CH1_DQ0_OFFSET,DDR_DQ_TOP_CFG,TRAINING_MODE, 1'b0 );
        `CSR_WRF1(DDR_CH1_DQ1_OFFSET,DDR_DQ_TOP_CFG,TRAINING_MODE, 1'b0 );
        `CSR_WRF1(DDR_CH1_CA_OFFSET ,DDR_CA_TOP_CFG,TRAINING_MODE, 1'b0 );
        `CSR_WRF1(DDR_DFICH0_OFFSET ,DDR_DFICH_TOP_1_CFG,DQBYTE_RDVALID_MASK, 4'hF );
        `CSR_WRF1(DDR_DFI_OFFSET    ,DDR_DFI_TOP_0_CFG,CA_LPBK_SEL, 1'b0 ); // select CH0_CA for loop back
    end
endtask

task automatic set_debug_bus ;
 	input bit ovr_sel;
	input bit[31:0] val;
	input bit[3:0] debug_bus_sel;
	input bit[3:0]debug_bus_sel1;
 begin
 if(ovr_sel ==1)begin
`CSR_WRF1(DDR_CTRL_OFFSET,DDR_CTRL_DEBUG1_CFG,OVR_SEL,ovr_sel );
`CSR_WRF1(DDR_CTRL_OFFSET,DDR_CTRL_DEBUG_CFG,VAL,val);
end
else if(ovr_sel ==0 && debug_bus_sel !=0) begin
`CSR_WRF1(DDR_CTRL_OFFSET,DDR_CTRL_DEBUG1_CFG,OVR_SEL, ovr_sel);
`CSR_WRF1(DDR_DFI_OFFSET,DDR_DFI_DEBUG_CFG,DEBUG_BUS_SEL, debug_bus_sel);
end
else if(ovr_sel ==0 && debug_bus_sel1 !=0) begin
`CSR_WRF1(DDR_CTRL_OFFSET,DDR_CTRL_DEBUG1_CFG,OVR_SEL, ovr_sel);
`CSR_WRF1(DDR_FSW_OFFSET,DDR_FSW_DEBUG_CFG,DEBUG_BUS_SEL,debug_bus_sel1);
end
end
endtask

task automatic pad_ddr_test;
	input bit[10:8] dtst_drvr_impd;
	input bit[16:12] dtst_ext_sel;

begin
`CSR_WRF1( DDR_CMN_OFFSET, DDR_CMN_TEST_CFG,DTST_DRVR_IMPD, dtst_drvr_impd);
`CSR_WRF1( DDR_CMN_OFFSET, DDR_CMN_TEST_CFG,DTST_EXT_SEL, dtst_ext_sel);
#10ns;

end
endtask

task automatic set_sa_lpde_dly;
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
                    `CSR_WRF8(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M0_R0_CFG_0,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r0_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M0_R0_CFG_0,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r0_dly,gear,0,0,0,0,0,0);
                end
                {RANK0,8'd1}: begin
                    `CSR_WRF8(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M0_R0_CFG_1,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r0_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M0_R0_CFG_1,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r0_dly,gear,0,0,0,0,0,0);
                end
                {RANK0,8'd2}: begin
                    `CSR_WRF8(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M0_R0_CFG_2,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r0_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M0_R0_CFG_2,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r0_dly,gear,0,0,0,0,0,0);
                end
                {RANK0,8'd3}: begin
                    `CSR_WRF8(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M0_R0_CFG_3,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r0_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M0_R0_CFG_3,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r0_dly,gear,0,0,0,0,0,0);
                end
                {RANK0,8'd4}: begin
                    `CSR_WRF8(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M0_R0_CFG_4,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r0_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M0_R0_CFG_4,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r0_dly,gear,0,0,0,0,0,0);
                end
                {RANK0,8'd5}: begin
                    `CSR_WRF8(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M0_R0_CFG_5,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r0_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M0_R0_CFG_5,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r0_dly,gear,0,0,0,0,0,0);
                end
                {RANK0,8'd6}: begin
                    `CSR_WRF8(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M0_R0_CFG_6,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r0_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M0_R0_CFG_5,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r0_dly,gear,0,0,0,0,0,0);
                end
                {RANK0,8'd6}: begin
                    `CSR_WRF8(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M0_R0_CFG_6,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r0_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M0_R0_CFG_6,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r0_dly,gear,0,0,0,0,0,0);
                end
                {RANK0,8'd7}: begin
                    `CSR_WRF8(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M0_R0_CFG_7,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r0_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M0_R0_CFG_7,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r0_dly,gear,0,0,0,0,0,0);
                end
                {RANK0,8'd8}: begin
                    `CSR_WRF8(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M0_R0_CFG_8,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r0_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M0_R0_CFG_8,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r0_dly,gear,0,0,0,0,0,0);
                end
                {RANK1,8'd0}: begin
                    `CSR_WRF8(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M0_R1_CFG_0,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r1_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M0_R1_CFG_0,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r1_dly,gear,0,0,0,0,0,0);
                end
                {RANK1,8'd1}: begin
                    `CSR_WRF8(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M0_R1_CFG_1,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r1_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M0_R1_CFG_1,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r1_dly,gear,0,0,0,0,0,0);
                end
                {RANK1,8'd2}: begin
                    `CSR_WRF8(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M0_R1_CFG_2,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r1_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M0_R1_CFG_2,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r1_dly,gear,0,0,0,0,0,0);
                end
                {RANK1,8'd3}: begin
                    `CSR_WRF8(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M0_R1_CFG_3,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r1_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M0_R1_CFG_3,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r1_dly,gear,0,0,0,0,0,0);
                end
                {RANK1,8'd4}: begin
                    `CSR_WRF8(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M0_R1_CFG_4,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r1_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M0_R1_CFG_4,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r1_dly,gear,0,0,0,0,0,0);
                end
                {RANK1,8'd5}: begin
                    `CSR_WRF8(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M0_R1_CFG_5,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r1_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M0_R1_CFG_5,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r1_dly,gear,0,0,0,0,0,0);
                end
                {RANK1,8'd6}: begin
                    `CSR_WRF8(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M0_R1_CFG_6,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r1_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M0_R1_CFG_6,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r1_dly,gear,0,0,0,0,0,0);
                end
                {RANK1,8'd7}: begin
                    `CSR_WRF8(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M0_R1_CFG_7,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r1_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M0_R1_CFG_7,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r1_dly,gear,0,0,0,0,0,0);
                end
                {RANK1,8'd8}: begin
                    `CSR_WRF8(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M0_R1_CFG_8,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r1_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M0_R1_CFG_8,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r1_dly,gear,0,0,0,0,0,0);
                end
                default : begin
                    `CSR_WRF8(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M0_R0_CFG_0,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r0_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M0_R0_CFG_1,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r0_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M0_R0_CFG_2,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r0_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M0_R0_CFG_3,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r0_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M0_R0_CFG_4,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r0_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M0_R0_CFG_5,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r0_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M0_R0_CFG_6,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r0_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M0_R0_CFG_7,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r0_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M0_R0_CFG_8,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r0_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M0_R0_CFG_0,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r0_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M0_R0_CFG_1,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r0_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M0_R0_CFG_2,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r0_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M0_R0_CFG_3,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r0_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M0_R0_CFG_4,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r0_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M0_R0_CFG_5,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r0_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M0_R0_CFG_6,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r0_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M0_R0_CFG_7,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r0_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M0_R0_CFG_8,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r0_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M0_R1_CFG_0,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r1_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M0_R1_CFG_1,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r1_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M0_R1_CFG_2,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r1_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M0_R1_CFG_3,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r1_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M0_R1_CFG_4,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r1_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M0_R1_CFG_5,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r1_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M0_R1_CFG_6,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r1_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M0_R1_CFG_7,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r1_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH0_DQ0_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M0_R1_CFG_8,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r1_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M0_R1_CFG_0,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r1_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M0_R1_CFG_1,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r1_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M0_R1_CFG_2,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r1_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M0_R1_CFG_3,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r1_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M0_R1_CFG_4,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r1_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M0_R1_CFG_5,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r1_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M0_R1_CFG_6,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r1_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M0_R1_CFG_7,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r1_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH1_DQ0_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M0_R1_CFG_8,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r1_dly,gear,0,0,0,0,0,0);
                end
            endcase
        end
        if((byte_sel == DQ1) || (byte_sel == DQ_ALL) || (byte_sel == ALL)) begin
            case({rank_sel,dq})
                {RANK0,8'd0} : begin
                    `CSR_WRF8(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M0_R0_CFG_0,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r0_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M0_R0_CFG_0,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r0_dly,gear,0,0,0,0,0,0);
                end
                {RANK0,8'd1}: begin
                    `CSR_WRF8(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M0_R0_CFG_1,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r0_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M0_R0_CFG_1,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r0_dly,gear,0,0,0,0,0,0);
                end
                {RANK0,8'd2}: begin
                    `CSR_WRF8(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M0_R0_CFG_2,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r0_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M0_R0_CFG_2,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r0_dly,gear,0,0,0,0,0,0);
                end
                {RANK0,8'd3}: begin
                    `CSR_WRF8(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M0_R0_CFG_3,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r0_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M0_R0_CFG_3,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r0_dly,gear,0,0,0,0,0,0);
                end
                {RANK0,8'd4}: begin
                    `CSR_WRF8(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M0_R0_CFG_4,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r0_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M0_R0_CFG_4,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r0_dly,gear,0,0,0,0,0,0);
                end
                {RANK0,8'd5}: begin
                    `CSR_WRF8(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M0_R0_CFG_5,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r0_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M0_R0_CFG_5,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r0_dly,gear,0,0,0,0,0,0);
                end
                {RANK0,8'd6}: begin
                    `CSR_WRF8(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M0_R0_CFG_6,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r0_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M0_R0_CFG_6,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r0_dly,gear,0,0,0,0,0,0);
                end
                {RANK0,8'd7}: begin
                    `CSR_WRF8(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M0_R0_CFG_7,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r0_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M0_R0_CFG_7,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r0_dly,gear,0,0,0,0,0,0);
                end
                {RANK0,8'd8}: begin
                    `CSR_WRF8(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M0_R0_CFG_8,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r0_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M0_R0_CFG_8,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r0_dly,gear,0,0,0,0,0,0);
                end
                {RANK1,8'd0}: begin
                    `CSR_WRF8(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M0_R1_CFG_0,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r1_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M0_R1_CFG_0,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r1_dly,gear,0,0,0,0,0,0);
                end
                {RANK1,8'd1}: begin
                    `CSR_WRF8(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M0_R1_CFG_1,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r1_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M0_R1_CFG_1,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r1_dly,gear,0,0,0,0,0,0);
                end
                {RANK1,8'd2}: begin
                    `CSR_WRF8(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M0_R1_CFG_2,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r1_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M0_R1_CFG_2,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r1_dly,gear,0,0,0,0,0,0);
                end
                {RANK1,8'd3}: begin
                    `CSR_WRF8(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M0_R1_CFG_3,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r1_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M0_R1_CFG_3,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r1_dly,gear,0,0,0,0,0,0);
                end
                {RANK1,8'd4}: begin
                    `CSR_WRF8(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M0_R1_CFG_4,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r1_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M0_R1_CFG_4,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r1_dly,gear,0,0,0,0,0,0);
                end
                {RANK1,8'd5}: begin
                    `CSR_WRF8(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M0_R1_CFG_5,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r1_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M0_R1_CFG_5,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r1_dly,gear,0,0,0,0,0,0);
                end
                {RANK1,8'd6}: begin
                    `CSR_WRF8(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M0_R1_CFG_6,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r1_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M0_R1_CFG_6,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r1_dly,gear,0,0,0,0,0,0);
                end
                {RANK1,8'd7}: begin
                    `CSR_WRF8(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M0_R1_CFG_7,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r1_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M0_R1_CFG_7,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r1_dly,gear,0,0,0,0,0,0);
                end
                {RANK1,8'd8}: begin
                    `CSR_WRF8(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M0_R1_CFG_8,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r1_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M0_R1_CFG_8,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r1_dly,gear,0,0,0,0,0,0);
                end
                default : begin
                    `CSR_WRF8(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M0_R0_CFG_0,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r0_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M0_R0_CFG_1,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r0_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M0_R0_CFG_2,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r0_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M0_R0_CFG_3,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r0_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M0_R0_CFG_4,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r0_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M0_R0_CFG_5,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r0_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M0_R0_CFG_6,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r0_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M0_R0_CFG_7,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r0_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M0_R0_CFG_8,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r0_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M0_R0_CFG_0,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r0_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M0_R0_CFG_1,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r0_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M0_R0_CFG_2,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r0_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M0_R0_CFG_3,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r0_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M0_R0_CFG_4,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r0_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M0_R0_CFG_5,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r0_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M0_R0_CFG_6,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r0_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M0_R0_CFG_7,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r0_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M0_R0_CFG_8,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r0_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M0_R1_CFG_0,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r1_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M0_R1_CFG_1,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r1_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M0_R1_CFG_2,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r1_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M0_R1_CFG_3,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r1_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M0_R1_CFG_4,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r1_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M0_R1_CFG_5,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r1_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M0_R1_CFG_6,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r1_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M0_R1_CFG_7,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r1_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH0_DQ1_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M0_R1_CFG_8,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r1_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M0_R1_CFG_0,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r1_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M0_R1_CFG_1,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r1_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M0_R1_CFG_2,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r1_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M0_R1_CFG_3,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r1_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M0_R1_CFG_4,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r1_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M0_R1_CFG_5,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r1_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M0_R1_CFG_6,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r1_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M0_R1_CFG_7,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r1_dly,gear,0,0,0,0,0,0);
                    `CSR_WRF8(DDR_CH1_DQ1_OFFSET,DDR_DQ_DQ_RX_SA_DLY_M0_R1_CFG_8,CTRL_0,GEAR_0,GEAR_90,GEAR_270,GEAR_180,CTRL_90,CTRL_270,CTRL_180,r1_dly,gear,0,0,0,0,0,0);
                end
            endcase
        end
    end
endtask

//-----------------------------------------------------------------------
// DFI APIs -  End
//-----------------------------------------------------------------------
task automatic dfi_buf_flush_dp;
       localparam M = 1;
       logic [IG_WIDTH-1:0] wdata_load [M:0];
       int x;
       int y;
       int z[1:0];
    begin
      z[0] = 'd5 ;
      z[1] = 'hFFE ;

      set_dfi_wdata_clr;
      set_dfi_rdata_clr;

      set_dfi_buf_mode(1'b1);

      for (x=0; x <= M; x=x+1) begin
         for (y=0; y < IG_WIDTH-TSWIDTH; y=y+1) begin
         wdata_load[x][y] = '1 ;
         end
         wdata_load[x][IG_WIDTH-1: IG_WIDTH-TSWIDTH] = z[x] ;
         $display ("Info: Buffer data packet[%d] : %x  ts: %d ", x, wdata_load[x], wdata_load[x][IG_WIDTH-1: IG_WIDTH-TSWIDTH] );
      end
      for (x=0; x <= M; x=x+1) begin
         push_dfi_ig_buf (wdata_load[x]);
      end
      set_dfibuf_ts_cfg(.en(1'b1), .rst(1'b0));
      wait_dfibuf_eg_not_empty();
      set_dfibuf_ts_cfg(.en(1'b0), .rst(1'b1));
      wait_hclk (10);
      set_dfi_buf_mode(1'b0);
    end
endtask
