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

class wddr_config extends uvm_object;

    `uvm_object_utils(wddr_config)

    rand logic [7:0] rl;
    rand logic [7:0] wl;
    rand logic [7:0] odtlon;

    rand int unsigned tphy_wrlat;
    rand int unsigned tphy_wrdata;
    rand int unsigned tphy_rdlat;
    rand int unsigned tphy_rdcslat;
    rand int unsigned trddata_en;
    rand int unsigned mr1;
    rand int unsigned mr2;
    rand int unsigned mr11;

    logic [15:0] freq;
    logic [3:0] fratio;
    logic [7:0] bl = 16;
    logic seta = 1;
    logic dbi = 0;
    int gb_set=0;

    int unsigned trfcpb = 10;
    int unsigned tcipw = 0;
    int unsigned tdipw = 0;
    int unsigned isDiffValidInSEMode = 0;
    int unsigned tlp_resp = 5;
    int unsigned tck_min_b = 422;
    int unsigned tdqsq = 84;
    int unsigned trpre = 2;
    int unsigned tdqs2dq = 0;
    int unsigned tcmdcke_minTck = 1;
    int unsigned tescke_minTck = 1;
    int unsigned tpbr2pbr = 10;
    int unsigned tvrefweak = 250 ;
    int unsigned twdqstol = 25;

    parameter  tck = 1.27;
    localparam tdqsck = 3.5;
    localparam tprst = 0.5;
    localparam twpre = 2.0;
    localparam twtr = 8;
    localparam twr = 16;
    localparam todton = 1.5;
    localparam trtp = 7.5;

    // Transaction gaps
    int unsigned gap_rdwr;
    int unsigned gap_wrrd;
    int unsigned gap_wrpr;
    int unsigned gap_rdpr;
    int unsigned gap_rdrd;
    int unsigned gap_wrwr;

    function new (string name="wddr_config");
        super.new(name);
    endfunction

    // x16 mode
    constraint c_rl {
       // freq == 230  -> {if (dbi == 0) rl == 6;  else rl == 6;  }
	freq == 230  -> {if (dbi == 0) rl == 7;  else rl == 7;  }

        freq == 422  -> {if (dbi == 0) rl == 10; else rl == 12; }
        freq == 652  -> {if (dbi == 0) rl == 14; else rl == 16; }
        freq == 806  -> {if (dbi == 0) rl == 18; else rl == 18; }
        freq == 1075 -> {if (dbi == 0) rl == 24; else rl == 28; }
        freq == 1612 -> {if (dbi == 0) rl == 32; else rl == 36; }
       freq == 2112 -> {if (dbi == 0) rl == 36; else rl == 40; }
    }

    // x16 mode
    constraint c_wl {
        freq == 230  -> {if (seta == 1) wl == 4;  else wl == 4; }
        freq == 422  -> {if (seta == 1) wl == 6;  else wl == 8; }
        freq == 652  -> {if (seta == 1) wl == 8;  else wl == 12;}
        freq == 806  -> {if (seta == 1) wl == 10; else wl == 18;}
        freq == 1075 -> {if (seta == 1) wl == 12; else wl == 22;}
        freq == 1612 -> {if (seta == 1) wl == 16; else wl == 30;}
        freq == 2112 -> {if (seta == 1) wl == 18; else wl == 34;}
    }

    constraint c_mr1 {
        freq == 230  -> mr1 == 'h04;
        freq == 422  -> mr1 == 'h04;
        freq == 652  -> mr1 == 'h24;
       // freq == 806  -> mr1 == 'h24;
        freq == 806  -> mr1 == 'h34;
        freq == 1075 -> mr1 == 'h4C;
        freq == 1612 -> mr1 == 'h6C;
        freq == 2112 -> mr1 == 'h7C;
    }

    constraint c_mr2 {
        freq == 230  -> mr2 == 'h0;   //00
        freq == 422  -> mr2 == 'h9;   //11
        freq == 652  -> mr2 == 'h12;  //22
        freq == 806  -> mr2 == 'h1b;  //22
        freq == 1075 -> mr2 == 'h24;  //44
        freq == 1612 -> mr2 == 'h36;  //66
        freq == 2112 -> mr2 == 'h3F;  //77
    }

    constraint c_mr11 {
        freq == 230  -> mr11 == 'h0;
        freq == 422  -> mr11 == 'h0;
        freq == 652  -> mr11 == 'h0;
        freq == 806  -> mr11 == 'h0;
        freq == 1075 -> mr11 == 'h1;
        freq == 1612 -> mr11 == 'h1;
        freq == 2112 -> mr11 == 'h1;
    }

    // Command to Enable
    constraint c_tphy_wrlat {

        ((freq == 230) && (fratio == 1))  -> tphy_wrlat == 2;
        ((freq == 422) && (fratio == 1))  -> tphy_wrlat == 1;
        ((freq == 652) && (fratio == 1))  -> tphy_wrlat == 3;
        ((freq == 806) && (fratio == 1))  -> tphy_wrlat == 5;
        ((freq == 230) && (fratio == 2))  -> tphy_wrlat == 2;
        ((freq == 422) && (fratio == 2))  -> tphy_wrlat == 0;
        ((freq == 652) && (fratio == 2))  -> tphy_wrlat == 2;
        ((freq == 806) && (fratio == 2))  -> tphy_wrlat == 4;
        freq == 1075                      -> tphy_wrlat == 0;
        freq == 1612                      -> tphy_wrlat == 2;
        freq == 2112                      -> tphy_wrlat == 4;
    }

    // Enable to Data
    constraint c_tphy_wrdata {
        ((freq == 230) && (fratio == 1)) -> tphy_wrdata == 2; //5;
        ((freq == 422) && (fratio == 1)) -> tphy_wrdata == 5; //5;
        ((freq == 652) && (fratio == 1)) -> tphy_wrdata == 5; //2;
        ((freq == 806) && (fratio == 1)) -> {if(gb_set==6) tphy_wrdata == 4; else tphy_wrdata == 5; }
        ((freq == 230) && (fratio == 2)) -> tphy_wrdata == 2; //5;
        ((freq == 422) && (fratio == 2)) -> tphy_wrdata == 6; //5;
        ((freq == 652) && (fratio == 2)) -> tphy_wrdata == 6; //2;
        ((freq == 806) && (fratio == 2)) -> {if(gb_set==6) tphy_wrdata == 4; else tphy_wrdata == 6; }
        freq == 1075 -> tphy_wrdata == 12;
        freq == 1612 -> tphy_wrdata == 6; //14;
        freq == 2112 -> tphy_wrdata == 6; //14;
        //freq == 2112 -> tphy_wrdata == 14;
    }

    // Command to CS lat
    // 1:2 mode - 8 cycle delay through WrDP -> rdata_en - 8 , PEXT = (8)*2
    constraint c_tphy_rdcslat {
        ((freq == 230) && (fratio == 1)) -> tphy_rdcslat ==  5; //6-1
        ((freq == 422) && (fratio == 1)) -> tphy_rdcslat ==  6; //7-1
        ((freq == 652) && (fratio == 1)) -> tphy_rdcslat == 10; //11-1
        ((freq == 806) && (fratio == 1)) -> tphy_rdcslat == 16; //17-1
        ((freq == 230) && (fratio == 2)) -> tphy_rdcslat ==  0; //6-8-2
        ((freq == 422) && (fratio == 2)) -> tphy_rdcslat ==  0; //7-8-2
        ((freq == 652) && (fratio == 2)) -> tphy_rdcslat ==  1; //11-8-2
        ((freq == 806) && (fratio == 2)) -> tphy_rdcslat ==  7; //17-8-2
        freq == 1075 -> tphy_rdcslat == 10; //20-8-2
        freq == 1612 -> tphy_rdcslat == 18; //28-8-2
        freq == 2112 -> tphy_rdcslat == 22; //32-8-2
    }

    // Enable to Valid
    constraint c_tphy_rdlat {
        ((freq == 230) && (fratio == 1)) -> tphy_rdlat == 11;
        ((freq == 422) && (fratio == 1)) -> tphy_rdlat == 11;
        ((freq == 652) && (fratio == 1)) -> tphy_rdlat == 11;
        ((freq == 806) && (fratio == 1)) -> tphy_rdlat == 11;
        //((freq == 806) && (fratio == 1)) -> tphy_rdlat == 12;
        ((freq == 230) && (fratio == 2)) -> tphy_rdlat == 18;
        ((freq == 422) && (fratio == 2)) -> tphy_rdlat == 18;
        ((freq == 652) && (fratio == 2)) -> tphy_rdlat == 18;
        ((freq == 806) && (fratio == 2)) -> tphy_rdlat == 21;
        freq == 1075 -> tphy_rdlat == 21;
        freq == 1612 -> tphy_rdlat == 21;
        freq == 2112 -> tphy_rdlat == 21;
    }

    // Commnad to Enable
    constraint c_trddata_en {

        ((freq == 230) && (fratio == 1))  -> trddata_en ==  6; //2;
        ((freq == 422) && (fratio == 1))  -> trddata_en ==  7; //5;
        ((freq == 652) && (fratio == 1))  -> trddata_en == 11; //7;
        ((freq == 806) && (fratio == 1))  -> trddata_en == 17; //11;
       // ((freq == 806) && (fratio == 1))  -> trddata_en == 18; //11;
        ((freq == 230) && (fratio == 2))  -> trddata_en ==  6; //2;
        ((freq == 422) && (fratio == 2))  -> trddata_en ==  6; //5;
        ((freq == 652) && (fratio == 2))  -> trddata_en == 10; //7;
        ((freq == 806) && (fratio == 2))  -> trddata_en == 16; //11;
        freq == 1075 -> trddata_en == 20; //17;
        freq == 1612 -> trddata_en == 28; //24;
        freq == 2112 -> trddata_en == 32; //32;
    }

    constraint c_odtlon {
        freq == 230  -> odtlon == 0;
        freq == 422  -> odtlon == 0;
        freq == 652  -> odtlon == 0;
        freq == 806  -> odtlon == 0;
        freq == 1075 -> {if (seta == 1) odtlon == 8; else odtlon == 24;}
        freq == 1612 -> {if (seta == 1) odtlon == 8; else odtlon == 24;}
        freq == 2112 -> {if (seta == 1) odtlon == 8; else odtlon == 24;}
    }

    //  constraint c_tck {
    //      freq == 230 -> tck == 0.49;
    //      freq == 806 -> tck == 1.23;
    //      freq == 2112 -> tck == 3.77;
    //  }

    function pre_randomoze;
    endfunction

    function post_randomize;
        if (freq > 1000)
            this.gap_rdwr = (((rl + $ceil(tdqsck/tck) + (bl/2) + $floor(tprst) - odtlon - $floor(todton/tck) +1 )/2) + 2);
        else
            this.gap_rdwr = (rl + $ceil(tdqsck/tck) + (bl/2) + $floor(tprst) - wl + twpre );

        this.gap_wrrd = (wl + (bl/2) + twtr + 1);
        this.gap_wrpr = (wl + (bl/2) + twr + 1);
        this.gap_rdpr = trtp;
       // this.gap_rdrd = 11;
        this.gap_rdrd = 8;
        this.gap_wrwr = 9;

    endfunction

    // Set methods
    function void set_freq(bit [15:0] freq);
        this.freq = freq;
    endfunction

    function void set_fratio(bit [3:0] fratio);
        this.fratio = fratio;
    endfunction

    function void set_bl(bit [7:0] bl);
        this.bl = bl;
    endfunction

endclass
