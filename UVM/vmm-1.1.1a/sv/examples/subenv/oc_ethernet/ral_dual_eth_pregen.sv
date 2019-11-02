`ifndef RAL_DUAL_ETH
`define RAL_DUAL_ETH

`include "vmm_ral.sv"

class ral_reg_MODER extends vmm_ral_reg;
	rand vmm_ral_field RECSMALL;
	rand vmm_ral_field PAD;
	rand vmm_ral_field HUGEN;
	rand vmm_ral_field CRCEN;
	rand vmm_ral_field DLYCRCEN;
	rand vmm_ral_field undocumented;
	rand vmm_ral_field FULLD;
	rand vmm_ral_field EXDFREN;
	rand vmm_ral_field NOBCKOF;
	rand vmm_ral_field LOOPBCK;
	rand vmm_ral_field IFG;
	rand vmm_ral_field PRO;
	rand vmm_ral_field IAM;
	rand vmm_ral_field BRO;
	rand vmm_ral_field NOPRE;
	rand vmm_ral_field TXEN;
	rand vmm_ral_field RXEN;

	function new(vmm_ral_block parent, string name, bit[`VMM_RAL_ADDR_WIDTH-1:0] offset, string domain, int cvr, 
				bit[1:0] rights = 2'b11, bit unmapped = 0);
		super.new(parent, name, 24, offset, domain, cvr, rights, unmapped);
		this.RECSMALL = new(this, "RECSMALL", 1, vmm_ral::RW, 1'h0, 1'hx, 16, 0, cvr);
		this.PAD = new(this, "PAD", 1, vmm_ral::RW, 1, 1'hx, 15, 0, cvr);
		this.HUGEN = new(this, "HUGEN", 1, vmm_ral::RW, 1'h0, 1'hx, 14, 0, cvr);
		this.CRCEN = new(this, "CRCEN", 1, vmm_ral::RW, 1, 1'hx, 13, 0, cvr);
		this.DLYCRCEN = new(this, "DLYCRCEN", 1, vmm_ral::RW, 1'h0, 1'hx, 12, 0, cvr);
		this.undocumented = new(this, "undocumented", 1, vmm_ral::OTHER, 1'h0, 1'hx, 11, 0, cvr);
		this.FULLD = new(this, "FULLD", 1, vmm_ral::RW, 1'h0, 1'hx, 10, 0, cvr);
		this.EXDFREN = new(this, "EXDFREN", 1, vmm_ral::RW, 1'h0, 1'hx, 9, 0, cvr);
		this.NOBCKOF = new(this, "NOBCKOF", 1, vmm_ral::RW, 1'h0, 1'hx, 8, 0, cvr);
		this.LOOPBCK = new(this, "LOOPBCK", 1, vmm_ral::RW, 1'h0, 1'hx, 7, 0, cvr);
		this.IFG = new(this, "IFG", 1, vmm_ral::RW, 1'h0, 1'hx, 6, 0, cvr);
		this.PRO = new(this, "PRO", 1, vmm_ral::RW, 1'h0, 1'hx, 5, 0, cvr);
		this.IAM = new(this, "IAM", 1, vmm_ral::RW, 1'h0, 1'hx, 4, 0, cvr);
		this.BRO = new(this, "BRO", 1, vmm_ral::RW, 1'h0, 1'hx, 3, 0, cvr);
		this.NOPRE = new(this, "NOPRE", 1, vmm_ral::RW, 1'h0, 1'hx, 2, 0, cvr);
		this.TXEN = new(this, "TXEN", 1, vmm_ral::RW, 1'h0, 1'hx, 1, 0, cvr);
		this.RXEN = new(this, "RXEN", 1, vmm_ral::RW, 1'h0, 1'hx, 0, 0, cvr);
	endfunction: new
endclass : ral_reg_MODER


class ral_reg_oc_ethernet_INT_SOURCE extends vmm_ral_reg;
	rand vmm_ral_field RXC;
	rand vmm_ral_field TXC;
	rand vmm_ral_field BUSY;
	rand vmm_ral_field RXE;
	rand vmm_ral_field RXB;
	rand vmm_ral_field TXE;
	rand vmm_ral_field TXB;

	function new(vmm_ral_block parent, string name, bit[`VMM_RAL_ADDR_WIDTH-1:0] offset, string domain, int cvr, 
				bit[1:0] rights = 2'b11, bit unmapped = 0);
		super.new(parent, name, 8, offset, domain, cvr, rights, unmapped);
		this.RXC = new(this, "RXC", 1, vmm_ral::W1C, 1'h0, 1'hx, 6, 0, cvr);
		this.TXC = new(this, "TXC", 1, vmm_ral::W1C, 1'h0, 1'hx, 5, 0, cvr);
		this.BUSY = new(this, "BUSY", 1, vmm_ral::W1C, 1'h0, 1'hx, 4, 0, cvr);
		this.RXE = new(this, "RXE", 1, vmm_ral::W1C, 1'h0, 1'hx, 3, 0, cvr);
		this.RXB = new(this, "RXB", 1, vmm_ral::W1C, 1'h0, 1'hx, 2, 0, cvr);
		this.TXE = new(this, "TXE", 1, vmm_ral::W1C, 1'h0, 1'hx, 1, 0, cvr);
		this.TXB = new(this, "TXB", 1, vmm_ral::W1C, 1'h0, 1'hx, 0, 0, cvr);
	endfunction: new
endclass : ral_reg_oc_ethernet_INT_SOURCE


class ral_reg_oc_ethernet_INT_MASK extends vmm_ral_reg;
	rand vmm_ral_field RXC_M;
	rand vmm_ral_field TXC_M;
	rand vmm_ral_field BUSY_M;
	rand vmm_ral_field RXE_M;
	rand vmm_ral_field RXB_M;
	rand vmm_ral_field TXE_M;
	rand vmm_ral_field TXB_M;

	function new(vmm_ral_block parent, string name, bit[`VMM_RAL_ADDR_WIDTH-1:0] offset, string domain, int cvr, 
				bit[1:0] rights = 2'b11, bit unmapped = 0);
		super.new(parent, name, 8, offset, domain, cvr, rights, unmapped);
		this.RXC_M = new(this, "RXC_M", 1, vmm_ral::RW, 1'h0, 1'hx, 6, 0, cvr);
		this.TXC_M = new(this, "TXC_M", 1, vmm_ral::RW, 1'h0, 1'hx, 5, 0, cvr);
		this.BUSY_M = new(this, "BUSY_M", 1, vmm_ral::RW, 1'h0, 1'hx, 4, 0, cvr);
		this.RXE_M = new(this, "RXE_M", 1, vmm_ral::RW, 1'h0, 1'hx, 3, 0, cvr);
		this.RXB_M = new(this, "RXB_M", 1, vmm_ral::RW, 1'h0, 1'hx, 2, 0, cvr);
		this.TXE_M = new(this, "TXE_M", 1, vmm_ral::RW, 1'h0, 1'hx, 1, 0, cvr);
		this.TXB_M = new(this, "TXB_M", 1, vmm_ral::RW, 1'h0, 1'hx, 0, 0, cvr);
	endfunction: new
endclass : ral_reg_oc_ethernet_INT_MASK


class ral_reg_IPGT extends vmm_ral_reg;
	rand vmm_ral_field IPGT;

	function new(vmm_ral_block parent, string name, bit[`VMM_RAL_ADDR_WIDTH-1:0] offset, string domain, int cvr, 
				bit[1:0] rights = 2'b11, bit unmapped = 0);
		super.new(parent, name, 8, offset, domain, cvr, rights, unmapped);
		this.IPGT = new(this, "IPGT", 7, vmm_ral::RW, 'h12, 7'hx, 0, 0, cvr);
	endfunction: new
endclass : ral_reg_IPGT


class ral_reg_IPGR1 extends vmm_ral_reg;
	rand vmm_ral_field IPGR1;

	function new(vmm_ral_block parent, string name, bit[`VMM_RAL_ADDR_WIDTH-1:0] offset, string domain, int cvr, 
				bit[1:0] rights = 2'b11, bit unmapped = 0);
		super.new(parent, name, 8, offset, domain, cvr, rights, unmapped);
		this.IPGR1 = new(this, "IPGR1", 7, vmm_ral::RW, 'h0C, 7'hx, 0, 0, cvr);
	endfunction: new
endclass : ral_reg_IPGR1


class ral_reg_IPGR2 extends vmm_ral_reg;
	rand vmm_ral_field IPGR2;

	function new(vmm_ral_block parent, string name, bit[`VMM_RAL_ADDR_WIDTH-1:0] offset, string domain, int cvr, 
				bit[1:0] rights = 2'b11, bit unmapped = 0);
		super.new(parent, name, 8, offset, domain, cvr, rights, unmapped);
		this.IPGR2 = new(this, "IPGR2", 7, vmm_ral::RW, 'h12, 7'hx, 0, 0, cvr);
	endfunction: new
endclass : ral_reg_IPGR2


class ral_reg_PACKETLEN extends vmm_ral_reg;
	rand vmm_ral_field MINFL;
	rand vmm_ral_field MAXFL;

	constraint MINFL_spec {
		MINFL.value == 'h40;
	}
	constraint MAXFL_spec {
		MAXFL.value == 'h600;
	}

	function new(vmm_ral_block parent, string name, bit[`VMM_RAL_ADDR_WIDTH-1:0] offset, string domain, int cvr, 
				bit[1:0] rights = 2'b11, bit unmapped = 0);
		super.new(parent, name, 32, offset, domain, cvr, rights, unmapped);
		this.MINFL = new(this, "MINFL", 16, vmm_ral::RW, 'h0040, 16'hx, 16, 1, cvr);
		this.MAXFL = new(this, "MAXFL", 16, vmm_ral::RW, 'h0600, 16'hx, 0, 1, cvr);
		Xadd_constraintsX("MINFL_spec");
		Xadd_constraintsX("MAXFL_spec");
	endfunction: new
endclass : ral_reg_PACKETLEN


class ral_reg_COLLCONF extends vmm_ral_reg;
	rand vmm_ral_field MAXRET;
	rand vmm_ral_field COLLVALID;

	function new(vmm_ral_block parent, string name, bit[`VMM_RAL_ADDR_WIDTH-1:0] offset, string domain, int cvr, 
				bit[1:0] rights = 2'b11, bit unmapped = 0);
		super.new(parent, name, 24, offset, domain, cvr, rights, unmapped);
		this.MAXRET = new(this, "MAXRET", 4, vmm_ral::RW, 'hF, 4'hx, 16, 0, cvr);
		this.COLLVALID = new(this, "COLLVALID", 6, vmm_ral::RW, 'h3F, 6'hx, 0, 0, cvr);
	endfunction: new
endclass : ral_reg_COLLCONF


class ral_reg_TX_BD_NUM extends vmm_ral_reg;
	rand vmm_ral_field TX_BD_NUM;

	constraint TX_BD_NUM_hardware {
		TX_BD_NUM.value <= 'h80;
	}

	function new(vmm_ral_block parent, string name, bit[`VMM_RAL_ADDR_WIDTH-1:0] offset, string domain, int cvr, 
				bit[1:0] rights = 2'b11, bit unmapped = 0);
		super.new(parent, name, 8, offset, domain, cvr, rights, unmapped);
		this.TX_BD_NUM = new(this, "TX_BD_NUM", 8, vmm_ral::OTHER, 'h40, 8'hx, 0, 1, cvr);
		Xadd_constraintsX("TX_BD_NUM_hardware");
	endfunction: new
endclass : ral_reg_TX_BD_NUM


class ral_reg_CTRLMODER extends vmm_ral_reg;
	rand vmm_ral_field TXFLOW;
	rand vmm_ral_field RXFLOW;
	rand vmm_ral_field PASSALL;

	function new(vmm_ral_block parent, string name, bit[`VMM_RAL_ADDR_WIDTH-1:0] offset, string domain, int cvr, 
				bit[1:0] rights = 2'b11, bit unmapped = 0);
		super.new(parent, name, 8, offset, domain, cvr, rights, unmapped);
		this.TXFLOW = new(this, "TXFLOW", 1, vmm_ral::RW, 1'h0, 1'hx, 2, 0, cvr);
		this.RXFLOW = new(this, "RXFLOW", 1, vmm_ral::RW, 1'h0, 1'hx, 1, 0, cvr);
		this.PASSALL = new(this, "PASSALL", 1, vmm_ral::RW, 1'h0, 1'hx, 0, 0, cvr);
	endfunction: new
endclass : ral_reg_CTRLMODER


class ral_reg_MIIMODER extends vmm_ral_reg;
	rand vmm_ral_field MIINOPRE;
	rand vmm_ral_field CLKDIV;

	function new(vmm_ral_block parent, string name, bit[`VMM_RAL_ADDR_WIDTH-1:0] offset, string domain, int cvr, 
				bit[1:0] rights = 2'b11, bit unmapped = 0);
		super.new(parent, name, 16, offset, domain, cvr, rights, unmapped);
		this.MIINOPRE = new(this, "MIINOPRE", 1, vmm_ral::RW, 1'h0, 1'hx, 8, 0, cvr);
		this.CLKDIV = new(this, "CLKDIV", 8, vmm_ral::RW, 'h64, 8'hx, 0, 0, cvr);
	endfunction: new
endclass : ral_reg_MIIMODER


class ral_reg_MIICOMMAND extends vmm_ral_reg;
	rand vmm_ral_field WCTRLDATA;
	rand vmm_ral_field RSTAT;
	rand vmm_ral_field SCANSTAT;

	function new(vmm_ral_block parent, string name, bit[`VMM_RAL_ADDR_WIDTH-1:0] offset, string domain, int cvr, 
				bit[1:0] rights = 2'b11, bit unmapped = 0);
		super.new(parent, name, 8, offset, domain, cvr, rights, unmapped);
		this.WCTRLDATA = new(this, "WCTRLDATA", 1, vmm_ral::OTHER, 1'h0, 1'hx, 2, 0, cvr);
		this.RSTAT = new(this, "RSTAT", 1, vmm_ral::OTHER, 1'h0, 1'hx, 1, 0, cvr);
		this.SCANSTAT = new(this, "SCANSTAT", 1, vmm_ral::OTHER, 1'h0, 1'hx, 0, 0, cvr);
	endfunction: new
endclass : ral_reg_MIICOMMAND


class ral_reg_MIIADDRESS extends vmm_ral_reg;
	rand vmm_ral_field RGAD;
	rand vmm_ral_field FIAD;

	function new(vmm_ral_block parent, string name, bit[`VMM_RAL_ADDR_WIDTH-1:0] offset, string domain, int cvr, 
				bit[1:0] rights = 2'b11, bit unmapped = 0);
		super.new(parent, name, 16, offset, domain, cvr, rights, unmapped);
		this.RGAD = new(this, "RGAD", 5, vmm_ral::RW, 5'h0, 5'hx, 8, 0, cvr);
		this.FIAD = new(this, "FIAD", 5, vmm_ral::RW, 5'h0, 5'hx, 0, 0, cvr);
	endfunction: new
endclass : ral_reg_MIIADDRESS


class ral_reg_MIITX_DATA extends vmm_ral_reg;
	rand vmm_ral_field CTRLDATA;

	function new(vmm_ral_block parent, string name, bit[`VMM_RAL_ADDR_WIDTH-1:0] offset, string domain, int cvr, 
				bit[1:0] rights = 2'b11, bit unmapped = 0);
		super.new(parent, name, 16, offset, domain, cvr, rights, unmapped);
		this.CTRLDATA = new(this, "CTRLDATA", 16, vmm_ral::RW, 16'h0, 16'hx, 0, 0, cvr);
	endfunction: new
endclass : ral_reg_MIITX_DATA


class ral_reg_MIIRX_DATA extends vmm_ral_reg;
	rand vmm_ral_field PRSD;

	function new(vmm_ral_block parent, string name, bit[`VMM_RAL_ADDR_WIDTH-1:0] offset, string domain, int cvr, 
				bit[1:0] rights = 2'b11, bit unmapped = 0);
		super.new(parent, name, 16, offset, domain, cvr, rights, unmapped);
		this.PRSD = new(this, "PRSD", 16, vmm_ral::RO, 16'h0, 16'hx, 0, 0, cvr);
	endfunction: new
endclass : ral_reg_MIIRX_DATA


class ral_reg_MIISTATUS extends vmm_ral_reg;
	rand vmm_ral_field NVALID;
	rand vmm_ral_field BUSY_N;
	rand vmm_ral_field LINKFAIL;

	function new(vmm_ral_block parent, string name, bit[`VMM_RAL_ADDR_WIDTH-1:0] offset, string domain, int cvr, 
				bit[1:0] rights = 2'b11, bit unmapped = 0);
		super.new(parent, name, 8, offset, domain, cvr, rights, unmapped);
		this.NVALID = new(this, "NVALID", 1, vmm_ral::RO, 1'h0, 1'hx, 2, 0, cvr);
		this.BUSY_N = new(this, "BUSY_N", 1, vmm_ral::RO, 1'h0, 1'hx, 1, 0, cvr);
		this.LINKFAIL = new(this, "LINKFAIL", 1, vmm_ral::RO, 1'h0, 1'hx, 0, 0, cvr);
	endfunction: new
endclass : ral_reg_MIISTATUS


class ral_reg_MAC_ADDR extends vmm_ral_reg;
	rand vmm_ral_field MAC_ADDR;

	function new(vmm_ral_block parent, string name, bit[`VMM_RAL_ADDR_WIDTH-1:0] offset, string domain, int cvr, 
				bit[1:0] rights = 2'b11, bit unmapped = 0);
		super.new(parent, name, 48, offset, domain, cvr, rights, unmapped);
		this.MAC_ADDR = new(this, "MAC_ADDR", 48, vmm_ral::RW, 48'h0, 48'hx, 0, 0, cvr);
	endfunction: new
endclass : ral_reg_MAC_ADDR


class ral_reg_HASH0 extends vmm_ral_reg;
	rand vmm_ral_field HASH0;

	function new(vmm_ral_block parent, string name, bit[`VMM_RAL_ADDR_WIDTH-1:0] offset, string domain, int cvr, 
				bit[1:0] rights = 2'b11, bit unmapped = 0);
		super.new(parent, name, 32, offset, domain, cvr, rights, unmapped);
		this.HASH0 = new(this, "HASH0", 32, vmm_ral::RW, 32'h0, 32'hx, 0, 0, cvr);
	endfunction: new
endclass : ral_reg_HASH0


class ral_reg_HASH1 extends vmm_ral_reg;
	rand vmm_ral_field HASH1;

	function new(vmm_ral_block parent, string name, bit[`VMM_RAL_ADDR_WIDTH-1:0] offset, string domain, int cvr, 
				bit[1:0] rights = 2'b11, bit unmapped = 0);
		super.new(parent, name, 32, offset, domain, cvr, rights, unmapped);
		this.HASH1 = new(this, "HASH1", 32, vmm_ral::RW, 32'h0, 32'hx, 0, 0, cvr);
	endfunction: new
endclass : ral_reg_HASH1


class ral_reg_TXCTRL extends vmm_ral_reg;
	rand vmm_ral_field TXPAUSEREQ;
	rand vmm_ral_field TXPAUSETV;

	function new(vmm_ral_block parent, string name, bit[`VMM_RAL_ADDR_WIDTH-1:0] offset, string domain, int cvr, 
				bit[1:0] rights = 2'b11, bit unmapped = 0);
		super.new(parent, name, 24, offset, domain, cvr, rights, unmapped);
		this.TXPAUSEREQ = new(this, "TXPAUSEREQ", 1, vmm_ral::RW, 1'h0, 1'hx, 16, 0, cvr);
		this.TXPAUSETV = new(this, "TXPAUSETV", 16, vmm_ral::RW, 16'h0, 16'hx, 0, 0, cvr);
	endfunction: new
endclass : ral_reg_TXCTRL


class ral_reg_oc_ethernet_TxBD_TxBD_CTRL extends vmm_ral_reg;
	rand vmm_ral_field CS;
	rand vmm_ral_field DF;
	rand vmm_ral_field LC;
	rand vmm_ral_field RL;
	rand vmm_ral_field RTRY;
	rand vmm_ral_field UR;
	rand vmm_ral_field CRC;
	rand vmm_ral_field PAD;
	rand vmm_ral_field WR;
	rand vmm_ral_field IRQ;
	rand vmm_ral_field RD;
	rand vmm_ral_field LEN;

	function new(vmm_ral_block parent, string name, bit[`VMM_RAL_ADDR_WIDTH-1:0] offset, string domain, int cvr, 
				bit[1:0] rights = 2'b11, bit unmapped = 0);
		super.new(parent, name, 32, offset, domain, cvr, rights, unmapped);
		this.CS = new(this, "CS", 1, vmm_ral::RW, 1'h0, 1'hx, 0, 0, cvr);
		this.DF = new(this, "DF", 1, vmm_ral::RW, 1'h0, 1'hx, 1, 0, cvr);
		this.LC = new(this, "LC", 1, vmm_ral::RW, 1'h0, 1'hx, 2, 0, cvr);
		this.RL = new(this, "RL", 1, vmm_ral::RW, 1'h0, 1'hx, 3, 0, cvr);
		this.RTRY = new(this, "RTRY", 4, vmm_ral::RW, 4'h0, 4'hx, 4, 0, cvr);
		this.UR = new(this, "UR", 1, vmm_ral::RW, 1'h0, 1'hx, 8, 0, cvr);
		this.CRC = new(this, "CRC", 1, vmm_ral::RW, 1'h0, 1'hx, 11, 0, cvr);
		this.PAD = new(this, "PAD", 1, vmm_ral::RW, 1'h0, 1'hx, 12, 0, cvr);
		this.WR = new(this, "WR", 1, vmm_ral::RW, 1'h0, 1'hx, 13, 0, cvr);
		this.IRQ = new(this, "IRQ", 1, vmm_ral::RW, 1'h0, 1'hx, 14, 0, cvr);
		this.RD = new(this, "RD", 1, vmm_ral::RW, 1'h0, 1'hx, 15, 0, cvr);
		this.LEN = new(this, "LEN", 16, vmm_ral::RW, 16'h0, 16'hx, 16, 0, cvr);
	endfunction: new
endclass : ral_reg_oc_ethernet_TxBD_TxBD_CTRL


class ral_reg_oc_ethernet_TxBD_TxPNT_val extends vmm_ral_reg;
	rand vmm_ral_field PTR;

	function new(vmm_ral_block parent, string name, bit[`VMM_RAL_ADDR_WIDTH-1:0] offset, string domain, int cvr, 
				bit[1:0] rights = 2'b11, bit unmapped = 0);
		super.new(parent, name, 32, offset, domain, cvr, rights, unmapped);
		this.PTR = new(this, "PTR", 32, vmm_ral::RW, 32'h0, 32'hx, 0, 0, cvr);
	endfunction: new
endclass : ral_reg_oc_ethernet_TxBD_TxPNT_val


class ral_regfile_oc_ethernet_TxBD;
	rand ral_reg_oc_ethernet_TxBD_TxBD_CTRL TxBD_CTRL;
	rand ral_reg_oc_ethernet_TxBD_TxPNT_val TxPNT_val;
	rand vmm_ral_field TxBD_CTRL_CS;
	rand vmm_ral_field CS;
	rand vmm_ral_field TxBD_CTRL_DF;
	rand vmm_ral_field DF;
	rand vmm_ral_field TxBD_CTRL_LC;
	rand vmm_ral_field LC;
	rand vmm_ral_field TxBD_CTRL_RL;
	rand vmm_ral_field RL;
	rand vmm_ral_field TxBD_CTRL_RTRY;
	rand vmm_ral_field RTRY;
	rand vmm_ral_field TxBD_CTRL_UR;
	rand vmm_ral_field UR;
	rand vmm_ral_field TxBD_CTRL_CRC;
	rand vmm_ral_field CRC;
	rand vmm_ral_field TxBD_CTRL_PAD;
	rand vmm_ral_field PAD;
	rand vmm_ral_field TxBD_CTRL_WR;
	rand vmm_ral_field WR;
	rand vmm_ral_field TxBD_CTRL_IRQ;
	rand vmm_ral_field IRQ;
	rand vmm_ral_field TxBD_CTRL_RD;
	rand vmm_ral_field RD;
	rand vmm_ral_field TxBD_CTRL_LEN;
	rand vmm_ral_field LEN;
	rand vmm_ral_field TxPNT_val_PTR;
	rand vmm_ral_field PTR;

	function new(vmm_ral_block parent, string name, bit[`VMM_RAL_ADDR_WIDTH-1:0] offset, string domain, int cvr);
		this.TxBD_CTRL = new(parent, $psprintf("%s.TxBD_CTRL",name), offset+`VMM_RAL_ADDR_WIDTH'h0, domain, cvr, 2'b11, 0);
		this.TxBD_CTRL_CS = this.TxBD_CTRL.CS;
		this.CS = this.TxBD_CTRL.CS;
		this.TxBD_CTRL_DF = this.TxBD_CTRL.DF;
		this.DF = this.TxBD_CTRL.DF;
		this.TxBD_CTRL_LC = this.TxBD_CTRL.LC;
		this.LC = this.TxBD_CTRL.LC;
		this.TxBD_CTRL_RL = this.TxBD_CTRL.RL;
		this.RL = this.TxBD_CTRL.RL;
		this.TxBD_CTRL_RTRY = this.TxBD_CTRL.RTRY;
		this.RTRY = this.TxBD_CTRL.RTRY;
		this.TxBD_CTRL_UR = this.TxBD_CTRL.UR;
		this.UR = this.TxBD_CTRL.UR;
		this.TxBD_CTRL_CRC = this.TxBD_CTRL.CRC;
		this.CRC = this.TxBD_CTRL.CRC;
		this.TxBD_CTRL_PAD = this.TxBD_CTRL.PAD;
		this.PAD = this.TxBD_CTRL.PAD;
		this.TxBD_CTRL_WR = this.TxBD_CTRL.WR;
		this.WR = this.TxBD_CTRL.WR;
		this.TxBD_CTRL_IRQ = this.TxBD_CTRL.IRQ;
		this.IRQ = this.TxBD_CTRL.IRQ;
		this.TxBD_CTRL_RD = this.TxBD_CTRL.RD;
		this.RD = this.TxBD_CTRL.RD;
		this.TxBD_CTRL_LEN = this.TxBD_CTRL.LEN;
		this.LEN = this.TxBD_CTRL.LEN;
		this.TxPNT_val = new(parent, $psprintf("%s.TxPNT_val",name), offset+`VMM_RAL_ADDR_WIDTH'h1, domain, cvr, 2'b11, 0);
		this.TxPNT_val_PTR = this.TxPNT_val.PTR;
		this.PTR = this.TxPNT_val.PTR;
	endfunction : new
endclass : ral_regfile_oc_ethernet_TxBD




class ral_reg_oc_ethernet_RxBD_RxBD_CTRL extends vmm_ral_reg;
	rand vmm_ral_field LC;
	rand vmm_ral_field CRC;
	rand vmm_ral_field SF;
	rand vmm_ral_field TL;
	rand vmm_ral_field DN;
	rand vmm_ral_field IS;
	rand vmm_ral_field OR;
	rand vmm_ral_field M;
	rand vmm_ral_field CF;
	rand vmm_ral_field WR;
	rand vmm_ral_field IRQ;
	rand vmm_ral_field E;
	rand vmm_ral_field LEN;

	function new(vmm_ral_block parent, string name, bit[`VMM_RAL_ADDR_WIDTH-1:0] offset, string domain, int cvr, 
				bit[1:0] rights = 2'b11, bit unmapped = 0);
		super.new(parent, name, 32, offset, domain, cvr, rights, unmapped);
		this.LC = new(this, "LC", 1, vmm_ral::RW, 1'h0, 1'hx, 0, 0, cvr);
		this.CRC = new(this, "CRC", 1, vmm_ral::RW, 1'h0, 1'hx, 1, 0, cvr);
		this.SF = new(this, "SF", 1, vmm_ral::RW, 1'h0, 1'hx, 2, 0, cvr);
		this.TL = new(this, "TL", 1, vmm_ral::RW, 1'h0, 1'hx, 3, 0, cvr);
		this.DN = new(this, "DN", 1, vmm_ral::RW, 1'h0, 1'hx, 4, 0, cvr);
		this.IS = new(this, "IS", 1, vmm_ral::RW, 1'h0, 1'hx, 5, 0, cvr);
		this.OR = new(this, "OR", 1, vmm_ral::RW, 1'h0, 1'hx, 6, 0, cvr);
		this.M = new(this, "M", 1, vmm_ral::RW, 1'h0, 1'hx, 7, 0, cvr);
		this.CF = new(this, "CF", 1, vmm_ral::RW, 1'h0, 1'hx, 8, 0, cvr);
		this.WR = new(this, "WR", 1, vmm_ral::RW, 1'h0, 1'hx, 13, 0, cvr);
		this.IRQ = new(this, "IRQ", 1, vmm_ral::RW, 1'h0, 1'hx, 14, 0, cvr);
		this.E = new(this, "E", 1, vmm_ral::RW, 1'h0, 1'hx, 15, 0, cvr);
		this.LEN = new(this, "LEN", 16, vmm_ral::RW, 16'h0, 16'hx, 16, 0, cvr);
	endfunction: new
endclass : ral_reg_oc_ethernet_RxBD_RxBD_CTRL


class ral_reg_oc_ethernet_RxBD_RxPNT_val extends vmm_ral_reg;
	rand vmm_ral_field PTR;

	function new(vmm_ral_block parent, string name, bit[`VMM_RAL_ADDR_WIDTH-1:0] offset, string domain, int cvr, 
				bit[1:0] rights = 2'b11, bit unmapped = 0);
		super.new(parent, name, 32, offset, domain, cvr, rights, unmapped);
		this.PTR = new(this, "PTR", 32, vmm_ral::RW, 32'h0, 32'hx, 0, 0, cvr);
	endfunction: new
endclass : ral_reg_oc_ethernet_RxBD_RxPNT_val


class ral_regfile_oc_ethernet_RxBD;
	rand ral_reg_oc_ethernet_RxBD_RxBD_CTRL RxBD_CTRL;
	rand ral_reg_oc_ethernet_RxBD_RxPNT_val RxPNT_val;
	rand vmm_ral_field RxBD_CTRL_LC;
	rand vmm_ral_field LC;
	rand vmm_ral_field RxBD_CTRL_CRC;
	rand vmm_ral_field CRC;
	rand vmm_ral_field RxBD_CTRL_SF;
	rand vmm_ral_field SF;
	rand vmm_ral_field RxBD_CTRL_TL;
	rand vmm_ral_field TL;
	rand vmm_ral_field RxBD_CTRL_DN;
	rand vmm_ral_field DN;
	rand vmm_ral_field RxBD_CTRL_IS;
	rand vmm_ral_field IS;
	rand vmm_ral_field RxBD_CTRL_OR;
	rand vmm_ral_field OR;
	rand vmm_ral_field RxBD_CTRL_M;
	rand vmm_ral_field M;
	rand vmm_ral_field RxBD_CTRL_CF;
	rand vmm_ral_field CF;
	rand vmm_ral_field RxBD_CTRL_WR;
	rand vmm_ral_field WR;
	rand vmm_ral_field RxBD_CTRL_IRQ;
	rand vmm_ral_field IRQ;
	rand vmm_ral_field RxBD_CTRL_E;
	rand vmm_ral_field E;
	rand vmm_ral_field RxBD_CTRL_LEN;
	rand vmm_ral_field LEN;
	rand vmm_ral_field RxPNT_val_PTR;
	rand vmm_ral_field PTR;

	function new(vmm_ral_block parent, string name, bit[`VMM_RAL_ADDR_WIDTH-1:0] offset, string domain, int cvr);
		this.RxBD_CTRL = new(parent, $psprintf("%s.RxBD_CTRL",name), offset+`VMM_RAL_ADDR_WIDTH'h0, domain, cvr, 2'b11, 0);
		this.RxBD_CTRL_LC = this.RxBD_CTRL.LC;
		this.LC = this.RxBD_CTRL.LC;
		this.RxBD_CTRL_CRC = this.RxBD_CTRL.CRC;
		this.CRC = this.RxBD_CTRL.CRC;
		this.RxBD_CTRL_SF = this.RxBD_CTRL.SF;
		this.SF = this.RxBD_CTRL.SF;
		this.RxBD_CTRL_TL = this.RxBD_CTRL.TL;
		this.TL = this.RxBD_CTRL.TL;
		this.RxBD_CTRL_DN = this.RxBD_CTRL.DN;
		this.DN = this.RxBD_CTRL.DN;
		this.RxBD_CTRL_IS = this.RxBD_CTRL.IS;
		this.IS = this.RxBD_CTRL.IS;
		this.RxBD_CTRL_OR = this.RxBD_CTRL.OR;
		this.OR = this.RxBD_CTRL.OR;
		this.RxBD_CTRL_M = this.RxBD_CTRL.M;
		this.M = this.RxBD_CTRL.M;
		this.RxBD_CTRL_CF = this.RxBD_CTRL.CF;
		this.CF = this.RxBD_CTRL.CF;
		this.RxBD_CTRL_WR = this.RxBD_CTRL.WR;
		this.WR = this.RxBD_CTRL.WR;
		this.RxBD_CTRL_IRQ = this.RxBD_CTRL.IRQ;
		this.IRQ = this.RxBD_CTRL.IRQ;
		this.RxBD_CTRL_E = this.RxBD_CTRL.E;
		this.E = this.RxBD_CTRL.E;
		this.RxBD_CTRL_LEN = this.RxBD_CTRL.LEN;
		this.LEN = this.RxBD_CTRL.LEN;
		this.RxPNT_val = new(parent, $psprintf("%s.RxPNT_val",name), offset+`VMM_RAL_ADDR_WIDTH'h1, domain, cvr, 2'b11, 0);
		this.RxPNT_val_PTR = this.RxPNT_val.PTR;
		this.PTR = this.RxPNT_val.PTR;
	endfunction : new
endclass : ral_regfile_oc_ethernet_RxBD




class ral_block_oc_ethernet extends vmm_ral_block;
	rand ral_reg_MODER MODER;
	rand ral_reg_oc_ethernet_INT_SOURCE INT_SOURCE;
	rand ral_reg_oc_ethernet_INT_MASK INT_MASK;
	rand ral_reg_IPGT IPGT;
	rand ral_reg_IPGR1 IPGR1;
	rand ral_reg_IPGR2 IPGR2;
	rand ral_reg_PACKETLEN PACKETLEN;
	rand ral_reg_COLLCONF COLLCONF;
	rand ral_reg_TX_BD_NUM TX_BD_NUM;
	rand ral_reg_CTRLMODER CTRLMODER;
	rand ral_reg_MIIMODER MIIMODER;
	rand ral_reg_MIICOMMAND MIICOMMAND;
	rand ral_reg_MIIADDRESS MIIADDRESS;
	rand ral_reg_MIITX_DATA MIITX_DATA;
	rand ral_reg_MIIRX_DATA MIIRX_DATA;
	rand ral_reg_MIISTATUS MIISTATUS;
	rand ral_reg_MAC_ADDR MAC_ADDR;
	rand ral_reg_HASH0 HASH0;
	rand ral_reg_HASH1 HASH1;
	rand ral_reg_TXCTRL TXCTRL;
	rand ral_regfile_oc_ethernet_TxBD TxBD[128];
	rand ral_regfile_oc_ethernet_RxBD RxBD[128];
	rand vmm_ral_field MODER_RECSMALL;
	rand vmm_ral_field RECSMALL;
	rand vmm_ral_field MODER_PAD;
	rand vmm_ral_field PAD;
	rand vmm_ral_field MODER_HUGEN;
	rand vmm_ral_field HUGEN;
	rand vmm_ral_field MODER_CRCEN;
	rand vmm_ral_field CRCEN;
	rand vmm_ral_field MODER_DLYCRCEN;
	rand vmm_ral_field DLYCRCEN;
	rand vmm_ral_field MODER_undocumented;
	rand vmm_ral_field undocumented;
	rand vmm_ral_field MODER_FULLD;
	rand vmm_ral_field FULLD;
	rand vmm_ral_field MODER_EXDFREN;
	rand vmm_ral_field EXDFREN;
	rand vmm_ral_field MODER_NOBCKOF;
	rand vmm_ral_field NOBCKOF;
	rand vmm_ral_field MODER_LOOPBCK;
	rand vmm_ral_field LOOPBCK;
	rand vmm_ral_field MODER_IFG;
	rand vmm_ral_field IFG;
	rand vmm_ral_field MODER_PRO;
	rand vmm_ral_field PRO;
	rand vmm_ral_field MODER_IAM;
	rand vmm_ral_field IAM;
	rand vmm_ral_field MODER_BRO;
	rand vmm_ral_field BRO;
	rand vmm_ral_field MODER_NOPRE;
	rand vmm_ral_field NOPRE;
	rand vmm_ral_field MODER_TXEN;
	rand vmm_ral_field TXEN;
	rand vmm_ral_field MODER_RXEN;
	rand vmm_ral_field RXEN;
	rand vmm_ral_field INT_SOURCE_RXC;
	rand vmm_ral_field RXC;
	rand vmm_ral_field INT_SOURCE_TXC;
	rand vmm_ral_field TXC;
	rand vmm_ral_field INT_SOURCE_BUSY;
	rand vmm_ral_field BUSY;
	rand vmm_ral_field INT_SOURCE_RXE;
	rand vmm_ral_field RXE;
	rand vmm_ral_field INT_SOURCE_RXB;
	rand vmm_ral_field RXB;
	rand vmm_ral_field INT_SOURCE_TXE;
	rand vmm_ral_field TXE;
	rand vmm_ral_field INT_SOURCE_TXB;
	rand vmm_ral_field TXB;
	rand vmm_ral_field INT_MASK_RXC_M;
	rand vmm_ral_field RXC_M;
	rand vmm_ral_field INT_MASK_TXC_M;
	rand vmm_ral_field TXC_M;
	rand vmm_ral_field INT_MASK_BUSY_M;
	rand vmm_ral_field BUSY_M;
	rand vmm_ral_field INT_MASK_RXE_M;
	rand vmm_ral_field RXE_M;
	rand vmm_ral_field INT_MASK_RXB_M;
	rand vmm_ral_field RXB_M;
	rand vmm_ral_field INT_MASK_TXE_M;
	rand vmm_ral_field TXE_M;
	rand vmm_ral_field INT_MASK_TXB_M;
	rand vmm_ral_field TXB_M;
	rand vmm_ral_field IPGT_IPGT;
	rand vmm_ral_field IPGR1_IPGR1;
	rand vmm_ral_field IPGR2_IPGR2;
	rand vmm_ral_field PACKETLEN_MINFL;
	rand vmm_ral_field MINFL;
	rand vmm_ral_field PACKETLEN_MAXFL;
	rand vmm_ral_field MAXFL;
	rand vmm_ral_field COLLCONF_MAXRET;
	rand vmm_ral_field MAXRET;
	rand vmm_ral_field COLLCONF_COLLVALID;
	rand vmm_ral_field COLLVALID;
	rand vmm_ral_field TX_BD_NUM_TX_BD_NUM;
	rand vmm_ral_field CTRLMODER_TXFLOW;
	rand vmm_ral_field TXFLOW;
	rand vmm_ral_field CTRLMODER_RXFLOW;
	rand vmm_ral_field RXFLOW;
	rand vmm_ral_field CTRLMODER_PASSALL;
	rand vmm_ral_field PASSALL;
	rand vmm_ral_field MIIMODER_MIINOPRE;
	rand vmm_ral_field MIINOPRE;
	rand vmm_ral_field MIIMODER_CLKDIV;
	rand vmm_ral_field CLKDIV;
	rand vmm_ral_field MIICOMMAND_WCTRLDATA;
	rand vmm_ral_field WCTRLDATA;
	rand vmm_ral_field MIICOMMAND_RSTAT;
	rand vmm_ral_field RSTAT;
	rand vmm_ral_field MIICOMMAND_SCANSTAT;
	rand vmm_ral_field SCANSTAT;
	rand vmm_ral_field MIIADDRESS_RGAD;
	rand vmm_ral_field RGAD;
	rand vmm_ral_field MIIADDRESS_FIAD;
	rand vmm_ral_field FIAD;
	rand vmm_ral_field MIITX_DATA_CTRLDATA;
	rand vmm_ral_field CTRLDATA;
	rand vmm_ral_field MIIRX_DATA_PRSD;
	rand vmm_ral_field PRSD;
	rand vmm_ral_field MIISTATUS_NVALID;
	rand vmm_ral_field NVALID;
	rand vmm_ral_field MIISTATUS_BUSY_N;
	rand vmm_ral_field BUSY_N;
	rand vmm_ral_field MIISTATUS_LINKFAIL;
	rand vmm_ral_field LINKFAIL;
	rand vmm_ral_field MAC_ADDR_MAC_ADDR;
	rand vmm_ral_field HASH0_HASH0;
	rand vmm_ral_field HASH1_HASH1;
	rand vmm_ral_field TXCTRL_TXPAUSEREQ;
	rand vmm_ral_field TXPAUSEREQ;
	rand vmm_ral_field TXCTRL_TXPAUSETV;
	rand vmm_ral_field TXPAUSETV;

	function new(int cover_on = vmm_ral::NO_COVERAGE, string name = "oc_ethernet", vmm_ral_sys parent = null, integer base_addr = 0);
		super.new(parent, name, "oc_ethernet", 4, vmm_ral::LITTLE_ENDIAN, base_addr, "", cover_on);
		this.MODER = new(this, "MODER", `VMM_RAL_ADDR_WIDTH'h0, "", cover_on, 2'b11, 0);
		this.MODER_RECSMALL = this.MODER.RECSMALL;
		this.RECSMALL = this.MODER.RECSMALL;
		this.MODER_PAD = this.MODER.PAD;
		this.PAD = this.MODER.PAD;
		this.MODER_HUGEN = this.MODER.HUGEN;
		this.HUGEN = this.MODER.HUGEN;
		this.MODER_CRCEN = this.MODER.CRCEN;
		this.CRCEN = this.MODER.CRCEN;
		this.MODER_DLYCRCEN = this.MODER.DLYCRCEN;
		this.DLYCRCEN = this.MODER.DLYCRCEN;
		this.MODER_undocumented = this.MODER.undocumented;
		this.undocumented = this.MODER.undocumented;
		this.MODER_FULLD = this.MODER.FULLD;
		this.FULLD = this.MODER.FULLD;
		this.MODER_EXDFREN = this.MODER.EXDFREN;
		this.EXDFREN = this.MODER.EXDFREN;
		this.MODER_NOBCKOF = this.MODER.NOBCKOF;
		this.NOBCKOF = this.MODER.NOBCKOF;
		this.MODER_LOOPBCK = this.MODER.LOOPBCK;
		this.LOOPBCK = this.MODER.LOOPBCK;
		this.MODER_IFG = this.MODER.IFG;
		this.IFG = this.MODER.IFG;
		this.MODER_PRO = this.MODER.PRO;
		this.PRO = this.MODER.PRO;
		this.MODER_IAM = this.MODER.IAM;
		this.IAM = this.MODER.IAM;
		this.MODER_BRO = this.MODER.BRO;
		this.BRO = this.MODER.BRO;
		this.MODER_NOPRE = this.MODER.NOPRE;
		this.NOPRE = this.MODER.NOPRE;
		this.MODER_TXEN = this.MODER.TXEN;
		this.TXEN = this.MODER.TXEN;
		this.MODER_RXEN = this.MODER.RXEN;
		this.RXEN = this.MODER.RXEN;
		this.INT_SOURCE = new(this, "INT_SOURCE", `VMM_RAL_ADDR_WIDTH'h1, "", cover_on, 2'b11, 0);
		this.INT_SOURCE_RXC = this.INT_SOURCE.RXC;
		this.RXC = this.INT_SOURCE.RXC;
		this.INT_SOURCE_TXC = this.INT_SOURCE.TXC;
		this.TXC = this.INT_SOURCE.TXC;
		this.INT_SOURCE_BUSY = this.INT_SOURCE.BUSY;
		this.BUSY = this.INT_SOURCE.BUSY;
		this.INT_SOURCE_RXE = this.INT_SOURCE.RXE;
		this.RXE = this.INT_SOURCE.RXE;
		this.INT_SOURCE_RXB = this.INT_SOURCE.RXB;
		this.RXB = this.INT_SOURCE.RXB;
		this.INT_SOURCE_TXE = this.INT_SOURCE.TXE;
		this.TXE = this.INT_SOURCE.TXE;
		this.INT_SOURCE_TXB = this.INT_SOURCE.TXB;
		this.TXB = this.INT_SOURCE.TXB;
		this.INT_MASK = new(this, "INT_MASK", `VMM_RAL_ADDR_WIDTH'h2, "", cover_on, 2'b11, 0);
		this.INT_MASK_RXC_M = this.INT_MASK.RXC_M;
		this.RXC_M = this.INT_MASK.RXC_M;
		this.INT_MASK_TXC_M = this.INT_MASK.TXC_M;
		this.TXC_M = this.INT_MASK.TXC_M;
		this.INT_MASK_BUSY_M = this.INT_MASK.BUSY_M;
		this.BUSY_M = this.INT_MASK.BUSY_M;
		this.INT_MASK_RXE_M = this.INT_MASK.RXE_M;
		this.RXE_M = this.INT_MASK.RXE_M;
		this.INT_MASK_RXB_M = this.INT_MASK.RXB_M;
		this.RXB_M = this.INT_MASK.RXB_M;
		this.INT_MASK_TXE_M = this.INT_MASK.TXE_M;
		this.TXE_M = this.INT_MASK.TXE_M;
		this.INT_MASK_TXB_M = this.INT_MASK.TXB_M;
		this.TXB_M = this.INT_MASK.TXB_M;
		this.IPGT = new(this, "IPGT", `VMM_RAL_ADDR_WIDTH'h3, "", cover_on, 2'b11, 0);
		this.IPGT_IPGT = this.IPGT.IPGT;
		this.IPGR1 = new(this, "IPGR1", `VMM_RAL_ADDR_WIDTH'h4, "", cover_on, 2'b11, 0);
		this.IPGR1_IPGR1 = this.IPGR1.IPGR1;
		this.IPGR2 = new(this, "IPGR2", `VMM_RAL_ADDR_WIDTH'h5, "", cover_on, 2'b11, 0);
		this.IPGR2_IPGR2 = this.IPGR2.IPGR2;
		this.PACKETLEN = new(this, "PACKETLEN", `VMM_RAL_ADDR_WIDTH'h6, "", cover_on, 2'b11, 0);
		this.PACKETLEN_MINFL = this.PACKETLEN.MINFL;
		this.MINFL = this.PACKETLEN.MINFL;
		this.PACKETLEN_MAXFL = this.PACKETLEN.MAXFL;
		this.MAXFL = this.PACKETLEN.MAXFL;
		this.COLLCONF = new(this, "COLLCONF", `VMM_RAL_ADDR_WIDTH'h7, "", cover_on, 2'b11, 0);
		this.COLLCONF_MAXRET = this.COLLCONF.MAXRET;
		this.MAXRET = this.COLLCONF.MAXRET;
		this.COLLCONF_COLLVALID = this.COLLCONF.COLLVALID;
		this.COLLVALID = this.COLLCONF.COLLVALID;
		this.TX_BD_NUM = new(this, "TX_BD_NUM", `VMM_RAL_ADDR_WIDTH'h8, "", cover_on, 2'b11, 0);
		this.TX_BD_NUM_TX_BD_NUM = this.TX_BD_NUM.TX_BD_NUM;
		this.CTRLMODER = new(this, "CTRLMODER", `VMM_RAL_ADDR_WIDTH'h9, "", cover_on, 2'b11, 0);
		this.CTRLMODER_TXFLOW = this.CTRLMODER.TXFLOW;
		this.TXFLOW = this.CTRLMODER.TXFLOW;
		this.CTRLMODER_RXFLOW = this.CTRLMODER.RXFLOW;
		this.RXFLOW = this.CTRLMODER.RXFLOW;
		this.CTRLMODER_PASSALL = this.CTRLMODER.PASSALL;
		this.PASSALL = this.CTRLMODER.PASSALL;
		this.MIIMODER = new(this, "MIIMODER", `VMM_RAL_ADDR_WIDTH'hA, "", cover_on, 2'b11, 0);
		this.MIIMODER_MIINOPRE = this.MIIMODER.MIINOPRE;
		this.MIINOPRE = this.MIIMODER.MIINOPRE;
		this.MIIMODER_CLKDIV = this.MIIMODER.CLKDIV;
		this.CLKDIV = this.MIIMODER.CLKDIV;
		this.MIICOMMAND = new(this, "MIICOMMAND", `VMM_RAL_ADDR_WIDTH'hB, "", cover_on, 2'b11, 0);
		this.MIICOMMAND_WCTRLDATA = this.MIICOMMAND.WCTRLDATA;
		this.WCTRLDATA = this.MIICOMMAND.WCTRLDATA;
		this.MIICOMMAND_RSTAT = this.MIICOMMAND.RSTAT;
		this.RSTAT = this.MIICOMMAND.RSTAT;
		this.MIICOMMAND_SCANSTAT = this.MIICOMMAND.SCANSTAT;
		this.SCANSTAT = this.MIICOMMAND.SCANSTAT;
		this.MIIADDRESS = new(this, "MIIADDRESS", `VMM_RAL_ADDR_WIDTH'hC, "", cover_on, 2'b11, 0);
		this.MIIADDRESS_RGAD = this.MIIADDRESS.RGAD;
		this.RGAD = this.MIIADDRESS.RGAD;
		this.MIIADDRESS_FIAD = this.MIIADDRESS.FIAD;
		this.FIAD = this.MIIADDRESS.FIAD;
		this.MIITX_DATA = new(this, "MIITX_DATA", `VMM_RAL_ADDR_WIDTH'hD, "", cover_on, 2'b11, 0);
		this.MIITX_DATA_CTRLDATA = this.MIITX_DATA.CTRLDATA;
		this.CTRLDATA = this.MIITX_DATA.CTRLDATA;
		this.MIIRX_DATA = new(this, "MIIRX_DATA", `VMM_RAL_ADDR_WIDTH'hE, "", cover_on, 2'b11, 0);
		this.MIIRX_DATA_PRSD = this.MIIRX_DATA.PRSD;
		this.PRSD = this.MIIRX_DATA.PRSD;
		this.MIISTATUS = new(this, "MIISTATUS", `VMM_RAL_ADDR_WIDTH'hF, "", cover_on, 2'b11, 0);
		this.MIISTATUS_NVALID = this.MIISTATUS.NVALID;
		this.NVALID = this.MIISTATUS.NVALID;
		this.MIISTATUS_BUSY_N = this.MIISTATUS.BUSY_N;
		this.BUSY_N = this.MIISTATUS.BUSY_N;
		this.MIISTATUS_LINKFAIL = this.MIISTATUS.LINKFAIL;
		this.LINKFAIL = this.MIISTATUS.LINKFAIL;
		this.MAC_ADDR = new(this, "MAC_ADDR", `VMM_RAL_ADDR_WIDTH'h10, "", cover_on, 2'b11, 0);
		this.MAC_ADDR_MAC_ADDR = this.MAC_ADDR.MAC_ADDR;
		this.HASH0 = new(this, "HASH0", `VMM_RAL_ADDR_WIDTH'h12, "", cover_on, 2'b11, 0);
		this.HASH0_HASH0 = this.HASH0.HASH0;
		this.HASH1 = new(this, "HASH1", `VMM_RAL_ADDR_WIDTH'h13, "", cover_on, 2'b11, 0);
		this.HASH1_HASH1 = this.HASH1.HASH1;
		this.TXCTRL = new(this, "TXCTRL", `VMM_RAL_ADDR_WIDTH'h14, "", cover_on, 2'b11, 0);
		this.TXCTRL_TXPAUSEREQ = this.TXCTRL.TXPAUSEREQ;
		this.TXPAUSEREQ = this.TXCTRL.TXPAUSEREQ;
		this.TXCTRL_TXPAUSETV = this.TXCTRL.TXPAUSETV;
		this.TXPAUSETV = this.TXCTRL.TXPAUSETV;
		`foreach_sa (this.TxBD,128,i) begin
			int J = i;
			this.TxBD[J] = new(this, $psprintf("TxBD[%0d]",J), `VMM_RAL_ADDR_WIDTH'h100+J*`VMM_RAL_ADDR_WIDTH'h2, "", cover_on);
		end
		`foreach_sa (this.RxBD,128,i) begin
			int J = i;
			this.RxBD[J] = new(this, $psprintf("RxBD[%0d]",J), `VMM_RAL_ADDR_WIDTH'h100+J*`VMM_RAL_ADDR_WIDTH'h2, "", cover_on);
		end
		this.Xlock_modelX();
	endfunction : new
endclass : ral_block_oc_ethernet


class ral_sys_dual_eth extends vmm_ral_sys;
	rand ral_block_oc_ethernet eth[2];

	function new(int cover_on = vmm_ral::NO_COVERAGE, string name = "dual_eth", vmm_ral_sys parent = null, integer base_addr = 0);
		super.new(parent, name, "dual_eth", 4, vmm_ral::LITTLE_ENDIAN, base_addr, "", cover_on);
		`foreach_sa (this.eth,2,i) begin
			int J = i;
			this.eth[J] = new(cover_on, $psprintf("eth[%0d]",J), this, `VMM_RAL_ADDR_WIDTH'h0+J*`VMM_RAL_ADDR_WIDTH'h4000);
			this.register_block(this.eth[J], "", "", `VMM_RAL_ADDR_WIDTH'h0+J*`VMM_RAL_ADDR_WIDTH'h4000);
		end
		this.Xlock_modelX();
	endfunction : new
endclass : ral_sys_dual_eth


`endif
