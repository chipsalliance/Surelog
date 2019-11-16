/*
* ========== Copyright Header Begin ==========================================
* 
* OpenSPARC T1 Processor File: sctag.h
* Copyright (c) 2006 Sun Microsystems, Inc.  All Rights Reserved.
* DO NOT ALTER OR REMOVE COPYRIGHT NOTICES.
* 
* The above named program is free software; you can redistribute it and/or
* modify it under the terms of the GNU General Public
* License version 2 as published by the Free Software Foundation.
* 
* The above named program is distributed in the hope that it will be 
* useful, but WITHOUT ANY WARRANTY; without even the implied warranty of
* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
* General Public License for more details.
* 
* You should have received a copy of the GNU General Public
* License along with this work; if not, write to the Free Software
* Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA 02110-1301, USA.
* 
* ========== Copyright Header End ============================================
*/

`define	IQ_SIZE	8
`define	OQ_SIZE	12
`define	TAG_WIDTH	28


`define	MBD_WIDTH	100

`define	MBD_ECC_HI	99
`define	MBD_ECC_LO	94
`define	MBD_EVICT	93
`define	MBD_DEP		92
`define	MBD_TECC	91
`define	MBD_ENTRY_HI	90
`define	MBD_ENTRY_LO	87

`define	MBD_POISON	86
`define	MBD_RDMA_HI	85
`define	MBD_RDMA_LO	84
`define	MBD_RQ_HI	83
`define	MBD_RQ_LO	79
`define	MBD_NC		78
`define	MBD_RSVD	77
`define	MBD_CP_HI	76
`define	MBD_CP_LO	74
`define	MBD_TH_HI	73
`define	MBD_TH_LO	72
`define	MBD_BF_HI	71
`define	MBD_BF_LO	69
`define	MBD_WY_HI	68
`define	MBD_WY_LO	67
`define	MBD_SZ_HI	66
`define	MBD_SZ_LO	64
`define	MBD_DATA_HI	63
`define	MBD_DATA_LO	0

`define	L2_FBF		33
`define	L2_MBF		32
`define	L2_SNP		31
`define	L2_CTRUE	30
`define	L2_EVICT  	29
`define	L2_DEP		28
`define	L2_TECC		27
`define	L2_ENTRY_HI	26
`define	L2_ENTRY_LO	23

`define	L2_POISON	22
`define	L2_RDMA_HI	21
`define	L2_RDMA_LO	20
`define	L2_RQTYP_HI	19
`define	L2_RQTYP_LO	15
`define	L2_NC		14
`define	L2_RSVD		13
`define	L2_CPUID_HI	12
`define	L2_CPUID_LO	10
`define	L2_TID_HI	9
`define	L2_TID_LO	8
`define	L2_BUFID_HI	7
`define	L2_BUFID_LO	5
`define	L2_L1WY_HI	4
`define	L2_L1WY_LO	3
`define	L2_SZ_HI	2
`define	L2_SZ_LO	0


`define	ERR_MEU		63
`define	ERR_MEC		62
`define	ERR_RW		61
`define	ERR_ASYNC	59
`define	ERR_TID_HI	58
`define	ERR_TID_LO	54
`define	ERR_LDAC	53
`define	ERR_LDAU	52
`define	ERR_LDWC	51
`define	ERR_LDWU	50
`define	ERR_LDRC	49
`define	ERR_LDRU	48
`define	ERR_LDSC	47
`define	ERR_LDSU	46
`define	ERR_LTC		45
`define	ERR_LRU		44
`define	ERR_LVU		43
`define	ERR_DAC		42
`define	ERR_DAU		41
`define	ERR_DRC		40
`define	ERR_DRU		39
`define	ERR_DSC		38
`define	ERR_DSU		37
`define	ERR_VEC		36
`define	ERR_VEU		35
`define	ERR_SYN_HI	31
`define	ERR_SYN_LO	0


`define	JBI_HDR_SZ	22
`define	JBI_ADDR_LO	0	
`define	JBI_ADDR_HI	7	
`define	JBI_SZ_LO	8	
`define	JBI_SZ_HI	10	
`define	JBI_RSVD	11	
`define	JBI_CTAG_LO	12	
`define	JBI_CTAG_HI	23	
`define	JBI_RQ_RD	24	
`define	JBI_RQ_WR8	25	
`define	JBI_RQ_WR64	26	
`define	JBI_RQ_POISON	27	


`define	JBI_ENTRY_LO	27
`define	JBI_ENTRY_HI	28


`define	JBINST_SZ_LO	0	
`define	JBINST_SZ_HI	2	
`define	JBINST_RSVD	3	
`define	JBINST_CTAG_LO	4	
`define	JBINST_CTAG_HI	15	
`define	JBINST_RQ_RD	16	
`define	JBINST_RQ_WR8	17	
`define	JBINST_RQ_WR64	18	
`define	JBINST_ENTRY_LO	19
`define	JBINST_ENTRY_HI	20
`define	JBINST_POISON 21


`define	ST_REQ_ST	1
`define	LD_REQ_ST	2
`define	IDLE	0
