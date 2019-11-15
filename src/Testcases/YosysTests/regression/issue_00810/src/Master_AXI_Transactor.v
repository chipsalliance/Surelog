
// Master AXI Transactor

// Connects a set of system interface registers to an AXI interface.
// Internal sequencing is done through the control interface.

// Expected usage for AXI reads and writes:
// - Set the address, type and length of transaction
// - Read/write the expected number of data words
// - If a write, read the response.

module Master_AXI_Transactor
#(
    parameter WORD_WIDTH    = 0,
    // set to clog2(WORD_WIDTH)
    parameter BYTE_COUNT    = 0,
    parameter ADDR_WIDTH    = 0,
    // Bytes per transfer
    // set to clog2(BYTE_COUNT)
    parameter AXSIZE        = 0,

    // Do not alter at instantiation. Set by AXI4 spec.
    parameter AXLEN_WIDTH   = 8,
    parameter AXSIZE_WIDTH  = 3,
    parameter AXBURST_WIDTH = 2,
    parameter BRESP_WIDTH   = 2,
    parameter RRESP_WIDTH   = 2
)
(
    input   wire                        clock,

// --

    // Read Address Channel
    // System interface
    input   wire    [ADDR_WIDTH-1:0]    ar_system_address,
    input   wire                        ar_system_address_wren,
    input   wire    [AXLEN_WIDTH-1:0]   ar_system_count,
    input   wire                        ar_system_count_wren,
    input   wire    [AXBURST_WIDTH-1:0] ar_system_type,
    input   wire                        ar_system_type_wren,
    input   wire                        ar_system_start,
    output  wire                        ar_system_ready,


    // AXI interface
    output  wire    [ADDR_WIDTH-1:0]    araddr,
    output  wire    [AXLEN_WIDTH-1:0]   arlen,
    output  wire    [AXSIZE_WIDTH-1:0]  arsize,
    output  wire    [AXBURST_WIDTH-1:0] arburst,
    output  wire                        arvalid,
    input   wire                        arready,

// --

    // Write Address Channel
    // System interface
    input   wire    [ADDR_WIDTH-1:0]    aw_system_address,
    input   wire                        aw_system_address_wren,
    input   wire    [AXLEN_WIDTH-1:0]   aw_system_count,
    input   wire                        aw_system_count_wren,
    input   wire    [AXBURST_WIDTH-1:0] aw_system_type,
    input   wire                        aw_system_type_wren,
    input   wire                        aw_system_start,
    output  wire                        aw_system_ready,

    // AXI interface
    output  wire    [ADDR_WIDTH-1:0]    awaddr,
    output  wire    [AXLEN_WIDTH-1:0]   awlen,
    output  wire    [AXSIZE_WIDTH-1:0]  awsize,
    output  wire    [AXBURST_WIDTH-1:0] awburst,
    output  wire                        awvalid,
    input   wire                        awready,

// --

    // Read Data Channel
    // System interface
    output  wire    [WORD_WIDTH-1:0]    r_system_data,
    output  wire                        r_system_error,
    output  wire                        r_system_valid,
    input   wire                        r_system_ready,

    // AXI interface
    input   wire    [WORD_WIDTH-1:0]    rdata,
    input   wire    [RRESP_WIDTH-1:0]   rresp,
    input   wire                        rlast,
    input   wire                        rvalid,
    output  wire                        rready,

// --

    // Write Data Channel
    // System interface
    input   wire    [WORD_WIDTH-1:0]    w_system_data,
    input   wire                        w_system_valid,
    output  wire                        w_system_ready,

    // AXI interface
    output  wire    [WORD_WIDTH-1:0]    wdata,
    output  wire    [BYTE_COUNT-1:0]    wstrb,
    output  wire                        wlast,
    output  wire                        wvalid,
    input   wire                        wready,

// --

    // Write Response Channel
    // System interface
    output  wire    [BRESP_WIDTH-1:0]   b_system_response,
    input   wire                        b_system_ready,
    output  wire                        b_system_valid,

    // AXI interface
    input   wire    [BRESP_WIDTH-1:0]   bresp,
    input   wire                        bvalid,
    output  wire                        bready
);

// --------------------------------------------------------------------------
// --------------------------------------------------------------------------

    wire ar_control_enable;
    wire ar_control_done;

    Master_AXI_Address_Channel
    #(
        .ADDR_WIDTH             (ADDR_WIDTH),
        .AXSIZE                 (AXSIZE)
    )
    Read_Address
    (
        .clock                  (clock),

        // System interface
        .system_address         (ar_system_address),
        .system_address_wren    (ar_system_address_wren),
        .system_count           (ar_system_count),
        .system_count_wren      (ar_system_count_wren),
        .system_type            (ar_system_type),
        .system_type_wren       (ar_system_type_wren),
        .system_start           (ar_system_start),
        .system_ready           (ar_system_ready),

        // Control interface
        .control_enable         (ar_control_enable),
        .control_done           (ar_control_done),

        // AXI interface        
        .axaddr                 (araddr),
        .axlen                  (arlen),
        .axsize                 (arsize),
        .axburst                (arburst),
        .axvalid                (arvalid),
        .axready                (arready)
    );

// --------------------------------------------------------------------------

    wire aw_control_enable;
    wire aw_control_done;

    Master_AXI_Address_Channel
    #(
        .ADDR_WIDTH             (ADDR_WIDTH),
        .AXSIZE                 (AXSIZE)
    )
    Write_Address
    (
        .clock                  (clock),

        // System interface
        .system_address         (aw_system_address),
        .system_address_wren    (aw_system_address_wren),
        .system_count           (aw_system_count),
        .system_count_wren      (aw_system_count_wren),
        .system_type            (aw_system_type),
        .system_type_wren       (aw_system_type_wren),
        .system_start           (aw_system_start),
        .system_ready           (aw_system_ready),

        // Control interface
        .control_enable         (aw_control_enable),
        .control_done           (aw_control_done),

        // AXI interface        
        .axaddr                 (awaddr),
        .axlen                  (awlen),
        .axsize                 (awsize),
        .axburst                (awburst),
        .axvalid                (awvalid),
        .axready                (awready)
    );

// --------------------------------------------------------------------------

    wire r_control_enable;
    wire r_control_done;

    Master_AXI_Read_Data_Channel
    #(
        .WORD_WIDTH     (WORD_WIDTH)
    )
    Read_Data
    (
        .clock          (clock),

        // System interface
        .system_data    (r_system_data),
        .system_error   (r_system_error),
        .system_valid   (r_system_valid),
        .system_ready   (r_system_ready),

        // Control interface
        .control_enable (r_control_enable),
        .control_done   (r_control_done),

        // AXI interface
        .rdata          (rdata),
        .rresp          (rresp),
        .rlast          (rlast),
        .rvalid         (rvalid),
        .rready         (rready)
    );

// --------------------------------------------------------------------------

    wire w_control_enable;
    wire w_control_done;

    Master_AXI_Write_Data_Channel
    #(
        .WORD_WIDTH     (WORD_WIDTH),
        .BYTE_COUNT     (BYTE_COUNT)
    )
    Write_Data
    (
        .clock          (clock),

        // System interface
        .system_data    (w_system_data),
        .system_valid   (w_system_valid),
        .system_ready   (w_system_ready),

        // Control interface
        .control_enable (w_control_enable),
        .control_done   (w_control_done),

        // Internal
        .axlen          (arlen),

        // AXI interface
        .wdata          (wdata),
        .wstrb          (wstrb),
        .wlast          (wlast),
        .wvalid         (wvalid),
        .wready         (wready)
    );

// --------------------------------------------------------------------------

    wire b_control_enable;
    wire b_control_done;

    Master_AXI_Write_Response_Channel
    // No user-settable parameters
    Write_Response
    (
        .clock              (clock),

        // System interface
        .system_response    (b_system_response),
        .system_ready       (b_system_ready),
        .system_valid       (b_system_valid),

        // Control interface
        .control_enable     (b_control_enable),
        .control_done       (b_control_done),

        // AXI interface
        .bresp              (bresp),
        .bvalid             (bvalid),
        .bready             (bready)
    );

// --------------------------------------------------------------------------

    Master_AXI_Sequencer_Read
    // No parameters
    Sequencer_Read
    (
        .clock              (clock),

        .ar_control_enable  (ar_control_enable),
        .ar_control_done    (ar_control_done),

        .r_control_enable   (r_control_enable),
        .r_control_done     (r_control_done)
    );

// --------------------------------------------------------------------------

    Master_AXI_Sequencer_Write
    // No parameters
    Sequencer_Write
    (
        .clock              (clock),

        .aw_control_enable  (aw_control_enable),
        .aw_control_done    (aw_control_done),

        .w_control_enable   (w_control_enable),
        .w_control_done     (w_control_done),

        .b_control_enable   (b_control_enable),
        .b_control_done     (b_control_done)
    );

`ifdef	FORMAL
	(* anyseq *) wire i_axi_reset_n;

	faxi_master #(
    		.C_AXI_ADDR_WIDTH(ADDR_WIDTH),
		.C_AXI_ID_WIDTH(2),
    		.C_AXI_DATA_WIDTH(WORD_WIDTH)
	) faxi(.i_clk(clock),
		.i_axi_reset_n(i_axi_reset_n),
		//
		// AW
		.i_axi_awaddr(awaddr),
		.i_axi_awlen(awlen),
		.i_axi_awid(0),
		.i_axi_awsize(awsize),
		.i_axi_awburst(awburst),
		.i_axi_awlock(0),
		.i_axi_awcache(0),
		.i_axi_awprot(0),
		.i_axi_awqos(0),
		.i_axi_awvalid(awvalid),
		.i_axi_awready(awready),
		//
		// W
        	.i_axi_wready(wready),
        	.i_axi_wdata(wdata),
        	.i_axi_wstrb(wstrb),
        	.i_axi_wlast(wlast),
        	.i_axi_wvalid(wvalid),
		//
		// B
		.i_axi_bresp(bresp),
		.i_axi_bvalid(bvalid),
		.i_axi_bready(bready),
		//
		// AR
		.i_axi_araddr(araddr),
		.i_axi_arid(0),
		.i_axi_arlen(arlen),
		.i_axi_arsize(arsize),
		.i_axi_arburst(arburst),
		.i_axi_arvalid(arvalid),
		.i_axi_arready(arready),
		.i_axi_arcache(0),
		.i_axi_arprot(0),
		.i_axi_arqos(0),
		.i_axi_arlock(0),
		//
		// R
        	.i_axi_rid(0),
        	.i_axi_rdata(rdata),
        	.i_axi_rresp(rresp),
        	.i_axi_rlast(rlast),
        	.i_axi_rvalid(rvalid),
        	.i_axi_rready(rready));
`endif
endmodule

