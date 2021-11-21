module tnoc_axi_write_read_demux
  import  tnoc_pkg::*;
#(
  parameter tnoc_packet_config  PACKET_CONFIG = TNOC_DEFAULT_PACKET_CONFIG,
  parameter tnoc_packet_type    WRITE_TYPE    = TNOC_WRITE,
  parameter tnoc_packet_type    READ_TYPE     = TNOC_READ,
  parameter int                 FIFO_DEPTH    = 4
)(
  tnoc_types            types,
  input var logic       i_clk,
  input var logic       i_rst_n,
  tnoc_flit_if.receiver receiver_if,
  tnoc_flit_if.sender   write_if,
  tnoc_flit_if.sender   read_if
);
  localparam  int CHANNELS  = PACKET_CONFIG.virtual_channels;

  typedef types.tnoc_flit           tnoc_flit;
  typedef types.tnoc_common_header  tnoc_common_header;

//--------------------------------------------------------------
//  Input FIFO
//--------------------------------------------------------------
  tnoc_flit_if #(
    .PACKET_CONFIG  (PACKET_CONFIG    ),
    .PORT_TYPE      (TNOC_LOCAL_PORT  )
  ) fifo_out_if(types);

  tnoc_flit_if_fifo #(
    .PACKET_CONFIG  (PACKET_CONFIG    ),
    .DEPTH          (FIFO_DEPTH       ),
    .THRESHOLD      (FIFO_DEPTH - 2   ),
    .PORT_TYPE      (TNOC_LOCAL_PORT  )
  ) u_input_fifo (
    .types          (types        ),
    .i_clk          (i_clk        ),
    .i_rst_n        (i_rst_n      ),
    .i_clear        ('0           ),
    .o_empty        (),
    .o_almost_full  (),
    .o_full         (),
    .receiver_if    (receiver_if  ),
    .sender_if      (fifo_out_if  )
  );

//--------------------------------------------------------------
//  Routing
//--------------------------------------------------------------
  tnoc_flit_if #(
    .PACKET_CONFIG  (PACKET_CONFIG    ),
    .PORT_TYPE      (TNOC_LOCAL_PORT  )
  ) write_read_if[2](types);

  for (genvar i = 0;i < CHANNELS;++i) begin : g_routing
    logic [1:0] route;
    logic [1:0] route_latched;

    always_comb begin
      route = (
        fifo_out_if.flit[i].head
      ) ? select_route(fifo_out_if.flit[i]) : route_latched;
    end

    always_ff @(posedge i_clk) begin
      if (fifo_out_if.get_head_flit_valid(i)) begin
        route_latched <= route;
      end
    end

    always_comb begin
      if (route[0]) begin
        write_read_if[0].valid[i] = fifo_out_if.valid[i];
        fifo_out_if.ready[i]      = write_read_if[0].ready[i];
        write_read_if[1].valid[i] = '0;
      end
      else if (route[1]) begin
        write_read_if[0].valid[i] = '0;
        write_read_if[1].valid[i] = fifo_out_if.valid[i];
        fifo_out_if.ready[i]      = write_read_if[1].ready[i];
      end
      else begin
        write_read_if[0].valid[i] = '0;
        write_read_if[1].valid[i] = '0;
        fifo_out_if.ready[i]      = '1;
      end

      write_read_if[0].flit[i]  = fifo_out_if.flit[i];
      write_read_if[1].flit[i]  = fifo_out_if.flit[i];
      fifo_out_if.vc_ready[i]   = '0;
    end
  end

  function automatic logic [1:0] select_route(
    tnoc_flit flit
  );
    tnoc_common_header  header;
    header  = tnoc_common_header'(flit.data);
    return {
      ((header.packet_type == READ_TYPE ) ? 1'b1 : 1'b0),
      ((header.packet_type == WRITE_TYPE) ? 1'b1 : 1'b0)
    };
  endfunction

//--------------------------------------------------------------
//  Arbitration
//--------------------------------------------------------------
  tnoc_flit_if #(
    .PACKET_CONFIG  (PACKET_CONFIG    ),
    .CHANNELS       (1                ),
    .PORT_TYPE      (TNOC_LOCAL_PORT  )
  ) flit_out_if[2](types);

  for (genvar i = 0;i < 2;++i) begin : g_arbiter
    tnoc_vc_arbiter #(
      .PACKET_CONFIG  (PACKET_CONFIG    ),
      .PORT_TYPE      (TNOC_LOCAL_PORT  ),
      .FIFO_DEPTH     (0                )
    ) u_arbiter (
      .types        (types            ),
      .i_clk        (i_clk            ),
      .i_rst_n      (i_rst_n          ),
      .receiver_if  (write_read_if[i] ),
      .sender_if    (flit_out_if[i]   )
    );
  end

  tnoc_flit_if_connector u_write_if_connector (
    .receiver_if  (flit_out_if[0] ),
    .sender_if    (write_if       )
  );

  tnoc_flit_if_connector u_read_if_connector (
    .receiver_if  (flit_out_if[1] ),
    .sender_if    (read_if        )
  );
endmodule
