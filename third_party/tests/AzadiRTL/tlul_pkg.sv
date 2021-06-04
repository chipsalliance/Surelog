package tlul_pkg;


    parameter ArbiterImpl = "PPC";
function automatic integer _clog2(integer value);
    integer result;
    value = value - 1;
    for (result = 0; value > 0; result = result + 1) begin
      value = value >> 1;
    end
    return result;
  endfunction


  /**
   * Math function: Number of bits needed to address |value| items.
   *
   *                  0        for value == 0
   * vbits =          1        for value == 1
   *         ceil(log2(value)) for value > 1
   *
   *
   * The primary use case for this function is the definition of registers/arrays
   * which are wide enough to contain |value| items.
   *
   * This function identical to $clog2() for all input values except the value 1;
   * it could be considered an "enhanced" $clog2() function.
   *
   *
   * Example 1:
   *   parameter Items = 1;
   *   localparam ItemsWidth = vbits(Items); // 1
   *   logic [ItemsWidth-1:0] item_register; // items_register is now [0:0]
   *
   * Example 2:
   *   parameter Items = 64;
   *   localparam ItemsWidth = vbits(Items); // 6
   *   logic [ItemsWidth-1:0] item_register; // items_register is now [5:0]
   *
   * Note: If you want to store the number "value" inside a register, you need
   * a register with size vbits(value + 1), since you also need to store
   * the number 0.
   *
   * Example 3:
   *   logic [vbits(64)-1:0]     store_64_logic_values; // width is [5:0]
   *   logic [vbits(64 + 1)-1:0] store_number_64;       // width is [6:0]
   */
  function automatic integer vbits(integer value);
`ifdef XCELIUM
    // The use of system functions was not allowed here in Verilog-2001, but is
    // valid since (System)Verilog-2005, which is also when $clog2() first
    // appeared.
    // Xcelium < 19.10 does not yet support the use of $clog2() here, fall back
    // to an implementation without a system function. Remove this workaround
    // if we require a newer Xcelium version.
    // See #2579 and #2597.
    return (value == 1) ? 1 : prim_util_pkg::_clog2(value);
`else
    return (value == 1) ? 1 : $clog2(value);
`endif
  endfunction

    localparam int TL_AW=32;
    localparam int TL_DW=32;
    localparam int TL_AIW=8;
    localparam int TL_DIW=1;
    localparam int TL_DBW=(TL_DW>>3);
    localparam int TL_SZW=$clog2($clog2(TL_DBW)+1);

// opcodes for channel D messages/operations defined in official TileLink spec
    typedef enum logic [2:0] {
        PutFullData     = 3'h0,
        PutPartialData  = 3'h1,
        Get             = 3'h4
    } tl_a_m_op;
// opcodes for channel D messages/operations defined in official TileLink spec
    typedef enum logic [2:0] {
        AccessAck     = 3'h0,
        AccessAckData = 3'h1
    } tl_d_m_op;

    typedef struct packed {
        logic                        a_valid;
        tl_a_m_op                    a_opcode;
        logic           [2:0]        a_param;
        logic           [TL_SZW-1:0] a_size;
        logic           [TL_AIW-1:0] a_source;
        logic           [TL_AW-1:0]  a_address;
        logic           [TL_DBW-1:0] a_mask;
        logic           [TL_DW-1:0]  a_data;
        logic                        d_ready;
    } tl_h2d_t;

    localparam tl_h2d_t TL_H2D_DEFAULT = '{
        d_ready:  1'b1,
        a_opcode: tl_a_m_op'('0),
        default:  '0
    };

    typedef struct packed {
        logic                   d_valid;
        tl_d_m_op               d_opcode;
        logic             [2:0] d_param;
        logic      [TL_SZW-1:0] d_size;
        logic      [TL_AIW-1:0] d_source;
        logic      [TL_DIW-1:0] d_sink;
        logic      [TL_DW-1:0]  d_data;
        logic                   d_error;
        logic                   a_ready;
    } tl_d2h_t;

    localparam tl_d2h_t TL_D2H_DEFAULT = '{
        a_ready:  1'b1,
        d_opcode: tl_d_m_op'('0),
        default:  '0
    };



endpackage
