module rggen_bit_field
  import  rggen_rtl_pkg::*;
#(
  parameter int                 WIDTH                     = 8,
  parameter bit [WIDTH-1:0]     INITIAL_VALUE             = '0,
  parameter rggen_sw_hw_access  PRECEDENCE_ACCESS         = RGGEN_HW_ACCESS,
  parameter rggen_sw_action     SW_READ_ACTION            = RGGEN_READ_DEFAULT,
  parameter rggen_sw_action     SW_WRITE_ACTION           = RGGEN_WRITE_DEFAULT,
  parameter bit                 SW_WRITE_ONCE             = '0,
  parameter rggen_polarity      SW_WRITE_ENABLE_POLARITY  = RGGEN_ACTIVE_HIGH,
  parameter rggen_polarity      HW_WRITE_ENABLE_POLARITY  = RGGEN_ACTIVE_HIGH,
  parameter int                 HW_SET_WIDTH              = WIDTH,
  parameter int                 HW_CLEAR_WIDTH            = WIDTH,
  parameter bit                 STORAGE                   = '1,
  parameter bit                 EXTERNAL_READ_DATA        = '0,
  parameter bit                 TRIGGER                   = '0
)(
  input   logic                       i_clk,
  input   logic                       i_rst_n,
  rggen_bit_field_if.bit_field        bit_field_if,
  output  logic                       o_write_trigger,
  output  logic                       o_read_trigger,
  input   logic                       i_sw_write_enable,
  input   logic                       i_hw_write_enable,
  input   logic [WIDTH-1:0]           i_hw_write_data,
  input   logic [HW_SET_WIDTH-1:0]    i_hw_set,
  input   logic [HW_CLEAR_WIDTH-1:0]  i_hw_clear,
  input   logic [WIDTH-1:0]           i_value,
  input   logic [WIDTH-1:0]           i_mask,
  output  logic [WIDTH-1:0]           o_value,
  output  logic [WIDTH-1:0]           o_value_unmasked
);
//--------------------------------------------------------------
//  Utility functions
//--------------------------------------------------------------
  function automatic logic [1:0] get_sw_update(
    logic             valid,
    logic [WIDTH-1:0] read_mask,
    logic             write_enable,
    logic [WIDTH-1:0] write_mask,
    logic             write_done
  );
    logic [1:0] action;
    logic [1:0] access;
    logic [1:0] update;

    action[0] = (SW_READ_ACTION  == RGGEN_READ_CLEAR) ||
                (SW_READ_ACTION  == RGGEN_READ_SET  );
    action[1] = (SW_WRITE_ACTION != RGGEN_WRITE_NONE);

    access[0] = (read_mask  != '0);
    access[1] = (write_mask != '0)  && (write_enable == SW_WRITE_ENABLE_POLARITY) && (!write_done);

    update[0] = valid && action[0] && access[0];
    update[1] = valid && action[1] && access[1];
    return update;
  endfunction

  function automatic logic get_hw_update(
    logic                       write_enable,
    logic [HW_SET_WIDTH-1:0]    set,
    logic [HW_CLEAR_WIDTH-1:0]  clear
  );
    logic update;
    update  = (write_enable == HW_WRITE_ENABLE_POLARITY) || (set != '0) || (clear != '0);
    return update;
  endfunction

  function automatic logic [WIDTH-1:0] get_next_value(
    logic [WIDTH-1:0]           current_value,
    logic [1:0]                 sw_update,
    logic [WIDTH-1:0]           sw_write_mask,
    logic [WIDTH-1:0]           sw_write_data,
    logic                       hw_write_enable,
    logic [WIDTH-1:0]           hw_write_data,
    logic [HW_SET_WIDTH-1:0]    hw_set,
    logic [HW_CLEAR_WIDTH-1:0]  hw_clear
  );
    logic [WIDTH-1:0] value;

    if (PRECEDENCE_ACCESS == RGGEN_SW_ACCESS) begin
      value =
        get_hw_next_value(
          current_value, hw_write_enable, hw_write_data,
          hw_set, hw_clear
        );
      value =
        get_sw_next_value(
          value, sw_update, sw_write_mask, sw_write_data
        );
    end
    else begin
      value =
        get_sw_next_value(
          current_value, sw_update, sw_write_mask, sw_write_data
        );
      value =
        get_hw_next_value(
          value, hw_write_enable, hw_write_data,
          hw_set, hw_clear
        );
    end

    return value;
  endfunction

  function automatic logic [WIDTH-1:0] get_sw_next_value(
    logic [WIDTH-1:0] current_value,
    logic [1:0]       update,
    logic [WIDTH-1:0] write_mask,
    logic [WIDTH-1:0] write_data
  );
    logic [WIDTH-1:0] value[2];
    logic [WIDTH-1:0] masked_data[2];

    case (SW_READ_ACTION)
      RGGEN_READ_CLEAR: value[0]  = '0;
      RGGEN_READ_SET:   value[0]  = '1;
      default:          value[0]  = current_value;
    endcase

    masked_data[0]  = write_mask & (~write_data);
    masked_data[1]  = write_mask & ( write_data);
    case (SW_WRITE_ACTION)
      RGGEN_WRITE_DEFAULT:  value[1]  = (current_value & (~write_mask)) | masked_data[1];
      RGGEN_WRITE_0_CLEAR:  value[1]  = current_value & (~masked_data[0]);
      RGGEN_WRITE_1_CLEAR:  value[1]  = current_value & (~masked_data[1]);
      RGGEN_WRITE_CLEAR:    value[1]  = '0;
      RGGEN_WRITE_0_SET:    value[1]  = current_value | masked_data[0];
      RGGEN_WRITE_1_SET:    value[1]  = current_value | masked_data[1];
      RGGEN_WRITE_SET:      value[1]  = '1;
      RGGEN_WRITE_0_TOGGLE: value[1]  = current_value ^ masked_data[0];
      RGGEN_WRITE_1_TOGGLE: value[1]  = current_value ^ masked_data[1];
      default:              value[1]  = current_value;
    endcase

    case (update)
      2'b01:    return value[0];
      2'b10:    return value[1];
      default:  return current_value;
    endcase
  endfunction

  function automatic logic [WIDTH-1:0] get_hw_next_value(
    logic [WIDTH-1:0]           current_value,
    logic                       write_enable,
    logic [WIDTH-1:0]           write_data,
    logic [HW_SET_WIDTH-1:0]    set,
    logic [HW_CLEAR_WIDTH-1:0]  clear
  );
    logic [WIDTH-1:0] set_clear[2];
    logic [WIDTH-1:0] value;

    if (HW_SET_WIDTH == WIDTH) begin
      set_clear[0][HW_SET_WIDTH-1:0]  = set;
    end
    else begin
      set_clear[0]  = {WIDTH{set[0]}};
    end

    if (HW_CLEAR_WIDTH == WIDTH) begin
      set_clear[1][HW_CLEAR_WIDTH-1:0]  = clear;
    end
    else begin
      set_clear[1]  = {WIDTH{clear[0]}};
    end

    if (write_enable == HW_WRITE_ENABLE_POLARITY) begin
      value = write_data;
    end
    else begin
      value = current_value;
    end

    return (value & (~set_clear[1])) | set_clear[0];;
  endfunction

//--------------------------------------------------------------
//  Body
//--------------------------------------------------------------
  localparam  bit SW_READABLE = SW_READ_ACTION != RGGEN_READ_NONE;

  logic [1:0]       sw_update;
  logic             sw_write_done;
  logic             hw_update;
  logic [1:0]       trigger;
  logic [WIDTH-1:0] value;
  logic [WIDTH-1:0] read_data;

  assign  bit_field_if.read_data  = read_data & i_mask;
  assign  bit_field_if.value      = value;
  assign  o_write_trigger         = trigger[0];
  assign  o_read_trigger          = trigger[1];
  assign  o_value                 = value & i_mask;
  assign  o_value_unmasked        = value;

  assign  sw_update =
    get_sw_update(
      bit_field_if.valid, bit_field_if.read_mask,
      i_sw_write_enable, bit_field_if.write_mask, sw_write_done
    );
  assign  hw_update =
    get_hw_update(
      i_hw_write_enable, i_hw_set, i_hw_clear
    );

  generate if (STORAGE && SW_WRITE_ONCE) begin : g_sw_write_done
    always_ff @(posedge i_clk, negedge i_rst_n) begin
      if (!i_rst_n) begin
        sw_write_done <= '0;
      end
      else if (sw_update[1]) begin
        sw_write_done <= '1;
      end
    end
  end
  else begin : g_sw_write_done
    assign  sw_write_done = '0;
  end endgenerate

  generate if (TRIGGER && (SW_WRITE_ACTION != RGGEN_WRITE_NONE)) begin : g_write_trigger
    always_ff @(posedge i_clk, negedge i_rst_n) begin
      if (!i_rst_n) begin
        trigger[0]  <= '0;
      end
      else begin
        trigger[0]  <= sw_update[1];
      end
    end
  end
  else begin : g_write_trigger
    assign  trigger[0]  = '0;
  end endgenerate

  generate if (TRIGGER && (SW_READ_ACTION != RGGEN_READ_NONE)) begin : g_read_trigger
    always_ff @(posedge i_clk, negedge i_rst_n) begin
      if (!i_rst_n) begin
        trigger[1]  <= '0;
      end
      else begin
        trigger[1]  <= bit_field_if.valid && (bit_field_if.read_mask != '0);
      end
    end
  end
  else begin : g_read_trigger
    assign  trigger[1]  = '0;
  end endgenerate

  generate if (STORAGE) begin : g_value
    logic [WIDTH-1:0] value_next;

    assign  value_next  =
      get_next_value(
        value, sw_update, bit_field_if.write_mask, bit_field_if.write_data,
        i_hw_write_enable, i_hw_write_data, i_hw_set, i_hw_clear
      );
    always_ff @(posedge i_clk, negedge i_rst_n) begin
      if (!i_rst_n) begin
        value <= INITIAL_VALUE;
      end
      else if (sw_update[0] || sw_update[1] || hw_update) begin
        value <= value_next;
      end
    end
  end
  else begin : g_value
    assign  value = i_value;
  end endgenerate

  generate if (!SW_READABLE) begin : g_read_data
    assign  read_data = '0;
  end
  else if (EXTERNAL_READ_DATA) begin : g_read_data
    assign  read_data = i_value;
  end
  else begin : g_read_data
    assign  read_data = value;
  end endgenerate
endmodule
