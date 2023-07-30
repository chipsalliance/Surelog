library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

use work.rggen_rtl.all;

entity uart_csr is
  generic (
    ADDRESS_WIDTH: positive := 5;
    PRE_DECODE: boolean := false;
    BASE_ADDRESS: unsigned := x"0";
    ERROR_STATUS: boolean := false;
    INSERT_SLICER: boolean := false;
    DLL_INITIAL_VALUE: unsigned(7 downto 0) := repeat(x"00", 8, 1);
    DLM_INITIAL_VALUE: unsigned(7 downto 0) := repeat(x"00", 8, 1)
  );
  port (
    i_clk: in std_logic;
    i_rst_n: in std_logic;
    i_psel: in std_logic;
    i_penable: in std_logic;
    i_paddr: in std_logic_vector(ADDRESS_WIDTH-1 downto 0);
    i_pprot: in std_logic_vector(2 downto 0);
    i_pwrite: in std_logic;
    i_pstrb: in std_logic_vector(3 downto 0);
    i_pwdata: in std_logic_vector(31 downto 0);
    o_pready: out std_logic;
    o_prdata: out std_logic_vector(31 downto 0);
    o_pslverr: out std_logic;
    i_rbr: in std_logic_vector(7 downto 0);
    o_rbr_read_trigger: out std_logic_vector(0 downto 0);
    o_thr: out std_logic_vector(7 downto 0);
    o_thr_write_trigger: out std_logic_vector(0 downto 0);
    o_ier_erbfi: out std_logic_vector(0 downto 0);
    o_ier_etbei: out std_logic_vector(0 downto 0);
    o_ier_elsi: out std_logic_vector(0 downto 0);
    o_ier_edssi: out std_logic_vector(0 downto 0);
    i_iir_intpend: in std_logic_vector(0 downto 0);
    i_iir_intid2: in std_logic_vector(2 downto 0);
    o_fcr_fifoen: out std_logic_vector(0 downto 0);
    o_fcr_rcvr_fifo_reset_trigger: out std_logic_vector(0 downto 0);
    o_fcr_xmit_fifo_reset_trigger: out std_logic_vector(0 downto 0);
    o_fcr_dma_mode_select: out std_logic_vector(0 downto 0);
    o_fcr_rcvr_fifo_trigger_level: out std_logic_vector(1 downto 0);
    o_lcr_wls: out std_logic_vector(1 downto 0);
    o_lcr_stb: out std_logic_vector(0 downto 0);
    o_lcr_pen: out std_logic_vector(0 downto 0);
    o_lcr_eps: out std_logic_vector(0 downto 0);
    o_lcr_stick_parity: out std_logic_vector(0 downto 0);
    o_lcr_set_break: out std_logic_vector(0 downto 0);
    o_lcr_dlab: out std_logic_vector(0 downto 0);
    o_mrc_dtr: out std_logic_vector(0 downto 0);
    o_mrc_rts: out std_logic_vector(0 downto 0);
    o_mrc_out1: out std_logic_vector(0 downto 0);
    o_mrc_out2: out std_logic_vector(0 downto 0);
    o_mrc_loop: out std_logic_vector(0 downto 0);
    i_lsr_dr: in std_logic_vector(0 downto 0);
    i_lsr_oe: in std_logic_vector(0 downto 0);
    o_lsr_oe_read_trigger: out std_logic_vector(0 downto 0);
    i_lsr_pe: in std_logic_vector(0 downto 0);
    o_lsr_pe_read_trigger: out std_logic_vector(0 downto 0);
    i_lsr_fe: in std_logic_vector(0 downto 0);
    o_lsr_fe_read_trigger: out std_logic_vector(0 downto 0);
    i_lsr_bi: in std_logic_vector(0 downto 0);
    o_lsr_bi_read_trigger: out std_logic_vector(0 downto 0);
    i_lsr_thre: in std_logic_vector(0 downto 0);
    i_lsr_temt: in std_logic_vector(0 downto 0);
    i_lsr_error_in_rcvr_fifo: in std_logic_vector(0 downto 0);
    i_msr_dcts: in std_logic_vector(0 downto 0);
    o_msr_dcts_read_trigger: out std_logic_vector(0 downto 0);
    i_msr_ddsr: in std_logic_vector(0 downto 0);
    o_msr_ddsr_read_trigger: out std_logic_vector(0 downto 0);
    i_msr_teri: in std_logic_vector(0 downto 0);
    i_msr_ddcd: in std_logic_vector(0 downto 0);
    o_msr_ddcd_read_trigger: out std_logic_vector(0 downto 0);
    i_msr_cts: in std_logic_vector(0 downto 0);
    i_msr_dsr: in std_logic_vector(0 downto 0);
    i_msr_ri: in std_logic_vector(0 downto 0);
    i_msr_dcd: in std_logic_vector(0 downto 0);
    o_scratch: out std_logic_vector(7 downto 0);
    o_dll: out std_logic_vector(7 downto 0);
    o_dlm: out std_logic_vector(7 downto 0)
  );
end uart_csr;

architecture rtl of uart_csr is
  signal register_valid: std_logic;
  signal register_access: std_logic_vector(1 downto 0);
  signal register_address: std_logic_vector(4 downto 0);
  signal register_write_data: std_logic_vector(31 downto 0);
  signal register_strobe: std_logic_vector(3 downto 0);
  signal register_active: std_logic_vector(11 downto 0);
  signal register_ready: std_logic_vector(11 downto 0);
  signal register_status: std_logic_vector(23 downto 0);
  signal register_read_data: std_logic_vector(383 downto 0);
  signal register_value: std_logic_vector(383 downto 0);
begin
  u_adapter: entity work.rggen_apb_adaper
    generic map (
      ADDRESS_WIDTH       => ADDRESS_WIDTH,
      LOCAL_ADDRESS_WIDTH => 5,
      BUS_WIDTH           => 32,
      REGISTERS           => 12,
      PRE_DECODE          => PRE_DECODE,
      BASE_ADDRESS        => BASE_ADDRESS,
      BYTE_SIZE           => 32,
      ERROR_STATUS        => ERROR_STATUS,
      INSERT_SLICER       => INSERT_SLICER
    )
    port map (
      i_clk                 => i_clk,
      i_rst_n               => i_rst_n,
      i_psel                => i_psel,
      i_penable             => i_penable,
      i_paddr               => i_paddr,
      i_pprot               => i_pprot,
      i_pwrite              => i_pwrite,
      i_pstrb               => i_pstrb,
      i_pwdata              => i_pwdata,
      o_pready              => o_pready,
      o_prdata              => o_prdata,
      o_pslverr             => o_pslverr,
      o_register_valid      => register_valid,
      o_register_access     => register_access,
      o_register_address    => register_address,
      o_register_write_data => register_write_data,
      o_register_strobe     => register_strobe,
      i_register_active     => register_active,
      i_register_ready      => register_ready,
      i_register_status     => register_status,
      i_register_read_data  => register_read_data
    );
  g_rbr: block
    signal bit_field_valid: std_logic;
    signal bit_field_read_mask: std_logic_vector(31 downto 0);
    signal bit_field_write_mask: std_logic_vector(31 downto 0);
    signal bit_field_write_data: std_logic_vector(31 downto 0);
    signal bit_field_read_data: std_logic_vector(31 downto 0);
    signal bit_field_value: std_logic_vector(31 downto 0);
    signal indirect_match: std_logic_vector(0 downto 0);
  begin
    \g_tie_off\: for \__i\ in 0 to 31 generate
      g: if (bit_slice(x"000000ff", \__i\) = '0') generate
        bit_field_read_data(\__i\) <= '0';
        bit_field_value(\__i\) <= '0';
      end generate;
    end generate;
    indirect_match(0) <= '1' when unsigned(register_value(167 downto 167)) = 0 else '0';
    u_register: entity work.rggen_indirect_register
      generic map (
        READABLE              => true,
        WRITABLE              => false,
        ADDRESS_WIDTH         => 5,
        OFFSET_ADDRESS        => x"00",
        BUS_WIDTH             => 32,
        DATA_WIDTH            => 32,
        INDIRECT_MATCH_WIDTH  => 1
      )
      port map (
        i_clk                   => i_clk,
        i_rst_n                 => i_rst_n,
        i_register_valid        => register_valid,
        i_register_access       => register_access,
        i_register_address      => register_address,
        i_register_write_data   => register_write_data,
        i_register_strobe       => register_strobe,
        o_register_active       => register_active(0),
        o_register_ready        => register_ready(0),
        o_register_status       => register_status(1 downto 0),
        o_register_read_data    => register_read_data(31 downto 0),
        o_register_value        => register_value(31 downto 0),
        i_indirect_match        => indirect_match,
        o_bit_field_valid       => bit_field_valid,
        o_bit_field_read_mask   => bit_field_read_mask,
        o_bit_field_write_mask  => bit_field_write_mask,
        o_bit_field_write_data  => bit_field_write_data,
        i_bit_field_read_data   => bit_field_read_data,
        i_bit_field_value       => bit_field_value
      );
    g_rbr: block
    begin
      u_bit_field: entity work.rggen_bit_field
        generic map (
          WIDTH               => 8,
          STORAGE             => false,
          EXTERNAL_READ_DATA  => true,
          TRIGGER             => true
        )
        port map (
          i_clk             => i_clk,
          i_rst_n           => i_rst_n,
          i_sw_valid        => bit_field_valid,
          i_sw_read_mask    => bit_field_read_mask(7 downto 0),
          i_sw_write_enable => "0",
          i_sw_write_mask   => bit_field_write_mask(7 downto 0),
          i_sw_write_data   => bit_field_write_data(7 downto 0),
          o_sw_read_data    => bit_field_read_data(7 downto 0),
          o_sw_value        => bit_field_value(7 downto 0),
          o_write_trigger   => open,
          o_read_trigger    => o_rbr_read_trigger,
          i_hw_write_enable => "0",
          i_hw_write_data   => (others => '0'),
          i_hw_set          => (others => '0'),
          i_hw_clear        => (others => '0'),
          i_value           => i_rbr,
          i_mask            => (others => '1'),
          o_value           => open,
          o_value_unmasked  => open
        );
    end block;
  end block;
  g_thr: block
    signal bit_field_valid: std_logic;
    signal bit_field_read_mask: std_logic_vector(31 downto 0);
    signal bit_field_write_mask: std_logic_vector(31 downto 0);
    signal bit_field_write_data: std_logic_vector(31 downto 0);
    signal bit_field_read_data: std_logic_vector(31 downto 0);
    signal bit_field_value: std_logic_vector(31 downto 0);
    signal indirect_match: std_logic_vector(0 downto 0);
  begin
    \g_tie_off\: for \__i\ in 0 to 31 generate
      g: if (bit_slice(x"000000ff", \__i\) = '0') generate
        bit_field_read_data(\__i\) <= '0';
        bit_field_value(\__i\) <= '0';
      end generate;
    end generate;
    indirect_match(0) <= '1' when unsigned(register_value(167 downto 167)) = 0 else '0';
    u_register: entity work.rggen_indirect_register
      generic map (
        READABLE              => false,
        WRITABLE              => true,
        ADDRESS_WIDTH         => 5,
        OFFSET_ADDRESS        => x"00",
        BUS_WIDTH             => 32,
        DATA_WIDTH            => 32,
        INDIRECT_MATCH_WIDTH  => 1
      )
      port map (
        i_clk                   => i_clk,
        i_rst_n                 => i_rst_n,
        i_register_valid        => register_valid,
        i_register_access       => register_access,
        i_register_address      => register_address,
        i_register_write_data   => register_write_data,
        i_register_strobe       => register_strobe,
        o_register_active       => register_active(1),
        o_register_ready        => register_ready(1),
        o_register_status       => register_status(3 downto 2),
        o_register_read_data    => register_read_data(63 downto 32),
        o_register_value        => register_value(63 downto 32),
        i_indirect_match        => indirect_match,
        o_bit_field_valid       => bit_field_valid,
        o_bit_field_read_mask   => bit_field_read_mask,
        o_bit_field_write_mask  => bit_field_write_mask,
        o_bit_field_write_data  => bit_field_write_data,
        i_bit_field_read_data   => bit_field_read_data,
        i_bit_field_value       => bit_field_value
      );
    g_thr: block
    begin
      u_bit_field: entity work.rggen_bit_field
        generic map (
          WIDTH           => 8,
          INITIAL_VALUE   => slice(x"ff", 8, 0),
          SW_READ_ACTION  => RGGEN_READ_NONE,
          SW_WRITE_ONCE   => false,
          TRIGGER         => true
        )
        port map (
          i_clk             => i_clk,
          i_rst_n           => i_rst_n,
          i_sw_valid        => bit_field_valid,
          i_sw_read_mask    => bit_field_read_mask(7 downto 0),
          i_sw_write_enable => "1",
          i_sw_write_mask   => bit_field_write_mask(7 downto 0),
          i_sw_write_data   => bit_field_write_data(7 downto 0),
          o_sw_read_data    => bit_field_read_data(7 downto 0),
          o_sw_value        => bit_field_value(7 downto 0),
          o_write_trigger   => o_thr_write_trigger,
          o_read_trigger    => open,
          i_hw_write_enable => "0",
          i_hw_write_data   => (others => '0'),
          i_hw_set          => (others => '0'),
          i_hw_clear        => (others => '0'),
          i_value           => (others => '0'),
          i_mask            => (others => '1'),
          o_value           => o_thr,
          o_value_unmasked  => open
        );
    end block;
  end block;
  g_ier: block
    signal bit_field_valid: std_logic;
    signal bit_field_read_mask: std_logic_vector(31 downto 0);
    signal bit_field_write_mask: std_logic_vector(31 downto 0);
    signal bit_field_write_data: std_logic_vector(31 downto 0);
    signal bit_field_read_data: std_logic_vector(31 downto 0);
    signal bit_field_value: std_logic_vector(31 downto 0);
    signal indirect_match: std_logic_vector(0 downto 0);
  begin
    \g_tie_off\: for \__i\ in 0 to 31 generate
      g: if (bit_slice(x"0000000f", \__i\) = '0') generate
        bit_field_read_data(\__i\) <= '0';
        bit_field_value(\__i\) <= '0';
      end generate;
    end generate;
    indirect_match(0) <= '1' when unsigned(register_value(167 downto 167)) = 0 else '0';
    u_register: entity work.rggen_indirect_register
      generic map (
        READABLE              => true,
        WRITABLE              => true,
        ADDRESS_WIDTH         => 5,
        OFFSET_ADDRESS        => x"04",
        BUS_WIDTH             => 32,
        DATA_WIDTH            => 32,
        INDIRECT_MATCH_WIDTH  => 1
      )
      port map (
        i_clk                   => i_clk,
        i_rst_n                 => i_rst_n,
        i_register_valid        => register_valid,
        i_register_access       => register_access,
        i_register_address      => register_address,
        i_register_write_data   => register_write_data,
        i_register_strobe       => register_strobe,
        o_register_active       => register_active(2),
        o_register_ready        => register_ready(2),
        o_register_status       => register_status(5 downto 4),
        o_register_read_data    => register_read_data(95 downto 64),
        o_register_value        => register_value(95 downto 64),
        i_indirect_match        => indirect_match,
        o_bit_field_valid       => bit_field_valid,
        o_bit_field_read_mask   => bit_field_read_mask,
        o_bit_field_write_mask  => bit_field_write_mask,
        o_bit_field_write_data  => bit_field_write_data,
        i_bit_field_read_data   => bit_field_read_data,
        i_bit_field_value       => bit_field_value
      );
    g_erbfi: block
    begin
      u_bit_field: entity work.rggen_bit_field
        generic map (
          WIDTH           => 1,
          INITIAL_VALUE   => slice(x"0", 1, 0),
          SW_WRITE_ONCE   => false,
          TRIGGER         => false
        )
        port map (
          i_clk             => i_clk,
          i_rst_n           => i_rst_n,
          i_sw_valid        => bit_field_valid,
          i_sw_read_mask    => bit_field_read_mask(0 downto 0),
          i_sw_write_enable => "1",
          i_sw_write_mask   => bit_field_write_mask(0 downto 0),
          i_sw_write_data   => bit_field_write_data(0 downto 0),
          o_sw_read_data    => bit_field_read_data(0 downto 0),
          o_sw_value        => bit_field_value(0 downto 0),
          o_write_trigger   => open,
          o_read_trigger    => open,
          i_hw_write_enable => "0",
          i_hw_write_data   => (others => '0'),
          i_hw_set          => (others => '0'),
          i_hw_clear        => (others => '0'),
          i_value           => (others => '0'),
          i_mask            => (others => '1'),
          o_value           => o_ier_erbfi,
          o_value_unmasked  => open
        );
    end block;
    g_etbei: block
    begin
      u_bit_field: entity work.rggen_bit_field
        generic map (
          WIDTH           => 1,
          INITIAL_VALUE   => slice(x"0", 1, 0),
          SW_WRITE_ONCE   => false,
          TRIGGER         => false
        )
        port map (
          i_clk             => i_clk,
          i_rst_n           => i_rst_n,
          i_sw_valid        => bit_field_valid,
          i_sw_read_mask    => bit_field_read_mask(1 downto 1),
          i_sw_write_enable => "1",
          i_sw_write_mask   => bit_field_write_mask(1 downto 1),
          i_sw_write_data   => bit_field_write_data(1 downto 1),
          o_sw_read_data    => bit_field_read_data(1 downto 1),
          o_sw_value        => bit_field_value(1 downto 1),
          o_write_trigger   => open,
          o_read_trigger    => open,
          i_hw_write_enable => "0",
          i_hw_write_data   => (others => '0'),
          i_hw_set          => (others => '0'),
          i_hw_clear        => (others => '0'),
          i_value           => (others => '0'),
          i_mask            => (others => '1'),
          o_value           => o_ier_etbei,
          o_value_unmasked  => open
        );
    end block;
    g_elsi: block
    begin
      u_bit_field: entity work.rggen_bit_field
        generic map (
          WIDTH           => 1,
          INITIAL_VALUE   => slice(x"0", 1, 0),
          SW_WRITE_ONCE   => false,
          TRIGGER         => false
        )
        port map (
          i_clk             => i_clk,
          i_rst_n           => i_rst_n,
          i_sw_valid        => bit_field_valid,
          i_sw_read_mask    => bit_field_read_mask(2 downto 2),
          i_sw_write_enable => "1",
          i_sw_write_mask   => bit_field_write_mask(2 downto 2),
          i_sw_write_data   => bit_field_write_data(2 downto 2),
          o_sw_read_data    => bit_field_read_data(2 downto 2),
          o_sw_value        => bit_field_value(2 downto 2),
          o_write_trigger   => open,
          o_read_trigger    => open,
          i_hw_write_enable => "0",
          i_hw_write_data   => (others => '0'),
          i_hw_set          => (others => '0'),
          i_hw_clear        => (others => '0'),
          i_value           => (others => '0'),
          i_mask            => (others => '1'),
          o_value           => o_ier_elsi,
          o_value_unmasked  => open
        );
    end block;
    g_edssi: block
    begin
      u_bit_field: entity work.rggen_bit_field
        generic map (
          WIDTH           => 1,
          INITIAL_VALUE   => slice(x"0", 1, 0),
          SW_WRITE_ONCE   => false,
          TRIGGER         => false
        )
        port map (
          i_clk             => i_clk,
          i_rst_n           => i_rst_n,
          i_sw_valid        => bit_field_valid,
          i_sw_read_mask    => bit_field_read_mask(3 downto 3),
          i_sw_write_enable => "1",
          i_sw_write_mask   => bit_field_write_mask(3 downto 3),
          i_sw_write_data   => bit_field_write_data(3 downto 3),
          o_sw_read_data    => bit_field_read_data(3 downto 3),
          o_sw_value        => bit_field_value(3 downto 3),
          o_write_trigger   => open,
          o_read_trigger    => open,
          i_hw_write_enable => "0",
          i_hw_write_data   => (others => '0'),
          i_hw_set          => (others => '0'),
          i_hw_clear        => (others => '0'),
          i_value           => (others => '0'),
          i_mask            => (others => '1'),
          o_value           => o_ier_edssi,
          o_value_unmasked  => open
        );
    end block;
  end block;
  g_iir: block
    signal bit_field_valid: std_logic;
    signal bit_field_read_mask: std_logic_vector(31 downto 0);
    signal bit_field_write_mask: std_logic_vector(31 downto 0);
    signal bit_field_write_data: std_logic_vector(31 downto 0);
    signal bit_field_read_data: std_logic_vector(31 downto 0);
    signal bit_field_value: std_logic_vector(31 downto 0);
  begin
    \g_tie_off\: for \__i\ in 0 to 31 generate
      g: if (bit_slice(x"0000000f", \__i\) = '0') generate
        bit_field_read_data(\__i\) <= '0';
        bit_field_value(\__i\) <= '0';
      end generate;
    end generate;
    u_register: entity work.rggen_default_register
      generic map (
        READABLE        => true,
        WRITABLE        => false,
        ADDRESS_WIDTH   => 5,
        OFFSET_ADDRESS  => x"08",
        BUS_WIDTH       => 32,
        DATA_WIDTH      => 32
      )
      port map (
        i_clk                   => i_clk,
        i_rst_n                 => i_rst_n,
        i_register_valid        => register_valid,
        i_register_access       => register_access,
        i_register_address      => register_address,
        i_register_write_data   => register_write_data,
        i_register_strobe       => register_strobe,
        o_register_active       => register_active(3),
        o_register_ready        => register_ready(3),
        o_register_status       => register_status(7 downto 6),
        o_register_read_data    => register_read_data(127 downto 96),
        o_register_value        => register_value(127 downto 96),
        o_bit_field_valid       => bit_field_valid,
        o_bit_field_read_mask   => bit_field_read_mask,
        o_bit_field_write_mask  => bit_field_write_mask,
        o_bit_field_write_data  => bit_field_write_data,
        i_bit_field_read_data   => bit_field_read_data,
        i_bit_field_value       => bit_field_value
      );
    g_intpend: block
    begin
      u_bit_field: entity work.rggen_bit_field
        generic map (
          WIDTH               => 1,
          STORAGE             => false,
          EXTERNAL_READ_DATA  => true,
          TRIGGER             => false
        )
        port map (
          i_clk             => i_clk,
          i_rst_n           => i_rst_n,
          i_sw_valid        => bit_field_valid,
          i_sw_read_mask    => bit_field_read_mask(0 downto 0),
          i_sw_write_enable => "0",
          i_sw_write_mask   => bit_field_write_mask(0 downto 0),
          i_sw_write_data   => bit_field_write_data(0 downto 0),
          o_sw_read_data    => bit_field_read_data(0 downto 0),
          o_sw_value        => bit_field_value(0 downto 0),
          o_write_trigger   => open,
          o_read_trigger    => open,
          i_hw_write_enable => "0",
          i_hw_write_data   => (others => '0'),
          i_hw_set          => (others => '0'),
          i_hw_clear        => (others => '0'),
          i_value           => i_iir_intpend,
          i_mask            => (others => '1'),
          o_value           => open,
          o_value_unmasked  => open
        );
    end block;
    g_intid2: block
    begin
      u_bit_field: entity work.rggen_bit_field
        generic map (
          WIDTH               => 3,
          STORAGE             => false,
          EXTERNAL_READ_DATA  => true,
          TRIGGER             => false
        )
        port map (
          i_clk             => i_clk,
          i_rst_n           => i_rst_n,
          i_sw_valid        => bit_field_valid,
          i_sw_read_mask    => bit_field_read_mask(3 downto 1),
          i_sw_write_enable => "0",
          i_sw_write_mask   => bit_field_write_mask(3 downto 1),
          i_sw_write_data   => bit_field_write_data(3 downto 1),
          o_sw_read_data    => bit_field_read_data(3 downto 1),
          o_sw_value        => bit_field_value(3 downto 1),
          o_write_trigger   => open,
          o_read_trigger    => open,
          i_hw_write_enable => "0",
          i_hw_write_data   => (others => '0'),
          i_hw_set          => (others => '0'),
          i_hw_clear        => (others => '0'),
          i_value           => i_iir_intid2,
          i_mask            => (others => '1'),
          o_value           => open,
          o_value_unmasked  => open
        );
    end block;
  end block;
  g_fcr: block
    signal bit_field_valid: std_logic;
    signal bit_field_read_mask: std_logic_vector(31 downto 0);
    signal bit_field_write_mask: std_logic_vector(31 downto 0);
    signal bit_field_write_data: std_logic_vector(31 downto 0);
    signal bit_field_read_data: std_logic_vector(31 downto 0);
    signal bit_field_value: std_logic_vector(31 downto 0);
  begin
    \g_tie_off\: for \__i\ in 0 to 31 generate
      g: if (bit_slice(x"000000cf", \__i\) = '0') generate
        bit_field_read_data(\__i\) <= '0';
        bit_field_value(\__i\) <= '0';
      end generate;
    end generate;
    u_register: entity work.rggen_default_register
      generic map (
        READABLE        => false,
        WRITABLE        => true,
        ADDRESS_WIDTH   => 5,
        OFFSET_ADDRESS  => x"08",
        BUS_WIDTH       => 32,
        DATA_WIDTH      => 32
      )
      port map (
        i_clk                   => i_clk,
        i_rst_n                 => i_rst_n,
        i_register_valid        => register_valid,
        i_register_access       => register_access,
        i_register_address      => register_address,
        i_register_write_data   => register_write_data,
        i_register_strobe       => register_strobe,
        o_register_active       => register_active(4),
        o_register_ready        => register_ready(4),
        o_register_status       => register_status(9 downto 8),
        o_register_read_data    => register_read_data(159 downto 128),
        o_register_value        => register_value(159 downto 128),
        o_bit_field_valid       => bit_field_valid,
        o_bit_field_read_mask   => bit_field_read_mask,
        o_bit_field_write_mask  => bit_field_write_mask,
        o_bit_field_write_data  => bit_field_write_data,
        i_bit_field_read_data   => bit_field_read_data,
        i_bit_field_value       => bit_field_value
      );
    g_fifoen: block
    begin
      u_bit_field: entity work.rggen_bit_field
        generic map (
          WIDTH           => 1,
          INITIAL_VALUE   => slice(x"0", 1, 0),
          SW_READ_ACTION  => RGGEN_READ_NONE,
          SW_WRITE_ONCE   => false,
          TRIGGER         => false
        )
        port map (
          i_clk             => i_clk,
          i_rst_n           => i_rst_n,
          i_sw_valid        => bit_field_valid,
          i_sw_read_mask    => bit_field_read_mask(0 downto 0),
          i_sw_write_enable => "1",
          i_sw_write_mask   => bit_field_write_mask(0 downto 0),
          i_sw_write_data   => bit_field_write_data(0 downto 0),
          o_sw_read_data    => bit_field_read_data(0 downto 0),
          o_sw_value        => bit_field_value(0 downto 0),
          o_write_trigger   => open,
          o_read_trigger    => open,
          i_hw_write_enable => "0",
          i_hw_write_data   => (others => '0'),
          i_hw_set          => (others => '0'),
          i_hw_clear        => (others => '0'),
          i_value           => (others => '0'),
          i_mask            => (others => '1'),
          o_value           => o_fcr_fifoen,
          o_value_unmasked  => open
        );
    end block;
    g_rcvr_fifo_reset: block
    begin
      u_bit_field: entity work.rggen_bit_field_w01trg
        generic map (
          WRITE_ONE_TRIGGER => true,
          WIDTH             => 1
        )
        port map (
          i_clk             => i_clk,
          i_rst_n           => i_rst_n,
          i_sw_valid        => bit_field_valid,
          i_sw_read_mask    => bit_field_read_mask(1 downto 1),
          i_sw_write_enable => "1",
          i_sw_write_mask   => bit_field_write_mask(1 downto 1),
          i_sw_write_data   => bit_field_write_data(1 downto 1),
          o_sw_read_data    => bit_field_read_data(1 downto 1),
          o_sw_value        => bit_field_value(1 downto 1),
          i_value           => (others => '0'),
          o_trigger         => o_fcr_rcvr_fifo_reset_trigger
        );
    end block;
    g_xmit_fifo_reset: block
    begin
      u_bit_field: entity work.rggen_bit_field_w01trg
        generic map (
          WRITE_ONE_TRIGGER => true,
          WIDTH             => 1
        )
        port map (
          i_clk             => i_clk,
          i_rst_n           => i_rst_n,
          i_sw_valid        => bit_field_valid,
          i_sw_read_mask    => bit_field_read_mask(2 downto 2),
          i_sw_write_enable => "1",
          i_sw_write_mask   => bit_field_write_mask(2 downto 2),
          i_sw_write_data   => bit_field_write_data(2 downto 2),
          o_sw_read_data    => bit_field_read_data(2 downto 2),
          o_sw_value        => bit_field_value(2 downto 2),
          i_value           => (others => '0'),
          o_trigger         => o_fcr_xmit_fifo_reset_trigger
        );
    end block;
    g_dma_mode_select: block
    begin
      u_bit_field: entity work.rggen_bit_field
        generic map (
          WIDTH           => 1,
          INITIAL_VALUE   => slice(x"0", 1, 0),
          SW_READ_ACTION  => RGGEN_READ_NONE,
          SW_WRITE_ONCE   => false,
          TRIGGER         => false
        )
        port map (
          i_clk             => i_clk,
          i_rst_n           => i_rst_n,
          i_sw_valid        => bit_field_valid,
          i_sw_read_mask    => bit_field_read_mask(3 downto 3),
          i_sw_write_enable => "1",
          i_sw_write_mask   => bit_field_write_mask(3 downto 3),
          i_sw_write_data   => bit_field_write_data(3 downto 3),
          o_sw_read_data    => bit_field_read_data(3 downto 3),
          o_sw_value        => bit_field_value(3 downto 3),
          o_write_trigger   => open,
          o_read_trigger    => open,
          i_hw_write_enable => "0",
          i_hw_write_data   => (others => '0'),
          i_hw_set          => (others => '0'),
          i_hw_clear        => (others => '0'),
          i_value           => (others => '0'),
          i_mask            => (others => '1'),
          o_value           => o_fcr_dma_mode_select,
          o_value_unmasked  => open
        );
    end block;
    g_rcvr_fifo_trigger_level: block
    begin
      u_bit_field: entity work.rggen_bit_field
        generic map (
          WIDTH           => 2,
          INITIAL_VALUE   => slice(x"0", 2, 0),
          SW_READ_ACTION  => RGGEN_READ_NONE,
          SW_WRITE_ONCE   => false,
          TRIGGER         => false
        )
        port map (
          i_clk             => i_clk,
          i_rst_n           => i_rst_n,
          i_sw_valid        => bit_field_valid,
          i_sw_read_mask    => bit_field_read_mask(7 downto 6),
          i_sw_write_enable => "1",
          i_sw_write_mask   => bit_field_write_mask(7 downto 6),
          i_sw_write_data   => bit_field_write_data(7 downto 6),
          o_sw_read_data    => bit_field_read_data(7 downto 6),
          o_sw_value        => bit_field_value(7 downto 6),
          o_write_trigger   => open,
          o_read_trigger    => open,
          i_hw_write_enable => "0",
          i_hw_write_data   => (others => '0'),
          i_hw_set          => (others => '0'),
          i_hw_clear        => (others => '0'),
          i_value           => (others => '0'),
          i_mask            => (others => '1'),
          o_value           => o_fcr_rcvr_fifo_trigger_level,
          o_value_unmasked  => open
        );
    end block;
  end block;
  g_lcr: block
    signal bit_field_valid: std_logic;
    signal bit_field_read_mask: std_logic_vector(31 downto 0);
    signal bit_field_write_mask: std_logic_vector(31 downto 0);
    signal bit_field_write_data: std_logic_vector(31 downto 0);
    signal bit_field_read_data: std_logic_vector(31 downto 0);
    signal bit_field_value: std_logic_vector(31 downto 0);
  begin
    \g_tie_off\: for \__i\ in 0 to 31 generate
      g: if (bit_slice(x"000000ff", \__i\) = '0') generate
        bit_field_read_data(\__i\) <= '0';
        bit_field_value(\__i\) <= '0';
      end generate;
    end generate;
    u_register: entity work.rggen_default_register
      generic map (
        READABLE        => true,
        WRITABLE        => true,
        ADDRESS_WIDTH   => 5,
        OFFSET_ADDRESS  => x"0c",
        BUS_WIDTH       => 32,
        DATA_WIDTH      => 32
      )
      port map (
        i_clk                   => i_clk,
        i_rst_n                 => i_rst_n,
        i_register_valid        => register_valid,
        i_register_access       => register_access,
        i_register_address      => register_address,
        i_register_write_data   => register_write_data,
        i_register_strobe       => register_strobe,
        o_register_active       => register_active(5),
        o_register_ready        => register_ready(5),
        o_register_status       => register_status(11 downto 10),
        o_register_read_data    => register_read_data(191 downto 160),
        o_register_value        => register_value(191 downto 160),
        o_bit_field_valid       => bit_field_valid,
        o_bit_field_read_mask   => bit_field_read_mask,
        o_bit_field_write_mask  => bit_field_write_mask,
        o_bit_field_write_data  => bit_field_write_data,
        i_bit_field_read_data   => bit_field_read_data,
        i_bit_field_value       => bit_field_value
      );
    g_wls: block
    begin
      u_bit_field: entity work.rggen_bit_field
        generic map (
          WIDTH           => 2,
          INITIAL_VALUE   => slice(x"3", 2, 0),
          SW_WRITE_ONCE   => false,
          TRIGGER         => false
        )
        port map (
          i_clk             => i_clk,
          i_rst_n           => i_rst_n,
          i_sw_valid        => bit_field_valid,
          i_sw_read_mask    => bit_field_read_mask(1 downto 0),
          i_sw_write_enable => "1",
          i_sw_write_mask   => bit_field_write_mask(1 downto 0),
          i_sw_write_data   => bit_field_write_data(1 downto 0),
          o_sw_read_data    => bit_field_read_data(1 downto 0),
          o_sw_value        => bit_field_value(1 downto 0),
          o_write_trigger   => open,
          o_read_trigger    => open,
          i_hw_write_enable => "0",
          i_hw_write_data   => (others => '0'),
          i_hw_set          => (others => '0'),
          i_hw_clear        => (others => '0'),
          i_value           => (others => '0'),
          i_mask            => (others => '1'),
          o_value           => o_lcr_wls,
          o_value_unmasked  => open
        );
    end block;
    g_stb: block
    begin
      u_bit_field: entity work.rggen_bit_field
        generic map (
          WIDTH           => 1,
          INITIAL_VALUE   => slice(x"0", 1, 0),
          SW_WRITE_ONCE   => false,
          TRIGGER         => false
        )
        port map (
          i_clk             => i_clk,
          i_rst_n           => i_rst_n,
          i_sw_valid        => bit_field_valid,
          i_sw_read_mask    => bit_field_read_mask(2 downto 2),
          i_sw_write_enable => "1",
          i_sw_write_mask   => bit_field_write_mask(2 downto 2),
          i_sw_write_data   => bit_field_write_data(2 downto 2),
          o_sw_read_data    => bit_field_read_data(2 downto 2),
          o_sw_value        => bit_field_value(2 downto 2),
          o_write_trigger   => open,
          o_read_trigger    => open,
          i_hw_write_enable => "0",
          i_hw_write_data   => (others => '0'),
          i_hw_set          => (others => '0'),
          i_hw_clear        => (others => '0'),
          i_value           => (others => '0'),
          i_mask            => (others => '1'),
          o_value           => o_lcr_stb,
          o_value_unmasked  => open
        );
    end block;
    g_pen: block
    begin
      u_bit_field: entity work.rggen_bit_field
        generic map (
          WIDTH           => 1,
          INITIAL_VALUE   => slice(x"0", 1, 0),
          SW_WRITE_ONCE   => false,
          TRIGGER         => false
        )
        port map (
          i_clk             => i_clk,
          i_rst_n           => i_rst_n,
          i_sw_valid        => bit_field_valid,
          i_sw_read_mask    => bit_field_read_mask(3 downto 3),
          i_sw_write_enable => "1",
          i_sw_write_mask   => bit_field_write_mask(3 downto 3),
          i_sw_write_data   => bit_field_write_data(3 downto 3),
          o_sw_read_data    => bit_field_read_data(3 downto 3),
          o_sw_value        => bit_field_value(3 downto 3),
          o_write_trigger   => open,
          o_read_trigger    => open,
          i_hw_write_enable => "0",
          i_hw_write_data   => (others => '0'),
          i_hw_set          => (others => '0'),
          i_hw_clear        => (others => '0'),
          i_value           => (others => '0'),
          i_mask            => (others => '1'),
          o_value           => o_lcr_pen,
          o_value_unmasked  => open
        );
    end block;
    g_eps: block
    begin
      u_bit_field: entity work.rggen_bit_field
        generic map (
          WIDTH           => 1,
          INITIAL_VALUE   => slice(x"0", 1, 0),
          SW_WRITE_ONCE   => false,
          TRIGGER         => false
        )
        port map (
          i_clk             => i_clk,
          i_rst_n           => i_rst_n,
          i_sw_valid        => bit_field_valid,
          i_sw_read_mask    => bit_field_read_mask(4 downto 4),
          i_sw_write_enable => "1",
          i_sw_write_mask   => bit_field_write_mask(4 downto 4),
          i_sw_write_data   => bit_field_write_data(4 downto 4),
          o_sw_read_data    => bit_field_read_data(4 downto 4),
          o_sw_value        => bit_field_value(4 downto 4),
          o_write_trigger   => open,
          o_read_trigger    => open,
          i_hw_write_enable => "0",
          i_hw_write_data   => (others => '0'),
          i_hw_set          => (others => '0'),
          i_hw_clear        => (others => '0'),
          i_value           => (others => '0'),
          i_mask            => (others => '1'),
          o_value           => o_lcr_eps,
          o_value_unmasked  => open
        );
    end block;
    g_stick_parity: block
    begin
      u_bit_field: entity work.rggen_bit_field
        generic map (
          WIDTH           => 1,
          INITIAL_VALUE   => slice(x"0", 1, 0),
          SW_WRITE_ONCE   => false,
          TRIGGER         => false
        )
        port map (
          i_clk             => i_clk,
          i_rst_n           => i_rst_n,
          i_sw_valid        => bit_field_valid,
          i_sw_read_mask    => bit_field_read_mask(5 downto 5),
          i_sw_write_enable => "1",
          i_sw_write_mask   => bit_field_write_mask(5 downto 5),
          i_sw_write_data   => bit_field_write_data(5 downto 5),
          o_sw_read_data    => bit_field_read_data(5 downto 5),
          o_sw_value        => bit_field_value(5 downto 5),
          o_write_trigger   => open,
          o_read_trigger    => open,
          i_hw_write_enable => "0",
          i_hw_write_data   => (others => '0'),
          i_hw_set          => (others => '0'),
          i_hw_clear        => (others => '0'),
          i_value           => (others => '0'),
          i_mask            => (others => '1'),
          o_value           => o_lcr_stick_parity,
          o_value_unmasked  => open
        );
    end block;
    g_set_break: block
    begin
      u_bit_field: entity work.rggen_bit_field
        generic map (
          WIDTH           => 1,
          INITIAL_VALUE   => slice(x"0", 1, 0),
          SW_WRITE_ONCE   => false,
          TRIGGER         => false
        )
        port map (
          i_clk             => i_clk,
          i_rst_n           => i_rst_n,
          i_sw_valid        => bit_field_valid,
          i_sw_read_mask    => bit_field_read_mask(6 downto 6),
          i_sw_write_enable => "1",
          i_sw_write_mask   => bit_field_write_mask(6 downto 6),
          i_sw_write_data   => bit_field_write_data(6 downto 6),
          o_sw_read_data    => bit_field_read_data(6 downto 6),
          o_sw_value        => bit_field_value(6 downto 6),
          o_write_trigger   => open,
          o_read_trigger    => open,
          i_hw_write_enable => "0",
          i_hw_write_data   => (others => '0'),
          i_hw_set          => (others => '0'),
          i_hw_clear        => (others => '0'),
          i_value           => (others => '0'),
          i_mask            => (others => '1'),
          o_value           => o_lcr_set_break,
          o_value_unmasked  => open
        );
    end block;
    g_dlab: block
    begin
      u_bit_field: entity work.rggen_bit_field
        generic map (
          WIDTH           => 1,
          INITIAL_VALUE   => slice(x"0", 1, 0),
          SW_WRITE_ONCE   => false,
          TRIGGER         => false
        )
        port map (
          i_clk             => i_clk,
          i_rst_n           => i_rst_n,
          i_sw_valid        => bit_field_valid,
          i_sw_read_mask    => bit_field_read_mask(7 downto 7),
          i_sw_write_enable => "1",
          i_sw_write_mask   => bit_field_write_mask(7 downto 7),
          i_sw_write_data   => bit_field_write_data(7 downto 7),
          o_sw_read_data    => bit_field_read_data(7 downto 7),
          o_sw_value        => bit_field_value(7 downto 7),
          o_write_trigger   => open,
          o_read_trigger    => open,
          i_hw_write_enable => "0",
          i_hw_write_data   => (others => '0'),
          i_hw_set          => (others => '0'),
          i_hw_clear        => (others => '0'),
          i_value           => (others => '0'),
          i_mask            => (others => '1'),
          o_value           => o_lcr_dlab,
          o_value_unmasked  => open
        );
    end block;
  end block;
  g_mrc: block
    signal bit_field_valid: std_logic;
    signal bit_field_read_mask: std_logic_vector(31 downto 0);
    signal bit_field_write_mask: std_logic_vector(31 downto 0);
    signal bit_field_write_data: std_logic_vector(31 downto 0);
    signal bit_field_read_data: std_logic_vector(31 downto 0);
    signal bit_field_value: std_logic_vector(31 downto 0);
  begin
    \g_tie_off\: for \__i\ in 0 to 31 generate
      g: if (bit_slice(x"0000001f", \__i\) = '0') generate
        bit_field_read_data(\__i\) <= '0';
        bit_field_value(\__i\) <= '0';
      end generate;
    end generate;
    u_register: entity work.rggen_default_register
      generic map (
        READABLE        => true,
        WRITABLE        => true,
        ADDRESS_WIDTH   => 5,
        OFFSET_ADDRESS  => x"10",
        BUS_WIDTH       => 32,
        DATA_WIDTH      => 32
      )
      port map (
        i_clk                   => i_clk,
        i_rst_n                 => i_rst_n,
        i_register_valid        => register_valid,
        i_register_access       => register_access,
        i_register_address      => register_address,
        i_register_write_data   => register_write_data,
        i_register_strobe       => register_strobe,
        o_register_active       => register_active(6),
        o_register_ready        => register_ready(6),
        o_register_status       => register_status(13 downto 12),
        o_register_read_data    => register_read_data(223 downto 192),
        o_register_value        => register_value(223 downto 192),
        o_bit_field_valid       => bit_field_valid,
        o_bit_field_read_mask   => bit_field_read_mask,
        o_bit_field_write_mask  => bit_field_write_mask,
        o_bit_field_write_data  => bit_field_write_data,
        i_bit_field_read_data   => bit_field_read_data,
        i_bit_field_value       => bit_field_value
      );
    g_dtr: block
    begin
      u_bit_field: entity work.rggen_bit_field
        generic map (
          WIDTH           => 1,
          INITIAL_VALUE   => slice(x"0", 1, 0),
          SW_WRITE_ONCE   => false,
          TRIGGER         => false
        )
        port map (
          i_clk             => i_clk,
          i_rst_n           => i_rst_n,
          i_sw_valid        => bit_field_valid,
          i_sw_read_mask    => bit_field_read_mask(0 downto 0),
          i_sw_write_enable => "1",
          i_sw_write_mask   => bit_field_write_mask(0 downto 0),
          i_sw_write_data   => bit_field_write_data(0 downto 0),
          o_sw_read_data    => bit_field_read_data(0 downto 0),
          o_sw_value        => bit_field_value(0 downto 0),
          o_write_trigger   => open,
          o_read_trigger    => open,
          i_hw_write_enable => "0",
          i_hw_write_data   => (others => '0'),
          i_hw_set          => (others => '0'),
          i_hw_clear        => (others => '0'),
          i_value           => (others => '0'),
          i_mask            => (others => '1'),
          o_value           => o_mrc_dtr,
          o_value_unmasked  => open
        );
    end block;
    g_rts: block
    begin
      u_bit_field: entity work.rggen_bit_field
        generic map (
          WIDTH           => 1,
          INITIAL_VALUE   => slice(x"0", 1, 0),
          SW_WRITE_ONCE   => false,
          TRIGGER         => false
        )
        port map (
          i_clk             => i_clk,
          i_rst_n           => i_rst_n,
          i_sw_valid        => bit_field_valid,
          i_sw_read_mask    => bit_field_read_mask(1 downto 1),
          i_sw_write_enable => "1",
          i_sw_write_mask   => bit_field_write_mask(1 downto 1),
          i_sw_write_data   => bit_field_write_data(1 downto 1),
          o_sw_read_data    => bit_field_read_data(1 downto 1),
          o_sw_value        => bit_field_value(1 downto 1),
          o_write_trigger   => open,
          o_read_trigger    => open,
          i_hw_write_enable => "0",
          i_hw_write_data   => (others => '0'),
          i_hw_set          => (others => '0'),
          i_hw_clear        => (others => '0'),
          i_value           => (others => '0'),
          i_mask            => (others => '1'),
          o_value           => o_mrc_rts,
          o_value_unmasked  => open
        );
    end block;
    g_out1: block
    begin
      u_bit_field: entity work.rggen_bit_field
        generic map (
          WIDTH           => 1,
          INITIAL_VALUE   => slice(x"0", 1, 0),
          SW_WRITE_ONCE   => false,
          TRIGGER         => false
        )
        port map (
          i_clk             => i_clk,
          i_rst_n           => i_rst_n,
          i_sw_valid        => bit_field_valid,
          i_sw_read_mask    => bit_field_read_mask(2 downto 2),
          i_sw_write_enable => "1",
          i_sw_write_mask   => bit_field_write_mask(2 downto 2),
          i_sw_write_data   => bit_field_write_data(2 downto 2),
          o_sw_read_data    => bit_field_read_data(2 downto 2),
          o_sw_value        => bit_field_value(2 downto 2),
          o_write_trigger   => open,
          o_read_trigger    => open,
          i_hw_write_enable => "0",
          i_hw_write_data   => (others => '0'),
          i_hw_set          => (others => '0'),
          i_hw_clear        => (others => '0'),
          i_value           => (others => '0'),
          i_mask            => (others => '1'),
          o_value           => o_mrc_out1,
          o_value_unmasked  => open
        );
    end block;
    g_out2: block
    begin
      u_bit_field: entity work.rggen_bit_field
        generic map (
          WIDTH           => 1,
          INITIAL_VALUE   => slice(x"0", 1, 0),
          SW_WRITE_ONCE   => false,
          TRIGGER         => false
        )
        port map (
          i_clk             => i_clk,
          i_rst_n           => i_rst_n,
          i_sw_valid        => bit_field_valid,
          i_sw_read_mask    => bit_field_read_mask(3 downto 3),
          i_sw_write_enable => "1",
          i_sw_write_mask   => bit_field_write_mask(3 downto 3),
          i_sw_write_data   => bit_field_write_data(3 downto 3),
          o_sw_read_data    => bit_field_read_data(3 downto 3),
          o_sw_value        => bit_field_value(3 downto 3),
          o_write_trigger   => open,
          o_read_trigger    => open,
          i_hw_write_enable => "0",
          i_hw_write_data   => (others => '0'),
          i_hw_set          => (others => '0'),
          i_hw_clear        => (others => '0'),
          i_value           => (others => '0'),
          i_mask            => (others => '1'),
          o_value           => o_mrc_out2,
          o_value_unmasked  => open
        );
    end block;
    g_loop: block
    begin
      u_bit_field: entity work.rggen_bit_field
        generic map (
          WIDTH           => 1,
          INITIAL_VALUE   => slice(x"0", 1, 0),
          SW_WRITE_ONCE   => false,
          TRIGGER         => false
        )
        port map (
          i_clk             => i_clk,
          i_rst_n           => i_rst_n,
          i_sw_valid        => bit_field_valid,
          i_sw_read_mask    => bit_field_read_mask(4 downto 4),
          i_sw_write_enable => "1",
          i_sw_write_mask   => bit_field_write_mask(4 downto 4),
          i_sw_write_data   => bit_field_write_data(4 downto 4),
          o_sw_read_data    => bit_field_read_data(4 downto 4),
          o_sw_value        => bit_field_value(4 downto 4),
          o_write_trigger   => open,
          o_read_trigger    => open,
          i_hw_write_enable => "0",
          i_hw_write_data   => (others => '0'),
          i_hw_set          => (others => '0'),
          i_hw_clear        => (others => '0'),
          i_value           => (others => '0'),
          i_mask            => (others => '1'),
          o_value           => o_mrc_loop,
          o_value_unmasked  => open
        );
    end block;
  end block;
  g_lsr: block
    signal bit_field_valid: std_logic;
    signal bit_field_read_mask: std_logic_vector(31 downto 0);
    signal bit_field_write_mask: std_logic_vector(31 downto 0);
    signal bit_field_write_data: std_logic_vector(31 downto 0);
    signal bit_field_read_data: std_logic_vector(31 downto 0);
    signal bit_field_value: std_logic_vector(31 downto 0);
  begin
    \g_tie_off\: for \__i\ in 0 to 31 generate
      g: if (bit_slice(x"000000ff", \__i\) = '0') generate
        bit_field_read_data(\__i\) <= '0';
        bit_field_value(\__i\) <= '0';
      end generate;
    end generate;
    u_register: entity work.rggen_default_register
      generic map (
        READABLE        => true,
        WRITABLE        => false,
        ADDRESS_WIDTH   => 5,
        OFFSET_ADDRESS  => x"14",
        BUS_WIDTH       => 32,
        DATA_WIDTH      => 32
      )
      port map (
        i_clk                   => i_clk,
        i_rst_n                 => i_rst_n,
        i_register_valid        => register_valid,
        i_register_access       => register_access,
        i_register_address      => register_address,
        i_register_write_data   => register_write_data,
        i_register_strobe       => register_strobe,
        o_register_active       => register_active(7),
        o_register_ready        => register_ready(7),
        o_register_status       => register_status(15 downto 14),
        o_register_read_data    => register_read_data(255 downto 224),
        o_register_value        => register_value(255 downto 224),
        o_bit_field_valid       => bit_field_valid,
        o_bit_field_read_mask   => bit_field_read_mask,
        o_bit_field_write_mask  => bit_field_write_mask,
        o_bit_field_write_data  => bit_field_write_data,
        i_bit_field_read_data   => bit_field_read_data,
        i_bit_field_value       => bit_field_value
      );
    g_dr: block
    begin
      u_bit_field: entity work.rggen_bit_field
        generic map (
          WIDTH               => 1,
          STORAGE             => false,
          EXTERNAL_READ_DATA  => true,
          TRIGGER             => false
        )
        port map (
          i_clk             => i_clk,
          i_rst_n           => i_rst_n,
          i_sw_valid        => bit_field_valid,
          i_sw_read_mask    => bit_field_read_mask(0 downto 0),
          i_sw_write_enable => "0",
          i_sw_write_mask   => bit_field_write_mask(0 downto 0),
          i_sw_write_data   => bit_field_write_data(0 downto 0),
          o_sw_read_data    => bit_field_read_data(0 downto 0),
          o_sw_value        => bit_field_value(0 downto 0),
          o_write_trigger   => open,
          o_read_trigger    => open,
          i_hw_write_enable => "0",
          i_hw_write_data   => (others => '0'),
          i_hw_set          => (others => '0'),
          i_hw_clear        => (others => '0'),
          i_value           => i_lsr_dr,
          i_mask            => (others => '1'),
          o_value           => open,
          o_value_unmasked  => open
        );
    end block;
    g_oe: block
    begin
      u_bit_field: entity work.rggen_bit_field
        generic map (
          WIDTH               => 1,
          STORAGE             => false,
          EXTERNAL_READ_DATA  => true,
          TRIGGER             => true
        )
        port map (
          i_clk             => i_clk,
          i_rst_n           => i_rst_n,
          i_sw_valid        => bit_field_valid,
          i_sw_read_mask    => bit_field_read_mask(1 downto 1),
          i_sw_write_enable => "0",
          i_sw_write_mask   => bit_field_write_mask(1 downto 1),
          i_sw_write_data   => bit_field_write_data(1 downto 1),
          o_sw_read_data    => bit_field_read_data(1 downto 1),
          o_sw_value        => bit_field_value(1 downto 1),
          o_write_trigger   => open,
          o_read_trigger    => o_lsr_oe_read_trigger,
          i_hw_write_enable => "0",
          i_hw_write_data   => (others => '0'),
          i_hw_set          => (others => '0'),
          i_hw_clear        => (others => '0'),
          i_value           => i_lsr_oe,
          i_mask            => (others => '1'),
          o_value           => open,
          o_value_unmasked  => open
        );
    end block;
    g_pe: block
    begin
      u_bit_field: entity work.rggen_bit_field
        generic map (
          WIDTH               => 1,
          STORAGE             => false,
          EXTERNAL_READ_DATA  => true,
          TRIGGER             => true
        )
        port map (
          i_clk             => i_clk,
          i_rst_n           => i_rst_n,
          i_sw_valid        => bit_field_valid,
          i_sw_read_mask    => bit_field_read_mask(2 downto 2),
          i_sw_write_enable => "0",
          i_sw_write_mask   => bit_field_write_mask(2 downto 2),
          i_sw_write_data   => bit_field_write_data(2 downto 2),
          o_sw_read_data    => bit_field_read_data(2 downto 2),
          o_sw_value        => bit_field_value(2 downto 2),
          o_write_trigger   => open,
          o_read_trigger    => o_lsr_pe_read_trigger,
          i_hw_write_enable => "0",
          i_hw_write_data   => (others => '0'),
          i_hw_set          => (others => '0'),
          i_hw_clear        => (others => '0'),
          i_value           => i_lsr_pe,
          i_mask            => (others => '1'),
          o_value           => open,
          o_value_unmasked  => open
        );
    end block;
    g_fe: block
    begin
      u_bit_field: entity work.rggen_bit_field
        generic map (
          WIDTH               => 1,
          STORAGE             => false,
          EXTERNAL_READ_DATA  => true,
          TRIGGER             => true
        )
        port map (
          i_clk             => i_clk,
          i_rst_n           => i_rst_n,
          i_sw_valid        => bit_field_valid,
          i_sw_read_mask    => bit_field_read_mask(3 downto 3),
          i_sw_write_enable => "0",
          i_sw_write_mask   => bit_field_write_mask(3 downto 3),
          i_sw_write_data   => bit_field_write_data(3 downto 3),
          o_sw_read_data    => bit_field_read_data(3 downto 3),
          o_sw_value        => bit_field_value(3 downto 3),
          o_write_trigger   => open,
          o_read_trigger    => o_lsr_fe_read_trigger,
          i_hw_write_enable => "0",
          i_hw_write_data   => (others => '0'),
          i_hw_set          => (others => '0'),
          i_hw_clear        => (others => '0'),
          i_value           => i_lsr_fe,
          i_mask            => (others => '1'),
          o_value           => open,
          o_value_unmasked  => open
        );
    end block;
    g_bi: block
    begin
      u_bit_field: entity work.rggen_bit_field
        generic map (
          WIDTH               => 1,
          STORAGE             => false,
          EXTERNAL_READ_DATA  => true,
          TRIGGER             => true
        )
        port map (
          i_clk             => i_clk,
          i_rst_n           => i_rst_n,
          i_sw_valid        => bit_field_valid,
          i_sw_read_mask    => bit_field_read_mask(4 downto 4),
          i_sw_write_enable => "0",
          i_sw_write_mask   => bit_field_write_mask(4 downto 4),
          i_sw_write_data   => bit_field_write_data(4 downto 4),
          o_sw_read_data    => bit_field_read_data(4 downto 4),
          o_sw_value        => bit_field_value(4 downto 4),
          o_write_trigger   => open,
          o_read_trigger    => o_lsr_bi_read_trigger,
          i_hw_write_enable => "0",
          i_hw_write_data   => (others => '0'),
          i_hw_set          => (others => '0'),
          i_hw_clear        => (others => '0'),
          i_value           => i_lsr_bi,
          i_mask            => (others => '1'),
          o_value           => open,
          o_value_unmasked  => open
        );
    end block;
    g_thre: block
    begin
      u_bit_field: entity work.rggen_bit_field
        generic map (
          WIDTH               => 1,
          STORAGE             => false,
          EXTERNAL_READ_DATA  => true,
          TRIGGER             => false
        )
        port map (
          i_clk             => i_clk,
          i_rst_n           => i_rst_n,
          i_sw_valid        => bit_field_valid,
          i_sw_read_mask    => bit_field_read_mask(5 downto 5),
          i_sw_write_enable => "0",
          i_sw_write_mask   => bit_field_write_mask(5 downto 5),
          i_sw_write_data   => bit_field_write_data(5 downto 5),
          o_sw_read_data    => bit_field_read_data(5 downto 5),
          o_sw_value        => bit_field_value(5 downto 5),
          o_write_trigger   => open,
          o_read_trigger    => open,
          i_hw_write_enable => "0",
          i_hw_write_data   => (others => '0'),
          i_hw_set          => (others => '0'),
          i_hw_clear        => (others => '0'),
          i_value           => i_lsr_thre,
          i_mask            => (others => '1'),
          o_value           => open,
          o_value_unmasked  => open
        );
    end block;
    g_temt: block
    begin
      u_bit_field: entity work.rggen_bit_field
        generic map (
          WIDTH               => 1,
          STORAGE             => false,
          EXTERNAL_READ_DATA  => true,
          TRIGGER             => false
        )
        port map (
          i_clk             => i_clk,
          i_rst_n           => i_rst_n,
          i_sw_valid        => bit_field_valid,
          i_sw_read_mask    => bit_field_read_mask(6 downto 6),
          i_sw_write_enable => "0",
          i_sw_write_mask   => bit_field_write_mask(6 downto 6),
          i_sw_write_data   => bit_field_write_data(6 downto 6),
          o_sw_read_data    => bit_field_read_data(6 downto 6),
          o_sw_value        => bit_field_value(6 downto 6),
          o_write_trigger   => open,
          o_read_trigger    => open,
          i_hw_write_enable => "0",
          i_hw_write_data   => (others => '0'),
          i_hw_set          => (others => '0'),
          i_hw_clear        => (others => '0'),
          i_value           => i_lsr_temt,
          i_mask            => (others => '1'),
          o_value           => open,
          o_value_unmasked  => open
        );
    end block;
    g_error_in_rcvr_fifo: block
    begin
      u_bit_field: entity work.rggen_bit_field
        generic map (
          WIDTH               => 1,
          STORAGE             => false,
          EXTERNAL_READ_DATA  => true,
          TRIGGER             => false
        )
        port map (
          i_clk             => i_clk,
          i_rst_n           => i_rst_n,
          i_sw_valid        => bit_field_valid,
          i_sw_read_mask    => bit_field_read_mask(7 downto 7),
          i_sw_write_enable => "0",
          i_sw_write_mask   => bit_field_write_mask(7 downto 7),
          i_sw_write_data   => bit_field_write_data(7 downto 7),
          o_sw_read_data    => bit_field_read_data(7 downto 7),
          o_sw_value        => bit_field_value(7 downto 7),
          o_write_trigger   => open,
          o_read_trigger    => open,
          i_hw_write_enable => "0",
          i_hw_write_data   => (others => '0'),
          i_hw_set          => (others => '0'),
          i_hw_clear        => (others => '0'),
          i_value           => i_lsr_error_in_rcvr_fifo,
          i_mask            => (others => '1'),
          o_value           => open,
          o_value_unmasked  => open
        );
    end block;
  end block;
  g_msr: block
    signal bit_field_valid: std_logic;
    signal bit_field_read_mask: std_logic_vector(31 downto 0);
    signal bit_field_write_mask: std_logic_vector(31 downto 0);
    signal bit_field_write_data: std_logic_vector(31 downto 0);
    signal bit_field_read_data: std_logic_vector(31 downto 0);
    signal bit_field_value: std_logic_vector(31 downto 0);
  begin
    \g_tie_off\: for \__i\ in 0 to 31 generate
      g: if (bit_slice(x"000000ff", \__i\) = '0') generate
        bit_field_read_data(\__i\) <= '0';
        bit_field_value(\__i\) <= '0';
      end generate;
    end generate;
    u_register: entity work.rggen_default_register
      generic map (
        READABLE        => true,
        WRITABLE        => false,
        ADDRESS_WIDTH   => 5,
        OFFSET_ADDRESS  => x"18",
        BUS_WIDTH       => 32,
        DATA_WIDTH      => 32
      )
      port map (
        i_clk                   => i_clk,
        i_rst_n                 => i_rst_n,
        i_register_valid        => register_valid,
        i_register_access       => register_access,
        i_register_address      => register_address,
        i_register_write_data   => register_write_data,
        i_register_strobe       => register_strobe,
        o_register_active       => register_active(8),
        o_register_ready        => register_ready(8),
        o_register_status       => register_status(17 downto 16),
        o_register_read_data    => register_read_data(287 downto 256),
        o_register_value        => register_value(287 downto 256),
        o_bit_field_valid       => bit_field_valid,
        o_bit_field_read_mask   => bit_field_read_mask,
        o_bit_field_write_mask  => bit_field_write_mask,
        o_bit_field_write_data  => bit_field_write_data,
        i_bit_field_read_data   => bit_field_read_data,
        i_bit_field_value       => bit_field_value
      );
    g_dcts: block
    begin
      u_bit_field: entity work.rggen_bit_field
        generic map (
          WIDTH               => 1,
          STORAGE             => false,
          EXTERNAL_READ_DATA  => true,
          TRIGGER             => true
        )
        port map (
          i_clk             => i_clk,
          i_rst_n           => i_rst_n,
          i_sw_valid        => bit_field_valid,
          i_sw_read_mask    => bit_field_read_mask(0 downto 0),
          i_sw_write_enable => "0",
          i_sw_write_mask   => bit_field_write_mask(0 downto 0),
          i_sw_write_data   => bit_field_write_data(0 downto 0),
          o_sw_read_data    => bit_field_read_data(0 downto 0),
          o_sw_value        => bit_field_value(0 downto 0),
          o_write_trigger   => open,
          o_read_trigger    => o_msr_dcts_read_trigger,
          i_hw_write_enable => "0",
          i_hw_write_data   => (others => '0'),
          i_hw_set          => (others => '0'),
          i_hw_clear        => (others => '0'),
          i_value           => i_msr_dcts,
          i_mask            => (others => '1'),
          o_value           => open,
          o_value_unmasked  => open
        );
    end block;
    g_ddsr: block
    begin
      u_bit_field: entity work.rggen_bit_field
        generic map (
          WIDTH               => 1,
          STORAGE             => false,
          EXTERNAL_READ_DATA  => true,
          TRIGGER             => true
        )
        port map (
          i_clk             => i_clk,
          i_rst_n           => i_rst_n,
          i_sw_valid        => bit_field_valid,
          i_sw_read_mask    => bit_field_read_mask(1 downto 1),
          i_sw_write_enable => "0",
          i_sw_write_mask   => bit_field_write_mask(1 downto 1),
          i_sw_write_data   => bit_field_write_data(1 downto 1),
          o_sw_read_data    => bit_field_read_data(1 downto 1),
          o_sw_value        => bit_field_value(1 downto 1),
          o_write_trigger   => open,
          o_read_trigger    => o_msr_ddsr_read_trigger,
          i_hw_write_enable => "0",
          i_hw_write_data   => (others => '0'),
          i_hw_set          => (others => '0'),
          i_hw_clear        => (others => '0'),
          i_value           => i_msr_ddsr,
          i_mask            => (others => '1'),
          o_value           => open,
          o_value_unmasked  => open
        );
    end block;
    g_teri: block
    begin
      u_bit_field: entity work.rggen_bit_field
        generic map (
          WIDTH               => 1,
          STORAGE             => false,
          EXTERNAL_READ_DATA  => true,
          TRIGGER             => false
        )
        port map (
          i_clk             => i_clk,
          i_rst_n           => i_rst_n,
          i_sw_valid        => bit_field_valid,
          i_sw_read_mask    => bit_field_read_mask(2 downto 2),
          i_sw_write_enable => "0",
          i_sw_write_mask   => bit_field_write_mask(2 downto 2),
          i_sw_write_data   => bit_field_write_data(2 downto 2),
          o_sw_read_data    => bit_field_read_data(2 downto 2),
          o_sw_value        => bit_field_value(2 downto 2),
          o_write_trigger   => open,
          o_read_trigger    => open,
          i_hw_write_enable => "0",
          i_hw_write_data   => (others => '0'),
          i_hw_set          => (others => '0'),
          i_hw_clear        => (others => '0'),
          i_value           => i_msr_teri,
          i_mask            => (others => '1'),
          o_value           => open,
          o_value_unmasked  => open
        );
    end block;
    g_ddcd: block
    begin
      u_bit_field: entity work.rggen_bit_field
        generic map (
          WIDTH               => 1,
          STORAGE             => false,
          EXTERNAL_READ_DATA  => true,
          TRIGGER             => true
        )
        port map (
          i_clk             => i_clk,
          i_rst_n           => i_rst_n,
          i_sw_valid        => bit_field_valid,
          i_sw_read_mask    => bit_field_read_mask(3 downto 3),
          i_sw_write_enable => "0",
          i_sw_write_mask   => bit_field_write_mask(3 downto 3),
          i_sw_write_data   => bit_field_write_data(3 downto 3),
          o_sw_read_data    => bit_field_read_data(3 downto 3),
          o_sw_value        => bit_field_value(3 downto 3),
          o_write_trigger   => open,
          o_read_trigger    => o_msr_ddcd_read_trigger,
          i_hw_write_enable => "0",
          i_hw_write_data   => (others => '0'),
          i_hw_set          => (others => '0'),
          i_hw_clear        => (others => '0'),
          i_value           => i_msr_ddcd,
          i_mask            => (others => '1'),
          o_value           => open,
          o_value_unmasked  => open
        );
    end block;
    g_cts: block
    begin
      u_bit_field: entity work.rggen_bit_field
        generic map (
          WIDTH               => 1,
          STORAGE             => false,
          EXTERNAL_READ_DATA  => true,
          TRIGGER             => false
        )
        port map (
          i_clk             => i_clk,
          i_rst_n           => i_rst_n,
          i_sw_valid        => bit_field_valid,
          i_sw_read_mask    => bit_field_read_mask(4 downto 4),
          i_sw_write_enable => "0",
          i_sw_write_mask   => bit_field_write_mask(4 downto 4),
          i_sw_write_data   => bit_field_write_data(4 downto 4),
          o_sw_read_data    => bit_field_read_data(4 downto 4),
          o_sw_value        => bit_field_value(4 downto 4),
          o_write_trigger   => open,
          o_read_trigger    => open,
          i_hw_write_enable => "0",
          i_hw_write_data   => (others => '0'),
          i_hw_set          => (others => '0'),
          i_hw_clear        => (others => '0'),
          i_value           => i_msr_cts,
          i_mask            => (others => '1'),
          o_value           => open,
          o_value_unmasked  => open
        );
    end block;
    g_dsr: block
    begin
      u_bit_field: entity work.rggen_bit_field
        generic map (
          WIDTH               => 1,
          STORAGE             => false,
          EXTERNAL_READ_DATA  => true,
          TRIGGER             => false
        )
        port map (
          i_clk             => i_clk,
          i_rst_n           => i_rst_n,
          i_sw_valid        => bit_field_valid,
          i_sw_read_mask    => bit_field_read_mask(5 downto 5),
          i_sw_write_enable => "0",
          i_sw_write_mask   => bit_field_write_mask(5 downto 5),
          i_sw_write_data   => bit_field_write_data(5 downto 5),
          o_sw_read_data    => bit_field_read_data(5 downto 5),
          o_sw_value        => bit_field_value(5 downto 5),
          o_write_trigger   => open,
          o_read_trigger    => open,
          i_hw_write_enable => "0",
          i_hw_write_data   => (others => '0'),
          i_hw_set          => (others => '0'),
          i_hw_clear        => (others => '0'),
          i_value           => i_msr_dsr,
          i_mask            => (others => '1'),
          o_value           => open,
          o_value_unmasked  => open
        );
    end block;
    g_ri: block
    begin
      u_bit_field: entity work.rggen_bit_field
        generic map (
          WIDTH               => 1,
          STORAGE             => false,
          EXTERNAL_READ_DATA  => true,
          TRIGGER             => false
        )
        port map (
          i_clk             => i_clk,
          i_rst_n           => i_rst_n,
          i_sw_valid        => bit_field_valid,
          i_sw_read_mask    => bit_field_read_mask(6 downto 6),
          i_sw_write_enable => "0",
          i_sw_write_mask   => bit_field_write_mask(6 downto 6),
          i_sw_write_data   => bit_field_write_data(6 downto 6),
          o_sw_read_data    => bit_field_read_data(6 downto 6),
          o_sw_value        => bit_field_value(6 downto 6),
          o_write_trigger   => open,
          o_read_trigger    => open,
          i_hw_write_enable => "0",
          i_hw_write_data   => (others => '0'),
          i_hw_set          => (others => '0'),
          i_hw_clear        => (others => '0'),
          i_value           => i_msr_ri,
          i_mask            => (others => '1'),
          o_value           => open,
          o_value_unmasked  => open
        );
    end block;
    g_dcd: block
    begin
      u_bit_field: entity work.rggen_bit_field
        generic map (
          WIDTH               => 1,
          STORAGE             => false,
          EXTERNAL_READ_DATA  => true,
          TRIGGER             => false
        )
        port map (
          i_clk             => i_clk,
          i_rst_n           => i_rst_n,
          i_sw_valid        => bit_field_valid,
          i_sw_read_mask    => bit_field_read_mask(7 downto 7),
          i_sw_write_enable => "0",
          i_sw_write_mask   => bit_field_write_mask(7 downto 7),
          i_sw_write_data   => bit_field_write_data(7 downto 7),
          o_sw_read_data    => bit_field_read_data(7 downto 7),
          o_sw_value        => bit_field_value(7 downto 7),
          o_write_trigger   => open,
          o_read_trigger    => open,
          i_hw_write_enable => "0",
          i_hw_write_data   => (others => '0'),
          i_hw_set          => (others => '0'),
          i_hw_clear        => (others => '0'),
          i_value           => i_msr_dcd,
          i_mask            => (others => '1'),
          o_value           => open,
          o_value_unmasked  => open
        );
    end block;
  end block;
  g_scratch: block
    signal bit_field_valid: std_logic;
    signal bit_field_read_mask: std_logic_vector(31 downto 0);
    signal bit_field_write_mask: std_logic_vector(31 downto 0);
    signal bit_field_write_data: std_logic_vector(31 downto 0);
    signal bit_field_read_data: std_logic_vector(31 downto 0);
    signal bit_field_value: std_logic_vector(31 downto 0);
  begin
    \g_tie_off\: for \__i\ in 0 to 31 generate
      g: if (bit_slice(x"000000ff", \__i\) = '0') generate
        bit_field_read_data(\__i\) <= '0';
        bit_field_value(\__i\) <= '0';
      end generate;
    end generate;
    u_register: entity work.rggen_default_register
      generic map (
        READABLE        => true,
        WRITABLE        => true,
        ADDRESS_WIDTH   => 5,
        OFFSET_ADDRESS  => x"1c",
        BUS_WIDTH       => 32,
        DATA_WIDTH      => 32
      )
      port map (
        i_clk                   => i_clk,
        i_rst_n                 => i_rst_n,
        i_register_valid        => register_valid,
        i_register_access       => register_access,
        i_register_address      => register_address,
        i_register_write_data   => register_write_data,
        i_register_strobe       => register_strobe,
        o_register_active       => register_active(9),
        o_register_ready        => register_ready(9),
        o_register_status       => register_status(19 downto 18),
        o_register_read_data    => register_read_data(319 downto 288),
        o_register_value        => register_value(319 downto 288),
        o_bit_field_valid       => bit_field_valid,
        o_bit_field_read_mask   => bit_field_read_mask,
        o_bit_field_write_mask  => bit_field_write_mask,
        o_bit_field_write_data  => bit_field_write_data,
        i_bit_field_read_data   => bit_field_read_data,
        i_bit_field_value       => bit_field_value
      );
    g_scratch: block
    begin
      u_bit_field: entity work.rggen_bit_field
        generic map (
          WIDTH           => 8,
          INITIAL_VALUE   => slice(x"00", 8, 0),
          SW_WRITE_ONCE   => false,
          TRIGGER         => false
        )
        port map (
          i_clk             => i_clk,
          i_rst_n           => i_rst_n,
          i_sw_valid        => bit_field_valid,
          i_sw_read_mask    => bit_field_read_mask(7 downto 0),
          i_sw_write_enable => "1",
          i_sw_write_mask   => bit_field_write_mask(7 downto 0),
          i_sw_write_data   => bit_field_write_data(7 downto 0),
          o_sw_read_data    => bit_field_read_data(7 downto 0),
          o_sw_value        => bit_field_value(7 downto 0),
          o_write_trigger   => open,
          o_read_trigger    => open,
          i_hw_write_enable => "0",
          i_hw_write_data   => (others => '0'),
          i_hw_set          => (others => '0'),
          i_hw_clear        => (others => '0'),
          i_value           => (others => '0'),
          i_mask            => (others => '1'),
          o_value           => o_scratch,
          o_value_unmasked  => open
        );
    end block;
  end block;
  g_dll: block
    signal bit_field_valid: std_logic;
    signal bit_field_read_mask: std_logic_vector(31 downto 0);
    signal bit_field_write_mask: std_logic_vector(31 downto 0);
    signal bit_field_write_data: std_logic_vector(31 downto 0);
    signal bit_field_read_data: std_logic_vector(31 downto 0);
    signal bit_field_value: std_logic_vector(31 downto 0);
    signal indirect_match: std_logic_vector(0 downto 0);
  begin
    \g_tie_off\: for \__i\ in 0 to 31 generate
      g: if (bit_slice(x"000000ff", \__i\) = '0') generate
        bit_field_read_data(\__i\) <= '0';
        bit_field_value(\__i\) <= '0';
      end generate;
    end generate;
    indirect_match(0) <= '1' when unsigned(register_value(167 downto 167)) = 1 else '0';
    u_register: entity work.rggen_indirect_register
      generic map (
        READABLE              => true,
        WRITABLE              => true,
        ADDRESS_WIDTH         => 5,
        OFFSET_ADDRESS        => x"00",
        BUS_WIDTH             => 32,
        DATA_WIDTH            => 32,
        INDIRECT_MATCH_WIDTH  => 1
      )
      port map (
        i_clk                   => i_clk,
        i_rst_n                 => i_rst_n,
        i_register_valid        => register_valid,
        i_register_access       => register_access,
        i_register_address      => register_address,
        i_register_write_data   => register_write_data,
        i_register_strobe       => register_strobe,
        o_register_active       => register_active(10),
        o_register_ready        => register_ready(10),
        o_register_status       => register_status(21 downto 20),
        o_register_read_data    => register_read_data(351 downto 320),
        o_register_value        => register_value(351 downto 320),
        i_indirect_match        => indirect_match,
        o_bit_field_valid       => bit_field_valid,
        o_bit_field_read_mask   => bit_field_read_mask,
        o_bit_field_write_mask  => bit_field_write_mask,
        o_bit_field_write_data  => bit_field_write_data,
        i_bit_field_read_data   => bit_field_read_data,
        i_bit_field_value       => bit_field_value
      );
    g_dll: block
    begin
      u_bit_field: entity work.rggen_bit_field
        generic map (
          WIDTH           => 8,
          INITIAL_VALUE   => slice(DLL_INITIAL_VALUE, 8, 0),
          SW_WRITE_ONCE   => false,
          TRIGGER         => false
        )
        port map (
          i_clk             => i_clk,
          i_rst_n           => i_rst_n,
          i_sw_valid        => bit_field_valid,
          i_sw_read_mask    => bit_field_read_mask(7 downto 0),
          i_sw_write_enable => "1",
          i_sw_write_mask   => bit_field_write_mask(7 downto 0),
          i_sw_write_data   => bit_field_write_data(7 downto 0),
          o_sw_read_data    => bit_field_read_data(7 downto 0),
          o_sw_value        => bit_field_value(7 downto 0),
          o_write_trigger   => open,
          o_read_trigger    => open,
          i_hw_write_enable => "0",
          i_hw_write_data   => (others => '0'),
          i_hw_set          => (others => '0'),
          i_hw_clear        => (others => '0'),
          i_value           => (others => '0'),
          i_mask            => (others => '1'),
          o_value           => o_dll,
          o_value_unmasked  => open
        );
    end block;
  end block;
  g_dlm: block
    signal bit_field_valid: std_logic;
    signal bit_field_read_mask: std_logic_vector(31 downto 0);
    signal bit_field_write_mask: std_logic_vector(31 downto 0);
    signal bit_field_write_data: std_logic_vector(31 downto 0);
    signal bit_field_read_data: std_logic_vector(31 downto 0);
    signal bit_field_value: std_logic_vector(31 downto 0);
    signal indirect_match: std_logic_vector(0 downto 0);
  begin
    \g_tie_off\: for \__i\ in 0 to 31 generate
      g: if (bit_slice(x"000000ff", \__i\) = '0') generate
        bit_field_read_data(\__i\) <= '0';
        bit_field_value(\__i\) <= '0';
      end generate;
    end generate;
    indirect_match(0) <= '1' when unsigned(register_value(167 downto 167)) = 1 else '0';
    u_register: entity work.rggen_indirect_register
      generic map (
        READABLE              => true,
        WRITABLE              => true,
        ADDRESS_WIDTH         => 5,
        OFFSET_ADDRESS        => x"04",
        BUS_WIDTH             => 32,
        DATA_WIDTH            => 32,
        INDIRECT_MATCH_WIDTH  => 1
      )
      port map (
        i_clk                   => i_clk,
        i_rst_n                 => i_rst_n,
        i_register_valid        => register_valid,
        i_register_access       => register_access,
        i_register_address      => register_address,
        i_register_write_data   => register_write_data,
        i_register_strobe       => register_strobe,
        o_register_active       => register_active(11),
        o_register_ready        => register_ready(11),
        o_register_status       => register_status(23 downto 22),
        o_register_read_data    => register_read_data(383 downto 352),
        o_register_value        => register_value(383 downto 352),
        i_indirect_match        => indirect_match,
        o_bit_field_valid       => bit_field_valid,
        o_bit_field_read_mask   => bit_field_read_mask,
        o_bit_field_write_mask  => bit_field_write_mask,
        o_bit_field_write_data  => bit_field_write_data,
        i_bit_field_read_data   => bit_field_read_data,
        i_bit_field_value       => bit_field_value
      );
    g_dlm: block
    begin
      u_bit_field: entity work.rggen_bit_field
        generic map (
          WIDTH           => 8,
          INITIAL_VALUE   => slice(DLM_INITIAL_VALUE, 8, 0),
          SW_WRITE_ONCE   => false,
          TRIGGER         => false
        )
        port map (
          i_clk             => i_clk,
          i_rst_n           => i_rst_n,
          i_sw_valid        => bit_field_valid,
          i_sw_read_mask    => bit_field_read_mask(7 downto 0),
          i_sw_write_enable => "1",
          i_sw_write_mask   => bit_field_write_mask(7 downto 0),
          i_sw_write_data   => bit_field_write_data(7 downto 0),
          o_sw_read_data    => bit_field_read_data(7 downto 0),
          o_sw_value        => bit_field_value(7 downto 0),
          o_write_trigger   => open,
          o_read_trigger    => open,
          i_hw_write_enable => "0",
          i_hw_write_data   => (others => '0'),
          i_hw_set          => (others => '0'),
          i_hw_clear        => (others => '0'),
          i_value           => (others => '0'),
          i_mask            => (others => '1'),
          o_value           => o_dlm,
          o_value_unmasked  => open
        );
    end block;
  end block;
end rtl;
