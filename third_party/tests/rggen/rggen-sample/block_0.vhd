library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

use work.rggen_rtl.all;

entity block_0 is
  generic (
    ADDRESS_WIDTH: positive := 8;
    PRE_DECODE: boolean := false;
    BASE_ADDRESS: unsigned := x"0";
    ERROR_STATUS: boolean := false;
    INSERT_SLICER: boolean := false;
    REGISTER_10_BIT_FIELD_1_INITIAL_VALUE: unsigned(7 downto 0) := repeat(x"0", 2, 4)
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
    o_register_0_bit_field_0: out std_logic_vector(3 downto 0);
    o_register_0_bit_field_1: out std_logic_vector(3 downto 0);
    o_register_0_bit_field_2: out std_logic_vector(0 downto 0);
    o_register_0_bit_field_3: out std_logic_vector(1 downto 0);
    o_register_0_bit_field_4: out std_logic_vector(1 downto 0);
    o_register_0_bit_field_5: out std_logic_vector(1 downto 0);
    o_register_0_bit_field_6: out std_logic_vector(1 downto 0);
    i_register_0_bit_field_6: in std_logic_vector(1 downto 0);
    o_register_1: out std_logic_vector(0 downto 0);
    i_register_2_bit_field_0: in std_logic_vector(3 downto 0);
    i_register_2_bit_field_2_latch: in std_logic_vector(0 downto 0);
    i_register_2_bit_field_2: in std_logic_vector(3 downto 0);
    o_register_2_bit_field_2: out std_logic_vector(3 downto 0);
    i_register_2_bit_field_3: in std_logic_vector(3 downto 0);
    o_register_2_bit_field_3: out std_logic_vector(3 downto 0);
    o_register_3_bit_field_0: out std_logic_vector(3 downto 0);
    o_register_3_bit_field_1: out std_logic_vector(3 downto 0);
    o_register_3_bit_field_2_trigger: out std_logic_vector(3 downto 0);
    o_register_3_bit_field_3_trigger: out std_logic_vector(3 downto 0);
    i_register_4_bit_field_0_set: in std_logic_vector(3 downto 0);
    o_register_4_bit_field_0: out std_logic_vector(3 downto 0);
    i_register_4_bit_field_1_set: in std_logic_vector(3 downto 0);
    o_register_4_bit_field_1: out std_logic_vector(3 downto 0);
    o_register_4_bit_field_1_unmasked: out std_logic_vector(3 downto 0);
    i_register_4_bit_field_3_clear: in std_logic_vector(3 downto 0);
    o_register_4_bit_field_3: out std_logic_vector(3 downto 0);
    i_register_5_bit_field_0_clear: in std_logic_vector(0 downto 0);
    o_register_5_bit_field_0: out std_logic_vector(1 downto 0);
    o_register_5_bit_field_1: out std_logic_vector(1 downto 0);
    i_register_5_bit_field_2_set: in std_logic_vector(0 downto 0);
    i_register_5_bit_field_2: in std_logic_vector(1 downto 0);
    o_register_5_bit_field_2: out std_logic_vector(1 downto 0);
    i_register_5_bit_field_3: in std_logic_vector(1 downto 0);
    o_register_5_bit_field_3: out std_logic_vector(1 downto 0);
    i_register_5_bit_field_4_enable: in std_logic_vector(0 downto 0);
    o_register_5_bit_field_4: out std_logic_vector(1 downto 0);
    o_register_5_bit_field_5: out std_logic_vector(1 downto 0);
    o_register_5_bit_field_6: out std_logic_vector(1 downto 0);
    i_register_5_bit_field_7_lock: in std_logic_vector(0 downto 0);
    o_register_5_bit_field_7: out std_logic_vector(1 downto 0);
    o_register_5_bit_field_8: out std_logic_vector(1 downto 0);
    o_register_5_bit_field_9: out std_logic_vector(1 downto 0);
    i_register_6_bit_field_0_set: in std_logic_vector(3 downto 0);
    o_register_6_bit_field_0: out std_logic_vector(3 downto 0);
    i_register_6_bit_field_1_set: in std_logic_vector(3 downto 0);
    o_register_6_bit_field_1: out std_logic_vector(3 downto 0);
    o_register_6_bit_field_1_unmasked: out std_logic_vector(3 downto 0);
    i_register_6_bit_field_3_set: in std_logic_vector(3 downto 0);
    o_register_6_bit_field_3: out std_logic_vector(3 downto 0);
    i_register_6_bit_field_4_set: in std_logic_vector(3 downto 0);
    o_register_6_bit_field_4: out std_logic_vector(3 downto 0);
    o_register_6_bit_field_4_unmasked: out std_logic_vector(3 downto 0);
    i_register_6_bit_field_6_clear: in std_logic_vector(3 downto 0);
    o_register_6_bit_field_6: out std_logic_vector(3 downto 0);
    i_register_6_bit_field_7_clear: in std_logic_vector(3 downto 0);
    o_register_6_bit_field_7: out std_logic_vector(3 downto 0);
    o_register_6_bit_field_8: out std_logic_vector(3 downto 0);
    o_register_6_bit_field_9: out std_logic_vector(3 downto 0);
    o_register_7_bit_field_0: out std_logic_vector(3 downto 0);
    o_register_7_bit_field_1: out std_logic_vector(3 downto 0);
    o_register_7_bit_field_2: out std_logic_vector(3 downto 0);
    o_register_7_bit_field_3: out std_logic_vector(3 downto 0);
    i_register_8_bit_field_0_set: in std_logic_vector(3 downto 0);
    o_register_8_bit_field_0: out std_logic_vector(3 downto 0);
    i_register_8_bit_field_1_clear: in std_logic_vector(3 downto 0);
    o_register_8_bit_field_1: out std_logic_vector(3 downto 0);
    i_register_8_bit_field_2_set: in std_logic_vector(3 downto 0);
    o_register_8_bit_field_2: out std_logic_vector(3 downto 0);
    i_register_8_bit_field_3_clear: in std_logic_vector(3 downto 0);
    o_register_8_bit_field_3: out std_logic_vector(3 downto 0);
    o_register_8_bit_field_4: out std_logic_vector(3 downto 0);
    o_register_8_bit_field_5: out std_logic_vector(3 downto 0);
    o_register_9_bit_field_0: out std_logic_vector(1 downto 0);
    o_register_9_bit_field_0_write_trigger: out std_logic_vector(0 downto 0);
    o_register_9_bit_field_0_read_trigger: out std_logic_vector(0 downto 0);
    i_register_9_bit_field_1: in std_logic_vector(1 downto 0);
    o_register_9_bit_field_1_read_trigger: out std_logic_vector(0 downto 0);
    o_register_9_bit_field_2: out std_logic_vector(1 downto 0);
    o_register_9_bit_field_2_write_trigger: out std_logic_vector(0 downto 0);
    o_register_9_bit_field_3: out std_logic_vector(1 downto 0);
    i_register_9_bit_field_3: in std_logic_vector(1 downto 0);
    o_register_9_bit_field_3_write_trigger: out std_logic_vector(0 downto 0);
    o_register_9_bit_field_3_read_trigger: out std_logic_vector(0 downto 0);
    i_register_9_bit_field_4: in std_logic_vector(1 downto 0);
    o_register_9_bit_field_4_trigger: out std_logic_vector(1 downto 0);
    i_register_9_bit_field_5: in std_logic_vector(1 downto 0);
    o_register_9_bit_field_5_trigger: out std_logic_vector(1 downto 0);
    o_register_10_bit_field_0: out std_logic_vector(31 downto 0);
    o_register_10_bit_field_1: out std_logic_vector(31 downto 0);
    o_register_10_bit_field_2: out std_logic_vector(31 downto 0);
    o_register_11_bit_field_0: out std_logic_vector(255 downto 0);
    o_register_11_bit_field_1: out std_logic_vector(255 downto 0);
    o_register_12_bit_field_0: out std_logic_vector(0 downto 0);
    o_register_12_bit_field_1: out std_logic_vector(0 downto 0);
    o_register_13_bit_field_0: out std_logic_vector(1 downto 0);
    i_register_13_bit_field_1: in std_logic_vector(1 downto 0);
    o_register_13_bit_field_2: out std_logic_vector(1 downto 0);
    o_register_13_bit_field_3: out std_logic_vector(1 downto 0);
    o_register_13_bit_field_3_write_trigger: out std_logic_vector(0 downto 0);
    o_register_13_bit_field_3_read_trigger: out std_logic_vector(0 downto 0);
    o_register_13_bit_field_4: out std_logic_vector(1 downto 0);
    o_register_13_bit_field_5: out std_logic_vector(1 downto 0);
    o_register_13_bit_field_6: out std_logic_vector(1 downto 0);
    i_register_13_bit_field_6_hw_clear: in std_logic_vector(1 downto 0);
    o_register_13_bit_field_7: out std_logic_vector(1 downto 0);
    i_register_13_bit_field_7_hw_set: in std_logic_vector(1 downto 0);
    o_register_13_bit_field_8: out std_logic_vector(1 downto 0);
    i_register_13_bit_field_8_hw_write_enable: in std_logic_vector(0 downto 0);
    i_register_13_bit_field_8_hw_write_data: in std_logic_vector(1 downto 0);
    o_register_15_valid: out std_logic;
    o_register_15_access: out std_logic_vector(1 downto 0);
    o_register_15_address: out std_logic_vector(7 downto 0);
    o_register_15_data: out std_logic_vector(31 downto 0);
    o_register_15_strobe: out std_logic_vector(3 downto 0);
    i_register_15_ready: in std_logic;
    i_register_15_status: in std_logic_vector(1 downto 0);
    i_register_15_data: in std_logic_vector(31 downto 0)
  );
end block_0;

architecture rtl of block_0 is
  signal register_valid: std_logic;
  signal register_access: std_logic_vector(1 downto 0);
  signal register_address: std_logic_vector(7 downto 0);
  signal register_write_data: std_logic_vector(31 downto 0);
  signal register_strobe: std_logic_vector(3 downto 0);
  signal register_active: std_logic_vector(24 downto 0);
  signal register_ready: std_logic_vector(24 downto 0);
  signal register_status: std_logic_vector(49 downto 0);
  signal register_read_data: std_logic_vector(799 downto 0);
  signal register_value: std_logic_vector(1599 downto 0);
begin
  u_adapter: entity work.rggen_apb_adaper
    generic map (
      ADDRESS_WIDTH       => ADDRESS_WIDTH,
      LOCAL_ADDRESS_WIDTH => 8,
      BUS_WIDTH           => 32,
      REGISTERS           => 25,
      PRE_DECODE          => PRE_DECODE,
      BASE_ADDRESS        => BASE_ADDRESS,
      BYTE_SIZE           => 256,
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
  g_register_0: block
    signal bit_field_valid: std_logic;
    signal bit_field_read_mask: std_logic_vector(31 downto 0);
    signal bit_field_write_mask: std_logic_vector(31 downto 0);
    signal bit_field_write_data: std_logic_vector(31 downto 0);
    signal bit_field_read_data: std_logic_vector(31 downto 0);
    signal bit_field_value: std_logic_vector(31 downto 0);
  begin
    \g_tie_off\: for \__i\ in 0 to 31 generate
      g: if (bit_slice(x"0001ffff", \__i\) = '0') generate
        bit_field_read_data(\__i\) <= '0';
        bit_field_value(\__i\) <= '0';
      end generate;
    end generate;
    u_register: entity work.rggen_default_register
      generic map (
        READABLE        => true,
        WRITABLE        => true,
        ADDRESS_WIDTH   => 8,
        OFFSET_ADDRESS  => x"00",
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
        o_register_active       => register_active(0),
        o_register_ready        => register_ready(0),
        o_register_status       => register_status(1 downto 0),
        o_register_read_data    => register_read_data(31 downto 0),
        o_register_value        => register_value(31 downto 0),
        o_bit_field_valid       => bit_field_valid,
        o_bit_field_read_mask   => bit_field_read_mask,
        o_bit_field_write_mask  => bit_field_write_mask,
        o_bit_field_write_data  => bit_field_write_data,
        i_bit_field_read_data   => bit_field_read_data,
        i_bit_field_value       => bit_field_value
      );
    g_bit_field_0: block
    begin
      u_bit_field: entity work.rggen_bit_field
        generic map (
          WIDTH           => 4,
          INITIAL_VALUE   => slice(x"0", 4, 0),
          SW_WRITE_ONCE   => false,
          TRIGGER         => false
        )
        port map (
          i_clk             => i_clk,
          i_rst_n           => i_rst_n,
          i_sw_valid        => bit_field_valid,
          i_sw_read_mask    => bit_field_read_mask(3 downto 0),
          i_sw_write_enable => "1",
          i_sw_write_mask   => bit_field_write_mask(3 downto 0),
          i_sw_write_data   => bit_field_write_data(3 downto 0),
          o_sw_read_data    => bit_field_read_data(3 downto 0),
          o_sw_value        => bit_field_value(3 downto 0),
          o_write_trigger   => open,
          o_read_trigger    => open,
          i_hw_write_enable => "0",
          i_hw_write_data   => (others => '0'),
          i_hw_set          => (others => '0'),
          i_hw_clear        => (others => '0'),
          i_value           => (others => '0'),
          i_mask            => (others => '1'),
          o_value           => o_register_0_bit_field_0,
          o_value_unmasked  => open
        );
    end block;
    g_bit_field_1: block
    begin
      u_bit_field: entity work.rggen_bit_field
        generic map (
          WIDTH           => 4,
          INITIAL_VALUE   => slice(x"0", 4, 0),
          SW_WRITE_ONCE   => false,
          TRIGGER         => false
        )
        port map (
          i_clk             => i_clk,
          i_rst_n           => i_rst_n,
          i_sw_valid        => bit_field_valid,
          i_sw_read_mask    => bit_field_read_mask(7 downto 4),
          i_sw_write_enable => "1",
          i_sw_write_mask   => bit_field_write_mask(7 downto 4),
          i_sw_write_data   => bit_field_write_data(7 downto 4),
          o_sw_read_data    => bit_field_read_data(7 downto 4),
          o_sw_value        => bit_field_value(7 downto 4),
          o_write_trigger   => open,
          o_read_trigger    => open,
          i_hw_write_enable => "0",
          i_hw_write_data   => (others => '0'),
          i_hw_set          => (others => '0'),
          i_hw_clear        => (others => '0'),
          i_value           => (others => '0'),
          i_mask            => (others => '1'),
          o_value           => o_register_0_bit_field_1,
          o_value_unmasked  => open
        );
    end block;
    g_bit_field_2: block
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
          i_sw_read_mask    => bit_field_read_mask(8 downto 8),
          i_sw_write_enable => "1",
          i_sw_write_mask   => bit_field_write_mask(8 downto 8),
          i_sw_write_data   => bit_field_write_data(8 downto 8),
          o_sw_read_data    => bit_field_read_data(8 downto 8),
          o_sw_value        => bit_field_value(8 downto 8),
          o_write_trigger   => open,
          o_read_trigger    => open,
          i_hw_write_enable => "0",
          i_hw_write_data   => (others => '0'),
          i_hw_set          => (others => '0'),
          i_hw_clear        => (others => '0'),
          i_value           => (others => '0'),
          i_mask            => (others => '1'),
          o_value           => o_register_0_bit_field_2,
          o_value_unmasked  => open
        );
    end block;
    g_bit_field_3: block
    begin
      u_bit_field: entity work.rggen_bit_field
        generic map (
          WIDTH           => 2,
          INITIAL_VALUE   => slice(x"0", 2, 0),
          SW_WRITE_ONCE   => true,
          TRIGGER         => false
        )
        port map (
          i_clk             => i_clk,
          i_rst_n           => i_rst_n,
          i_sw_valid        => bit_field_valid,
          i_sw_read_mask    => bit_field_read_mask(10 downto 9),
          i_sw_write_enable => "1",
          i_sw_write_mask   => bit_field_write_mask(10 downto 9),
          i_sw_write_data   => bit_field_write_data(10 downto 9),
          o_sw_read_data    => bit_field_read_data(10 downto 9),
          o_sw_value        => bit_field_value(10 downto 9),
          o_write_trigger   => open,
          o_read_trigger    => open,
          i_hw_write_enable => "0",
          i_hw_write_data   => (others => '0'),
          i_hw_set          => (others => '0'),
          i_hw_clear        => (others => '0'),
          i_value           => (others => '0'),
          i_mask            => (others => '1'),
          o_value           => o_register_0_bit_field_3,
          o_value_unmasked  => open
        );
    end block;
    g_bit_field_4: block
    begin
      u_bit_field: entity work.rggen_bit_field
        generic map (
          WIDTH           => 2,
          INITIAL_VALUE   => slice(x"0", 2, 0),
          SW_READ_ACTION  => RGGEN_READ_CLEAR
        )
        port map (
          i_clk             => i_clk,
          i_rst_n           => i_rst_n,
          i_sw_valid        => bit_field_valid,
          i_sw_read_mask    => bit_field_read_mask(12 downto 11),
          i_sw_write_enable => "1",
          i_sw_write_mask   => bit_field_write_mask(12 downto 11),
          i_sw_write_data   => bit_field_write_data(12 downto 11),
          o_sw_read_data    => bit_field_read_data(12 downto 11),
          o_sw_value        => bit_field_value(12 downto 11),
          o_write_trigger   => open,
          o_read_trigger    => open,
          i_hw_write_enable => "0",
          i_hw_write_data   => (others => '0'),
          i_hw_set          => (others => '0'),
          i_hw_clear        => (others => '0'),
          i_value           => (others => '0'),
          i_mask            => (others => '1'),
          o_value           => o_register_0_bit_field_4,
          o_value_unmasked  => open
        );
    end block;
    g_bit_field_5: block
    begin
      u_bit_field: entity work.rggen_bit_field
        generic map (
          WIDTH           => 2,
          INITIAL_VALUE   => slice(x"0", 2, 0),
          SW_READ_ACTION  => RGGEN_READ_SET
        )
        port map (
          i_clk             => i_clk,
          i_rst_n           => i_rst_n,
          i_sw_valid        => bit_field_valid,
          i_sw_read_mask    => bit_field_read_mask(14 downto 13),
          i_sw_write_enable => "1",
          i_sw_write_mask   => bit_field_write_mask(14 downto 13),
          i_sw_write_data   => bit_field_write_data(14 downto 13),
          o_sw_read_data    => bit_field_read_data(14 downto 13),
          o_sw_value        => bit_field_value(14 downto 13),
          o_write_trigger   => open,
          o_read_trigger    => open,
          i_hw_write_enable => "0",
          i_hw_write_data   => (others => '0'),
          i_hw_set          => (others => '0'),
          i_hw_clear        => (others => '0'),
          i_value           => (others => '0'),
          i_mask            => (others => '1'),
          o_value           => o_register_0_bit_field_5,
          o_value_unmasked  => open
        );
    end block;
    g_bit_field_6: block
    begin
      u_bit_field: entity work.rggen_bit_field
        generic map (
          WIDTH               => 2,
          INITIAL_VALUE       => slice(x"0", 2, 0),
          EXTERNAL_READ_DATA  => true,
          TRIGGER             => false
        )
        port map (
          i_clk             => i_clk,
          i_rst_n           => i_rst_n,
          i_sw_valid        => bit_field_valid,
          i_sw_read_mask    => bit_field_read_mask(16 downto 15),
          i_sw_write_enable => "1",
          i_sw_write_mask   => bit_field_write_mask(16 downto 15),
          i_sw_write_data   => bit_field_write_data(16 downto 15),
          o_sw_read_data    => bit_field_read_data(16 downto 15),
          o_sw_value        => bit_field_value(16 downto 15),
          o_write_trigger   => open,
          o_read_trigger    => open,
          i_hw_write_enable => "0",
          i_hw_write_data   => (others => '0'),
          i_hw_set          => (others => '0'),
          i_hw_clear        => (others => '0'),
          i_value           => i_register_0_bit_field_6,
          i_mask            => (others => '1'),
          o_value           => o_register_0_bit_field_6,
          o_value_unmasked  => open
        );
    end block;
  end block;
  g_register_1: block
    signal bit_field_valid: std_logic;
    signal bit_field_read_mask: std_logic_vector(31 downto 0);
    signal bit_field_write_mask: std_logic_vector(31 downto 0);
    signal bit_field_write_data: std_logic_vector(31 downto 0);
    signal bit_field_read_data: std_logic_vector(31 downto 0);
    signal bit_field_value: std_logic_vector(31 downto 0);
  begin
    \g_tie_off\: for \__i\ in 0 to 31 generate
      g: if (bit_slice(x"00000001", \__i\) = '0') generate
        bit_field_read_data(\__i\) <= '0';
        bit_field_value(\__i\) <= '0';
      end generate;
    end generate;
    u_register: entity work.rggen_default_register
      generic map (
        READABLE        => true,
        WRITABLE        => true,
        ADDRESS_WIDTH   => 8,
        OFFSET_ADDRESS  => x"04",
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
        o_register_active       => register_active(1),
        o_register_ready        => register_ready(1),
        o_register_status       => register_status(3 downto 2),
        o_register_read_data    => register_read_data(63 downto 32),
        o_register_value        => register_value(95 downto 64),
        o_bit_field_valid       => bit_field_valid,
        o_bit_field_read_mask   => bit_field_read_mask,
        o_bit_field_write_mask  => bit_field_write_mask,
        o_bit_field_write_data  => bit_field_write_data,
        i_bit_field_read_data   => bit_field_read_data,
        i_bit_field_value       => bit_field_value
      );
    g_register_1: block
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
          o_value           => o_register_1,
          o_value_unmasked  => open
        );
    end block;
  end block;
  g_register_2: block
    signal bit_field_valid: std_logic;
    signal bit_field_read_mask: std_logic_vector(31 downto 0);
    signal bit_field_write_mask: std_logic_vector(31 downto 0);
    signal bit_field_write_data: std_logic_vector(31 downto 0);
    signal bit_field_read_data: std_logic_vector(31 downto 0);
    signal bit_field_value: std_logic_vector(31 downto 0);
  begin
    \g_tie_off\: for \__i\ in 0 to 31 generate
      g: if (bit_slice(x"00ffff0f", \__i\) = '0') generate
        bit_field_read_data(\__i\) <= '0';
        bit_field_value(\__i\) <= '0';
      end generate;
    end generate;
    u_register: entity work.rggen_default_register
      generic map (
        READABLE        => true,
        WRITABLE        => false,
        ADDRESS_WIDTH   => 8,
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
        o_register_active       => register_active(2),
        o_register_ready        => register_ready(2),
        o_register_status       => register_status(5 downto 4),
        o_register_read_data    => register_read_data(95 downto 64),
        o_register_value        => register_value(159 downto 128),
        o_bit_field_valid       => bit_field_valid,
        o_bit_field_read_mask   => bit_field_read_mask,
        o_bit_field_write_mask  => bit_field_write_mask,
        o_bit_field_write_data  => bit_field_write_data,
        i_bit_field_read_data   => bit_field_read_data,
        i_bit_field_value       => bit_field_value
      );
    g_bit_field_0: block
    begin
      u_bit_field: entity work.rggen_bit_field
        generic map (
          WIDTH               => 4,
          STORAGE             => false,
          EXTERNAL_READ_DATA  => true,
          TRIGGER             => false
        )
        port map (
          i_clk             => i_clk,
          i_rst_n           => i_rst_n,
          i_sw_valid        => bit_field_valid,
          i_sw_read_mask    => bit_field_read_mask(3 downto 0),
          i_sw_write_enable => "0",
          i_sw_write_mask   => bit_field_write_mask(3 downto 0),
          i_sw_write_data   => bit_field_write_data(3 downto 0),
          o_sw_read_data    => bit_field_read_data(3 downto 0),
          o_sw_value        => bit_field_value(3 downto 0),
          o_write_trigger   => open,
          o_read_trigger    => open,
          i_hw_write_enable => "0",
          i_hw_write_data   => (others => '0'),
          i_hw_set          => (others => '0'),
          i_hw_clear        => (others => '0'),
          i_value           => i_register_2_bit_field_0,
          i_mask            => (others => '1'),
          o_value           => open,
          o_value_unmasked  => open
        );
    end block;
    g_bit_field_1: block
    begin
      u_bit_field: entity work.rggen_bit_field
        generic map (
          WIDTH               => 8,
          STORAGE             => false,
          EXTERNAL_READ_DATA  => true
        )
        port map (
          i_clk             => '0',
          i_rst_n           => '0',
          i_sw_valid        => bit_field_valid,
          i_sw_read_mask    => bit_field_read_mask(15 downto 8),
          i_sw_write_enable => "0",
          i_sw_write_mask   => bit_field_write_mask(15 downto 8),
          i_sw_write_data   => bit_field_write_data(15 downto 8),
          o_sw_read_data    => bit_field_read_data(15 downto 8),
          o_sw_value        => bit_field_value(15 downto 8),
          o_write_trigger   => open,
          o_read_trigger    => open,
          i_hw_write_enable => "0",
          i_hw_write_data   => (others => '0'),
          i_hw_set          => (others => '0'),
          i_hw_clear        => (others => '0'),
          i_value           => slice(x"ab", 8, 0),
          i_mask            => (others => '1'),
          o_value           => open,
          o_value_unmasked  => open
        );
    end block;
    g_bit_field_2: block
    begin
      u_bit_field: entity work.rggen_bit_field
        generic map (
          WIDTH           => 4,
          INITIAL_VALUE   => slice(x"0", 4, 0),
          SW_WRITE_ACTION => RGGEN_WRITE_NONE
        )
        port map (
          i_clk             => i_clk,
          i_rst_n           => i_rst_n,
          i_sw_valid        => bit_field_valid,
          i_sw_read_mask    => bit_field_read_mask(19 downto 16),
          i_sw_write_enable => "1",
          i_sw_write_mask   => bit_field_write_mask(19 downto 16),
          i_sw_write_data   => bit_field_write_data(19 downto 16),
          o_sw_read_data    => bit_field_read_data(19 downto 16),
          o_sw_value        => bit_field_value(19 downto 16),
          o_write_trigger   => open,
          o_read_trigger    => open,
          i_hw_write_enable => i_register_2_bit_field_2_latch,
          i_hw_write_data   => i_register_2_bit_field_2,
          i_hw_set          => (others => '0'),
          i_hw_clear        => (others => '0'),
          i_value           => (others => '0'),
          i_mask            => (others => '1'),
          o_value           => o_register_2_bit_field_2,
          o_value_unmasked  => open
        );
    end block;
    g_bit_field_3: block
    begin
      u_bit_field: entity work.rggen_bit_field
        generic map (
          WIDTH           => 4,
          INITIAL_VALUE   => slice(x"0", 4, 0),
          SW_WRITE_ACTION => RGGEN_WRITE_NONE
        )
        port map (
          i_clk             => i_clk,
          i_rst_n           => i_rst_n,
          i_sw_valid        => bit_field_valid,
          i_sw_read_mask    => bit_field_read_mask(23 downto 20),
          i_sw_write_enable => "1",
          i_sw_write_mask   => bit_field_write_mask(23 downto 20),
          i_sw_write_data   => bit_field_write_data(23 downto 20),
          o_sw_read_data    => bit_field_read_data(23 downto 20),
          o_sw_value        => bit_field_value(23 downto 20),
          o_write_trigger   => open,
          o_read_trigger    => open,
          i_hw_write_enable => register_value(208 downto 208),
          i_hw_write_data   => i_register_2_bit_field_3,
          i_hw_set          => (others => '0'),
          i_hw_clear        => (others => '0'),
          i_value           => (others => '0'),
          i_mask            => (others => '1'),
          o_value           => o_register_2_bit_field_3,
          o_value_unmasked  => open
        );
    end block;
  end block;
  g_register_3: block
    signal bit_field_valid: std_logic;
    signal bit_field_read_mask: std_logic_vector(31 downto 0);
    signal bit_field_write_mask: std_logic_vector(31 downto 0);
    signal bit_field_write_data: std_logic_vector(31 downto 0);
    signal bit_field_read_data: std_logic_vector(31 downto 0);
    signal bit_field_value: std_logic_vector(31 downto 0);
  begin
    \g_tie_off\: for \__i\ in 0 to 31 generate
      g: if (bit_slice(x"000f0fff", \__i\) = '0') generate
        bit_field_read_data(\__i\) <= '0';
        bit_field_value(\__i\) <= '0';
      end generate;
    end generate;
    u_register: entity work.rggen_default_register
      generic map (
        READABLE        => false,
        WRITABLE        => true,
        ADDRESS_WIDTH   => 8,
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
        o_register_value        => register_value(223 downto 192),
        o_bit_field_valid       => bit_field_valid,
        o_bit_field_read_mask   => bit_field_read_mask,
        o_bit_field_write_mask  => bit_field_write_mask,
        o_bit_field_write_data  => bit_field_write_data,
        i_bit_field_read_data   => bit_field_read_data,
        i_bit_field_value       => bit_field_value
      );
    g_bit_field_0: block
    begin
      u_bit_field: entity work.rggen_bit_field
        generic map (
          WIDTH           => 4,
          INITIAL_VALUE   => slice(x"0", 4, 0),
          SW_READ_ACTION  => RGGEN_READ_NONE,
          SW_WRITE_ONCE   => false,
          TRIGGER         => false
        )
        port map (
          i_clk             => i_clk,
          i_rst_n           => i_rst_n,
          i_sw_valid        => bit_field_valid,
          i_sw_read_mask    => bit_field_read_mask(3 downto 0),
          i_sw_write_enable => "1",
          i_sw_write_mask   => bit_field_write_mask(3 downto 0),
          i_sw_write_data   => bit_field_write_data(3 downto 0),
          o_sw_read_data    => bit_field_read_data(3 downto 0),
          o_sw_value        => bit_field_value(3 downto 0),
          o_write_trigger   => open,
          o_read_trigger    => open,
          i_hw_write_enable => "0",
          i_hw_write_data   => (others => '0'),
          i_hw_set          => (others => '0'),
          i_hw_clear        => (others => '0'),
          i_value           => (others => '0'),
          i_mask            => (others => '1'),
          o_value           => o_register_3_bit_field_0,
          o_value_unmasked  => open
        );
    end block;
    g_bit_field_1: block
    begin
      u_bit_field: entity work.rggen_bit_field
        generic map (
          WIDTH           => 4,
          INITIAL_VALUE   => slice(x"0", 4, 0),
          SW_READ_ACTION  => RGGEN_READ_NONE,
          SW_WRITE_ONCE   => true,
          TRIGGER         => false
        )
        port map (
          i_clk             => i_clk,
          i_rst_n           => i_rst_n,
          i_sw_valid        => bit_field_valid,
          i_sw_read_mask    => bit_field_read_mask(7 downto 4),
          i_sw_write_enable => "1",
          i_sw_write_mask   => bit_field_write_mask(7 downto 4),
          i_sw_write_data   => bit_field_write_data(7 downto 4),
          o_sw_read_data    => bit_field_read_data(7 downto 4),
          o_sw_value        => bit_field_value(7 downto 4),
          o_write_trigger   => open,
          o_read_trigger    => open,
          i_hw_write_enable => "0",
          i_hw_write_data   => (others => '0'),
          i_hw_set          => (others => '0'),
          i_hw_clear        => (others => '0'),
          i_value           => (others => '0'),
          i_mask            => (others => '1'),
          o_value           => o_register_3_bit_field_1,
          o_value_unmasked  => open
        );
    end block;
    g_bit_field_2: block
    begin
      u_bit_field: entity work.rggen_bit_field_w01trg
        generic map (
          WRITE_ONE_TRIGGER => false,
          WIDTH             => 4
        )
        port map (
          i_clk             => i_clk,
          i_rst_n           => i_rst_n,
          i_sw_valid        => bit_field_valid,
          i_sw_read_mask    => bit_field_read_mask(11 downto 8),
          i_sw_write_enable => "1",
          i_sw_write_mask   => bit_field_write_mask(11 downto 8),
          i_sw_write_data   => bit_field_write_data(11 downto 8),
          o_sw_read_data    => bit_field_read_data(11 downto 8),
          o_sw_value        => bit_field_value(11 downto 8),
          i_value           => (others => '0'),
          o_trigger         => o_register_3_bit_field_2_trigger
        );
    end block;
    g_bit_field_3: block
    begin
      u_bit_field: entity work.rggen_bit_field_w01trg
        generic map (
          WRITE_ONE_TRIGGER => true,
          WIDTH             => 4
        )
        port map (
          i_clk             => i_clk,
          i_rst_n           => i_rst_n,
          i_sw_valid        => bit_field_valid,
          i_sw_read_mask    => bit_field_read_mask(19 downto 16),
          i_sw_write_enable => "1",
          i_sw_write_mask   => bit_field_write_mask(19 downto 16),
          i_sw_write_data   => bit_field_write_data(19 downto 16),
          o_sw_read_data    => bit_field_read_data(19 downto 16),
          o_sw_value        => bit_field_value(19 downto 16),
          i_value           => (others => '0'),
          o_trigger         => o_register_3_bit_field_3_trigger
        );
    end block;
  end block;
  g_register_4: block
    signal bit_field_valid: std_logic;
    signal bit_field_read_mask: std_logic_vector(31 downto 0);
    signal bit_field_write_mask: std_logic_vector(31 downto 0);
    signal bit_field_write_data: std_logic_vector(31 downto 0);
    signal bit_field_read_data: std_logic_vector(31 downto 0);
    signal bit_field_value: std_logic_vector(31 downto 0);
  begin
    \g_tie_off\: for \__i\ in 0 to 31 generate
      g: if (bit_slice(x"000fff0f", \__i\) = '0') generate
        bit_field_read_data(\__i\) <= '0';
        bit_field_value(\__i\) <= '0';
      end generate;
    end generate;
    u_register: entity work.rggen_default_register
      generic map (
        READABLE        => true,
        WRITABLE        => false,
        ADDRESS_WIDTH   => 8,
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
        o_register_active       => register_active(4),
        o_register_ready        => register_ready(4),
        o_register_status       => register_status(9 downto 8),
        o_register_read_data    => register_read_data(159 downto 128),
        o_register_value        => register_value(287 downto 256),
        o_bit_field_valid       => bit_field_valid,
        o_bit_field_read_mask   => bit_field_read_mask,
        o_bit_field_write_mask  => bit_field_write_mask,
        o_bit_field_write_data  => bit_field_write_data,
        i_bit_field_read_data   => bit_field_read_data,
        i_bit_field_value       => bit_field_value
      );
    g_bit_field_0: block
    begin
      u_bit_field: entity work.rggen_bit_field
        generic map (
          WIDTH           => 4,
          INITIAL_VALUE   => slice(x"0", 4, 0),
          SW_READ_ACTION  => RGGEN_READ_CLEAR,
          SW_WRITE_ACTION => RGGEN_WRITE_NONE,
          HW_SET_WIDTH    => 4
        )
        port map (
          i_clk             => i_clk,
          i_rst_n           => i_rst_n,
          i_sw_valid        => bit_field_valid,
          i_sw_read_mask    => bit_field_read_mask(3 downto 0),
          i_sw_write_enable => "0",
          i_sw_write_mask   => bit_field_write_mask(3 downto 0),
          i_sw_write_data   => bit_field_write_data(3 downto 0),
          o_sw_read_data    => bit_field_read_data(3 downto 0),
          o_sw_value        => bit_field_value(3 downto 0),
          o_write_trigger   => open,
          o_read_trigger    => open,
          i_hw_write_enable => "0",
          i_hw_write_data   => (others => '0'),
          i_hw_set          => i_register_4_bit_field_0_set,
          i_hw_clear        => (others => '0'),
          i_value           => (others => '0'),
          i_mask            => (others => '1'),
          o_value           => o_register_4_bit_field_0,
          o_value_unmasked  => open
        );
    end block;
    g_bit_field_1: block
    begin
      u_bit_field: entity work.rggen_bit_field
        generic map (
          WIDTH           => 4,
          INITIAL_VALUE   => slice(x"0", 4, 0),
          SW_READ_ACTION  => RGGEN_READ_CLEAR,
          SW_WRITE_ACTION => RGGEN_WRITE_NONE,
          HW_SET_WIDTH    => 4
        )
        port map (
          i_clk             => i_clk,
          i_rst_n           => i_rst_n,
          i_sw_valid        => bit_field_valid,
          i_sw_read_mask    => bit_field_read_mask(11 downto 8),
          i_sw_write_enable => "0",
          i_sw_write_mask   => bit_field_write_mask(11 downto 8),
          i_sw_write_data   => bit_field_write_data(11 downto 8),
          o_sw_read_data    => bit_field_read_data(11 downto 8),
          o_sw_value        => bit_field_value(11 downto 8),
          o_write_trigger   => open,
          o_read_trigger    => open,
          i_hw_write_enable => "0",
          i_hw_write_data   => (others => '0'),
          i_hw_set          => i_register_4_bit_field_1_set,
          i_hw_clear        => (others => '0'),
          i_value           => (others => '0'),
          i_mask            => register_value(3 downto 0),
          o_value           => o_register_4_bit_field_1,
          o_value_unmasked  => o_register_4_bit_field_1_unmasked
        );
    end block;
    g_bit_field_2: block
    begin
      u_bit_field: entity work.rggen_bit_field
        generic map (
          WIDTH               => 4,
          STORAGE             => false,
          EXTERNAL_READ_DATA  => true,
          TRIGGER             => false
        )
        port map (
          i_clk             => i_clk,
          i_rst_n           => i_rst_n,
          i_sw_valid        => bit_field_valid,
          i_sw_read_mask    => bit_field_read_mask(15 downto 12),
          i_sw_write_enable => "0",
          i_sw_write_mask   => bit_field_write_mask(15 downto 12),
          i_sw_write_data   => bit_field_write_data(15 downto 12),
          o_sw_read_data    => bit_field_read_data(15 downto 12),
          o_sw_value        => bit_field_value(15 downto 12),
          o_write_trigger   => open,
          o_read_trigger    => open,
          i_hw_write_enable => "0",
          i_hw_write_data   => (others => '0'),
          i_hw_set          => (others => '0'),
          i_hw_clear        => (others => '0'),
          i_value           => register_value(267 downto 264),
          i_mask            => (others => '1'),
          o_value           => open,
          o_value_unmasked  => open
        );
    end block;
    g_bit_field_3: block
    begin
      u_bit_field: entity work.rggen_bit_field
        generic map (
          WIDTH           => 4,
          INITIAL_VALUE   => slice(x"0", 4, 0),
          SW_READ_ACTION  => RGGEN_READ_SET,
          SW_WRITE_ACTION => RGGEN_WRITE_NONE,
          HW_CLEAR_WIDTH  => 4
        )
        port map (
          i_clk             => i_clk,
          i_rst_n           => i_rst_n,
          i_sw_valid        => bit_field_valid,
          i_sw_read_mask    => bit_field_read_mask(19 downto 16),
          i_sw_write_enable => "0",
          i_sw_write_mask   => bit_field_write_mask(19 downto 16),
          i_sw_write_data   => bit_field_write_data(19 downto 16),
          o_sw_read_data    => bit_field_read_data(19 downto 16),
          o_sw_value        => bit_field_value(19 downto 16),
          o_write_trigger   => open,
          o_read_trigger    => open,
          i_hw_write_enable => "0",
          i_hw_write_data   => (others => '0'),
          i_hw_set          => (others => '0'),
          i_hw_clear        => i_register_4_bit_field_3_clear,
          i_value           => (others => '0'),
          i_mask            => (others => '1'),
          o_value           => o_register_4_bit_field_3,
          o_value_unmasked  => open
        );
    end block;
  end block;
  g_register_5: block
    signal bit_field_valid: std_logic;
    signal bit_field_read_mask: std_logic_vector(31 downto 0);
    signal bit_field_write_mask: std_logic_vector(31 downto 0);
    signal bit_field_write_data: std_logic_vector(31 downto 0);
    signal bit_field_read_data: std_logic_vector(31 downto 0);
    signal bit_field_value: std_logic_vector(31 downto 0);
  begin
    \g_tie_off\: for \__i\ in 0 to 31 generate
      g: if (bit_slice(x"003f3fff", \__i\) = '0') generate
        bit_field_read_data(\__i\) <= '0';
        bit_field_value(\__i\) <= '0';
      end generate;
    end generate;
    u_register: entity work.rggen_default_register
      generic map (
        READABLE        => true,
        WRITABLE        => true,
        ADDRESS_WIDTH   => 8,
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
        o_register_active       => register_active(5),
        o_register_ready        => register_ready(5),
        o_register_status       => register_status(11 downto 10),
        o_register_read_data    => register_read_data(191 downto 160),
        o_register_value        => register_value(351 downto 320),
        o_bit_field_valid       => bit_field_valid,
        o_bit_field_read_mask   => bit_field_read_mask,
        o_bit_field_write_mask  => bit_field_write_mask,
        o_bit_field_write_data  => bit_field_write_data,
        i_bit_field_read_data   => bit_field_read_data,
        i_bit_field_value       => bit_field_value
      );
    g_bit_field_0: block
    begin
      u_bit_field: entity work.rggen_bit_field
        generic map (
          WIDTH           => 2,
          INITIAL_VALUE   => slice(x"0", 2, 0),
          HW_CLEAR_WIDTH  => 1
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
          i_hw_clear        => i_register_5_bit_field_0_clear,
          i_value           => (others => '0'),
          i_mask            => (others => '1'),
          o_value           => o_register_5_bit_field_0,
          o_value_unmasked  => open
        );
    end block;
    g_bit_field_1: block
    begin
      u_bit_field: entity work.rggen_bit_field
        generic map (
          WIDTH           => 2,
          INITIAL_VALUE   => slice(x"0", 2, 0),
          HW_CLEAR_WIDTH  => 1
        )
        port map (
          i_clk             => i_clk,
          i_rst_n           => i_rst_n,
          i_sw_valid        => bit_field_valid,
          i_sw_read_mask    => bit_field_read_mask(3 downto 2),
          i_sw_write_enable => "1",
          i_sw_write_mask   => bit_field_write_mask(3 downto 2),
          i_sw_write_data   => bit_field_write_data(3 downto 2),
          o_sw_read_data    => bit_field_read_data(3 downto 2),
          o_sw_value        => bit_field_value(3 downto 2),
          o_write_trigger   => open,
          o_read_trigger    => open,
          i_hw_write_enable => "0",
          i_hw_write_data   => (others => '0'),
          i_hw_set          => (others => '0'),
          i_hw_clear        => register_value(200 downto 200),
          i_value           => (others => '0'),
          i_mask            => (others => '1'),
          o_value           => o_register_5_bit_field_1,
          o_value_unmasked  => open
        );
    end block;
    g_bit_field_2: block
    begin
      u_bit_field: entity work.rggen_bit_field
        generic map (
          WIDTH         => 2,
          INITIAL_VALUE => slice(x"0", 2, 0)
        )
        port map (
          i_clk             => i_clk,
          i_rst_n           => i_rst_n,
          i_sw_valid        => bit_field_valid,
          i_sw_read_mask    => bit_field_read_mask(5 downto 4),
          i_sw_write_enable => "1",
          i_sw_write_mask   => bit_field_write_mask(5 downto 4),
          i_sw_write_data   => bit_field_write_data(5 downto 4),
          o_sw_read_data    => bit_field_read_data(5 downto 4),
          o_sw_value        => bit_field_value(5 downto 4),
          o_write_trigger   => open,
          o_read_trigger    => open,
          i_hw_write_enable => i_register_5_bit_field_2_set,
          i_hw_write_data   => i_register_5_bit_field_2,
          i_hw_set          => (others => '0'),
          i_hw_clear        => (others => '0'),
          i_value           => (others => '0'),
          i_mask            => (others => '1'),
          o_value           => o_register_5_bit_field_2,
          o_value_unmasked  => open
        );
    end block;
    g_bit_field_3: block
    begin
      u_bit_field: entity work.rggen_bit_field
        generic map (
          WIDTH         => 2,
          INITIAL_VALUE => slice(x"0", 2, 0)
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
          i_hw_write_enable => register_value(208 downto 208),
          i_hw_write_data   => i_register_5_bit_field_3,
          i_hw_set          => (others => '0'),
          i_hw_clear        => (others => '0'),
          i_value           => (others => '0'),
          i_mask            => (others => '1'),
          o_value           => o_register_5_bit_field_3,
          o_value_unmasked  => open
        );
    end block;
    g_bit_field_4: block
    begin
      u_bit_field: entity work.rggen_bit_field
        generic map (
          WIDTH                     => 2,
          INITIAL_VALUE             => slice(x"0", 2, 0),
          SW_WRITE_ENABLE_POLARITY  => RGGEN_ACTIVE_HIGH
        )
        port map (
          i_clk             => i_clk,
          i_rst_n           => i_rst_n,
          i_sw_valid        => bit_field_valid,
          i_sw_read_mask    => bit_field_read_mask(9 downto 8),
          i_sw_write_enable => i_register_5_bit_field_4_enable,
          i_sw_write_mask   => bit_field_write_mask(9 downto 8),
          i_sw_write_data   => bit_field_write_data(9 downto 8),
          o_sw_read_data    => bit_field_read_data(9 downto 8),
          o_sw_value        => bit_field_value(9 downto 8),
          o_write_trigger   => open,
          o_read_trigger    => open,
          i_hw_write_enable => "0",
          i_hw_write_data   => (others => '0'),
          i_hw_set          => (others => '0'),
          i_hw_clear        => (others => '0'),
          i_value           => (others => '0'),
          i_mask            => (others => '1'),
          o_value           => o_register_5_bit_field_4,
          o_value_unmasked  => open
        );
    end block;
    g_bit_field_5: block
    begin
      u_bit_field: entity work.rggen_bit_field
        generic map (
          WIDTH                     => 2,
          INITIAL_VALUE             => slice(x"0", 2, 0),
          SW_WRITE_ENABLE_POLARITY  => RGGEN_ACTIVE_HIGH
        )
        port map (
          i_clk             => i_clk,
          i_rst_n           => i_rst_n,
          i_sw_valid        => bit_field_valid,
          i_sw_read_mask    => bit_field_read_mask(11 downto 10),
          i_sw_write_enable => register_value(8 downto 8),
          i_sw_write_mask   => bit_field_write_mask(11 downto 10),
          i_sw_write_data   => bit_field_write_data(11 downto 10),
          o_sw_read_data    => bit_field_read_data(11 downto 10),
          o_sw_value        => bit_field_value(11 downto 10),
          o_write_trigger   => open,
          o_read_trigger    => open,
          i_hw_write_enable => "0",
          i_hw_write_data   => (others => '0'),
          i_hw_set          => (others => '0'),
          i_hw_clear        => (others => '0'),
          i_value           => (others => '0'),
          i_mask            => (others => '1'),
          o_value           => o_register_5_bit_field_5,
          o_value_unmasked  => open
        );
    end block;
    g_bit_field_6: block
    begin
      u_bit_field: entity work.rggen_bit_field
        generic map (
          WIDTH                     => 2,
          INITIAL_VALUE             => slice(x"0", 2, 0),
          SW_WRITE_ENABLE_POLARITY  => RGGEN_ACTIVE_HIGH
        )
        port map (
          i_clk             => i_clk,
          i_rst_n           => i_rst_n,
          i_sw_valid        => bit_field_valid,
          i_sw_read_mask    => bit_field_read_mask(13 downto 12),
          i_sw_write_enable => register_value(64 downto 64),
          i_sw_write_mask   => bit_field_write_mask(13 downto 12),
          i_sw_write_data   => bit_field_write_data(13 downto 12),
          o_sw_read_data    => bit_field_read_data(13 downto 12),
          o_sw_value        => bit_field_value(13 downto 12),
          o_write_trigger   => open,
          o_read_trigger    => open,
          i_hw_write_enable => "0",
          i_hw_write_data   => (others => '0'),
          i_hw_set          => (others => '0'),
          i_hw_clear        => (others => '0'),
          i_value           => (others => '0'),
          i_mask            => (others => '1'),
          o_value           => o_register_5_bit_field_6,
          o_value_unmasked  => open
        );
    end block;
    g_bit_field_7: block
    begin
      u_bit_field: entity work.rggen_bit_field
        generic map (
          WIDTH                     => 2,
          INITIAL_VALUE             => slice(x"0", 2, 0),
          SW_WRITE_ENABLE_POLARITY  => RGGEN_ACTIVE_LOW
        )
        port map (
          i_clk             => i_clk,
          i_rst_n           => i_rst_n,
          i_sw_valid        => bit_field_valid,
          i_sw_read_mask    => bit_field_read_mask(17 downto 16),
          i_sw_write_enable => i_register_5_bit_field_7_lock,
          i_sw_write_mask   => bit_field_write_mask(17 downto 16),
          i_sw_write_data   => bit_field_write_data(17 downto 16),
          o_sw_read_data    => bit_field_read_data(17 downto 16),
          o_sw_value        => bit_field_value(17 downto 16),
          o_write_trigger   => open,
          o_read_trigger    => open,
          i_hw_write_enable => "0",
          i_hw_write_data   => (others => '0'),
          i_hw_set          => (others => '0'),
          i_hw_clear        => (others => '0'),
          i_value           => (others => '0'),
          i_mask            => (others => '1'),
          o_value           => o_register_5_bit_field_7,
          o_value_unmasked  => open
        );
    end block;
    g_bit_field_8: block
    begin
      u_bit_field: entity work.rggen_bit_field
        generic map (
          WIDTH                     => 2,
          INITIAL_VALUE             => slice(x"0", 2, 0),
          SW_WRITE_ENABLE_POLARITY  => RGGEN_ACTIVE_LOW
        )
        port map (
          i_clk             => i_clk,
          i_rst_n           => i_rst_n,
          i_sw_valid        => bit_field_valid,
          i_sw_read_mask    => bit_field_read_mask(19 downto 18),
          i_sw_write_enable => register_value(8 downto 8),
          i_sw_write_mask   => bit_field_write_mask(19 downto 18),
          i_sw_write_data   => bit_field_write_data(19 downto 18),
          o_sw_read_data    => bit_field_read_data(19 downto 18),
          o_sw_value        => bit_field_value(19 downto 18),
          o_write_trigger   => open,
          o_read_trigger    => open,
          i_hw_write_enable => "0",
          i_hw_write_data   => (others => '0'),
          i_hw_set          => (others => '0'),
          i_hw_clear        => (others => '0'),
          i_value           => (others => '0'),
          i_mask            => (others => '1'),
          o_value           => o_register_5_bit_field_8,
          o_value_unmasked  => open
        );
    end block;
    g_bit_field_9: block
    begin
      u_bit_field: entity work.rggen_bit_field
        generic map (
          WIDTH                     => 2,
          INITIAL_VALUE             => slice(x"0", 2, 0),
          SW_WRITE_ENABLE_POLARITY  => RGGEN_ACTIVE_LOW
        )
        port map (
          i_clk             => i_clk,
          i_rst_n           => i_rst_n,
          i_sw_valid        => bit_field_valid,
          i_sw_read_mask    => bit_field_read_mask(21 downto 20),
          i_sw_write_enable => register_value(64 downto 64),
          i_sw_write_mask   => bit_field_write_mask(21 downto 20),
          i_sw_write_data   => bit_field_write_data(21 downto 20),
          o_sw_read_data    => bit_field_read_data(21 downto 20),
          o_sw_value        => bit_field_value(21 downto 20),
          o_write_trigger   => open,
          o_read_trigger    => open,
          i_hw_write_enable => "0",
          i_hw_write_data   => (others => '0'),
          i_hw_set          => (others => '0'),
          i_hw_clear        => (others => '0'),
          i_value           => (others => '0'),
          i_mask            => (others => '1'),
          o_value           => o_register_5_bit_field_9,
          o_value_unmasked  => open
        );
    end block;
  end block;
  g_register_6: block
    signal bit_field_valid: std_logic;
    signal bit_field_read_mask: std_logic_vector(63 downto 0);
    signal bit_field_write_mask: std_logic_vector(63 downto 0);
    signal bit_field_write_data: std_logic_vector(63 downto 0);
    signal bit_field_read_data: std_logic_vector(63 downto 0);
    signal bit_field_value: std_logic_vector(63 downto 0);
  begin
    \g_tie_off\: for \__i\ in 0 to 63 generate
      g: if (bit_slice(x"000000ffffffffff", \__i\) = '0') generate
        bit_field_read_data(\__i\) <= '0';
        bit_field_value(\__i\) <= '0';
      end generate;
    end generate;
    u_register: entity work.rggen_default_register
      generic map (
        READABLE        => true,
        WRITABLE        => true,
        ADDRESS_WIDTH   => 8,
        OFFSET_ADDRESS  => x"14",
        BUS_WIDTH       => 32,
        DATA_WIDTH      => 64
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
        o_register_value        => register_value(447 downto 384),
        o_bit_field_valid       => bit_field_valid,
        o_bit_field_read_mask   => bit_field_read_mask,
        o_bit_field_write_mask  => bit_field_write_mask,
        o_bit_field_write_data  => bit_field_write_data,
        i_bit_field_read_data   => bit_field_read_data,
        i_bit_field_value       => bit_field_value
      );
    g_bit_field_0: block
    begin
      u_bit_field: entity work.rggen_bit_field
        generic map (
          WIDTH           => 4,
          INITIAL_VALUE   => slice(x"0", 4, 0),
          SW_READ_ACTION  => RGGEN_READ_DEFAULT,
          SW_WRITE_ACTION => RGGEN_WRITE_0_CLEAR,
          HW_SET_WIDTH    => 4
        )
        port map (
          i_clk             => i_clk,
          i_rst_n           => i_rst_n,
          i_sw_valid        => bit_field_valid,
          i_sw_read_mask    => bit_field_read_mask(3 downto 0),
          i_sw_write_enable => "1",
          i_sw_write_mask   => bit_field_write_mask(3 downto 0),
          i_sw_write_data   => bit_field_write_data(3 downto 0),
          o_sw_read_data    => bit_field_read_data(3 downto 0),
          o_sw_value        => bit_field_value(3 downto 0),
          o_write_trigger   => open,
          o_read_trigger    => open,
          i_hw_write_enable => "0",
          i_hw_write_data   => (others => '0'),
          i_hw_set          => i_register_6_bit_field_0_set,
          i_hw_clear        => (others => '0'),
          i_value           => (others => '0'),
          i_mask            => (others => '1'),
          o_value           => o_register_6_bit_field_0,
          o_value_unmasked  => open
        );
    end block;
    g_bit_field_1: block
    begin
      u_bit_field: entity work.rggen_bit_field
        generic map (
          WIDTH           => 4,
          INITIAL_VALUE   => slice(x"0", 4, 0),
          SW_READ_ACTION  => RGGEN_READ_DEFAULT,
          SW_WRITE_ACTION => RGGEN_WRITE_0_CLEAR,
          HW_SET_WIDTH    => 4
        )
        port map (
          i_clk             => i_clk,
          i_rst_n           => i_rst_n,
          i_sw_valid        => bit_field_valid,
          i_sw_read_mask    => bit_field_read_mask(7 downto 4),
          i_sw_write_enable => "1",
          i_sw_write_mask   => bit_field_write_mask(7 downto 4),
          i_sw_write_data   => bit_field_write_data(7 downto 4),
          o_sw_read_data    => bit_field_read_data(7 downto 4),
          o_sw_value        => bit_field_value(7 downto 4),
          o_write_trigger   => open,
          o_read_trigger    => open,
          i_hw_write_enable => "0",
          i_hw_write_data   => (others => '0'),
          i_hw_set          => i_register_6_bit_field_1_set,
          i_hw_clear        => (others => '0'),
          i_value           => (others => '0'),
          i_mask            => register_value(3 downto 0),
          o_value           => o_register_6_bit_field_1,
          o_value_unmasked  => o_register_6_bit_field_1_unmasked
        );
    end block;
    g_bit_field_2: block
    begin
      u_bit_field: entity work.rggen_bit_field
        generic map (
          WIDTH               => 4,
          STORAGE             => false,
          EXTERNAL_READ_DATA  => true,
          TRIGGER             => false
        )
        port map (
          i_clk             => i_clk,
          i_rst_n           => i_rst_n,
          i_sw_valid        => bit_field_valid,
          i_sw_read_mask    => bit_field_read_mask(11 downto 8),
          i_sw_write_enable => "0",
          i_sw_write_mask   => bit_field_write_mask(11 downto 8),
          i_sw_write_data   => bit_field_write_data(11 downto 8),
          o_sw_read_data    => bit_field_read_data(11 downto 8),
          o_sw_value        => bit_field_value(11 downto 8),
          o_write_trigger   => open,
          o_read_trigger    => open,
          i_hw_write_enable => "0",
          i_hw_write_data   => (others => '0'),
          i_hw_set          => (others => '0'),
          i_hw_clear        => (others => '0'),
          i_value           => register_value(391 downto 388),
          i_mask            => (others => '1'),
          o_value           => open,
          o_value_unmasked  => open
        );
    end block;
    g_bit_field_3: block
    begin
      u_bit_field: entity work.rggen_bit_field
        generic map (
          WIDTH           => 4,
          INITIAL_VALUE   => slice(x"0", 4, 0),
          SW_READ_ACTION  => RGGEN_READ_DEFAULT,
          SW_WRITE_ACTION => RGGEN_WRITE_1_CLEAR,
          HW_SET_WIDTH    => 4
        )
        port map (
          i_clk             => i_clk,
          i_rst_n           => i_rst_n,
          i_sw_valid        => bit_field_valid,
          i_sw_read_mask    => bit_field_read_mask(15 downto 12),
          i_sw_write_enable => "1",
          i_sw_write_mask   => bit_field_write_mask(15 downto 12),
          i_sw_write_data   => bit_field_write_data(15 downto 12),
          o_sw_read_data    => bit_field_read_data(15 downto 12),
          o_sw_value        => bit_field_value(15 downto 12),
          o_write_trigger   => open,
          o_read_trigger    => open,
          i_hw_write_enable => "0",
          i_hw_write_data   => (others => '0'),
          i_hw_set          => i_register_6_bit_field_3_set,
          i_hw_clear        => (others => '0'),
          i_value           => (others => '0'),
          i_mask            => (others => '1'),
          o_value           => o_register_6_bit_field_3,
          o_value_unmasked  => open
        );
    end block;
    g_bit_field_4: block
    begin
      u_bit_field: entity work.rggen_bit_field
        generic map (
          WIDTH           => 4,
          INITIAL_VALUE   => slice(x"0", 4, 0),
          SW_READ_ACTION  => RGGEN_READ_DEFAULT,
          SW_WRITE_ACTION => RGGEN_WRITE_1_CLEAR,
          HW_SET_WIDTH    => 4
        )
        port map (
          i_clk             => i_clk,
          i_rst_n           => i_rst_n,
          i_sw_valid        => bit_field_valid,
          i_sw_read_mask    => bit_field_read_mask(19 downto 16),
          i_sw_write_enable => "1",
          i_sw_write_mask   => bit_field_write_mask(19 downto 16),
          i_sw_write_data   => bit_field_write_data(19 downto 16),
          o_sw_read_data    => bit_field_read_data(19 downto 16),
          o_sw_value        => bit_field_value(19 downto 16),
          o_write_trigger   => open,
          o_read_trigger    => open,
          i_hw_write_enable => "0",
          i_hw_write_data   => (others => '0'),
          i_hw_set          => i_register_6_bit_field_4_set,
          i_hw_clear        => (others => '0'),
          i_value           => (others => '0'),
          i_mask            => register_value(3 downto 0),
          o_value           => o_register_6_bit_field_4,
          o_value_unmasked  => o_register_6_bit_field_4_unmasked
        );
    end block;
    g_bit_field_5: block
    begin
      u_bit_field: entity work.rggen_bit_field
        generic map (
          WIDTH               => 4,
          STORAGE             => false,
          EXTERNAL_READ_DATA  => true,
          TRIGGER             => false
        )
        port map (
          i_clk             => i_clk,
          i_rst_n           => i_rst_n,
          i_sw_valid        => bit_field_valid,
          i_sw_read_mask    => bit_field_read_mask(23 downto 20),
          i_sw_write_enable => "0",
          i_sw_write_mask   => bit_field_write_mask(23 downto 20),
          i_sw_write_data   => bit_field_write_data(23 downto 20),
          o_sw_read_data    => bit_field_read_data(23 downto 20),
          o_sw_value        => bit_field_value(23 downto 20),
          o_write_trigger   => open,
          o_read_trigger    => open,
          i_hw_write_enable => "0",
          i_hw_write_data   => (others => '0'),
          i_hw_set          => (others => '0'),
          i_hw_clear        => (others => '0'),
          i_value           => register_value(403 downto 400),
          i_mask            => (others => '1'),
          o_value           => open,
          o_value_unmasked  => open
        );
    end block;
    g_bit_field_6: block
    begin
      u_bit_field: entity work.rggen_bit_field
        generic map (
          WIDTH           => 4,
          INITIAL_VALUE   => slice(x"0", 4, 0),
          SW_READ_ACTION  => RGGEN_READ_DEFAULT,
          SW_WRITE_ACTION => RGGEN_WRITE_0_SET,
          HW_CLEAR_WIDTH  => 4
        )
        port map (
          i_clk             => i_clk,
          i_rst_n           => i_rst_n,
          i_sw_valid        => bit_field_valid,
          i_sw_read_mask    => bit_field_read_mask(27 downto 24),
          i_sw_write_enable => "1",
          i_sw_write_mask   => bit_field_write_mask(27 downto 24),
          i_sw_write_data   => bit_field_write_data(27 downto 24),
          o_sw_read_data    => bit_field_read_data(27 downto 24),
          o_sw_value        => bit_field_value(27 downto 24),
          o_write_trigger   => open,
          o_read_trigger    => open,
          i_hw_write_enable => "0",
          i_hw_write_data   => (others => '0'),
          i_hw_set          => (others => '0'),
          i_hw_clear        => i_register_6_bit_field_6_clear,
          i_value           => (others => '0'),
          i_mask            => (others => '1'),
          o_value           => o_register_6_bit_field_6,
          o_value_unmasked  => open
        );
    end block;
    g_bit_field_7: block
    begin
      u_bit_field: entity work.rggen_bit_field
        generic map (
          WIDTH           => 4,
          INITIAL_VALUE   => slice(x"0", 4, 0),
          SW_READ_ACTION  => RGGEN_READ_DEFAULT,
          SW_WRITE_ACTION => RGGEN_WRITE_1_SET,
          HW_CLEAR_WIDTH  => 4
        )
        port map (
          i_clk             => i_clk,
          i_rst_n           => i_rst_n,
          i_sw_valid        => bit_field_valid,
          i_sw_read_mask    => bit_field_read_mask(31 downto 28),
          i_sw_write_enable => "1",
          i_sw_write_mask   => bit_field_write_mask(31 downto 28),
          i_sw_write_data   => bit_field_write_data(31 downto 28),
          o_sw_read_data    => bit_field_read_data(31 downto 28),
          o_sw_value        => bit_field_value(31 downto 28),
          o_write_trigger   => open,
          o_read_trigger    => open,
          i_hw_write_enable => "0",
          i_hw_write_data   => (others => '0'),
          i_hw_set          => (others => '0'),
          i_hw_clear        => i_register_6_bit_field_7_clear,
          i_value           => (others => '0'),
          i_mask            => (others => '1'),
          o_value           => o_register_6_bit_field_7,
          o_value_unmasked  => open
        );
    end block;
    g_bit_field_8: block
    begin
      u_bit_field: entity work.rggen_bit_field
        generic map (
          WIDTH           => 4,
          INITIAL_VALUE   => slice(x"0", 4, 0),
          SW_WRITE_ACTION => RGGEN_WRITE_0_TOGGLE
        )
        port map (
          i_clk             => i_clk,
          i_rst_n           => i_rst_n,
          i_sw_valid        => bit_field_valid,
          i_sw_read_mask    => bit_field_read_mask(35 downto 32),
          i_sw_write_enable => "1",
          i_sw_write_mask   => bit_field_write_mask(35 downto 32),
          i_sw_write_data   => bit_field_write_data(35 downto 32),
          o_sw_read_data    => bit_field_read_data(35 downto 32),
          o_sw_value        => bit_field_value(35 downto 32),
          o_write_trigger   => open,
          o_read_trigger    => open,
          i_hw_write_enable => "0",
          i_hw_write_data   => (others => '0'),
          i_hw_set          => (others => '0'),
          i_hw_clear        => (others => '0'),
          i_value           => (others => '0'),
          i_mask            => (others => '1'),
          o_value           => o_register_6_bit_field_8,
          o_value_unmasked  => open
        );
    end block;
    g_bit_field_9: block
    begin
      u_bit_field: entity work.rggen_bit_field
        generic map (
          WIDTH           => 4,
          INITIAL_VALUE   => slice(x"0", 4, 0),
          SW_WRITE_ACTION => RGGEN_WRITE_1_TOGGLE
        )
        port map (
          i_clk             => i_clk,
          i_rst_n           => i_rst_n,
          i_sw_valid        => bit_field_valid,
          i_sw_read_mask    => bit_field_read_mask(39 downto 36),
          i_sw_write_enable => "1",
          i_sw_write_mask   => bit_field_write_mask(39 downto 36),
          i_sw_write_data   => bit_field_write_data(39 downto 36),
          o_sw_read_data    => bit_field_read_data(39 downto 36),
          o_sw_value        => bit_field_value(39 downto 36),
          o_write_trigger   => open,
          o_read_trigger    => open,
          i_hw_write_enable => "0",
          i_hw_write_data   => (others => '0'),
          i_hw_set          => (others => '0'),
          i_hw_clear        => (others => '0'),
          i_value           => (others => '0'),
          i_mask            => (others => '1'),
          o_value           => o_register_6_bit_field_9,
          o_value_unmasked  => open
        );
    end block;
  end block;
  g_register_7: block
    signal bit_field_valid: std_logic;
    signal bit_field_read_mask: std_logic_vector(31 downto 0);
    signal bit_field_write_mask: std_logic_vector(31 downto 0);
    signal bit_field_write_data: std_logic_vector(31 downto 0);
    signal bit_field_read_data: std_logic_vector(31 downto 0);
    signal bit_field_value: std_logic_vector(31 downto 0);
  begin
    \g_tie_off\: for \__i\ in 0 to 31 generate
      g: if (bit_slice(x"0f0f0f0f", \__i\) = '0') generate
        bit_field_read_data(\__i\) <= '0';
        bit_field_value(\__i\) <= '0';
      end generate;
    end generate;
    u_register: entity work.rggen_default_register
      generic map (
        READABLE        => true,
        WRITABLE        => true,
        ADDRESS_WIDTH   => 8,
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
        o_register_active       => register_active(7),
        o_register_ready        => register_ready(7),
        o_register_status       => register_status(15 downto 14),
        o_register_read_data    => register_read_data(255 downto 224),
        o_register_value        => register_value(479 downto 448),
        o_bit_field_valid       => bit_field_valid,
        o_bit_field_read_mask   => bit_field_read_mask,
        o_bit_field_write_mask  => bit_field_write_mask,
        o_bit_field_write_data  => bit_field_write_data,
        i_bit_field_read_data   => bit_field_read_data,
        i_bit_field_value       => bit_field_value
      );
    g_bit_field_0: block
    begin
      u_bit_field: entity work.rggen_bit_field
        generic map (
          WIDTH           => 4,
          INITIAL_VALUE   => slice(x"0", 4, 0),
          SW_READ_ACTION  => RGGEN_READ_SET,
          SW_WRITE_ACTION => RGGEN_WRITE_0_CLEAR
        )
        port map (
          i_clk             => i_clk,
          i_rst_n           => i_rst_n,
          i_sw_valid        => bit_field_valid,
          i_sw_read_mask    => bit_field_read_mask(3 downto 0),
          i_sw_write_enable => "1",
          i_sw_write_mask   => bit_field_write_mask(3 downto 0),
          i_sw_write_data   => bit_field_write_data(3 downto 0),
          o_sw_read_data    => bit_field_read_data(3 downto 0),
          o_sw_value        => bit_field_value(3 downto 0),
          o_write_trigger   => open,
          o_read_trigger    => open,
          i_hw_write_enable => "0",
          i_hw_write_data   => (others => '0'),
          i_hw_set          => (others => '0'),
          i_hw_clear        => (others => '0'),
          i_value           => (others => '0'),
          i_mask            => (others => '1'),
          o_value           => o_register_7_bit_field_0,
          o_value_unmasked  => open
        );
    end block;
    g_bit_field_1: block
    begin
      u_bit_field: entity work.rggen_bit_field
        generic map (
          WIDTH           => 4,
          INITIAL_VALUE   => slice(x"0", 4, 0),
          SW_READ_ACTION  => RGGEN_READ_SET,
          SW_WRITE_ACTION => RGGEN_WRITE_1_CLEAR
        )
        port map (
          i_clk             => i_clk,
          i_rst_n           => i_rst_n,
          i_sw_valid        => bit_field_valid,
          i_sw_read_mask    => bit_field_read_mask(11 downto 8),
          i_sw_write_enable => "1",
          i_sw_write_mask   => bit_field_write_mask(11 downto 8),
          i_sw_write_data   => bit_field_write_data(11 downto 8),
          o_sw_read_data    => bit_field_read_data(11 downto 8),
          o_sw_value        => bit_field_value(11 downto 8),
          o_write_trigger   => open,
          o_read_trigger    => open,
          i_hw_write_enable => "0",
          i_hw_write_data   => (others => '0'),
          i_hw_set          => (others => '0'),
          i_hw_clear        => (others => '0'),
          i_value           => (others => '0'),
          i_mask            => (others => '1'),
          o_value           => o_register_7_bit_field_1,
          o_value_unmasked  => open
        );
    end block;
    g_bit_field_2: block
    begin
      u_bit_field: entity work.rggen_bit_field
        generic map (
          WIDTH           => 4,
          INITIAL_VALUE   => slice(x"0", 4, 0),
          SW_READ_ACTION  => RGGEN_READ_CLEAR,
          SW_WRITE_ACTION => RGGEN_WRITE_0_SET
        )
        port map (
          i_clk             => i_clk,
          i_rst_n           => i_rst_n,
          i_sw_valid        => bit_field_valid,
          i_sw_read_mask    => bit_field_read_mask(19 downto 16),
          i_sw_write_enable => "1",
          i_sw_write_mask   => bit_field_write_mask(19 downto 16),
          i_sw_write_data   => bit_field_write_data(19 downto 16),
          o_sw_read_data    => bit_field_read_data(19 downto 16),
          o_sw_value        => bit_field_value(19 downto 16),
          o_write_trigger   => open,
          o_read_trigger    => open,
          i_hw_write_enable => "0",
          i_hw_write_data   => (others => '0'),
          i_hw_set          => (others => '0'),
          i_hw_clear        => (others => '0'),
          i_value           => (others => '0'),
          i_mask            => (others => '1'),
          o_value           => o_register_7_bit_field_2,
          o_value_unmasked  => open
        );
    end block;
    g_bit_field_3: block
    begin
      u_bit_field: entity work.rggen_bit_field
        generic map (
          WIDTH           => 4,
          INITIAL_VALUE   => slice(x"0", 4, 0),
          SW_READ_ACTION  => RGGEN_READ_CLEAR,
          SW_WRITE_ACTION => RGGEN_WRITE_1_SET
        )
        port map (
          i_clk             => i_clk,
          i_rst_n           => i_rst_n,
          i_sw_valid        => bit_field_valid,
          i_sw_read_mask    => bit_field_read_mask(27 downto 24),
          i_sw_write_enable => "1",
          i_sw_write_mask   => bit_field_write_mask(27 downto 24),
          i_sw_write_data   => bit_field_write_data(27 downto 24),
          o_sw_read_data    => bit_field_read_data(27 downto 24),
          o_sw_value        => bit_field_value(27 downto 24),
          o_write_trigger   => open,
          o_read_trigger    => open,
          i_hw_write_enable => "0",
          i_hw_write_data   => (others => '0'),
          i_hw_set          => (others => '0'),
          i_hw_clear        => (others => '0'),
          i_value           => (others => '0'),
          i_mask            => (others => '1'),
          o_value           => o_register_7_bit_field_3,
          o_value_unmasked  => open
        );
    end block;
  end block;
  g_register_8: block
    signal bit_field_valid: std_logic;
    signal bit_field_read_mask: std_logic_vector(63 downto 0);
    signal bit_field_write_mask: std_logic_vector(63 downto 0);
    signal bit_field_write_data: std_logic_vector(63 downto 0);
    signal bit_field_read_data: std_logic_vector(63 downto 0);
    signal bit_field_value: std_logic_vector(63 downto 0);
  begin
    \g_tie_off\: for \__i\ in 0 to 63 generate
      g: if (bit_slice(x"00000f0f0f0f0f0f", \__i\) = '0') generate
        bit_field_read_data(\__i\) <= '0';
        bit_field_value(\__i\) <= '0';
      end generate;
    end generate;
    u_register: entity work.rggen_default_register
      generic map (
        READABLE        => true,
        WRITABLE        => true,
        ADDRESS_WIDTH   => 8,
        OFFSET_ADDRESS  => x"20",
        BUS_WIDTH       => 32,
        DATA_WIDTH      => 64
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
        o_register_value        => register_value(575 downto 512),
        o_bit_field_valid       => bit_field_valid,
        o_bit_field_read_mask   => bit_field_read_mask,
        o_bit_field_write_mask  => bit_field_write_mask,
        o_bit_field_write_data  => bit_field_write_data,
        i_bit_field_read_data   => bit_field_read_data,
        i_bit_field_value       => bit_field_value
      );
    g_bit_field_0: block
    begin
      u_bit_field: entity work.rggen_bit_field
        generic map (
          WIDTH           => 4,
          INITIAL_VALUE   => slice(x"0", 4, 0),
          SW_READ_ACTION  => RGGEN_READ_DEFAULT,
          SW_WRITE_ACTION => RGGEN_WRITE_CLEAR,
          HW_SET_WIDTH    => 4
        )
        port map (
          i_clk             => i_clk,
          i_rst_n           => i_rst_n,
          i_sw_valid        => bit_field_valid,
          i_sw_read_mask    => bit_field_read_mask(3 downto 0),
          i_sw_write_enable => "1",
          i_sw_write_mask   => bit_field_write_mask(3 downto 0),
          i_sw_write_data   => bit_field_write_data(3 downto 0),
          o_sw_read_data    => bit_field_read_data(3 downto 0),
          o_sw_value        => bit_field_value(3 downto 0),
          o_write_trigger   => open,
          o_read_trigger    => open,
          i_hw_write_enable => "0",
          i_hw_write_data   => (others => '0'),
          i_hw_set          => i_register_8_bit_field_0_set,
          i_hw_clear        => (others => '0'),
          i_value           => (others => '0'),
          i_mask            => (others => '1'),
          o_value           => o_register_8_bit_field_0,
          o_value_unmasked  => open
        );
    end block;
    g_bit_field_1: block
    begin
      u_bit_field: entity work.rggen_bit_field
        generic map (
          WIDTH           => 4,
          INITIAL_VALUE   => slice(x"0", 4, 0),
          SW_READ_ACTION  => RGGEN_READ_DEFAULT,
          SW_WRITE_ACTION => RGGEN_WRITE_SET,
          HW_CLEAR_WIDTH  => 4
        )
        port map (
          i_clk             => i_clk,
          i_rst_n           => i_rst_n,
          i_sw_valid        => bit_field_valid,
          i_sw_read_mask    => bit_field_read_mask(11 downto 8),
          i_sw_write_enable => "1",
          i_sw_write_mask   => bit_field_write_mask(11 downto 8),
          i_sw_write_data   => bit_field_write_data(11 downto 8),
          o_sw_read_data    => bit_field_read_data(11 downto 8),
          o_sw_value        => bit_field_value(11 downto 8),
          o_write_trigger   => open,
          o_read_trigger    => open,
          i_hw_write_enable => "0",
          i_hw_write_data   => (others => '0'),
          i_hw_set          => (others => '0'),
          i_hw_clear        => i_register_8_bit_field_1_clear,
          i_value           => (others => '0'),
          i_mask            => (others => '1'),
          o_value           => o_register_8_bit_field_1,
          o_value_unmasked  => open
        );
    end block;
    g_bit_field_2: block
    begin
      u_bit_field: entity work.rggen_bit_field
        generic map (
          WIDTH           => 4,
          INITIAL_VALUE   => slice(x"0", 4, 0),
          SW_READ_ACTION  => RGGEN_READ_NONE,
          SW_WRITE_ACTION => RGGEN_WRITE_CLEAR,
          HW_SET_WIDTH    => 4
        )
        port map (
          i_clk             => i_clk,
          i_rst_n           => i_rst_n,
          i_sw_valid        => bit_field_valid,
          i_sw_read_mask    => bit_field_read_mask(19 downto 16),
          i_sw_write_enable => "1",
          i_sw_write_mask   => bit_field_write_mask(19 downto 16),
          i_sw_write_data   => bit_field_write_data(19 downto 16),
          o_sw_read_data    => bit_field_read_data(19 downto 16),
          o_sw_value        => bit_field_value(19 downto 16),
          o_write_trigger   => open,
          o_read_trigger    => open,
          i_hw_write_enable => "0",
          i_hw_write_data   => (others => '0'),
          i_hw_set          => i_register_8_bit_field_2_set,
          i_hw_clear        => (others => '0'),
          i_value           => (others => '0'),
          i_mask            => (others => '1'),
          o_value           => o_register_8_bit_field_2,
          o_value_unmasked  => open
        );
    end block;
    g_bit_field_3: block
    begin
      u_bit_field: entity work.rggen_bit_field
        generic map (
          WIDTH           => 4,
          INITIAL_VALUE   => slice(x"0", 4, 0),
          SW_READ_ACTION  => RGGEN_READ_NONE,
          SW_WRITE_ACTION => RGGEN_WRITE_SET,
          HW_CLEAR_WIDTH  => 4
        )
        port map (
          i_clk             => i_clk,
          i_rst_n           => i_rst_n,
          i_sw_valid        => bit_field_valid,
          i_sw_read_mask    => bit_field_read_mask(27 downto 24),
          i_sw_write_enable => "1",
          i_sw_write_mask   => bit_field_write_mask(27 downto 24),
          i_sw_write_data   => bit_field_write_data(27 downto 24),
          o_sw_read_data    => bit_field_read_data(27 downto 24),
          o_sw_value        => bit_field_value(27 downto 24),
          o_write_trigger   => open,
          o_read_trigger    => open,
          i_hw_write_enable => "0",
          i_hw_write_data   => (others => '0'),
          i_hw_set          => (others => '0'),
          i_hw_clear        => i_register_8_bit_field_3_clear,
          i_value           => (others => '0'),
          i_mask            => (others => '1'),
          o_value           => o_register_8_bit_field_3,
          o_value_unmasked  => open
        );
    end block;
    g_bit_field_4: block
    begin
      u_bit_field: entity work.rggen_bit_field
        generic map (
          WIDTH           => 4,
          INITIAL_VALUE   => slice(x"0", 4, 0),
          SW_READ_ACTION  => RGGEN_READ_SET,
          SW_WRITE_ACTION => RGGEN_WRITE_CLEAR
        )
        port map (
          i_clk             => i_clk,
          i_rst_n           => i_rst_n,
          i_sw_valid        => bit_field_valid,
          i_sw_read_mask    => bit_field_read_mask(35 downto 32),
          i_sw_write_enable => "1",
          i_sw_write_mask   => bit_field_write_mask(35 downto 32),
          i_sw_write_data   => bit_field_write_data(35 downto 32),
          o_sw_read_data    => bit_field_read_data(35 downto 32),
          o_sw_value        => bit_field_value(35 downto 32),
          o_write_trigger   => open,
          o_read_trigger    => open,
          i_hw_write_enable => "0",
          i_hw_write_data   => (others => '0'),
          i_hw_set          => (others => '0'),
          i_hw_clear        => (others => '0'),
          i_value           => (others => '0'),
          i_mask            => (others => '1'),
          o_value           => o_register_8_bit_field_4,
          o_value_unmasked  => open
        );
    end block;
    g_bit_field_5: block
    begin
      u_bit_field: entity work.rggen_bit_field
        generic map (
          WIDTH           => 4,
          INITIAL_VALUE   => slice(x"0", 4, 0),
          SW_READ_ACTION  => RGGEN_READ_CLEAR,
          SW_WRITE_ACTION => RGGEN_WRITE_SET
        )
        port map (
          i_clk             => i_clk,
          i_rst_n           => i_rst_n,
          i_sw_valid        => bit_field_valid,
          i_sw_read_mask    => bit_field_read_mask(43 downto 40),
          i_sw_write_enable => "1",
          i_sw_write_mask   => bit_field_write_mask(43 downto 40),
          i_sw_write_data   => bit_field_write_data(43 downto 40),
          o_sw_read_data    => bit_field_read_data(43 downto 40),
          o_sw_value        => bit_field_value(43 downto 40),
          o_write_trigger   => open,
          o_read_trigger    => open,
          i_hw_write_enable => "0",
          i_hw_write_data   => (others => '0'),
          i_hw_set          => (others => '0'),
          i_hw_clear        => (others => '0'),
          i_value           => (others => '0'),
          i_mask            => (others => '1'),
          o_value           => o_register_8_bit_field_5,
          o_value_unmasked  => open
        );
    end block;
  end block;
  g_register_9: block
    signal bit_field_valid: std_logic;
    signal bit_field_read_mask: std_logic_vector(31 downto 0);
    signal bit_field_write_mask: std_logic_vector(31 downto 0);
    signal bit_field_write_data: std_logic_vector(31 downto 0);
    signal bit_field_read_data: std_logic_vector(31 downto 0);
    signal bit_field_value: std_logic_vector(31 downto 0);
  begin
    \g_tie_off\: for \__i\ in 0 to 31 generate
      g: if (bit_slice(x"00000fff", \__i\) = '0') generate
        bit_field_read_data(\__i\) <= '0';
        bit_field_value(\__i\) <= '0';
      end generate;
    end generate;
    u_register: entity work.rggen_default_register
      generic map (
        READABLE        => true,
        WRITABLE        => true,
        ADDRESS_WIDTH   => 8,
        OFFSET_ADDRESS  => x"28",
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
        o_register_value        => register_value(607 downto 576),
        o_bit_field_valid       => bit_field_valid,
        o_bit_field_read_mask   => bit_field_read_mask,
        o_bit_field_write_mask  => bit_field_write_mask,
        o_bit_field_write_data  => bit_field_write_data,
        i_bit_field_read_data   => bit_field_read_data,
        i_bit_field_value       => bit_field_value
      );
    g_bit_field_0: block
    begin
      u_bit_field: entity work.rggen_bit_field
        generic map (
          WIDTH           => 2,
          INITIAL_VALUE   => slice(x"0", 2, 0),
          SW_WRITE_ONCE   => false,
          TRIGGER         => true
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
          o_write_trigger   => o_register_9_bit_field_0_write_trigger,
          o_read_trigger    => o_register_9_bit_field_0_read_trigger,
          i_hw_write_enable => "0",
          i_hw_write_data   => (others => '0'),
          i_hw_set          => (others => '0'),
          i_hw_clear        => (others => '0'),
          i_value           => (others => '0'),
          i_mask            => (others => '1'),
          o_value           => o_register_9_bit_field_0,
          o_value_unmasked  => open
        );
    end block;
    g_bit_field_1: block
    begin
      u_bit_field: entity work.rggen_bit_field
        generic map (
          WIDTH               => 2,
          STORAGE             => false,
          EXTERNAL_READ_DATA  => true,
          TRIGGER             => true
        )
        port map (
          i_clk             => i_clk,
          i_rst_n           => i_rst_n,
          i_sw_valid        => bit_field_valid,
          i_sw_read_mask    => bit_field_read_mask(3 downto 2),
          i_sw_write_enable => "0",
          i_sw_write_mask   => bit_field_write_mask(3 downto 2),
          i_sw_write_data   => bit_field_write_data(3 downto 2),
          o_sw_read_data    => bit_field_read_data(3 downto 2),
          o_sw_value        => bit_field_value(3 downto 2),
          o_write_trigger   => open,
          o_read_trigger    => o_register_9_bit_field_1_read_trigger,
          i_hw_write_enable => "0",
          i_hw_write_data   => (others => '0'),
          i_hw_set          => (others => '0'),
          i_hw_clear        => (others => '0'),
          i_value           => i_register_9_bit_field_1,
          i_mask            => (others => '1'),
          o_value           => open,
          o_value_unmasked  => open
        );
    end block;
    g_bit_field_2: block
    begin
      u_bit_field: entity work.rggen_bit_field
        generic map (
          WIDTH           => 2,
          INITIAL_VALUE   => slice(x"0", 2, 0),
          SW_READ_ACTION  => RGGEN_READ_NONE,
          SW_WRITE_ONCE   => false,
          TRIGGER         => true
        )
        port map (
          i_clk             => i_clk,
          i_rst_n           => i_rst_n,
          i_sw_valid        => bit_field_valid,
          i_sw_read_mask    => bit_field_read_mask(5 downto 4),
          i_sw_write_enable => "1",
          i_sw_write_mask   => bit_field_write_mask(5 downto 4),
          i_sw_write_data   => bit_field_write_data(5 downto 4),
          o_sw_read_data    => bit_field_read_data(5 downto 4),
          o_sw_value        => bit_field_value(5 downto 4),
          o_write_trigger   => o_register_9_bit_field_2_write_trigger,
          o_read_trigger    => open,
          i_hw_write_enable => "0",
          i_hw_write_data   => (others => '0'),
          i_hw_set          => (others => '0'),
          i_hw_clear        => (others => '0'),
          i_value           => (others => '0'),
          i_mask            => (others => '1'),
          o_value           => o_register_9_bit_field_2,
          o_value_unmasked  => open
        );
    end block;
    g_bit_field_3: block
    begin
      u_bit_field: entity work.rggen_bit_field
        generic map (
          WIDTH               => 2,
          INITIAL_VALUE       => slice(x"0", 2, 0),
          EXTERNAL_READ_DATA  => true,
          TRIGGER             => true
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
          o_write_trigger   => o_register_9_bit_field_3_write_trigger,
          o_read_trigger    => o_register_9_bit_field_3_read_trigger,
          i_hw_write_enable => "0",
          i_hw_write_data   => (others => '0'),
          i_hw_set          => (others => '0'),
          i_hw_clear        => (others => '0'),
          i_value           => i_register_9_bit_field_3,
          i_mask            => (others => '1'),
          o_value           => o_register_9_bit_field_3,
          o_value_unmasked  => open
        );
    end block;
    g_bit_field_4: block
    begin
      u_bit_field: entity work.rggen_bit_field_w01trg
        generic map (
          WRITE_ONE_TRIGGER => false,
          WIDTH             => 2
        )
        port map (
          i_clk             => i_clk,
          i_rst_n           => i_rst_n,
          i_sw_valid        => bit_field_valid,
          i_sw_read_mask    => bit_field_read_mask(9 downto 8),
          i_sw_write_enable => "1",
          i_sw_write_mask   => bit_field_write_mask(9 downto 8),
          i_sw_write_data   => bit_field_write_data(9 downto 8),
          o_sw_read_data    => bit_field_read_data(9 downto 8),
          o_sw_value        => bit_field_value(9 downto 8),
          i_value           => i_register_9_bit_field_4,
          o_trigger         => o_register_9_bit_field_4_trigger
        );
    end block;
    g_bit_field_5: block
    begin
      u_bit_field: entity work.rggen_bit_field_w01trg
        generic map (
          WRITE_ONE_TRIGGER => true,
          WIDTH             => 2
        )
        port map (
          i_clk             => i_clk,
          i_rst_n           => i_rst_n,
          i_sw_valid        => bit_field_valid,
          i_sw_read_mask    => bit_field_read_mask(11 downto 10),
          i_sw_write_enable => "1",
          i_sw_write_mask   => bit_field_write_mask(11 downto 10),
          i_sw_write_data   => bit_field_write_data(11 downto 10),
          o_sw_read_data    => bit_field_read_data(11 downto 10),
          o_sw_value        => bit_field_value(11 downto 10),
          i_value           => i_register_9_bit_field_5,
          o_trigger         => o_register_9_bit_field_5_trigger
        );
    end block;
  end block;
  g_register_10: block
  begin
    g: for i in 0 to 3 generate
      signal bit_field_valid: std_logic;
      signal bit_field_read_mask: std_logic_vector(31 downto 0);
      signal bit_field_write_mask: std_logic_vector(31 downto 0);
      signal bit_field_write_data: std_logic_vector(31 downto 0);
      signal bit_field_read_data: std_logic_vector(31 downto 0);
      signal bit_field_value: std_logic_vector(31 downto 0);
    begin
      \g_tie_off\: for \__i\ in 0 to 31 generate
        g: if (bit_slice(x"3f3f3f3f", \__i\) = '0') generate
          bit_field_read_data(\__i\) <= '0';
          bit_field_value(\__i\) <= '0';
        end generate;
      end generate;
      u_register: entity work.rggen_default_register
        generic map (
          READABLE        => true,
          WRITABLE        => true,
          ADDRESS_WIDTH   => 8,
          OFFSET_ADDRESS  => x"30"+8*i,
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
          o_register_active       => register_active(10+i),
          o_register_ready        => register_ready(10+i),
          o_register_status       => register_status(2*(10+i)+1 downto 2*(10+i)),
          o_register_read_data    => register_read_data(32*(10+i)+31 downto 32*(10+i)),
          o_register_value        => register_value(64*(10+i)+0+31 downto 64*(10+i)+0),
          o_bit_field_valid       => bit_field_valid,
          o_bit_field_read_mask   => bit_field_read_mask,
          o_bit_field_write_mask  => bit_field_write_mask,
          o_bit_field_write_data  => bit_field_write_data,
          i_bit_field_read_data   => bit_field_read_data,
          i_bit_field_value       => bit_field_value
        );
      g_bit_field_0: block
      begin
        g: for j in 0 to 3 generate
        begin
          u_bit_field: entity work.rggen_bit_field
            generic map (
              WIDTH           => 2,
              INITIAL_VALUE   => slice(x"0", 2, 0),
              SW_WRITE_ONCE   => false,
              TRIGGER         => false
            )
            port map (
              i_clk             => i_clk,
              i_rst_n           => i_rst_n,
              i_sw_valid        => bit_field_valid,
              i_sw_read_mask    => bit_field_read_mask(0+8*j+1 downto 0+8*j),
              i_sw_write_enable => "1",
              i_sw_write_mask   => bit_field_write_mask(0+8*j+1 downto 0+8*j),
              i_sw_write_data   => bit_field_write_data(0+8*j+1 downto 0+8*j),
              o_sw_read_data    => bit_field_read_data(0+8*j+1 downto 0+8*j),
              o_sw_value        => bit_field_value(0+8*j+1 downto 0+8*j),
              o_write_trigger   => open,
              o_read_trigger    => open,
              i_hw_write_enable => "0",
              i_hw_write_data   => (others => '0'),
              i_hw_set          => (others => '0'),
              i_hw_clear        => (others => '0'),
              i_value           => (others => '0'),
              i_mask            => (others => '1'),
              o_value           => o_register_10_bit_field_0(2*(4*i+j)+1 downto 2*(4*i+j)),
              o_value_unmasked  => open
            );
        end generate;
      end block;
      g_bit_field_1: block
      begin
        g: for j in 0 to 3 generate
        begin
          u_bit_field: entity work.rggen_bit_field
            generic map (
              WIDTH           => 2,
              INITIAL_VALUE   => slice(REGISTER_10_BIT_FIELD_1_INITIAL_VALUE, 2, j),
              SW_WRITE_ONCE   => false,
              TRIGGER         => false
            )
            port map (
              i_clk             => i_clk,
              i_rst_n           => i_rst_n,
              i_sw_valid        => bit_field_valid,
              i_sw_read_mask    => bit_field_read_mask(2+8*j+1 downto 2+8*j),
              i_sw_write_enable => "1",
              i_sw_write_mask   => bit_field_write_mask(2+8*j+1 downto 2+8*j),
              i_sw_write_data   => bit_field_write_data(2+8*j+1 downto 2+8*j),
              o_sw_read_data    => bit_field_read_data(2+8*j+1 downto 2+8*j),
              o_sw_value        => bit_field_value(2+8*j+1 downto 2+8*j),
              o_write_trigger   => open,
              o_read_trigger    => open,
              i_hw_write_enable => "0",
              i_hw_write_data   => (others => '0'),
              i_hw_set          => (others => '0'),
              i_hw_clear        => (others => '0'),
              i_value           => (others => '0'),
              i_mask            => (others => '1'),
              o_value           => o_register_10_bit_field_1(2*(4*i+j)+1 downto 2*(4*i+j)),
              o_value_unmasked  => open
            );
        end generate;
      end block;
      g_bit_field_2: block
      begin
        g: for j in 0 to 3 generate
        begin
          u_bit_field: entity work.rggen_bit_field
            generic map (
              WIDTH           => 2,
              INITIAL_VALUE   => slice(x"e4", 2, j),
              SW_WRITE_ONCE   => false,
              TRIGGER         => false
            )
            port map (
              i_clk             => i_clk,
              i_rst_n           => i_rst_n,
              i_sw_valid        => bit_field_valid,
              i_sw_read_mask    => bit_field_read_mask(4+8*j+1 downto 4+8*j),
              i_sw_write_enable => "1",
              i_sw_write_mask   => bit_field_write_mask(4+8*j+1 downto 4+8*j),
              i_sw_write_data   => bit_field_write_data(4+8*j+1 downto 4+8*j),
              o_sw_read_data    => bit_field_read_data(4+8*j+1 downto 4+8*j),
              o_sw_value        => bit_field_value(4+8*j+1 downto 4+8*j),
              o_write_trigger   => open,
              o_read_trigger    => open,
              i_hw_write_enable => "0",
              i_hw_write_data   => (others => '0'),
              i_hw_set          => (others => '0'),
              i_hw_clear        => (others => '0'),
              i_value           => (others => '0'),
              i_mask            => (others => '1'),
              o_value           => o_register_10_bit_field_2(2*(4*i+j)+1 downto 2*(4*i+j)),
              o_value_unmasked  => open
            );
        end generate;
      end block;
    end generate;
  end block;
  g_register_11: block
  begin
    g: for i in 0 to 1 generate
    begin
      g: for j in 0 to 3 generate
        signal bit_field_valid: std_logic;
        signal bit_field_read_mask: std_logic_vector(63 downto 0);
        signal bit_field_write_mask: std_logic_vector(63 downto 0);
        signal bit_field_write_data: std_logic_vector(63 downto 0);
        signal bit_field_read_data: std_logic_vector(63 downto 0);
        signal bit_field_value: std_logic_vector(63 downto 0);
        signal indirect_match: std_logic_vector(2 downto 0);
      begin
        \g_tie_off\: for \__i\ in 0 to 63 generate
          g: if (bit_slice(x"ffffffffffffffff", \__i\) = '0') generate
            bit_field_read_data(\__i\) <= '0';
            bit_field_value(\__i\) <= '0';
          end generate;
        end generate;
        indirect_match(0) <= '1' when unsigned(register_value(3 downto 0)) = i else '0';
        indirect_match(1) <= '1' when unsigned(register_value(7 downto 4)) = j else '0';
        indirect_match(2) <= '1' when unsigned(register_value(8 downto 8)) = 0 else '0';
        u_register: entity work.rggen_indirect_register
          generic map (
            READABLE              => true,
            WRITABLE              => true,
            ADDRESS_WIDTH         => 8,
            OFFSET_ADDRESS        => x"50",
            BUS_WIDTH             => 32,
            DATA_WIDTH            => 64,
            INDIRECT_MATCH_WIDTH  => 3
          )
          port map (
            i_clk                   => i_clk,
            i_rst_n                 => i_rst_n,
            i_register_valid        => register_valid,
            i_register_access       => register_access,
            i_register_address      => register_address,
            i_register_write_data   => register_write_data,
            i_register_strobe       => register_strobe,
            o_register_active       => register_active(14+4*i+j),
            o_register_ready        => register_ready(14+4*i+j),
            o_register_status       => register_status(2*(14+4*i+j)+1 downto 2*(14+4*i+j)),
            o_register_read_data    => register_read_data(32*(14+4*i+j)+31 downto 32*(14+4*i+j)),
            o_register_value        => register_value(64*(14+4*i+j)+0+63 downto 64*(14+4*i+j)+0),
            i_indirect_match        => indirect_match,
            o_bit_field_valid       => bit_field_valid,
            o_bit_field_read_mask   => bit_field_read_mask,
            o_bit_field_write_mask  => bit_field_write_mask,
            o_bit_field_write_data  => bit_field_write_data,
            i_bit_field_read_data   => bit_field_read_data,
            i_bit_field_value       => bit_field_value
          );
        g_bit_field_0: block
        begin
          g: for k in 0 to 3 generate
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
                i_sw_read_mask    => bit_field_read_mask(0+16*k+7 downto 0+16*k),
                i_sw_write_enable => "1",
                i_sw_write_mask   => bit_field_write_mask(0+16*k+7 downto 0+16*k),
                i_sw_write_data   => bit_field_write_data(0+16*k+7 downto 0+16*k),
                o_sw_read_data    => bit_field_read_data(0+16*k+7 downto 0+16*k),
                o_sw_value        => bit_field_value(0+16*k+7 downto 0+16*k),
                o_write_trigger   => open,
                o_read_trigger    => open,
                i_hw_write_enable => "0",
                i_hw_write_data   => (others => '0'),
                i_hw_set          => (others => '0'),
                i_hw_clear        => (others => '0'),
                i_value           => (others => '0'),
                i_mask            => (others => '1'),
                o_value           => o_register_11_bit_field_0(8*(16*i+4*j+k)+7 downto 8*(16*i+4*j+k)),
                o_value_unmasked  => open
              );
          end generate;
        end block;
        g_bit_field_1: block
        begin
          g: for k in 0 to 3 generate
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
                i_sw_read_mask    => bit_field_read_mask(8+16*k+7 downto 8+16*k),
                i_sw_write_enable => "1",
                i_sw_write_mask   => bit_field_write_mask(8+16*k+7 downto 8+16*k),
                i_sw_write_data   => bit_field_write_data(8+16*k+7 downto 8+16*k),
                o_sw_read_data    => bit_field_read_data(8+16*k+7 downto 8+16*k),
                o_sw_value        => bit_field_value(8+16*k+7 downto 8+16*k),
                o_write_trigger   => open,
                o_read_trigger    => open,
                i_hw_write_enable => "0",
                i_hw_write_data   => (others => '0'),
                i_hw_set          => (others => '0'),
                i_hw_clear        => (others => '0'),
                i_value           => (others => '0'),
                i_mask            => (others => '1'),
                o_value           => o_register_11_bit_field_1(8*(16*i+4*j+k)+7 downto 8*(16*i+4*j+k)),
                o_value_unmasked  => open
              );
          end generate;
        end block;
      end generate;
    end generate;
  end block;
  g_register_12: block
    signal bit_field_valid: std_logic;
    signal bit_field_read_mask: std_logic_vector(63 downto 0);
    signal bit_field_write_mask: std_logic_vector(63 downto 0);
    signal bit_field_write_data: std_logic_vector(63 downto 0);
    signal bit_field_read_data: std_logic_vector(63 downto 0);
    signal bit_field_value: std_logic_vector(63 downto 0);
    signal indirect_match: std_logic_vector(0 downto 0);
  begin
    \g_tie_off\: for \__i\ in 0 to 63 generate
      g: if (bit_slice(x"0000000100000001", \__i\) = '0') generate
        bit_field_read_data(\__i\) <= '0';
        bit_field_value(\__i\) <= '0';
      end generate;
    end generate;
    indirect_match(0) <= '1' when unsigned(register_value(8 downto 8)) = 1 else '0';
    u_register: entity work.rggen_indirect_register
      generic map (
        READABLE              => true,
        WRITABLE              => true,
        ADDRESS_WIDTH         => 8,
        OFFSET_ADDRESS        => x"50",
        BUS_WIDTH             => 32,
        DATA_WIDTH            => 64,
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
        o_register_active       => register_active(22),
        o_register_ready        => register_ready(22),
        o_register_status       => register_status(45 downto 44),
        o_register_read_data    => register_read_data(735 downto 704),
        o_register_value        => register_value(1471 downto 1408),
        i_indirect_match        => indirect_match,
        o_bit_field_valid       => bit_field_valid,
        o_bit_field_read_mask   => bit_field_read_mask,
        o_bit_field_write_mask  => bit_field_write_mask,
        o_bit_field_write_data  => bit_field_write_data,
        i_bit_field_read_data   => bit_field_read_data,
        i_bit_field_value       => bit_field_value
      );
    g_bit_field_0: block
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
          o_value           => o_register_12_bit_field_0,
          o_value_unmasked  => open
        );
    end block;
    g_bit_field_1: block
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
          i_sw_read_mask    => bit_field_read_mask(32 downto 32),
          i_sw_write_enable => "1",
          i_sw_write_mask   => bit_field_write_mask(32 downto 32),
          i_sw_write_data   => bit_field_write_data(32 downto 32),
          o_sw_read_data    => bit_field_read_data(32 downto 32),
          o_sw_value        => bit_field_value(32 downto 32),
          o_write_trigger   => open,
          o_read_trigger    => open,
          i_hw_write_enable => "0",
          i_hw_write_data   => (others => '0'),
          i_hw_set          => (others => '0'),
          i_hw_clear        => (others => '0'),
          i_value           => (others => '0'),
          i_mask            => (others => '1'),
          o_value           => o_register_12_bit_field_1,
          o_value_unmasked  => open
        );
    end block;
  end block;
  g_register_13: block
    signal bit_field_valid: std_logic;
    signal bit_field_read_mask: std_logic_vector(31 downto 0);
    signal bit_field_write_mask: std_logic_vector(31 downto 0);
    signal bit_field_write_data: std_logic_vector(31 downto 0);
    signal bit_field_read_data: std_logic_vector(31 downto 0);
    signal bit_field_value: std_logic_vector(31 downto 0);
  begin
    \g_tie_off\: for \__i\ in 0 to 31 generate
      g: if (bit_slice(x"0003ffff", \__i\) = '0') generate
        bit_field_read_data(\__i\) <= '0';
        bit_field_value(\__i\) <= '0';
      end generate;
    end generate;
    u_register: entity work.rggen_default_register
      generic map (
        READABLE        => true,
        WRITABLE        => true,
        ADDRESS_WIDTH   => 8,
        OFFSET_ADDRESS  => x"60",
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
        o_register_active       => register_active(23),
        o_register_ready        => register_ready(23),
        o_register_status       => register_status(47 downto 46),
        o_register_read_data    => register_read_data(767 downto 736),
        o_register_value        => register_value(1503 downto 1472),
        o_bit_field_valid       => bit_field_valid,
        o_bit_field_read_mask   => bit_field_read_mask,
        o_bit_field_write_mask  => bit_field_write_mask,
        o_bit_field_write_data  => bit_field_write_data,
        i_bit_field_read_data   => bit_field_read_data,
        i_bit_field_value       => bit_field_value
      );
    g_bit_field_0: block
    begin
      u_bit_field: entity work.rggen_bit_field
        generic map (
          WIDTH               => 2,
          INITIAL_VALUE       => slice(x"0", 2, 0),
          SW_READ_ACTION      => RGGEN_READ_DEFAULT,
          SW_WRITE_ACTION     => RGGEN_WRITE_DEFAULT,
          SW_WRITE_ONCE       => false,
          HW_SET_WIDTH        => 2,
          HW_CLEAR_WIDTH      => 2,
          STORAGE             => true,
          EXTERNAL_READ_DATA  => false,
          TRIGGER             => false
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
          o_value           => o_register_13_bit_field_0,
          o_value_unmasked  => open
        );
    end block;
    g_bit_field_1: block
    begin
      u_bit_field: entity work.rggen_bit_field
        generic map (
          WIDTH               => 2,
          INITIAL_VALUE       => slice(x"0", 2, 0),
          SW_READ_ACTION      => RGGEN_READ_DEFAULT,
          SW_WRITE_ACTION     => RGGEN_WRITE_NONE,
          SW_WRITE_ONCE       => false,
          HW_SET_WIDTH        => 2,
          HW_CLEAR_WIDTH      => 2,
          STORAGE             => false,
          EXTERNAL_READ_DATA  => true,
          TRIGGER             => false
        )
        port map (
          i_clk             => i_clk,
          i_rst_n           => i_rst_n,
          i_sw_valid        => bit_field_valid,
          i_sw_read_mask    => bit_field_read_mask(3 downto 2),
          i_sw_write_enable => "1",
          i_sw_write_mask   => bit_field_write_mask(3 downto 2),
          i_sw_write_data   => bit_field_write_data(3 downto 2),
          o_sw_read_data    => bit_field_read_data(3 downto 2),
          o_sw_value        => bit_field_value(3 downto 2),
          o_write_trigger   => open,
          o_read_trigger    => open,
          i_hw_write_enable => "0",
          i_hw_write_data   => (others => '0'),
          i_hw_set          => (others => '0'),
          i_hw_clear        => (others => '0'),
          i_value           => i_register_13_bit_field_1,
          i_mask            => (others => '1'),
          o_value           => open,
          o_value_unmasked  => open
        );
    end block;
    g_bit_field_2: block
    begin
      u_bit_field: entity work.rggen_bit_field
        generic map (
          WIDTH               => 2,
          INITIAL_VALUE       => slice(x"0", 2, 0),
          SW_READ_ACTION      => RGGEN_READ_DEFAULT,
          SW_WRITE_ACTION     => RGGEN_WRITE_DEFAULT,
          SW_WRITE_ONCE       => true,
          HW_SET_WIDTH        => 2,
          HW_CLEAR_WIDTH      => 2,
          STORAGE             => true,
          EXTERNAL_READ_DATA  => false,
          TRIGGER             => false
        )
        port map (
          i_clk             => i_clk,
          i_rst_n           => i_rst_n,
          i_sw_valid        => bit_field_valid,
          i_sw_read_mask    => bit_field_read_mask(5 downto 4),
          i_sw_write_enable => "1",
          i_sw_write_mask   => bit_field_write_mask(5 downto 4),
          i_sw_write_data   => bit_field_write_data(5 downto 4),
          o_sw_read_data    => bit_field_read_data(5 downto 4),
          o_sw_value        => bit_field_value(5 downto 4),
          o_write_trigger   => open,
          o_read_trigger    => open,
          i_hw_write_enable => "0",
          i_hw_write_data   => (others => '0'),
          i_hw_set          => (others => '0'),
          i_hw_clear        => (others => '0'),
          i_value           => (others => '0'),
          i_mask            => (others => '1'),
          o_value           => o_register_13_bit_field_2,
          o_value_unmasked  => open
        );
    end block;
    g_bit_field_3: block
    begin
      u_bit_field: entity work.rggen_bit_field
        generic map (
          WIDTH               => 2,
          INITIAL_VALUE       => slice(x"0", 2, 0),
          SW_READ_ACTION      => RGGEN_READ_DEFAULT,
          SW_WRITE_ACTION     => RGGEN_WRITE_DEFAULT,
          SW_WRITE_ONCE       => false,
          HW_SET_WIDTH        => 2,
          HW_CLEAR_WIDTH      => 2,
          STORAGE             => true,
          EXTERNAL_READ_DATA  => false,
          TRIGGER             => true
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
          o_write_trigger   => o_register_13_bit_field_3_write_trigger,
          o_read_trigger    => o_register_13_bit_field_3_read_trigger,
          i_hw_write_enable => "0",
          i_hw_write_data   => (others => '0'),
          i_hw_set          => (others => '0'),
          i_hw_clear        => (others => '0'),
          i_value           => (others => '0'),
          i_mask            => (others => '1'),
          o_value           => o_register_13_bit_field_3,
          o_value_unmasked  => open
        );
    end block;
    g_bit_field_4: block
    begin
      u_bit_field: entity work.rggen_bit_field
        generic map (
          WIDTH               => 2,
          INITIAL_VALUE       => slice(x"0", 2, 0),
          SW_READ_ACTION      => RGGEN_READ_CLEAR,
          SW_WRITE_ACTION     => RGGEN_WRITE_1_SET,
          SW_WRITE_ONCE       => false,
          HW_SET_WIDTH        => 2,
          HW_CLEAR_WIDTH      => 2,
          STORAGE             => true,
          EXTERNAL_READ_DATA  => false,
          TRIGGER             => false
        )
        port map (
          i_clk             => i_clk,
          i_rst_n           => i_rst_n,
          i_sw_valid        => bit_field_valid,
          i_sw_read_mask    => bit_field_read_mask(9 downto 8),
          i_sw_write_enable => "1",
          i_sw_write_mask   => bit_field_write_mask(9 downto 8),
          i_sw_write_data   => bit_field_write_data(9 downto 8),
          o_sw_read_data    => bit_field_read_data(9 downto 8),
          o_sw_value        => bit_field_value(9 downto 8),
          o_write_trigger   => open,
          o_read_trigger    => open,
          i_hw_write_enable => "0",
          i_hw_write_data   => (others => '0'),
          i_hw_set          => (others => '0'),
          i_hw_clear        => (others => '0'),
          i_value           => (others => '0'),
          i_mask            => (others => '1'),
          o_value           => o_register_13_bit_field_4,
          o_value_unmasked  => open
        );
    end block;
    g_bit_field_5: block
    begin
      u_bit_field: entity work.rggen_bit_field
        generic map (
          WIDTH               => 2,
          INITIAL_VALUE       => slice(x"0", 2, 0),
          SW_READ_ACTION      => RGGEN_READ_SET,
          SW_WRITE_ACTION     => RGGEN_WRITE_1_CLEAR,
          SW_WRITE_ONCE       => false,
          HW_SET_WIDTH        => 2,
          HW_CLEAR_WIDTH      => 2,
          STORAGE             => true,
          EXTERNAL_READ_DATA  => false,
          TRIGGER             => false
        )
        port map (
          i_clk             => i_clk,
          i_rst_n           => i_rst_n,
          i_sw_valid        => bit_field_valid,
          i_sw_read_mask    => bit_field_read_mask(11 downto 10),
          i_sw_write_enable => "1",
          i_sw_write_mask   => bit_field_write_mask(11 downto 10),
          i_sw_write_data   => bit_field_write_data(11 downto 10),
          o_sw_read_data    => bit_field_read_data(11 downto 10),
          o_sw_value        => bit_field_value(11 downto 10),
          o_write_trigger   => open,
          o_read_trigger    => open,
          i_hw_write_enable => "0",
          i_hw_write_data   => (others => '0'),
          i_hw_set          => (others => '0'),
          i_hw_clear        => (others => '0'),
          i_value           => (others => '0'),
          i_mask            => (others => '1'),
          o_value           => o_register_13_bit_field_5,
          o_value_unmasked  => open
        );
    end block;
    g_bit_field_6: block
    begin
      u_bit_field: entity work.rggen_bit_field
        generic map (
          WIDTH               => 2,
          INITIAL_VALUE       => slice(x"0", 2, 0),
          SW_READ_ACTION      => RGGEN_READ_DEFAULT,
          SW_WRITE_ACTION     => RGGEN_WRITE_1_SET,
          SW_WRITE_ONCE       => false,
          HW_SET_WIDTH        => 2,
          HW_CLEAR_WIDTH      => 2,
          STORAGE             => true,
          EXTERNAL_READ_DATA  => false,
          TRIGGER             => false
        )
        port map (
          i_clk             => i_clk,
          i_rst_n           => i_rst_n,
          i_sw_valid        => bit_field_valid,
          i_sw_read_mask    => bit_field_read_mask(13 downto 12),
          i_sw_write_enable => "1",
          i_sw_write_mask   => bit_field_write_mask(13 downto 12),
          i_sw_write_data   => bit_field_write_data(13 downto 12),
          o_sw_read_data    => bit_field_read_data(13 downto 12),
          o_sw_value        => bit_field_value(13 downto 12),
          o_write_trigger   => open,
          o_read_trigger    => open,
          i_hw_write_enable => "0",
          i_hw_write_data   => (others => '0'),
          i_hw_set          => (others => '0'),
          i_hw_clear        => i_register_13_bit_field_6_hw_clear,
          i_value           => (others => '0'),
          i_mask            => (others => '1'),
          o_value           => o_register_13_bit_field_6,
          o_value_unmasked  => open
        );
    end block;
    g_bit_field_7: block
    begin
      u_bit_field: entity work.rggen_bit_field
        generic map (
          WIDTH               => 2,
          INITIAL_VALUE       => slice(x"0", 2, 0),
          SW_READ_ACTION      => RGGEN_READ_DEFAULT,
          SW_WRITE_ACTION     => RGGEN_WRITE_1_CLEAR,
          SW_WRITE_ONCE       => false,
          HW_SET_WIDTH        => 2,
          HW_CLEAR_WIDTH      => 2,
          STORAGE             => true,
          EXTERNAL_READ_DATA  => false,
          TRIGGER             => false
        )
        port map (
          i_clk             => i_clk,
          i_rst_n           => i_rst_n,
          i_sw_valid        => bit_field_valid,
          i_sw_read_mask    => bit_field_read_mask(15 downto 14),
          i_sw_write_enable => "1",
          i_sw_write_mask   => bit_field_write_mask(15 downto 14),
          i_sw_write_data   => bit_field_write_data(15 downto 14),
          o_sw_read_data    => bit_field_read_data(15 downto 14),
          o_sw_value        => bit_field_value(15 downto 14),
          o_write_trigger   => open,
          o_read_trigger    => open,
          i_hw_write_enable => "0",
          i_hw_write_data   => (others => '0'),
          i_hw_set          => i_register_13_bit_field_7_hw_set,
          i_hw_clear        => (others => '0'),
          i_value           => (others => '0'),
          i_mask            => (others => '1'),
          o_value           => o_register_13_bit_field_7,
          o_value_unmasked  => open
        );
    end block;
    g_bit_field_8: block
    begin
      u_bit_field: entity work.rggen_bit_field
        generic map (
          WIDTH               => 2,
          INITIAL_VALUE       => slice(x"0", 2, 0),
          SW_READ_ACTION      => RGGEN_READ_DEFAULT,
          SW_WRITE_ACTION     => RGGEN_WRITE_DEFAULT,
          SW_WRITE_ONCE       => false,
          HW_SET_WIDTH        => 2,
          HW_CLEAR_WIDTH      => 2,
          STORAGE             => true,
          EXTERNAL_READ_DATA  => false,
          TRIGGER             => false
        )
        port map (
          i_clk             => i_clk,
          i_rst_n           => i_rst_n,
          i_sw_valid        => bit_field_valid,
          i_sw_read_mask    => bit_field_read_mask(17 downto 16),
          i_sw_write_enable => "1",
          i_sw_write_mask   => bit_field_write_mask(17 downto 16),
          i_sw_write_data   => bit_field_write_data(17 downto 16),
          o_sw_read_data    => bit_field_read_data(17 downto 16),
          o_sw_value        => bit_field_value(17 downto 16),
          o_write_trigger   => open,
          o_read_trigger    => open,
          i_hw_write_enable => i_register_13_bit_field_8_hw_write_enable,
          i_hw_write_data   => i_register_13_bit_field_8_hw_write_data,
          i_hw_set          => (others => '0'),
          i_hw_clear        => (others => '0'),
          i_value           => (others => '0'),
          i_mask            => (others => '1'),
          o_value           => o_register_13_bit_field_8,
          o_value_unmasked  => open
        );
    end block;
  end block;
  g_register_15: block
  begin
    u_register: entity work.rggen_external_register
      generic map (
        ADDRESS_WIDTH => 8,
        BUS_WIDTH     => 32,
        START_ADDRESS => x"80",
        BYTE_SIZE     => 128
      )
      port map (
        i_clk                 => i_clk,
        i_rst_n               => i_rst_n,
        i_register_valid      => register_valid,
        i_register_access     => register_access,
        i_register_address    => register_address,
        i_register_write_data => register_write_data,
        i_register_strobe     => register_strobe,
        o_register_active     => register_active(24),
        o_register_ready      => register_ready(24),
        o_register_status     => register_status(49 downto 48),
        o_register_read_data  => register_read_data(799 downto 768),
        o_register_value      => register_value(1567 downto 1536),
        o_external_valid      => o_register_15_valid,
        o_external_access     => o_register_15_access,
        o_external_address    => o_register_15_address,
        o_external_data       => o_register_15_data,
        o_external_strobe     => o_register_15_strobe,
        i_external_ready      => i_register_15_ready,
        i_external_status     => i_register_15_status,
        i_external_data       => i_register_15_data
      );
  end block;
end rtl;
