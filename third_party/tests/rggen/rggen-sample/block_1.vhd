library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

use work.rggen_rtl.all;

entity block_1 is
  generic (
    ADDRESS_WIDTH: positive := 7;
    PRE_DECODE: boolean := false;
    BASE_ADDRESS: unsigned := x"0";
    ERROR_STATUS: boolean := false;
    INSERT_SLICER: boolean := false
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
    o_register_file_0_register_0_bit_field_0: out std_logic_vector(7 downto 0);
    o_register_file_0_register_1_bit_field_0: out std_logic_vector(7 downto 0);
    o_register_file_1_register_0_bit_field_0: out std_logic_vector(15 downto 0);
    o_register_file_1_register_1_bit_field_0: out std_logic_vector(15 downto 0);
    o_register_file_2_register_file_0_register_0_bit_field_0: out std_logic_vector(95 downto 0);
    o_register_file_2_register_file_0_register_0_bit_field_1: out std_logic_vector(95 downto 0);
    o_register_file_2_register_file_0_register_0_bit_field_2: out std_logic_vector(95 downto 0);
    o_register_file_2_register_file_0_register_1_bit_field_0: out std_logic_vector(3 downto 0)
  );
end block_1;

architecture rtl of block_1 is
  signal register_valid: std_logic;
  signal register_access: std_logic_vector(1 downto 0);
  signal register_address: std_logic_vector(6 downto 0);
  signal register_write_data: std_logic_vector(31 downto 0);
  signal register_strobe: std_logic_vector(3 downto 0);
  signal register_active: std_logic_vector(19 downto 0);
  signal register_ready: std_logic_vector(19 downto 0);
  signal register_status: std_logic_vector(39 downto 0);
  signal register_read_data: std_logic_vector(639 downto 0);
  signal register_value: std_logic_vector(639 downto 0);
begin
  u_adapter: entity work.rggen_apb_adaper
    generic map (
      ADDRESS_WIDTH       => ADDRESS_WIDTH,
      LOCAL_ADDRESS_WIDTH => 7,
      BUS_WIDTH           => 32,
      REGISTERS           => 20,
      PRE_DECODE          => PRE_DECODE,
      BASE_ADDRESS        => BASE_ADDRESS,
      BYTE_SIZE           => 128,
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
  g_register_file_0: block
  begin
    g_register_0: block
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
          ADDRESS_WIDTH   => 7,
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
            o_value           => o_register_file_0_register_0_bit_field_0,
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
        g: if (bit_slice(x"000000ff", \__i\) = '0') generate
          bit_field_read_data(\__i\) <= '0';
          bit_field_value(\__i\) <= '0';
        end generate;
      end generate;
      u_register: entity work.rggen_default_register
        generic map (
          READABLE        => true,
          WRITABLE        => true,
          ADDRESS_WIDTH   => 7,
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
          o_register_value        => register_value(63 downto 32),
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
            o_value           => o_register_file_0_register_1_bit_field_0,
            o_value_unmasked  => open
          );
      end block;
    end block;
  end block;
  g_register_file_1: block
  begin
    g_register_0: block
    begin
      g: for i in 0 to 1 generate
        signal bit_field_valid: std_logic;
        signal bit_field_read_mask: std_logic_vector(31 downto 0);
        signal bit_field_write_mask: std_logic_vector(31 downto 0);
        signal bit_field_write_data: std_logic_vector(31 downto 0);
        signal bit_field_read_data: std_logic_vector(31 downto 0);
        signal bit_field_value: std_logic_vector(31 downto 0);
        signal indirect_match: std_logic_vector(1 downto 0);
      begin
        \g_tie_off\: for \__i\ in 0 to 31 generate
          g: if (bit_slice(x"000000ff", \__i\) = '0') generate
            bit_field_read_data(\__i\) <= '0';
            bit_field_value(\__i\) <= '0';
          end generate;
        end generate;
        indirect_match(0) <= '1' when unsigned(register_value(7 downto 0)) = i else '0';
        indirect_match(1) <= '1' when unsigned(register_value(39 downto 32)) = 0 else '0';
        u_register: entity work.rggen_indirect_register
          generic map (
            READABLE              => true,
            WRITABLE              => true,
            ADDRESS_WIDTH         => 7,
            OFFSET_ADDRESS        => x"10",
            BUS_WIDTH             => 32,
            DATA_WIDTH            => 32,
            INDIRECT_MATCH_WIDTH  => 2
          )
          port map (
            i_clk                   => i_clk,
            i_rst_n                 => i_rst_n,
            i_register_valid        => register_valid,
            i_register_access       => register_access,
            i_register_address      => register_address,
            i_register_write_data   => register_write_data,
            i_register_strobe       => register_strobe,
            o_register_active       => register_active(2+i),
            o_register_ready        => register_ready(2+i),
            o_register_status       => register_status(2*(2+i)+1 downto 2*(2+i)),
            o_register_read_data    => register_read_data(32*(2+i)+31 downto 32*(2+i)),
            o_register_value        => register_value(32*(2+i)+0+31 downto 32*(2+i)+0),
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
              o_value           => o_register_file_1_register_0_bit_field_0(8*(i)+7 downto 8*(i)),
              o_value_unmasked  => open
            );
        end block;
      end generate;
    end block;
    g_register_1: block
    begin
      g: for i in 0 to 1 generate
        signal bit_field_valid: std_logic;
        signal bit_field_read_mask: std_logic_vector(31 downto 0);
        signal bit_field_write_mask: std_logic_vector(31 downto 0);
        signal bit_field_write_data: std_logic_vector(31 downto 0);
        signal bit_field_read_data: std_logic_vector(31 downto 0);
        signal bit_field_value: std_logic_vector(31 downto 0);
        signal indirect_match: std_logic_vector(1 downto 0);
      begin
        \g_tie_off\: for \__i\ in 0 to 31 generate
          g: if (bit_slice(x"000000ff", \__i\) = '0') generate
            bit_field_read_data(\__i\) <= '0';
            bit_field_value(\__i\) <= '0';
          end generate;
        end generate;
        indirect_match(0) <= '1' when unsigned(register_value(7 downto 0)) = i else '0';
        indirect_match(1) <= '1' when unsigned(register_value(39 downto 32)) = 1 else '0';
        u_register: entity work.rggen_indirect_register
          generic map (
            READABLE              => true,
            WRITABLE              => true,
            ADDRESS_WIDTH         => 7,
            OFFSET_ADDRESS        => x"10",
            BUS_WIDTH             => 32,
            DATA_WIDTH            => 32,
            INDIRECT_MATCH_WIDTH  => 2
          )
          port map (
            i_clk                   => i_clk,
            i_rst_n                 => i_rst_n,
            i_register_valid        => register_valid,
            i_register_access       => register_access,
            i_register_address      => register_address,
            i_register_write_data   => register_write_data,
            i_register_strobe       => register_strobe,
            o_register_active       => register_active(4+i),
            o_register_ready        => register_ready(4+i),
            o_register_status       => register_status(2*(4+i)+1 downto 2*(4+i)),
            o_register_read_data    => register_read_data(32*(4+i)+31 downto 32*(4+i)),
            o_register_value        => register_value(32*(4+i)+0+31 downto 32*(4+i)+0),
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
              o_value           => o_register_file_1_register_1_bit_field_0(8*(i)+7 downto 8*(i)),
              o_value_unmasked  => open
            );
        end block;
      end generate;
    end block;
  end block;
  g_register_file_2: block
  begin
    g: for i in 0 to 1 generate
    begin
      g_register_file_0: block
      begin
        g_register_0: block
        begin
          g: for j in 0 to 1 generate
          begin
            g: for k in 0 to 2 generate
              signal bit_field_valid: std_logic;
              signal bit_field_read_mask: std_logic_vector(31 downto 0);
              signal bit_field_write_mask: std_logic_vector(31 downto 0);
              signal bit_field_write_data: std_logic_vector(31 downto 0);
              signal bit_field_read_data: std_logic_vector(31 downto 0);
              signal bit_field_value: std_logic_vector(31 downto 0);
            begin
              \g_tie_off\: for \__i\ in 0 to 31 generate
                g: if (bit_slice(x"00ffffff", \__i\) = '0') generate
                  bit_field_read_data(\__i\) <= '0';
                  bit_field_value(\__i\) <= '0';
                end generate;
              end generate;
              u_register: entity work.rggen_default_register
                generic map (
                  READABLE        => true,
                  WRITABLE        => true,
                  ADDRESS_WIDTH   => 7,
                  OFFSET_ADDRESS  => x"20"+32*i+4*(3*j+k),
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
                  o_register_active       => register_active(6+7*i+3*j+k),
                  o_register_ready        => register_ready(6+7*i+3*j+k),
                  o_register_status       => register_status(2*(6+7*i+3*j+k)+1 downto 2*(6+7*i+3*j+k)),
                  o_register_read_data    => register_read_data(32*(6+7*i+3*j+k)+31 downto 32*(6+7*i+3*j+k)),
                  o_register_value        => register_value(32*(6+7*i+3*j+k)+0+31 downto 32*(6+7*i+3*j+k)+0),
                  o_bit_field_valid       => bit_field_valid,
                  o_bit_field_read_mask   => bit_field_read_mask,
                  o_bit_field_write_mask  => bit_field_write_mask,
                  o_bit_field_write_data  => bit_field_write_data,
                  i_bit_field_read_data   => bit_field_read_data,
                  i_bit_field_value       => bit_field_value
                );
              g_bit_field_0: block
              begin
                g: for l in 0 to 1 generate
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
                      i_sw_read_mask    => bit_field_read_mask(0+4*l+3 downto 0+4*l),
                      i_sw_write_enable => "1",
                      i_sw_write_mask   => bit_field_write_mask(0+4*l+3 downto 0+4*l),
                      i_sw_write_data   => bit_field_write_data(0+4*l+3 downto 0+4*l),
                      o_sw_read_data    => bit_field_read_data(0+4*l+3 downto 0+4*l),
                      o_sw_value        => bit_field_value(0+4*l+3 downto 0+4*l),
                      o_write_trigger   => open,
                      o_read_trigger    => open,
                      i_hw_write_enable => "0",
                      i_hw_write_data   => (others => '0'),
                      i_hw_set          => (others => '0'),
                      i_hw_clear        => (others => '0'),
                      i_value           => (others => '0'),
                      i_mask            => (others => '1'),
                      o_value           => o_register_file_2_register_file_0_register_0_bit_field_0(4*(12*i+6*j+2*k+l)+3 downto 4*(12*i+6*j+2*k+l)),
                      o_value_unmasked  => open
                    );
                end generate;
              end block;
              g_bit_field_1: block
              begin
                g: for l in 0 to 1 generate
                begin
                  u_bit_field: entity work.rggen_bit_field
                    generic map (
                      WIDTH                     => 4,
                      INITIAL_VALUE             => slice(x"0", 4, 0),
                      SW_WRITE_ENABLE_POLARITY  => RGGEN_ACTIVE_HIGH
                    )
                    port map (
                      i_clk             => i_clk,
                      i_rst_n           => i_rst_n,
                      i_sw_valid        => bit_field_valid,
                      i_sw_read_mask    => bit_field_read_mask(8+4*l+3 downto 8+4*l),
                      i_sw_write_enable => register_value(0 downto 0),
                      i_sw_write_mask   => bit_field_write_mask(8+4*l+3 downto 8+4*l),
                      i_sw_write_data   => bit_field_write_data(8+4*l+3 downto 8+4*l),
                      o_sw_read_data    => bit_field_read_data(8+4*l+3 downto 8+4*l),
                      o_sw_value        => bit_field_value(8+4*l+3 downto 8+4*l),
                      o_write_trigger   => open,
                      o_read_trigger    => open,
                      i_hw_write_enable => "0",
                      i_hw_write_data   => (others => '0'),
                      i_hw_set          => (others => '0'),
                      i_hw_clear        => (others => '0'),
                      i_value           => (others => '0'),
                      i_mask            => (others => '1'),
                      o_value           => o_register_file_2_register_file_0_register_0_bit_field_1(4*(12*i+6*j+2*k+l)+3 downto 4*(12*i+6*j+2*k+l)),
                      o_value_unmasked  => open
                    );
                end generate;
              end block;
              g_bit_field_2: block
              begin
                g: for l in 0 to 1 generate
                begin
                  u_bit_field: entity work.rggen_bit_field
                    generic map (
                      WIDTH                     => 4,
                      INITIAL_VALUE             => slice(x"0", 4, 0),
                      SW_WRITE_ENABLE_POLARITY  => RGGEN_ACTIVE_LOW
                    )
                    port map (
                      i_clk             => i_clk,
                      i_rst_n           => i_rst_n,
                      i_sw_valid        => bit_field_valid,
                      i_sw_read_mask    => bit_field_read_mask(16+4*l+3 downto 16+4*l),
                      i_sw_write_enable => register_value(32*(6+7*i+6)+0+1*l+0 downto 32*(6+7*i+6)+0+1*l),
                      i_sw_write_mask   => bit_field_write_mask(16+4*l+3 downto 16+4*l),
                      i_sw_write_data   => bit_field_write_data(16+4*l+3 downto 16+4*l),
                      o_sw_read_data    => bit_field_read_data(16+4*l+3 downto 16+4*l),
                      o_sw_value        => bit_field_value(16+4*l+3 downto 16+4*l),
                      o_write_trigger   => open,
                      o_read_trigger    => open,
                      i_hw_write_enable => "0",
                      i_hw_write_data   => (others => '0'),
                      i_hw_set          => (others => '0'),
                      i_hw_clear        => (others => '0'),
                      i_value           => (others => '0'),
                      i_mask            => (others => '1'),
                      o_value           => o_register_file_2_register_file_0_register_0_bit_field_2(4*(12*i+6*j+2*k+l)+3 downto 4*(12*i+6*j+2*k+l)),
                      o_value_unmasked  => open
                    );
                end generate;
              end block;
            end generate;
          end generate;
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
            g: if (bit_slice(x"00000003", \__i\) = '0') generate
              bit_field_read_data(\__i\) <= '0';
              bit_field_value(\__i\) <= '0';
            end generate;
          end generate;
          u_register: entity work.rggen_default_register
            generic map (
              READABLE        => true,
              WRITABLE        => true,
              ADDRESS_WIDTH   => 7,
              OFFSET_ADDRESS  => x"20"+32*i+x"18",
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
              o_register_active       => register_active(6+7*i+6),
              o_register_ready        => register_ready(6+7*i+6),
              o_register_status       => register_status(2*(6+7*i+6)+1 downto 2*(6+7*i+6)),
              o_register_read_data    => register_read_data(32*(6+7*i+6)+31 downto 32*(6+7*i+6)),
              o_register_value        => register_value(32*(6+7*i+6)+0+31 downto 32*(6+7*i+6)+0),
              o_bit_field_valid       => bit_field_valid,
              o_bit_field_read_mask   => bit_field_read_mask,
              o_bit_field_write_mask  => bit_field_write_mask,
              o_bit_field_write_data  => bit_field_write_data,
              i_bit_field_read_data   => bit_field_read_data,
              i_bit_field_value       => bit_field_value
            );
          g_bit_field_0: block
          begin
            g: for j in 0 to 1 generate
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
                  i_sw_read_mask    => bit_field_read_mask(0+1*j+0 downto 0+1*j),
                  i_sw_write_enable => "1",
                  i_sw_write_mask   => bit_field_write_mask(0+1*j+0 downto 0+1*j),
                  i_sw_write_data   => bit_field_write_data(0+1*j+0 downto 0+1*j),
                  o_sw_read_data    => bit_field_read_data(0+1*j+0 downto 0+1*j),
                  o_sw_value        => bit_field_value(0+1*j+0 downto 0+1*j),
                  o_write_trigger   => open,
                  o_read_trigger    => open,
                  i_hw_write_enable => "0",
                  i_hw_write_data   => (others => '0'),
                  i_hw_set          => (others => '0'),
                  i_hw_clear        => (others => '0'),
                  i_value           => (others => '0'),
                  i_mask            => (others => '1'),
                  o_value           => o_register_file_2_register_file_0_register_1_bit_field_0(1*(2*i+j)+0 downto 1*(2*i+j)),
                  o_value_unmasked  => open
                );
            end generate;
          end block;
        end block;
      end block;
    end generate;
  end block;
end rtl;
