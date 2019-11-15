entity top_vhdl is
generic (WIDTH : integer := 1; INIT : bit := '1'; greeting : string(1 to 9) := "hello    ");
port (clk : in bit; i : in bit_vector(WIDTH-1 downto 0); o : out bit := INIT);
end entity;
architecture rtl of top_vhdl is
begin
	process
	begin
		report greeting;
		--wait;
	end process;
	process (clk)
	begin
		if rising_edge(clk) then
			o <= xor i;
		end if;
	end process;
end rtl;
