library ieee;
use ieee.std_logic_1164.all;

entity foo_m is
	port (
		clock : in std_logic;
		a : in std_logic;
		b : in std_logic;
		x : out std_logic;
		y : out std_logic
	);
end entity;

architecture rtl of foo_m is
begin
	process (clock) begin
		if (rising_edge(clock)) then
			x <= a and b;
			y <= a or b;
		end if;
	end process;
end architecture;
