library ieee;
use ieee.std_logic_1164.all;

library foo;
use foo.foo_m;

library bar;
use bar.bar_m;

entity top is
	port (
		clock : in std_logic;
		a : in std_logic;
		b : in std_logic;
		x : out std_logic;
		y : out std_logic
	);
end entity;

architecture rtl of top is
	component foo_m is
		port (
			clock : in std_logic;
			a : in std_logic;
			b : in std_logic;
			x : out std_logic;
			y : out std_logic
		);
	end component;
	component bar_m is
		port (
			clock : in std_logic;
			a : in std_logic;
			b : in std_logic;
			x : out std_logic;
			y : out std_logic
		);
	end component;
	signal t1, t2 : std_logic;
begin
	foo_inst : foo_m port map (
		clock => clock,
		a     => a,
		b     => b,
		x     => t1,
		y     => t2
	);

	bar_inst : bar_m port map (
		clock => clock,
		a     => t1,
		b     => t2,
		x     => x,
		y     => y
	);
end architecture;
