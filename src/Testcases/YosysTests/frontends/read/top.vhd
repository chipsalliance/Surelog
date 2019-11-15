library IEEE;
    use IEEE.STD_LOGIC_1164.ALL;

entity top is
	Port (  x : in STD_LOGIC;
			y : in STD_LOGIC;
			cin : in STD_LOGIC;
			clk : in STD_LOGIC;
			A : out STD_LOGIC;
			cout : out STD_LOGIC
		);
end entity;

architecture beh of top is
begin
	A <= y + cin;
	cout <= y + A;
end architecture;
