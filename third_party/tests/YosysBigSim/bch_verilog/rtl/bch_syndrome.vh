`include "bch.vh"

function integer syndrome_size;
	input [31:0] m;
	input [31:0] s;
	integer b;
	integer c;
	integer done;
	integer ret;
begin
	ret = 0;
	b = lpow(m, s);
	c = b;
	done = 0;

	while (!done) begin
		ret = ret + 1;
		c = finite_mult(m, c, c);
		if (c == b)
			done = 1;
	end
	syndrome_size = ret;
end
endfunction

/* 0 = first method, 1 = second method */
function integer syndrome_method;
	input [31:0] m;
	input [31:0] t;
	input [31:0] s;
	integer done;
	integer s_size;
	integer i;
	integer first_way;
begin
	s_size = syndrome_size(m, s);

	/* We can only use the first way if syndrome size is full */
	first_way = s_size == m;
	done = !first_way;

	i = s;
	while (!done) begin
		if (i <= 2 * t - 1) begin
			if (i != s) begin
				/* Cannot use first way */
				first_way = 0;
				done = 1;
			end
		end
		i = (i * 2) % m2n(m);
		if (i == s)
			/* yay, we can use the first way */
			done = 1;
	end

	syndrome_method = !first_way;
end
endfunction

function integer next_syndrome;
	input [31:0] m;
	input [31:0] s;
	integer tmp;
	integer n;
	integer done;
	integer ret;
begin

	n = m2n(m);
	ret = s + 2;
	tmp = ret;
	done = 0;

	while (!done) begin
		tmp = tmp * 2;
		if (tmp >= n)
			tmp = tmp - n;
		if (tmp < ret) begin
			ret = ret + 2;
			tmp = ret;
		end else if (tmp == ret)
			done = 1;
	end
	next_syndrome = ret;
end
endfunction

function integer syndrome_count;
	input [31:0] m;
	input [31:0] t;
	integer s;
	integer ret;
begin
	s = 1;
	ret = 0;
	while (s <= 2 * t - 1) begin
		ret = ret + 1;
		s = next_syndrome(m, s);
	end
	syndrome_count = ret;
end
endfunction

/*
 * dat goes from 1..2*t-1, its the output syndromes
 * Each dat is generated from a syn, an lfsr register
 * syn1 (dat1, dat2, dat4), syn3 (dat3), syn5 (dat5)
 * idxes number syns (syn1->0, syn3->1, syn5->2, etc)
 */
function integer syn2idx;
	input [31:0] m;
	input [31:0] syn;
	integer s;
	integer ret;
begin
	s = 1;
	ret = 0;
	while (s != syn) begin
		ret = ret + 1;
		s = next_syndrome(m, s);
	end
	syn2idx = ret;
end
endfunction

function integer idx2syn;
	input [31:0] m;
	input [31:0] idx;
	integer i;
	integer ret;
begin
	ret = 1;
	i = 0;
	while (i != idx) begin
		i = i + 1;
		ret = next_syndrome(m, ret);
	end
	idx2syn = ret;
end
endfunction

function integer dat2syn;
	input [31:0] m;
	input [31:0] dat;
	integer s;
	integer i;
	integer done;
	integer ret;
begin
	s = 1;
	ret = 0;

	while (!ret) begin
		done = 0;
		i = s;
		while (!done && !ret) begin
			if (i == dat)
				ret = s;
			i = (i * 2) % m2n(m);
			if (i == s)
				done = 1;
		end
		if (i == dat)
			ret = s;
		s = next_syndrome(m, s);
	end
	dat2syn = ret;
end
endfunction

function integer dat2idx;
	input [31:0] m;
	input [31:0] dat;
	integer s;
	integer i;
	integer done1;
	integer done2;
	integer ret;
begin
	s = 1;
	ret = 0;
	done1 = 0;
	while (!done1) begin
		done2 = 0;
		i = s;
		while (!done1 && !done2) begin
			if (i == dat)
				done1 = 1;
			i = (i * 2) % m2n(m);
			if (i == s)
				done2 = 1;
		end
		s = next_syndrome(m, s);
		if (!done1)
			ret = ret + 1;
	end
	dat2idx = ret;
end
endfunction
