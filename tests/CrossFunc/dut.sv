module mod_m;
	logic [31:0] a, b;
	covergroup cg(int cg_lim);
	coverpoint a;
	coverpoint b;
	aXb : cross a, b
	{
    
		function CrossQueueType myFunc1(int f_lim);
			for (int i = 0; i < f_lim; ++i)
			myFunc1.push_back('{i,i});
		endfunction
    
		bins one = myFunc1(cg_lim);
		bins two = myFunc2(cg_lim);
    
		function CrossQueueType myFunc2(logic [31:0] f_lim);
			for (logic [31:0] i = 0; i < f_lim; ++i)
			myFunc2.push_back('{2*i,2*i});
		endfunction
    
	}
	endgroup
	cg cg_inst = new(3);
	
	covergroup yy;
	cross a, b
	{
	ignore_bins ignore = binsof(a) intersect { 5, [1:3] };
	}
	endgroup
endmodule
