module top #() ();
    typedef int unsigned ASSIGN_VADDR_RET_T[2];
    function static ASSIGN_VADDR_RET_T ASSIGN_VADDR();
        for (int i = 0; i < 2; i++) begin
             ASSIGN_VADDR[i] = 5;
        end
    endfunction

    localparam int unsigned VADDR[2] = ASSIGN_VADDR();

	if (VADDR[0] != 5) begin
		$info("--[0] (%d) should be 5",VADDR[0]);
	end;
	if (VADDR[1] != 5) begin
		$info("--[1] (%d) should be 5",VADDR[1]);
	end;
	if (VADDR[1] == 5) begin
		$info("--[1] (%d) is 5!!!",VADDR[1]);
	end;
endmodule

module main;
    top #()top1 ();
endmodule

