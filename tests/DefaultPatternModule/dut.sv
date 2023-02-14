module top #(
)(
);
localparam int unsigned CNT = 2;
// localparam int unsigned V[CNT] = '{3,3};
localparam int unsigned V[CNT] = '{default: 3};
/*
typedef int unsigned ASSIGN_VADDR_RET_T[CNT];
function static ASSIGN_VADDR_RET_T ASSIGN_VADDR();
    for (int i = 0; i < CNT; i++) begin
         ASSIGN_VADDR[i] = V[i];
    end
endfunction

localparam int unsigned VADDR[CNT] = ASSIGN_VADDR();

if (VADDR[0] != 3) begin
	$info("--[0] (%d) should be 3",VADDR[0]);
end;
if (VADDR[1] != 3) begin
	$info("--[1] (%d) should be 3",VADDR[1]);
end;

if (VADDR[1] == 3) begin
	$info("--[1] (%d) should be 5",VADDR[1]);
end;
*/
endmodule
/*
module main;
top #() top1();
endmodule
*/