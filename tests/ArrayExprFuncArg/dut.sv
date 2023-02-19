module top #(
)(
);
localparam int unsigned CNT = 3;
// localparam int unsigned V[CNT] = '{3,3};
//localparam int unsigned V[CNT] = '{default: 3};
 localparam int unsigned V[CNT] = '{3,5,4};

typedef int unsigned ASSIGN_VADDR_RET_T[CNT];
function static ASSIGN_VADDR_RET_T ASSIGN_VADDR();
   for (int i = 0; i < CNT; i++) begin
	ASSIGN_VADDR[i] = V[i];
       end
endfunction

localparam int unsigned VADDR[CNT] = ASSIGN_VADDR();
if (VADDR[0] == 3) begin
   $info("VADDR[0] == 3");
end
if (VADDR[2] == 4) begin
   $info("VADDR[2] == 4");
end


function static int unsigned MAX_VADDR_CNT(int unsigned SRC[CNT], int unsigned ICNT);
    MAX_VADDR_CNT = 0;
    for (int i = 0; i < ICNT; i++) begin
        if (SRC[i] > MAX_VADDR_CNT) begin
            MAX_VADDR_CNT = SRC[i];
        end
    end
endfunction

localparam int unsigned MAX_VADDR = MAX_VADDR_CNT(VADDR, CNT);	
if (MAX_VADDR == 3) begin
   $info("MAX_VADDR == 3");
end
if (MAX_VADDR == 5) begin
   $info("MAX_VADDR == 5");
end   
if (MAX_VADDR != 3) begin
   $info("MAX_VADDR != 3");
end
endmodule

module main;
top #() top1();
endmodule
