class top;

function f2 (int i, int j);
endfunction


function f1();
   for ( int j=0,i=4;j<8;j++, i++) begin
      f2(i,j);
f3(i,j);
   end  
  for ( int j=0,i = 4; ; j++, i++) begin
      f2(i,j);
f4(i,j);
   end  
   for ( ; j < 8; j++) begin
 f2(i,j);
f5(i,j);
   end 

   for ( ; ; ) begin
 f2(i,j);
 f6(i,j);
   end 
   

endfunction

endclass