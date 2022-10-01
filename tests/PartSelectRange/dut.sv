module test();

  parameter [3:0] MAP = 4'b01_00;
  parameter N = 2;
   
  genvar i;
  for(i=0;i<N;i=i+1)
     begin: loop
	if (MAP[i*2+1:i*2] == 2'b00)
	  begin: foo
	     foo i0 ();
	  end
	else if (MAP[i*2+1:i*2] == 2'b01)
	  begin: bar
	     bar i0 ();
	  end
     end

endmodule
