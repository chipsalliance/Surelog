module ForNarrowRequest();

  int array[10];

endmodule


module InitializedBlockRAM();

  generate
    if (1) begin : body
        ForNarrowRequest ram ();
    end
  endgenerate

  function automatic void InitializeMemory();
    $readmemh(body.ram.array);
  endfunction

endmodule // InitializedBlockRAM
