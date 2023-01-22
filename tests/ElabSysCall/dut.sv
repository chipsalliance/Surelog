module top_fatal();
if (1) begin
  $fatal("Cache way size must be at most 4kB");
end
endmodule

module top_error();
if (1) begin
  $error("Cache way size must be at most 4kB");
end
endmodule

module top_warning();
if (1) begin
  $warning("Cache way size must be at most 4kB");
end
endmodule


module top_info();
if (1) begin
  $info("Cache way size must be at most 4kB");
end
endmodule