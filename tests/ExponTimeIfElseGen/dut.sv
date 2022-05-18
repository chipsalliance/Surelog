module Foo ( );
   parameter ADDR_OFFSET_PART_1 = 1;
   
    generate
        for( genvar i = 0 ; i <= 17 ; i++ ) begin
            if( i == ADDR_OFFSET_PART_0 ) begin
                always_ff @(posedge clk) begin
                    if( shift_foo_bar ) begin
                        foo_bar_4[i] <= foo_bar_4[i+1];
                    end

                end
            end
            else if( i == ADDR_OFFSET_PART_1 ) begin
                always_ff @(posedge clk) begin
                    if( shift_foo_bar ) begin
                        foo_bar_4[i] <= foo_bar_4[i+1];
                    end

                end
            end
            else if( i == ADDR_OFFSET_PART_2 ) begin
                always_ff @(posedge clk) begin
                    if( shift_foo_bar ) begin
                        foo_bar_4[i] <= foo_bar_4[i+1];
                    end

                end
            end
            else if( i == ADDR_OFFSET_PART_3 ) begin
                always_ff @(posedge clk) begin
                    if( shift_foo_bar ) begin
                        foo_bar_4[i] <= foo_bar_4[i+1];
                    end

                end
            end
            else if( i == ADDR_OFFSET_0 ) begin
                always_ff @(posedge clk) begin
                    if( shift_foo_bar ) begin
                        foo_bar_4[i] <= foo_bar_4[i+1];
                    end

                end
            end
            else if( i == ADDR_OFFSET_1 ) begin
                always_ff @(posedge clk) begin
                    if( shift_foo_bar ) begin
                        foo_bar_4[i] <= foo_bar_4[i+1];
                    end

                end
            end
            else if( i == ADDR_OFFSET_2 ) begin
                always_ff @(posedge clk) begin
                    if( shift_foo_bar ) begin
                        foo_bar_4[i] <= foo_bar_4[i+1];
                    end

                end
            end
            else if( i == ADDR_OFFSET_3 ) begin
                always_ff @(posedge clk) begin
                    if( shift_foo_bar ) begin
                        foo_bar_4[i] <= foo_bar_4[i+1];
                    end

                end
            end
            else if( i == ADDR_OFFSET_PART_0_STRIDE ) begin
                always_ff @(posedge clk) begin
                    if( shift_foo_bar ) begin
                        foo_bar_4[i] <= foo_bar_4[i+1];
                    end

                end
            end
            else if( i == ADDR_OFFSET_PART_1_STRIDE ) begin
                always_ff @(posedge clk) begin
                    if( shift_foo_bar ) begin
                        foo_bar_4[i] <= foo_bar_4[i+1];
                    end

                end
            end

        end
    endgenerate


endmodule // Foo
