


module vcache_profiler ();

    always @(negedge clk_i) begin
        
        if (~reset_i & trace_en_i) begin
          trace_fd = $fopen(tracefile_lp, "a");

          // If miss handler has finished the dma request and result is ready
          // for a missed request
          if (inc_miss_ld)
            print_operation_trace(trace_fd, my_name, "miss_ld");
          else if (inc_miss_st)
            print_operation_trace(trace_fd, my_name, "miss_st");


          // If miss handler is still busy on a request
          else if (miss_v) begin
            print_operation_trace(trace_fd, my_name, "miss");
          end 

        
          // If response is ready for a hit request
          else begin

            if (inc_ld) begin
              if (inc_ld_ld) 
                print_operation_trace(trace_fd, my_name, "ld_ld");
              else if (inc_ld_ldu)
                print_operation_trace(trace_fd, my_name, "ld_ldu");
              else if (inc_ld_lw)
                print_operation_trace(trace_fd, my_name, "ld_lw");
              else if (inc_ld_lwu)
                print_operation_trace(trace_fd, my_name, "ld_lwu");
              else if (inc_ld_lh)
                print_operation_trace(trace_fd, my_name, "ld_lh");
              else if (inc_ld_lhu)
                print_operation_trace(trace_fd, my_name, "ld_lhu");
              else if (inc_ld_lb) 
                print_operation_trace(trace_fd, my_name, "ld_lb");
              else if (inc_ld_lbu)
                print_operation_trace(trace_fd, my_name, "ld_lbu");
              else
                print_operation_trace(trace_fd, my_name, "ld");
            end


            else if (inc_st) begin
              if (inc_sm_sd)
                print_operation_trace(trace_fd, my_name, "sm_sd");  
              else if (inc_sm_sw)
                print_operation_trace(trace_fd, my_name, "sm_sw");  
              else if (inc_sm_sh)
                print_operation_trace(trace_fd, my_name, "sm_sh");  
              else if (inc_sm_sb)
                print_operation_trace(trace_fd, my_name, "sm_sb");  
              else
                print_operation_trace(trace_fd, my_name, "st");
            end


            else if (inc_stall_rsp)
              print_operation_trace(trace_fd, my_name, "stall_rsp");

            else if (inc_tagst)
              print_operation_trace(trace_fd, my_name, "tagst");
            else if (inc_tagfl)
              print_operation_trace(trace_fd, my_name, "tagfl");
            else if (inc_taglv)
              print_operation_trace(trace_fd, my_name, "taglv");
            else if (inc_tagla)
              print_operation_trace(trace_fd, my_name, "tagla");

             
            else if (inc_afl)
              print_operation_trace(trace_fd, my_name, "afl");
              
            else if (inc_aflinv)
              print_operation_trace(trace_fd, my_name, "aflinv");
              
            else if (inc_ainv)
              print_operation_trace(trace_fd, my_name, "ainv");
              
            else if (inc_alock)
              print_operation_trace(trace_fd, my_name, "alock");
              
            else if (inc_aunlock)
              print_operation_trace(trace_fd, my_name, "aunlock");
              
            else if (inc_atomic)
              print_operation_trace(trace_fd, my_name, "atomic");

              
            else if (inc_amoswap)
              print_operation_trace(trace_fd, my_name, "amoswap");
            else if (inc_amoor)
              print_operation_trace(trace_fd, my_name, "amoor");
            else if (inc_amoadd)
              print_operation_trace(trace_fd, my_name, "amoadd");
            else
              print_operation_trace(trace_fd, my_name, "idle");
              
          end

        end // if (~reset_i & trace_en_i)
    end // always @ (negedge clk_i)


endmodule
