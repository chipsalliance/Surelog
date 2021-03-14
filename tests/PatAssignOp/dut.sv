
module top ();
  localparam coh_noc_dims_p         = 2;
  localparam coh_noc_trans_p        = 0;
  localparam  coh_noc_x_cord_width_p = 10;
  localparam  coh_noc_y_cord_width_p = 20;
  localparam int coh_noc_cord_markers_pos_p[coh_noc_dims_p:0] = coh_noc_trans_p ? '{coh_noc_x_cord_width_p+coh_noc_y_cord_width_p, coh_noc_y_cord_width_p, 0}                
      : '{coh_noc_y_cord_width_p+coh_noc_x_cord_width_p, coh_noc_x_cord_width_p, 0};
  localparam coh_noc_cord_width_p   = coh_noc_cord_markers_pos_p[coh_noc_dims_p];  
  if (coh_noc_cord_width_p != 30) begin
     BAD bad();
  end
     
endmodule
