interface AXI_BUS #(
 parameter AXI_ID_WIDTH   = -1
);

  typedef logic [AXI_ID_WIDTH-1:0]   id_t;
  
  id_t       aw_id;
   
  modport Master (
    output aw_id
  );

 
endinterface


