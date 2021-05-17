
// blah













`define declare_bsg_ready_and_link_sif_s(in_data_width,in_struct_name)    \
   typedef struct packed {                                                \
      logic       v;                                                      \
      logic       ready_and_rev;                                          \
      logic [in_data_width-1:0] data;                                     \
  } in_struct_name
