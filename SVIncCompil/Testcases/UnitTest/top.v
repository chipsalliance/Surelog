
`define declare_bp_fe_be_if(vaddr_width_mp, paddr_width_mp, asid_width_mp, branch_metadata_fwd_width_mp) \
                                                                                             \
  typedef struct packed                                                                            \
  {                                                                                                \
    logic [`bp_fe_fetch_padding_width(vaddr_width_mp, branch_metadata_fwd_width_mp)-1:0]           \
                                              padding;                                             \
  }  bp_fe_fetch_s;                                                                                \
                                                                                                   \

`define BSG_MAX(x,y) (((x)>(y)) ? (x) : (y))

`define fetch(vaddr_width_mp, branch_metadata_fwd_width_mp)                 \
  (vaddr_width_mp + bp_instr_width_gp + branch_metadata_fwd_width_mp)

`define exception(vaddr_width_mp)                                           \
  (vaddr_width_mp + $bits(bp_fe_exception_code_e))

   
`define queue(vaddr_width_mp, branch_metadata_fwd_width_mp)                      \
  (1 + `BSG_MAX(`fetch(vaddr_width_mp,branch_metadata_fwd_width_mp)         \
                , `exception(vaddr_width_mp)                                \
                )                                                                                  \
   )

   

class c2;

//`declare_bp_fe_be_if(vaddr_width_p, paddr_width_p, asid_width_p, branch_metadata_fwd_width_p);
   
`queue(vaddr_width_p, branch_metadata_fwd_width_p);                          
 endclass



