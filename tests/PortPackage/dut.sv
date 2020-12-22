package dm;

 typedef struct packed {
        logic [31:24] zero1;
        logic         dataaccess;
    } hartinfo_t;

endpackage

module dm_top #(
    parameter int                 NrHarts          = 1
) (
    dm::hartinfo_t [NrHarts-1:0]  hartinfo_i
);


endmodule
