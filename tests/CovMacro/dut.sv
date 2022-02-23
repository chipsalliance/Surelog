
module DUT;
endmodule

module top();
    int unsigned i;
    real r;
    DUT unit1();
    DUT unit2();

    initial begin
        i = $coverage_control(`SV_COV_CHECK, `SV_COV_TOGGLE, `SV_COV_HIER, $root.top);
        i = $coverage_control(`SV_COV_RESET, `SV_COV_TOGGLE, `SV_COV_MODULE, "DUT");
        i = $coverage_control(`SV_COV_RESET, `SV_COV_TOGGLE, `SV_COV_MODULE, $root.top.unit1);
        i = $coverage_control(`SV_COV_STOP,  `SV_COV_TOGGLE, `SV_COV_HIER, $root.top.unit2);
        i = $coverage_control(`SV_COV_START, `SV_COV_TOGGLE, `SV_COV_HIER, "DUT");
        i = $coverage_get_max(`SV_COV_TOGGLE, `SV_COV_HIER, "DUT");
        r = $coverage_get(`SV_COV_STATEMENT, `SV_COV_HIER, $root.top.unit1);
        i = $coverage_merge(`SV_COV_ASSERTION, "some_name");
        i = $coverage_save(`SV_COV_FSM_STATE, "some_name");
        $set_coverage_db_name("coverage.db");
        $load_coverage_db("coverage.db");
        r = $get_coverage();
    end
endmodule
