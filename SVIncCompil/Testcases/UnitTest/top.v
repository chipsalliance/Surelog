
`ifndef DV_CHECK_FATAL
  `define DV_CHECK_FATAL(T_, MSG_="", ID_=`gfn, WITH_C_=) \
    DV_CHECK(T_, MSG_, fatal, ID_, WITH_C_)
`endif


// Shorthand for common foo.randomize() with { } + fatal check
`ifndef DV_CHECK_RANDOMIZE_WITH_FATAL
  `define DV_CHECK_RANDOMIZE_WITH_FATAL(VAR_, WITH_C_, MSG_="Randomization failed!", ID_=`gfn) \
    `DV_CHECK_FATAL(VAR_.randomize(), MSG_, ID_, with { WITH_C_ })
`endif


`define gfn toto


    `DV_CHECK_RANDOMIZE_WITH_FATAL(valid_leaf_pte,
      // Set the correct privileged mode
      if(privileged_mode == USER_MODE) {
        u == 1'b1;
      } else {
        // Accessing user mode page from supervisor mode is only allowed when MSTATUS.SUM and
        // MSTATUS.MPRV are both 1
        if(!(cfg.mstatus_sum && cfg.mstatus_mprv)) {
          u == 1'b0;
        }
      }
      // Set a,d bit to 1 avoid page/access fault exceptions
      a == 1'b1;
      d == 1'b1;
      // Default: Readable, writable, executable page
      soft xwr == R_W_EXECUTE_PAGE;
      // Page is valid
      v == 1'b1;
    )

    `DV_CHECK_RANDOMIZE_WITH_FATAL(valid_leaf_pte,
      if(privileged_mode == USER_MODE) {
        u == 1'b1;
      } else {
        if(!(cfg.mstatus_sum && cfg.mstatus_mprv)) {
          u == 1'b0;
        }
      }
      // Set a,d bit to 1 avoid page/access fault exceptions
      a == 1'b1;
      d == 1'b1;
      // Default: Readable, writable, executable page
      soft xwr == R_W_EXECUTE_PAGE;
      // Page is valid
      v == 1'b1;
    )
