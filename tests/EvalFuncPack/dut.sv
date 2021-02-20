
package prim_util_pkg;



  function automatic integer _clog2(integer value);
    integer result;
    value = value - 1;
    for (result = 0; value > 0; result = result + 1) begin
      value = value >> 1;
    end
    return result;
  endfunction

function automatic integer vbits(integer value);

    return (value == 1) ? 1 : prim_util_pkg::_clog2(value);

  endfunction


endpackage

package flash_ctrl_pkg;

parameter int InfoTypes = 3;
parameter int InfosPerBank    = max_info_pages('{
    10,
    1,
    2
  });

 parameter int InfoPageW       = prim_util_pkg::vbits(InfosPerBank);

function automatic integer max_info_pages(int infos[InfoTypes]);
    int current_max = 0;
    for (int i = 0; i < InfoTypes; i++) begin
      if (infos[i] > current_max) begin
        current_max = infos[i];
      end
    end
    return current_max;
  endfunction // max_info_banks

endpackage


package otp_ctrl_pkg;

  import prim_util_pkg::vbits;
  


  parameter int NumPartWidth = vbits(InfosPerBank);

  
endpackage

module flash_ctrl_info_cfg import flash_ctrl_pkg::*; ();

logic [InfoPageW-1:0] CurPage;

endmodule // flash_ctrl_info_cfg

