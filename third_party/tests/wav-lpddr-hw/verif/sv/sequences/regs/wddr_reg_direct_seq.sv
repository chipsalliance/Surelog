/*********************************************************************************
Copyright (c) 2021 Wavious LLC

This program is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

This program is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with this program.  If not, see <http://www.gnu.org/licenses/>.

*********************************************************************************/
class wddr_reg_direct_seq extends wddr_base_seq;

    `uvm_object_utils(wddr_reg_direct_seq)

    function new(string name="wddr_reg_direct_seq");
        super.new(name);
    endfunction

    logic [31:0] data = 0;

    string reg_array[] = {
        "WDDR_CH0_DQ0_DQ_DQS_TX_DDR_M0_R0_CFG_7",
        "WDDR_CH1_DQ0_DQ_DQS_TX_DDR_M0_R0_CFG_7",
        "WDDR_CH1_DQ0_DQ_DQS_TX_DDR_M0_R1_CFG_7",
        "WDDR_CH1_DQ1_DQ_DQS_TX_DDR_M0_R1_CFG_7",
        //"WDDR_CH0_DQ1_DQ_DQS_TX_DDR_M0_R1_CFG_7",
        "WDDR_CH1_DQ0_DQ_DQS_TX_DDR_X_SEL_M0_R1_CFG_7"
    };

    virtual task body();

        for ( int i =0 ; i < reg_array.size() ; i++)
        begin
            reg_name = $sformatf(reg_array[i]);
            regstr = reg_model.get_reg_by_name({reg_name});
            regstr.write(status, 32'hF);
            reg_name = $sformatf(reg_array[i]);
            regstr = reg_model.get_reg_by_name({reg_name});
            regstr.read(status, data);
            if ( data != 32'hF )
                `uvm_error(get_type_name(), $sformatf("ERROR: %s register value read  = %h ", reg_array[i], data));
        end

    endtask

endclass: wddr_reg_direct_seq

