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
class wddr_dt_pll_seq extends wddr_base_seq;

    function new(string name="wddr_dt_pll_seq");
        super.new(name);
    endfunction

    `uvm_object_utils(wddr_dt_pll_seq)

    virtual task body();
        super.body();

        // t_pll_sanity(err_cnt);

        if ( err_cnt != 0 ) `uvm_error(get_type_name(), $sformatf("Task t_pll_sanity err_cnt = %d ", err_cnt));

        `uvm_info(get_type_name(), $sformatf("PLL sequence completed!!!!!!!!"),UVM_LOW)

    endtask : body

endclass
