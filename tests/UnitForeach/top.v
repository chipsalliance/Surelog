class moreobj;
     function mine();
     endfunction
endclass


class uvm_reg_map;
/*
    function test();

  for (i = 0; i < 16; i = i +1) begin
    	  	$display1 ("here");
    	end
 
               begin
                        uvm_severity q[$];
   $display3 ("here");
                end

                begin
                        string q[$];
  
                end
$display2 ("here");


    foreach (m_extensions[ext_]) begin
  		uvm_report_server srvr;
	    srvr=uvm_report_server::get_server();        
    	srvr.report_summarize();
srvr1.report_summarize();
    end

   begin
		uvm_report_server srvr;
	    srvr=uvm_report_server::get_server();        
    	srvr.report_summarize();
srvr1.report_summarize();
    end

  endfunction
*/



  local moreobj     m_submaps[uvm_reg_map];   
  local moreobj     m_submaps2[*];   
  local moreobj     m_submaps3[$];
  function void set_check_on_read();
      string sarray[10];
     moreobj an_obj;
     m_submaps3.push_back(an_obj);

     foreach (m_submaps[submap]) begin
          submap.set_check_on_read();
          submap.bad1();
          m_submaps[submap].bad2();
          m_submaps[submap].mine();
      end

     foreach (m_submaps2[i]) begin
          i.bad3();
          m_submaps[i].bad4();
          m_submaps[i].mine();
      end

    foreach (m_submaps3[i]) begin
         i.bad5();
         m_submaps3[i].bad6();
         m_submaps3[i].mine();
      end


     foreach (sarray[submap]) begin
         submap.set_check_on_read();
         submap.bad6();
      end

   endfunction



endclass
