module top ();

   function bit m_matches_type_pair(string match_type_pair,
      string requested_type);
   endfunction

   function void func();
      m_matches_type_pair(.match_type_pair("a"),
                             .requested_type("b"));

      m_matches_type_pair("c", "d");  
      
      m_matches_type_pair(.requested_type("e"),
                             .match_type_pair("f"));

   endfunction

endmodule

