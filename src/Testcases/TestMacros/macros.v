`define ASSERT_EQUALS(x,y) \
    repeat(1)\
    begin\
        if( (x) != (y) ) \
	// A Macro comment \	   
        begin\
            $write( "assert failed %d != %d\n", (x), (y) );\
            $finish;\
        end\
    end 

    // test the assert( should fail)
    `ASSERT_EQUALS(t_data_in,16'hfffe)

`define ASSERT_EQUALS2(x,y) \
    repeat(1)

      
