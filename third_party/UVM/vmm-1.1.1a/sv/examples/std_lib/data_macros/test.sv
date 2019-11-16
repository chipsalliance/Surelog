
`include "vmm.sv"

class base;
endclass

class obj extends base;
   int field;
endclass

class vmm_obj extends vmm_data;
  int field;
  `vmm_data_member_begin(vmm_obj)
    `vmm_data_member_scalar(field,vmm_data::DO_ALL);
  `vmm_data_member_end(vmm_obj)
endclass


class trans extends vmm_data;

    typedef enum {OFF, ON} enum_t;

    int scalar = 1234;
    int scalar_array[$];
    int scalar_dynamic_array[];
    int scalar_aa_scalar[int];
    int scalar_aa_string[string];
    string str = "MyString";
    string string_array[$];
    string string_dynamic_array[];
    string string_aa_scalar[int];
    string string_aa_string[string];
    enum_t enm = ON;
    enum_t enum_array[$];
    enum_t enum_dynamic_array[];
    enum_t enum_aa_scalar[int];
    enum_t enum_aa_string[string];
    obj handle;
    obj handle_array[$];
    obj handle_dynamic_array[];
    obj handle_aa_scalar[int];
    obj handle_aa_string[string];
    vmm_obj vmm_handle;
    vmm_obj vmm_handle_array[$];
    vmm_obj vmm_handle_dynamic_array[];
    vmm_obj vmm_handle_aa_scalar[int];
    vmm_obj vmm_handle_aa_string[string];

    bit initialized = initialize();
    function bit initialize();
      scalar_array.push_back(6);
      scalar_array.push_back(7);
      scalar_array.push_back(8);
      scalar_array.push_back(9);
      scalar_dynamic_array = new[4];
      foreach(scalar_dynamic_array[i]) scalar_dynamic_array[i] = 10+i;
      for(int i=1; i<5; ++i) scalar_aa_scalar[i] = -i;
      scalar_aa_string["a"] = -1;
      scalar_aa_string["b"] = -2;
      scalar_aa_string["c"] = -3;
      scalar_aa_string["d"] = -4;
      string_array.push_back("S");
      string_array.push_back("T");
      string_array.push_back("R");
      string_array.push_back("I");
      string_array.push_back("N");
      string_array.push_back("G");
      string_dynamic_array=new[6];
      string_dynamic_array[0] = "d";
      string_dynamic_array[1] = "y";
      string_dynamic_array[2] = "n";
      string_dynamic_array[3] = "s";
      string_dynamic_array[4] = "t";
      string_dynamic_array[5] = "r";
      string_aa_scalar[1] = "a";
      string_aa_scalar[2] = "b";
      string_aa_scalar[3] = "c";
      string_aa_scalar[4] = "d";
      string_aa_string["A"] = "a";
      string_aa_string["B"] = "b";
      string_aa_string["C"] = "c";
      enum_array.push_back(OFF);
      enum_array.push_back(ON);
      enum_array.push_back(ON);
      enum_array.push_back(OFF);
      enum_array.push_back(ON);
      enum_array.push_back(OFF);
      enum_array.push_back(ON);
      enum_array.push_back(OFF);
      enum_array.push_back(OFF);
      enum_dynamic_array = new[7];
      enum_dynamic_array[0] = ON;
      enum_dynamic_array[1] = ON;
      enum_dynamic_array[2] = OFF;
      enum_dynamic_array[3] = ON;
      enum_dynamic_array[4] = OFF;
      enum_dynamic_array[5] = ON;
      enum_dynamic_array[6] = ON;
      enum_aa_scalar[1] = ON;
      enum_aa_scalar[2] = OFF;
      enum_aa_scalar[3] = OFF;
      enum_aa_scalar[4] = ON;
      enum_aa_string["LR"] = ON;
      enum_aa_string["BEDRM"] = OFF;
      enum_aa_string["KITCHEN"] = ON;
      enum_aa_string["BASEMENT"] = OFF;
    endfunction

  `vmm_data_member_begin(trans)
    `vmm_data_member_scalar(scalar, vmm_data::DO_ALL)
    `vmm_data_member_scalar_array(scalar_array, vmm_data::DO_ALL)
    `vmm_data_member_scalar_da(scalar_dynamic_array, vmm_data::DO_ALL)
    `vmm_data_member_scalar_aa_scalar(scalar_aa_scalar, vmm_data::DO_ALL)
    `vmm_data_member_scalar_aa_string(scalar_aa_string, vmm_data::DO_ALL)
    `vmm_data_member_string(str, vmm_data::DO_ALL)
    `vmm_data_member_string_array(string_array, vmm_data::DO_ALL)
    `vmm_data_member_string_da(string_dynamic_array, vmm_data::DO_ALL)
    `vmm_data_member_string_aa_scalar(string_aa_scalar, vmm_data::DO_ALL)
    `vmm_data_member_string_aa_string(string_aa_string, vmm_data::DO_ALL)
    `vmm_data_member_enum(enm, vmm_data::DO_ALL)
    `vmm_data_member_enum_array(enum_array, vmm_data::DO_ALL)
    `vmm_data_member_enum_da(enum_dynamic_array, vmm_data::DO_ALL)
    `vmm_data_member_enum_aa_scalar(enum_aa_scalar, vmm_data::DO_ALL)
    `vmm_data_member_enum_aa_string(enum_aa_string, vmm_data::DO_ALL)
    `vmm_data_member_handle(handle, vmm_data::DO_ALL)
    `vmm_data_member_handle_array(handle_array, vmm_data::DO_ALL)
    `vmm_data_member_handle_da(handle_dynamic_array, vmm_data::DO_ALL)
    `vmm_data_member_handle_aa_scalar(handle_aa_scalar, vmm_data::DO_ALL)
    `vmm_data_member_handle_aa_string(handle_aa_string, vmm_data::DO_ALL)
    `vmm_data_member_vmm_data(vmm_handle, vmm_data::DO_ALL, vmm_data::DO_REF)
    `vmm_data_member_vmm_data_array(vmm_handle_array, vmm_data::DO_ALL, vmm_data::DO_DEEP)
    `vmm_data_member_vmm_data_da(vmm_handle_dynamic_array, vmm_data::DO_ALL, vmm_data::DO_DEEP)
    `vmm_data_member_vmm_data_aa_scalar(vmm_handle_aa_scalar, vmm_data::DO_ALL, vmm_data::DO_DEEP)
    `vmm_data_member_vmm_data_aa_string(vmm_handle_aa_string, vmm_data::DO_ALL, vmm_data::DO_DEEP)
  `vmm_data_member_end(trans)
  
  // NOTE: the `vmm_data_member_end macro defines a ctor; user-defined ctors not possible
  function void init();
    
    handle_dynamic_array = new[4];
    vmm_handle_dynamic_array = new[4];
    vmm_handle = new;

    handle = new; handle.field=100; handle_array.push_back(handle);
    //handle = new; handle.field=200; handle_array.push_back(handle);
    handle = new; handle.field=300; handle_array.push_back(handle);
    handle = new; handle.field=400; handle_array.push_back(handle);

    handle = new; handle.field=500; handle_dynamic_array[0] = handle;
    //handle = new; handle.field=600; handle_dynamic_array[1] = handle;
    handle = new; handle.field=700; handle_dynamic_array[2] = handle;
    handle = new; handle.field=800; handle_dynamic_array[3] = handle;

    handle_aa_scalar[1] = handle_dynamic_array[0];
    handle_aa_scalar[2] = handle_dynamic_array[1];
    //handle_aa_scalar[3] = handle_dynamic_array[2];
    handle_aa_scalar[4] = handle_dynamic_array[3];

    //handle_aa_string["A"] = handle_dynamic_array[0];
    handle_aa_string["B"] = handle_dynamic_array[1];
    handle_aa_string["C"] = handle_dynamic_array[2];
    handle_aa_string["D"] = handle_dynamic_array[3];

    vmm_handle = new; vmm_handle.field='h100; vmm_handle_array.push_back(vmm_handle);
    vmm_handle = new; vmm_handle.field='h200; vmm_handle_array.push_back(vmm_handle);
    vmm_handle = new; vmm_handle.field='h300; vmm_handle_array.push_back(vmm_handle);
    vmm_handle = new; vmm_handle.field='h400; vmm_handle_array.push_back(vmm_handle);

    vmm_handle = new; vmm_handle.field='h500; vmm_handle_dynamic_array[0] = vmm_handle;
    vmm_handle = new; vmm_handle.field='h600; vmm_handle_dynamic_array[1] = vmm_handle;
    vmm_handle = new; vmm_handle.field='h700; vmm_handle_dynamic_array[2] = vmm_handle;
    vmm_handle = new; vmm_handle.field='h800; vmm_handle_dynamic_array[3] = vmm_handle;

    vmm_handle_aa_scalar[1] = vmm_handle_dynamic_array[0];
    vmm_handle_aa_scalar[2] = vmm_handle_dynamic_array[1];
    vmm_handle_aa_scalar[3] = vmm_handle_dynamic_array[2];
    vmm_handle_aa_scalar[4] = vmm_handle_dynamic_array[3];

    vmm_handle_aa_string["A"] = vmm_handle_dynamic_array[0];
    vmm_handle_aa_string["B"] = vmm_handle_dynamic_array[1];
    vmm_handle_aa_string["C"] = vmm_handle_dynamic_array[2];
    vmm_handle_aa_string["D"] = vmm_handle_dynamic_array[3];

  endfunction

  //`vmm_data_byte_size(_max, _n)

endclass


module test;

trans t = new;

initial begin
  t.init();
  t.display();
end

endmodule



