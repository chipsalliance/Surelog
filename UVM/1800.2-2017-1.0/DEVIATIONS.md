# List of issues and clarifications to be addressed in the next version of the standard.

During development of the Accellera UVM 2017 Implementation, the UVM Working Group has encountered
the following issues which resulted in the implementation deviating from the 1800.2-2017 standard.

# Issues

1. The `uvm_callbacks::get_all` method as defined in section 10.7.2.5 is insufficient to retrieve all callbacks registered on a given *instance* of an object, as there is no way to filter based on an object instance.  The implementation adds an additional argument to the method to overcome the issue of resolving the instance specific callbacks. 

The implemented signature is:
<pre>
  static function void get_all ( ref CB all_callbacks[$] <b>, input T obj=null</b> ); 
</pre>

[Mantis 6377](https://accellera.mantishub.io/view.php?id=6377)

2. The `uvm_packer::set_packed_*` and `uvm_packer::get_packed_*` methods as defined in sections 16.5.3.1 and 16.5.3.2 use `signed` arguments while the `uvm_object::pack` and `uvm_object::unpack` methods are specified in sections 5.3.10 and 5.3.11 as `unsigned`. The implementation keeps the arguments `unsigned`, so as to remain consistent with the other packing APIs.

The implemented sigatures are:
<pre>
virtual function void uvm_packer::set_packed_bits( ref bit <b>unsigned</b> stream[] );
virtual function void uvm_packer::set_packed_bytes( ref byte <b>unsigned</b> stream[] );
virtual function void uvm_packer::set_packed_ints( ref int <b>unsigned</b> stream[] );
virtual function void uvm_packer::set_packed_longints( ref longint <b>unsigned</b> stream[] );

virtual function void uvm_packer::get_packed_bits( ref bit <b>unsigned</b> stream[] );
virtual function void uvm_packer::get_packed_bytes( ref byte <b>unsigned</b> stream[] );
virtual function void uvm_packer::get_packed_ints( ref int <b>unsigned</b> stream[] );
virtual function void uvm_packer::get_packed_longints( ref longint <b>unsigned</b> stream[] );
</pre>

[Mantis 6423](https://accellera.mantishub.io/view.php?id=6423)

3. The `uvm_phase::get_objection` method is defined in section 9.3.1.7.1 as being non-`virtual`.  The implementation has made the function virtual to ensure uniformity with the other **Phase done objections** methods defined in section 9.3.1.7.  

<pre>
  <b>virtual</b> function int uvm_phase::get_objection_count( uvm_object obj=null );
</pre>

[Mantis 6260](https://accellera.mantishub.io/view.php?id=6260)

4.  The `uvm_printer` and `uvm_comparer` classes have methods defined for configuration in sections 16.2.5 and 16.3.4.  Each of these configuration values is specified as being cleared via a call to `flush`; however since `uvm_object` always calls `flush` on these policies when they're invoked with an active object depth of 0 (see 16.1.3.4), only the default values could ever be used.  The implementation does _NOT_ clear these values on a flush.

[Mantis 6482](https://accellera.mantishub.io/view.php?id=6482)

5.  The `uvm_printer::set_default`, `uvm_table_printer::set_default`, `uvm_tree_printer::set_default`, and `uvm_line_printer::set_default` methods defined in sections 16.2.2.2, 16.2.10.2.3, 16.2.11.2.3, and 16.2.12.2.3 allow the user to set the associated default printer instances.  The standard does not explicitly call out what happens when these default values are set to `null`, indicating that all of the associated `get_default` calls should be guarded with `null` checks on the return value.  Instead of forcing these checks on the user, the implementation ensures that the return value will never be `null`.  When `get_default` is called after a corresponding `set_default(null)`, the implementation returns the printer instance that would have been returned if `get_default` had been called without *any* previous calls to `set_default`.

[Mantis 6308](https://accellera.mantishub.io/view.php?id=6308)

6. Section 16.4.7.7 states that the `uvm_recorder::do_record_object` method is `pure virtual`, while also stating that it has a default implementation.  As it is impossible to provide a default implemntation to a `pure virtual` method in SystemVerilog, the implementation declares the function as `virtual`.

<pre>
  <del>pure</del> virtual protected function void do_record_object(string name, uvm_object value);
</pre>

[Mantis 6591](https://accellera.mantishub.io/view.php?id=6591) 

7. The `uvm_resource_db::read_by_name` and `uvm_resource_db::read_by_type` methods are defined in sections C.3.2.2.6 and C.3.2.2.7 as having an *output* argument *val* of type *T*.  This is backwards incompatible with previous UVM versions, and would result in the user needing to keep additional copies values in order to avoid a failed read overwriting a previous value.  As such, the implementation keeps the arguments as *inouts* to avoid these problems.

<pre>
  static function bit uvm_resource_db::read_by_type(input string scope, <b>inout</b> T val, input uvm_object accessor = null);
  static function bit uvm_resource_db::read_by_name(input string scope, input string name, <b>inout</b> T val, input uvm_object accessor = null);
</pre>

[Mantis 6807](https://accellera.mantishub.io/view.php?id=6807) 

8. The `uvm_sequence_base::do_kill` method is defined in 14.2.5.12 as being non-`virtual`.  This runs in contradiction to the fact that the method is defined as being a user hook.  As such, the implementation declares the method as `virtual` to allow extension.

<pre>
  virtual function void do_kill();
</pre>

[Mantis 6768](https://accellera.mantishub.io/view.php?id=6768) 

9.  The `uvm_sequencer_base::ungrab` and `uvm_sequencer_base::unlock()` methods are specified in sections 15.3.2.12 and 15.3.2.13 as being tasks.  This is backwards incompatible with prior UVM releases, and produces a problem for any user code which needs to unlock in zero time.  As such, the implementation declares the methods as `function void`.

<pre>
  virtual function void unlock( uvm_sequence_base sequence_ptr )
  virtual function void ungrab( uvm_sequence_base sequence_ptr )
</pre>

[Mantis 6769](https://accellera.mantishub.io/view.php?id=6769)

10.  Section 18.2.3.5 says that an address map may be added to multiple address maps if it is accessible from multiple pysical interfaces.  This map structure was not supported in UVM1.2 and an attempt to add to multiple address maps would result in an error.  Adding such support will require extensive rework and likely API enhancements, which was not in the scope of the 1.0 implementation effort.  This implementation will still produce an error if an address map is added to multiple address maps.

[Mantis 4009](https://accellera.mantishub.io/view.php?id=4009)
