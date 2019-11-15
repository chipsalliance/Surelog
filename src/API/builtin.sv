// SURELOG 
// Builtin SystemVerilog classes

class mailbox;

  function new (int bound = 0);
  endfunction

  function int num();
  endfunction

  task put (message);
  endtask

  function try_put (message);
  endfunction

  task get (ref message);
  endtask

  function int try_get (ref message);
  endfunction

  task peek (ref message);
  endtask

  function int try_peek(ref message);
  endfunction

endclass


class process;

  typedef enum { FINISHED, RUNNING, WAITING, SUSPENDED, KILLED } state;

  static function process self();
  endfunction

  function state status();
  endfunction

  task kill();
  endtask

  task await();
  endtask

  task suspend();
  endtask

  task resume();
  endtask

endclass


class semaphore;

  function new(int keyCount = 0 );
  endfunction

  task put(int keyCount = 1);
  endtask

  task get(int keyCount = 1);
  endtask

  function int try_get(int keyCount = 1);
  endfunction

endclass

