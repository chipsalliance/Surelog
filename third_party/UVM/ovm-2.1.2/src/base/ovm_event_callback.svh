//
//------------------------------------------------------------------------------
//   Copyright 2007-2009 Mentor Graphics Corporation
//   Copyright 2007-2009 Cadence Design Systems, Inc.
//   All Rights Reserved Worldwide
//
//   Licensed under the Apache License, Version 2.0 (the
//   "License"); you may not use this file except in
//   compliance with the License.  You may obtain a copy of
//   the License at
//
//       http://www.apache.org/licenses/LICENSE-2.0
//
//   Unless required by applicable law or agreed to in
//   writing, software distributed under the License is
//   distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
//   CONDITIONS OF ANY KIND, either express or implied.  See
//   the License for the specific language governing
//   permissions and limitations under the License.
//------------------------------------------------------------------------------

typedef class ovm_object;
typedef class ovm_event;

//------------------------------------------------------------------------------
//
// CLASS: ovm_event_callback
//
// The ovm_event_callback class is an abstract class that is used to create
// callback objects which may be attached to <ovm_events>. To use, you
// derive a new class and override any or both <pre_trigger> and <post_trigger>.
//
// Callbacks are an alternative to using processes that wait on events. When a
// callback is attached to an event, that callback object's callback function
// is called each time the event is triggered.
//
//------------------------------------------------------------------------------

virtual class ovm_event_callback extends ovm_object;

  // Function: new
  //
  // Creates a new callback object.

  function new (string name=""); 
    super.new(name);
  endfunction


  // Function: pre_trigger
  //
  // This callback is called just before triggering the associated event.
  // In a derived class, override this method to implement any pre-trigger
  // functionality.
  //
  // If your callback returns 1, then the event will not trigger and the
  // post-trigger callback is not called. This provides a way for a callback
  // to prevent the event from triggering.
  //
  // In the function, ~e~ is the <ovm_event> that is being triggered, and ~data~
  // is the optional data associated with the event trigger.

  virtual function bit pre_trigger (ovm_event e, ovm_object data=null);
    return 0;
  endfunction


  // Function: post_trigger
  //
  // This callback is called after triggering the associated event.
  // In a derived class, override this method to implement any post-trigger
  // functionality.
  //
  //
  // In the function, ~e~ is the <ovm_event> that is being triggered, and ~data~
  // is the optional data associated with the event trigger.

  virtual function void post_trigger (ovm_event e, ovm_object data=null);
    return;
  endfunction


  virtual function ovm_object create (string name=""); 
    return null;
  endfunction

endclass


