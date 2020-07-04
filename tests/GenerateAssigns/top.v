module dut(input a, input b, output y);
  parameter p = 2, q = 4;
  //---------------------------------------------------------
  // Code to either generate a u1.g1 instance or no instance.
  // The u1.g1 instance of one of the following gates:
  // (and, or, xor, xnor) is generated if
  // {p,q} == {1,0}, {1,2}, {2,0}, {2,1}, {2,2}, {2, default}
  //---------------------------------------------------------

  if (p == 1)
    if (q == 0)
      begin : u1
        // If p==1 and q==0, then instantiate
        assign y = a & b;
        // AND with hierarchical name test.u1.g1
      end
    else if (q == 2)
      begin : u1
      // If p==1 and q==2, then instantiate
        assign y = a | b;
      // OR with hierarchical name test.u1.g1
      end
    else
      begin :u1
        assign y = a ~& b;
      end
  else
    begin : u2
      case (q)
        0, 1, 2:
          begin : u1
            // If p==2 and q==0,1, or 2, then instantiate
            assign y = a ^ b;
          end
        default:
          begin : u1
            // If p==2 and q!=0,1, or 2, then instantiate
            assign y = a ~^ b;
          end
      endcase
    end

endmodule
