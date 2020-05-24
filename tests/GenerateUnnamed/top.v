module test1;
  parameter p = 2, q = 4;
  wire a, b, c;
  //---------------------------------------------------------
  // Code to either generate a u1.g1 instance or no instance.
  // The u1.g1 instance of one of the following gates:
  // (and, or, xor, xnor) is generated if
  // {p,q} == {1,0}, {1,2}, {2,0}, {2,1}, {2,2}, {2, default}
  //---------------------------------------------------------

  or sg1(a, b, c);

  if (p == 1)
    if (q == 0)
      begin : u1
        // If p==1 and q==0, then instantiate
        and g1(a, b, c);
        // AND with hierarchical name test.u1.g1
      end
    else if (q == 2)
      begin : u1
      // If p==1 and q==2, then instantiate
      or g1(a, b, c);
      // OR with hierarchical name test.u1.g1
      end
    // "else" added to end "if (q == 2)" statement
    else ;
  // If p==1 and q!=0 or 2, then no instantiation
  else if (p == 2) begin 
    case (q)
      0, 1, 2:
        begin : u1
          // If p==2 and q==0,1, or 2, then instantiate
          xor g2(a, b, c); // XOR with hierarchical name test.u1.g1
        end
      default:
        begin : u1
          // If p==2 and q!=0,1, or 2, then instantiate
          xnor g3(a, b, c); // XNOR with hierarchical name test.u1.g1
        end
    endcase

    if (1)
      begin 
        xnor g4(a, b, c); 
      end


    if (1)
      begin : n5
        xnor g5(a, b, c); 
      end

  end 

endmodule



module test2;
  parameter p = 2, q = 4;
  wire a, b, c;
  //---------------------------------------------------------
  // Code to either generate a u1.g1 instance or no instance.
  // The u1.g1 instance of one of the following gates:
  // (and, or, xor, xnor) is generated if
  // {p,q} == {1,0}, {1,2}, {2,0}, {2,1}, {2,2}, {2, default}
  //---------------------------------------------------------

  or sg1(a, b, c);

  if (p == 1)
    if (q == 0)
      begin : u1
        // If p==1 and q==0, then instantiate
        and g1(a, b, c);
        // AND with hierarchical name test.u1.g1
      end
  else if (q == 2)
    begin : u1
      // If p==1 and q==2, then instantiate
      or g1(a, b, c);
      // OR with hierarchical name test.u1.g1
    end
  // "else" added to end "if (q == 2)" statement
  else ;
  // If p==1 and q!=0 or 2, then no instantiation
  else if (p == 2) begin : pp2
    case (q)
      0, 1, 2:
        begin : u1
          // If p==2 and q==0,1, or 2, then instantiate
          xor g2(a, b, c); // XOR with hierarchical name test.u1.g1
        end
      default:
        begin : u1
          // If p==2 and q!=0,1, or 2, then instantiate
          xnor g3(a, b, c); // XNOR with hierarchical name test.u1.g1
        end
    endcase

    if (1)
      begin 
        xnor g4(a, b, c); 
      end


    if (1)
      begin : n5
        xnor g5(a, b, c); 
      end

  end 

endmodule


