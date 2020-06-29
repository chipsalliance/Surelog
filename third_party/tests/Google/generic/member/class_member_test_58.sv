/*
:name: class_member_test_58
:description: Test
:tags: 8.3
*/
class myclass extends uvm_object;
constraint solve_this {
  solve x before y;
  solve x.z before y.x;
  solve x.z, f, g before q, r, y.x;
  solve x.z[2], f[1], g before q, r[4], y[3].x;
}
endclass