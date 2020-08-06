/*
:name: class_member_test_57
:description: Test
:tags: 8.3
*/
class foo_class extends bar;
constraint gain_constraint {
  A dist {1 := 90, 0 := 10 };
  if (c_g[A:B] == 0) c_g[K:0] == 0;
  if (c_g[A:B] == 1) { c_g[K:0] == 1; }
  c_g[A:B] != '1;
}
endclass