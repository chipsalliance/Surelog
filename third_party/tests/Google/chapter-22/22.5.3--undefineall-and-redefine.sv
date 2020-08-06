/*
:name: 22.5.3--undefineall-and-redefine
:description: Test
:tags: 22.5.3
:type: preprocessing
*/
`define FOO "foo"
`undefineall
`define FOO 5
`undefineall
`define FOO(x,y) (x + y)
