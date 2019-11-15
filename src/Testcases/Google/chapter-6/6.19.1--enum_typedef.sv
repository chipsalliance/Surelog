/*
:name: enum_typedef
:description: typedef enum tests
:should_fail: 0
:tags: 6.19.1
*/
module top();
	typedef enum {a, b, c} e;
	e val;
endmodule
