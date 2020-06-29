/*
:name: associative-arrays-other-types
:description: Test associative arrays support
:tags: 7.8.5 7.8
*/
module top ();

typedef struct {
    byte B;
    int I[*];
} Unpkt;

int arr [ Unpkt ];

endmodule
