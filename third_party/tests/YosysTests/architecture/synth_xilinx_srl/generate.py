#!/usr/bin/python3
import re, glob

N = 131

def assert_static_area(fp, i, name):
    if i < 3:
        srl32,srl16,fd = (0,0,i)
    else:
        srl32 = i // 32
        if (i % 32) == 0:
            srl16 = 0
            fd = 0
        elif (i % 32) == 1:
            srl16 = 0
            fd = 1
        elif (i % 32) <= 17:
            srl16 = 1
            fd = (i % 32) - 16
        else:
            srl32 += 1
            srl16 = 0
            fd = 0
    fp.write('''
`ifndef _AUTOTB
module __test ;
    wire [4095:0] assert_area = "cd; select t:FD* -assert-count {0}; select t:SRL16E -assert-count {1}; select t:SRLC32E -assert-count {2}; cd {3}_{4}; select t:BUFG t:FD* t:SRL16E t:SRLC32E %% %n t:* %i -assert-none";
endmodule
`endif
'''.format(fd, srl16, srl32, name, i))

def assert_dynamic_area(fp, i, name):
    if i < 3:
        srl32,srl16,fd = (0,0,i)
        lut3 = 1 if i > 1 else 0
        lut5 = 0
    else:
        srl32 = i // 32
        if (i % 128) == 0 or (i % 32) == 0:
            srl16 = 0
            fd = 0
        elif (i % 128) == 1:
            srl16 = 0
            fd = 1
        elif (i % 32) <= 16:
            srl16 = 1
            fd = 0
        else:
            srl32 += 1
            srl16 = 0
            fd = 0
        lut3 = 1 if i > 128 and i < 257 else 0
        lut5 = 1 if i > 256 else 0
    muxf8 = (srl32+srl16) // 4
    if ((srl32 + srl16) % 4) == 0:
        muxf7 = muxf8 * 2
    elif ((srl32 + srl16) % 4) == 3:
        muxf8 += 1
        muxf7 = muxf8 * 2
    else:
        muxf7 = (srl32+srl16) // 2
    fp.write('''
`ifndef _AUTOTB
module __test ;
    wire [4095:0] assert_area = "cd; select t:FD* -assert-count {0}; select t:SRL16E -assert-count {1}; select t:SRLC32E -assert-count {2}; select t:MUXF7 -assert-count {3}; select t:MUXF8 -assert-count {4}; select t:LUT3 -assert-count {5}; select t:LUT5 -assert-count {6}; cd {7}_{8}; select t:BUFG t:FD* t:SRL16E t:SRLC32E t:MUXF7 t:MUXF8 t:LUT3 t:LUT5 %% %n t:* %i -assert-none";
endmodule
`endif
'''.format(fd, srl16, srl32, muxf7, muxf8, lut3, lut5, name, i))


# Test 1: pos_clk_no_enable_no_init_not_inferred
for i in range(1,N+1):
    with open('pos_clk_no_enable_no_init_not_inferred_%d.v' % i, 'w') as fp:
        fp.write('''
(* top *)
module pos_clk_no_enable_no_init_not_inferred_{0} #(parameter width=1, depth={0}) (input clk, input [width-1:0] i, output [width-1:0] q);
generate 
    wire [depth:0] int [width-1:0];
    genvar w, d;
    for (w = 0; w < width; w=w+1) begin
        assign int[w][0] = i[w];
        for (d = 0; d < depth; d=d+1) begin
            \$_DFFE_PP_ r(.C(clk), .D(int[w][d]), .E(1'b1), .Q(int[w][d+1]));
        end
        assign q[w] = int[w][depth];
    end
endgenerate
endmodule
'''.format(i))
        assert_static_area(fp, i, 'pos_clk_no_enable_no_init_not_inferred')

# Test 2: pos_clk_with_enable_no_init_not_inferred
for i in range(1,N+1):
    with open('pos_clk_with_enable_no_init_not_inferred_%d.v' % i, 'w') as fp:
        fp.write('''
(* top *)
module pos_clk_with_enable_no_init_not_inferred_{0} #(parameter width=1, depth={0}) (input clk, input [width-1:0] i, input e, output [width-1:0] q);
generate 
    wire [depth:0] int [width-1:0];
    genvar w, d;
    for (w = 0; w < width; w=w+1) begin
        assign int[w][0] = i[w];
        for (d = 0; d < depth; d=d+1) begin
            \$_DFFE_PP_ r(.C(clk), .D(int[w][d]), .E(e), .Q(int[w][d+1]));
        end
        assign q[w] = int[w][depth];
    end
endgenerate
endmodule
'''.format(i))
        assert_static_area(fp, i, 'pos_clk_with_enable_no_init_not_inferred')

# Test 3: pos_clk_with_enable_with_init_inferred
for i in range(1,N+1):
    with open('pos_clk_with_enable_with_init_inferred_%d.v' % i, 'w') as fp:
        fp.write('''
(* top *)
module pos_clk_with_enable_with_init_inferred_{0} #(parameter width=1, depth={0}) (input clk, input [width-1:0] i, input e, output [width-1:0] q);
generate 
    reg [depth-1:0] int [width-1:0];

    genvar w, d;
    for (w = 0; w < width; w=w+1) begin
        for (d = 0; d < depth; d=d+1)
            initial int[w][d] <= ~((d+w) % 2);

        if (depth == 1) begin
            always @(posedge clk) if (e) int[w] <= i[w];
            assign q[w] = int[w];
        end
        else begin
            always @(posedge clk) if (e) int[w] <= {{ int[w][depth-2:0], i[w] }};
            assign q[w] = int[w][depth-1];
        end
    end
endgenerate
endmodule
'''.format(i))
        assert_static_area(fp, i, 'pos_clk_with_enable_with_init_inferred')

# Test 4: neg_clk_no_enable_no_init_not_inferred
for i in range(1,N+1):
    with open('neg_clk_no_enable_no_init_not_inferred_%d.v' % i, 'w') as fp:
        fp.write('''
(* top *)
module neg_clk_no_enable_no_init_not_inferred_{0} #(parameter width=1, depth={0}) (input clk, input [width-1:0] i, output [width-1:0] q);
generate 
    wire [depth:0] int [width-1:0];
    genvar w, d;
    for (w = 0; w < width; w=w+1) begin
        assign int[w][0] = i[w];
        for (d = 0; d < depth; d=d+1) begin
            \$_DFFE_NP_ r(.C(clk), .D(int[w][d]), .E(1'b1), .Q(int[w][d+1]));
        end
        assign q[w] = int[w][depth];
    end
endgenerate
endmodule
'''.format(i))
        assert_static_area(fp, i, 'neg_clk_no_enable_no_init_not_inferred')

# Test 5: neg_clk_no_enable_no_init_inferred
for i in range(1,N+1):
    with open('neg_clk_no_enable_no_init_inferred_%d.v' % i, 'w') as fp:
        fp.write('''
(* top *)
module neg_clk_no_enable_no_init_inferred_{0} #(parameter width=1, depth={0}) (input clk, input [width-1:0] i, output [width-1:0] q);
generate 
    reg [depth-1:0] int [width-1:0];

    genvar w, d;
    for (w = 0; w < width; w=w+1) begin
        if (depth == 1) begin
            always @(negedge clk) int[w] <= i[w];
            assign q[w] = int[w];
        end
        else begin
            always @(negedge clk) int[w] <= {{ int[w][depth-2:0], i[w] }};
            assign q[w] = int[w][depth-1];
        end
    end
endgenerate
endmodule
'''.format(i))
        assert_static_area(fp, i, 'neg_clk_no_enable_no_init_inferred')

# Test 6: neg_clk_with_enable_with_init_inferred
for i in range(1,N+1):
    with open('neg_clk_with_enable_with_init_inferred_%d.v' % i, 'w') as fp:
        fp.write('''
(* top *)
module neg_clk_with_enable_with_init_inferred_{0} #(parameter width=1, depth={0}) (input clk, input [width-1:0] i, input e, output [width-1:0] q);
generate 
    reg [depth-1:0] int [width-1:0];

    genvar w, d;
    for (w = 0; w < width; w=w+1) begin
        for (d = 0; d < depth; d=d+1)
            initial int[w][d] <= ~((d+w) % 2);

        if (depth == 1) begin
            always @(negedge clk) if (e) int[w] <= i[w];
            assign q[w] = int[w];
        end
        else begin
            always @(negedge clk) if (e) int[w] <= {{ int[w][depth-2:0], i[w] }};
            assign q[w] = int[w][depth-1];
        end
    end
endgenerate
endmodule
'''.format(i))
        assert_static_area(fp, i, 'neg_clk_with_enable_with_init_inferred')

# Test 10: pos_clk_no_enable_no_init_not_inferred_var_len
for i in range(1,N+1):
    with open('pos_clk_no_enable_no_init_not_inferred_var_len_%d.v' % i, 'w') as fp:
        fp.write('''
(* top *)
module pos_clk_no_enable_no_init_not_inferred_var_len_{0} #(parameter width=1, depth={0}) (input clk, input [width-1:0] i, input [31:0] l, output [width-1:0] q);
generate 
    wire [depth:0] int [width-1:0];
    genvar w, d;
    for (w = 0; w < width; w=w+1) begin
        assign int[w][0] = i[w];
        for (d = 0; d < depth; d=d+1) begin
            \$_DFFE_PP_ r(.C(clk), .D(int[w][d]), .E(1'b1), .Q(int[w][d+1]));
        end
        wire [depth-1:0] t;
        assign t = int[w][depth:1];
        assign q[w] = t[l];
    end
endgenerate
endmodule
'''.format(i))
        assert_dynamic_area(fp, i, 'pos_clk_no_enable_no_init_not_inferred_var_len')

# Test 11: neg_clk_with_enable_with_init_inferred_var_len
for i in range(1,N+1):
    with open('neg_clk_with_enable_with_init_inferred_var_len_%d.v' % i, 'w') as fp:
        fp.write('''
(* top *)
module neg_clk_with_enable_with_init_inferred_var_len_{0} #(parameter width=1, depth={0}) (input clk, input [width-1:0] i, input e, input [31:0] l, output [width-1:0] q);
generate 
    reg [depth-1:0] int [width-1:0];

    genvar w, d;
    for (w = 0; w < width; w=w+1) begin
        for (d = 0; d < depth; d=d+1)
            initial int[w][d] <= ~((d+w) % 2);

        if (depth == 1) begin
            always @(negedge clk) if (e) int[w] <= i[w];
            assign q[w] = int[w];
        end
        else begin
            always @(negedge clk) if (e) int[w] <= {{ int[w][depth-2:0], i[w] }};
            assign q[w] = int[w][l];
        end
    end
endgenerate
endmodule
'''.format(i))
        assert_dynamic_area(fp, i, 'neg_clk_with_enable_with_init_inferred_var_len')

import lfsr_area
re_lfsr = re.compile(r'lfsr_(\d+)\.v')
for fn in glob.glob('lfsr_*.v'):
    m = re_lfsr.match(fn)
    if not m: continue

    W = int(m.group(1))

    with open(fn, 'a') as f:
        print('''
`ifndef _AUTOTB
module __test ;
    wire [4095:0] assert_area = "%s";
endmodule
`endif
''' % lfsr_area.area[W], file=f)

# Test 15: pos_clk_no_enable_no_init_not_inferred
for i in range(128+1,128+N+1):
    with open('pos_clk_no_enable_no_init_not_inferred_%d.v' % i, 'w') as fp:
        fp.write('''
(* top *)
module pos_clk_no_enable_no_init_not_inferred_{0} #(parameter width=1, depth={0}) (input clk, input [width-1:0] i, output [width-1:0] q);
generate 
    wire [depth:0] int [width-1:0];
    genvar w, d;
    for (w = 0; w < width; w=w+1) begin
        assign int[w][0] = i[w];
        for (d = 0; d < depth; d=d+1) begin
            \$_DFFE_PP_ r(.C(clk), .D(int[w][d]), .E(1'b1), .Q(int[w][d+1]));
        end
        assign q[w] = int[w][depth];
    end
endgenerate
endmodule
'''.format(i))
        assert_static_area(fp, i, 'pos_clk_no_enable_no_init_not_inferred')

# Test 16: neg_clk_with_enable_with_init_inferred_var_len
for i in range(128+1,128+N+1):
    with open('neg_clk_with_enable_with_init_inferred_var_len_%d.v' % i, 'w') as fp:
        fp.write('''
(* top *)
module neg_clk_with_enable_with_init_inferred_var_len_{0} #(parameter width=1, depth={0}) (input clk, input [width-1:0] i, input e, input [31:0] l, output [width-1:0] q);
generate 
    reg [depth-1:0] int [width-1:0];

    genvar w, d;
    for (w = 0; w < width; w=w+1) begin
        for (d = 0; d < depth; d=d+1)
            initial int[w][d] <= ~((d+w) % 2);

        if (depth == 1) begin
            always @(negedge clk) if (e) int[w] <= i[w];
            assign q[w] = int[w];
        end
        else begin
            always @(negedge clk) if (e) int[w] <= {{ int[w][depth-2:0], i[w] }};
            assign q[w] = int[w][l];
        end
    end
endgenerate
endmodule
'''.format(i))
        assert_dynamic_area(fp, i, 'neg_clk_with_enable_with_init_inferred_var_len')

# Test 18: neg_clk_with_enable_with_init_inferred2
for i in range(1,N+1):
    with open('neg_clk_with_enable_with_init_inferred2_%d.v' % i, 'w') as fp:
        fp.write('''
(* top *)
module neg_clk_with_enable_with_init_inferred2_{0} #(parameter width=1, depth={0}) (input clk, input [width-1:0] i, input e, output [width-1:0] q);
generate 
    reg [width-1:0] int [depth-1:0];

    genvar w, d;
    for (d = 0; d < depth; d=d+1) begin
        for (w = 0; w < width; w=w+1) begin
            //initial int[d][w] <= ~((d+w) % 2);

            if (d == 0) begin
                always @(negedge clk) if (e) int[d][w] <= i[w];
            end
            else begin
                always @(negedge clk) if (e) int[d][w] <= int[d-1][w];
            end
        end
    end
    assign q = int[depth-1];
endgenerate
endmodule'''.format(i))
        assert_static_area(fp, i, 'neg_clk_with_enable_with_init_inferred2')

# Test 19: pos_clk_with_enable_no_init_inferred2_var_len
for i in range(1,N+1):
    with open('pos_clk_with_enable_no_init_inferred2_var_len_%d.v' % i, 'w') as fp:
        fp.write('''
(* top *)
module pos_clk_with_enable_no_init_inferred2_var_len_{0} #(parameter width=1, depth={0}) (input clk, input [width-1:0] i, input e, input [31:0] l, output [width-1:0] q);
generate 
    reg [width-1:0] int [depth-1:0];

    genvar w, d;
    for (d = 0; d < depth; d=d+1) begin
        for (w = 0; w < width; w=w+1) begin
            initial int[d][w] <= ~((d+w) % 2);

            if (d == 0) begin
                always @(posedge clk) if (e) int[d][w] <= i[w];
            end
            else begin
                always @(posedge clk) if (e) int[d][w] <= int[d-1][w];
            end
        end
    end
    assign q = int[l];
endgenerate
endmodule'''.format(i))
        assert_dynamic_area(fp, i, 'pos_clk_with_enable_no_init_inferred2_var_len')
