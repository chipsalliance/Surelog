all: work
	touch .stamp

clean::
	rm -f .stamp

define template
$(foreach design,$(1),
$(foreach script,$(2),
work:: $(design)/work_$(script)/.stamp

$(design)/work_$(script)/.stamp:
	./run.sh $(design) $(script)

clean::
	rm -rf $(design)/work_$(script)
))
endef

#issue_00790
$(eval $(call template,issue_00790,issue_00790))

#issue_00018
$(eval $(call template,issue_00018,issue_00018))

#issue_00041
$(eval $(call template,issue_00041,issue_00041))

#issue_00059
$(eval $(call template,issue_00059,issue_00059))

#issue_00065
ifeq ($(ENABLE_HEAVY_TESTS),1)
$(eval $(call template,issue_00065,issue_00065))
endif

#issue_00067
$(eval $(call template,issue_00067,issue_00067))

#issue_00071
$(eval $(call template,issue_00071,issue_00071))

#issue_00078
$(eval $(call template,issue_00078,issue_00078))

#issue_00081
$(eval $(call template,issue_00081,issue_00081))

#issue_00082
#yosys> read_verilog top_fault.v
#1. Executing Verilog-2005 frontend.
#Parsing Verilog input from `top_fault.v' to AST representation.
#top_fault.v:4: ERROR: Internal error - should not happen - no AST_WIRE node.
#
$(eval $(call template,issue_00082,issue_00082))

#issue_00083
#Warning: Deep recursion in AST simplifier.
#Does this design contain insanely long expressions?
#run.sh: line 21: 17264 Segmentation fault      (core dumped) yosys -ql yosys.log ../../scripts/$2.ys
#make: *** [Makefile:24: issue_00083/work_issue_00083/.stamp] Error 139
#
$(eval $(call template,issue_00083,issue_00083))

#issue_00084
$(eval $(call template,issue_00084,issue_00084))

#issue_00085
$(eval $(call template,issue_00085,issue_00085))

#issue_00086
$(eval $(call template,issue_00086,issue_00086))

#issue_00088
$(eval $(call template,issue_00088,issue_00088))

#issue_00089
$(eval $(call template,issue_00089,issue_00089))

#issue_00091
$(eval $(call template,issue_00091,issue_00091))

#issue_00093
$(eval $(call template,issue_00093,issue_00093))

#issue_00095
$(eval $(call template,issue_00095,issue_00095))

#issue_00096
$(eval $(call template,issue_00096,issue_00096))

#issue_00098
$(eval $(call template,issue_00098,issue_00098))

#issue_00099
$(eval $(call template,issue_00099,issue_00099))

#issue_00102
$(eval $(call template,issue_00102,issue_00102))

#issue_00111
$(eval $(call template,issue_00111,issue_00111))

#issue_00114
$(eval $(call template,issue_00114,issue_00114))

#issue_00126
$(eval $(call template,issue_00126,issue_00126))

#issue_00128
$(eval $(call template,issue_00128,issue_00128))

#issue_00132
$(eval $(call template,issue_00132,issue_00132))

#issue_00133
$(eval $(call template,issue_00133,issue_00133))

#issue_00134
$(eval $(call template,issue_00134,issue_00134))

#issue_00160
$(eval $(call template,issue_00160,issue_00160))

#issue_00171
$(eval $(call template,issue_00171,issue_00171))

#issue_00173
$(eval $(call template,issue_00173,issue_00173))

#issue_00174
$(eval $(call template,issue_00174,issue_00174))

#issue_00175
$(eval $(call template,issue_00175,issue_00175))

#issue_00182
$(eval $(call template,issue_00182,issue_00182))

#issue_00183
$(eval $(call template,issue_00183,issue_00183))

#issue_00186
$(eval $(call template,issue_00186,issue_00186))

#issue_00194
$(eval $(call template,issue_00194,issue_00194))

#issue_00195
$(eval $(call template,issue_00195,issue_00195))

#issue_00196
$(eval $(call template,issue_00196,issue_00196))

#issue_00210
$(eval $(call template,issue_00210,issue_00210))

#issue_00253
$(eval $(call template,issue_00253,issue_00253))

#issue_00282
$(eval $(call template,issue_00282,issue_00282))

#issue_00283
$(eval $(call template,issue_00283,issue_00283))

#issue_00287
$(eval $(call template,issue_00287,issue_00287))

#issue_00289
$(eval $(call template,issue_00289,issue_00289))

#issue_00291
$(eval $(call template,issue_00291,issue_00291))

#issue_00300
$(eval $(call template,issue_00300,issue_00300))

#issue_00306
$(eval $(call template,issue_00306,issue_00306))

#issue_00314
$(eval $(call template,issue_00314,issue_00314))

#issue_00317
$(eval $(call template,issue_00317,issue_00317))

#issue_00341
$(eval $(call template,issue_00341,issue_00341))

#issue_00342
$(eval $(call template,issue_00342,issue_00342))

#issue_00349
$(eval $(call template,issue_00349,issue_00349))

#issue_00350
$(eval $(call template,issue_00350,issue_00350))

#issue_00361
$(eval $(call template,issue_00361,issue_00361))

#issue_00362
$(eval $(call template,issue_00362,issue_00362))

#issue_00372
$(eval $(call template,issue_00372,issue_00372))

#issue_00391
$(eval $(call template,issue_00391,issue_00391))

#issue_00432
$(eval $(call template,issue_00432,issue_00432))

#issue_00444
$(eval $(call template,issue_00444,issue_00444))

#issue_00449
$(eval $(call template,issue_00449,issue_00449))

#issue_00457
$(eval $(call template,issue_00457,issue_00457))

#issue_00474
$(eval $(call template,issue_00474,issue_00474))

#issue_00481
$(eval $(call template,issue_00481,issue_00481))

#issue_00502
$(eval $(call template,issue_00502,issue_00502))

#issue_00524
$(eval $(call template,issue_00524,issue_00524))

#issue_00527
$(eval $(call template,issue_00527,issue_00527))

#issue_00567
$(eval $(call template,issue_00567,issue_00567))

#issue_00582
$(eval $(call template,issue_00582,issue_00582))

#issue_00589
$(eval $(call template,issue_00589,issue_00589))

#issue_00594
$(eval $(call template,issue_00594,issue_00594))

#issue_00603
$(eval $(call template,issue_00603,issue_00603))

#issue_00628
$(eval $(call template,issue_00628,issue_00628))

#issue_00630
$(eval $(call template,issue_00630,issue_00630))

#issue_00635
$(eval $(call template,issue_00635,issue_00635))

#issue_00639
$(eval $(call template,issue_00639,issue_00639))

#issue_00642
$(eval $(call template,issue_00642,issue_00642))

#issue_00644
$(eval $(call template,issue_00644,issue_00644))

#issue_00655
$(eval $(call template,issue_00655,issue_00655))

#issue_00675
$(eval $(call template,issue_00675,issue_00675))

#issue_00685
$(eval $(call template,issue_00685,issue_00685))

#issue_00689
$(eval $(call template,issue_00689,issue_00689))

#issue_00699
$(eval $(call template,issue_00699,issue_00699))

#issue_00705
$(eval $(call template,issue_00705,issue_00705))

#issue_00708
$(eval $(call template,issue_00708,issue_00708))

#issue_00737
$(eval $(call template,issue_00737,issue_00737))

#issue_00763
$(eval $(call template,issue_00763,issue_00763))

#issue_00767
$(eval $(call template,issue_00767,issue_00767))

#issue_00774
ifeq ($(ENABLE_HEAVY_TESTS),1)
$(eval $(call template,issue_00774,issue_00774))
endif

#issue_00781
$(eval $(call template,issue_00781,issue_00781))

#issue_00785
$(eval $(call template,issue_00785,issue_00785))

#issue_00807
$(eval $(call template,issue_00807,issue_00807))

#issue_00809
$(eval $(call template,issue_00809,issue_00809))

#issue_00810
$(eval $(call template,issue_00810,issue_00810))

#issue_00814
$(eval $(call template,issue_00814,issue_00814))

#issue_00823
$(eval $(call template,issue_00823,issue_00823))

#issue_00826
$(eval $(call template,issue_00826,issue_00826))

#issue_00831
$(eval $(call template,issue_00831,issue_00831))

#issue_00835
$(eval $(call template,issue_00835,issue_00835))

#issue_00857
$(eval $(call template,issue_00857,issue_00857))

#issue_00862
$(eval $(call template,issue_00862,issue_00862))

#issue_00865 - test failed (should be ok after merge https://github.com/YosysHQ/yosys/pull/866)
$(eval $(call template,issue_00865,issue_00865))

#issue_00867
$(eval $(call template,issue_00867,issue_00867))

#issue_00870
$(eval $(call template,issue_00870,issue_00870))

#issue_00873
$(eval $(call template,issue_00873,issue_00873))

#issue_00888
$(eval $(call template,issue_00888,issue_00888))

#issue_00896
$(eval $(call template,issue_00896,issue_00896))

#issue_00922
$(eval $(call template,issue_00922,issue_00922))

#issue_00931
$(eval $(call template,issue_00931,issue_00931))

#issue_00935
$(eval $(call template,issue_00935,issue_00935))

#issue_00938
$(eval $(call template,issue_00938,issue_00938))

#issue_00940
$(eval $(call template,issue_00940,issue_00940))

#issue_00948
$(eval $(call template,issue_00948,issue_00948))

#issue_00954
$(eval $(call template,issue_00954,issue_00954))

#issue_00955
$(eval $(call template,issue_00955,issue_00955))

#issue_00956
$(eval $(call template,issue_00956,issue_00956))

#issue_00961
$(eval $(call template,issue_00961,issue_00961))

#issue_00968
$(eval $(call template,issue_00968,issue_00968))

#issue_00981
$(eval $(call template,issue_00981,issue_00981))

#issue_00982
$(eval $(call template,issue_00982,issue_00982))

#issue_00987
$(eval $(call template,issue_00987,issue_00987))

#issue_00993
$(eval $(call template,issue_00993,issue_00993))

#issue_00997
$(eval $(call template,issue_00997,issue_00997))

#issue_01002
$(eval $(call template,issue_01002,issue_01002))

#issue_01016
$(eval $(call template,issue_01016,issue_01016))

#issue_01022
$(eval $(call template,issue_01022,issue_01022))

#issue_01023
$(eval $(call template,issue_01023,issue_01023))

#issue_01033
$(eval $(call template,issue_01033,issue_01033))

#issue_01034
$(eval $(call template,issue_01034,issue_01034))

#issue_01040
$(eval $(call template,issue_01040,issue_01040))

#issue_01047
$(eval $(call template,issue_01047,issue_01047))

#issue_01063
$(eval $(call template,issue_01063,issue_01063))

#issue_01065
$(eval $(call template,issue_01065,issue_01065))

#issue_01070
$(eval $(call template,issue_01070,issue_01070))

#issue_01084
$(eval $(call template,issue_01084,issue_01084))

#issue_01091
$(eval $(call template,issue_01091,issue_01091))

#issue_01093
$(eval $(call template,issue_01093,issue_01093))

#issue_01115
$(eval $(call template,issue_01115,issue_01115))

#issue_01118
$(eval $(call template,issue_01118,issue_01118))

#issue_01128
$(eval $(call template,issue_01128,issue_01128))

#issue_01131
$(eval $(call template,issue_01131,issue_01131))

#issue_01132
$(eval $(call template,issue_01132,issue_01132))

#issue_01135
$(eval $(call template,issue_01135,issue_01135))

#issue_01144
$(eval $(call template,issue_01144,issue_01144))

#issue_01145
$(eval $(call template,issue_01145,issue_01145))

#issue_01220
$(eval $(call template,issue_01220,issue_01220))

#issue_01223
$(eval $(call template,issue_01223,issue_01223))

#issue_01231
$(eval $(call template,issue_01231,issue_01231))

#issue_01243
$(eval $(call template,issue_01243,issue_01243))

#issue_01273
$(eval $(call template,issue_01273,issue_01273))

#issue_01284
$(eval $(call template,issue_01284,issue_01284))

#issue_01329
$(eval $(call template,issue_01329,issue_01329))

#issue_01364
$(eval $(call template,issue_01364,issue_01364))

#issue_01372
$(eval $(call template,issue_01372,issue_01372))




#Still open bugs (should be failed):
#issue_00329
$(eval $(call template,issue_00329,issue_00329))

#issue_00623
$(eval $(call template,issue_00623,issue_00623))

#issue_00656
$(eval $(call template,issue_00656,issue_00656))

#issue_01014
$(eval $(call template,issue_01014,issue_01014))

#issue_01126
$(eval $(call template,issue_01126,issue_01126))

#issue_01161
$(eval $(call template,issue_01161,issue_01161))

#issue_01193
$(eval $(call template,issue_01193,issue_01193))

#issue_01206
$(eval $(call template,issue_01206,issue_01206))

#issue_01216
$(eval $(call template,issue_01216,issue_01216))

#issue_01217
$(eval $(call template,issue_01217,issue_01217))

#issue_01225
$(eval $(call template,issue_01225,issue_01225))

#issue_01259
$(eval $(call template,issue_01259,issue_01259))

#issue_01291
$(eval $(call template,issue_01291,issue_01291))

#issue_01360
$(eval $(call template,issue_01360,issue_01360))




.PHONY: all clean
