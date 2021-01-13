SHELL=/bin/bash
NAME := lowrisc_systems_top_earlgrey_nexysvideo_0.1
BITSTREAM := lowrisc_systems_top_earlgrey_nexysvideo_0.1.bit
PART := xc7a200tsbg484-1

all: $(BITSTREAM)

$(NAME).runs/synth_1/__synthesis_is_complete__: $(NAME)_synth.tcl $(NAME).xpr
	vivado -notrace -mode batch -source $^

synth: $(NAME).runs/synth_1/__synthesis_is_complete__

$(BITSTREAM): $(NAME)_run.tcl $(NAME).xpr
	vivado -notrace -mode batch -source $< $(NAME).xpr

$(NAME).xpr: $(NAME).tcl
	vivado -notrace -mode batch -source $<

build-gui: $(NAME).xpr
	vivado $<

pgm: $(NAME)_pgm.tcl $(BITSTREAM)
	export HW_TARGET=$(HW_TARGET); \
	export JTAG_FREQ=$(JTAG_FREQ); \
	vivado -quiet -nolog -notrace -mode batch -source $< -tclargs $(PART) $(BITSTREAM)
