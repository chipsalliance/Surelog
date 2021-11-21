SIMULATION_DIRECTORIES	:= $(subst /makefile,,$(wildcard */makefile))
SUMULATION_TARGETS			:= $(addprefix simulation_, $(SIMULATION_DIRECTORIES))
CLEAN_TARGETS						:= $(addprefix clean_, $(SIMULATION_DIRECTORIES))

SIMULATOR	?= vcs

.PHONY: all $(SUMULATION_TARGETS) clean $(CLEAN_TARGETS)

all: $(SUMULATION_TARGETS)

$(SUMULATION_TARGETS):
	make -C $(subst simulation_,,$@) SIMULATOR=$(SIMULATOR)

clean: $(CLEAN_TARGETS)

$(CLEAN_TARGETS):
	make -C $(subst clean_,,$@) clean_all
