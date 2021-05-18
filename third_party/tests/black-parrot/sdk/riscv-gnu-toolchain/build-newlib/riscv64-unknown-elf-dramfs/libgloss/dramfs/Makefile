#----------------------------------------------------------------------
# Newlib File System sources
#----------------------------------------------------------------------

dramfs_incs = \
	-I/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-newlib/libgloss/dramfs/dramfs \
	-I/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-newlib/libgloss/dramfs/dramfs/littlefs/lfs \
	-I/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-newlib/libgloss/dramfs/dramfs/littlefs/bd

dramfs_srcs = \
	dramfs_fs.c \
	dramfs_fdtable.c \
	lfs.c \
	lfs_util.c \
	lfs_bd.c

dramfs_hdrs = \
	dramfs/dramfs_fs.h \
	dramfs/dramfs_fdtable.h \
	dramfs/littlefs/lfs/lfs.h \
	dramfs/littlefs/bd/lfs_bd.h

dramfs_mkfs_srcs = \
	dramfs_mklfs.c \
	dramfs_util.c \
	lfs.c \
	lfs_util.c \
	lfs_bd.c

dramfs_mkfs_bin = \
	dramfs_mklfs

#-------------------------------------------------------------------------
# Source files
#-------------------------------------------------------------------------
gloss_srcs = \
	sys_close.c \
	sys_execve.c \
	sys_exit.c \
	sys_fork.c \
	sys_fstat.c \
	sys_getpid.c \
	sys_gettimeofday.c \
	sys_isatty.c \
	sys_kill.c \
	sys_link.c \
	sys_lseek.c \
	sys_open.c \
	sys_read.c \
	sys_sbrk.c \
	sys_stat.c \
	sys_times.c \
	sys_unlink.c \
	sys_wait.c \
	sys_write.c

# Multilib support variables.
# TOP is used instead of MULTI{BUILD,SRC}TOP.

MULTIDIRS = 
MULTISUBDIR = 
MULTIDO = true
MULTICLEAN = true

#-------------------------------------------------------------------------
# Basic setup
#-------------------------------------------------------------------------

# Remove all default implicit rules since they can cause subtle bugs
# and they just make things run slower

.SUFFIXES:
% : %,v
% : RCS/%,v
% : RCS/%
% : s.%
% : SCCS/s.%

# Default is to build the prereqs of the all target (defined at bottom)

default : all
.PHONY : default

# Source directory

obj_dir := .
src_dir := /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-newlib/libgloss/dramfs
VPATH   := $(src_dir) $(src_dir)/machine

# Installation directories

prefix  := /home/alain/black-parrot/sdk/install
DESTDIR ?= $(prefix)

install_hdrs_dir := $(DESTDIR)$(prefix)/$(target_alias)/include/machine
install_libs_dir  = $(DESTDIR)$(prefix)/$(target_alias)/lib${MULTISUBDIR}
install_bins_dir := $(DESTDIR)$(prefix)/$(target_alias)/bin

#-------------------------------------------------------------------------
# NEWLIB FS build rules 
#-------------------------------------------------------------------------

dramfs_objs = $(patsubst %.c, %.o, $(dramfs_srcs))

vpath %.c /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-newlib/libgloss/dramfs/dramfs /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-newlib/libgloss/dramfs/dramfs/littlefs/lfs /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-newlib/libgloss/dramfs/dramfs/littlefs/bd

DRAMFS_CC     = riscv64-unknown-elf-dramfs-gcc -B/home/alain/black-parrot/sdk/riscv-gnu-toolchain/build-newlib/riscv64-unknown-elf-dramfs/newlib/ -isystem /home/alain/black-parrot/sdk/riscv-gnu-toolchain/build-newlib/riscv64-unknown-elf-dramfs/newlib/targ-include -isystem /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-newlib/newlib/libc/include -B/home/alain/black-parrot/sdk/riscv-gnu-toolchain/build-newlib/riscv64-unknown-elf-dramfs/libgloss/riscv64 -L/home/alain/black-parrot/sdk/riscv-gnu-toolchain/build-newlib/riscv64-unknown-elf-dramfs/libgloss/libnosys -L/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-newlib/libgloss/riscv64   
DRAMFS_CFLAGS = -O1
DRAMFS_CFLAGS += $(dramfs_incs)
DRAMFS_CFLAGS += -std=c99 -mcmodel=medany
DRAMFS_CFLAGS += -DLFS_NO_ASSERT -DLFS_NO_DEBUG \
                        -DLFS_NO_WARN -DLFS_NO_ERROR -DLFS_NO_INTRINSICS

$(dramfs_objs): %.o : %.c
	$(DRAMFS_CC) $(DRAMFS_CFLAGS) -c $< -o $@

gloss_hdrs += $(dramfs_hdrs)
gloss_objs += $(dramfs_objs)
junk += $(dramfs_objs)

#-------------------------------------------------------------------------
# NEWLIB mkfs rules 
#-------------------------------------------------------------------------

dramfs_mkfs_objs = $(patsubst %.c, %_host.o, $(dramfs_mkfs_srcs))

DRAMFS_MKFS_CC     = gcc
DRAMFS_MKFS_CFLAGS = -O1
DRAMFS_MKFS_CFLAGS += $(dramfs_incs)
DRAMFS_MKFS_CFLAGS += -std=gnu99

$(dramfs_mkfs_objs): %_host.o : %.c
	$(DRAMFS_MKFS_CC) $(DRAMFS_MKFS_CFLAGS) -c $< -o $@

$(dramfs_mkfs_bin): $(dramfs_mkfs_objs)
	$(DRAMFS_MKFS_CC) $(dramfs_mkfs_objs) -o $@

gloss_bins += $(dramfs_mkfs_bin)

#-------------------------------------------------------------------------
# Programs and flags 
#-------------------------------------------------------------------------

# C compiler

CC            := riscv64-unknown-elf-dramfs-gcc -B/home/alain/black-parrot/sdk/riscv-gnu-toolchain/build-newlib/riscv64-unknown-elf-dramfs/newlib/ -isystem /home/alain/black-parrot/sdk/riscv-gnu-toolchain/build-newlib/riscv64-unknown-elf-dramfs/newlib/targ-include -isystem /home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-newlib/newlib/libc/include -B/home/alain/black-parrot/sdk/riscv-gnu-toolchain/build-newlib/riscv64-unknown-elf-dramfs/libgloss/riscv64 -L/home/alain/black-parrot/sdk/riscv-gnu-toolchain/build-newlib/riscv64-unknown-elf-dramfs/libgloss/libnosys -L/home/alain/black-parrot/sdk/riscv-gnu-toolchain/riscv-newlib/libgloss/riscv64   
CFLAGS        := @CFLAGS@
CFLAGS        += -mcmodel=medany
CPPFLAGS      := -I$(obj_dir) -I$(src_dir) $(dramfs_incs) -mcmodel=medany
COMPILE       := $(CC) -MMD -MP $(CPPFLAGS) $(CFLAGS)

# Library creation

AR            := riscv64-unknown-elf-dramfs-ar
RANLIB        := riscv64-unknown-elf-dramfs-ranlib

# Installation

INSTALL       := /usr/bin/install -c
INSTALL_DATA  := /usr/bin/install -c -m 644

#-------------------------------------------------------------------------
# Build Object Files from C Source
#-------------------------------------------------------------------------

gloss_c_srcs = $(filter %.c, $(gloss_srcs))
gloss_c_objs = $(patsubst %.c, %.o, $(notdir $(gloss_c_srcs)))
gloss_c_deps = $(patsubst %.c, %.d, $(notdir $(gloss_c_srcs)))

$(gloss_c_objs) : %.o : %.c
	$(COMPILE) -c $<

gloss_objs += $(gloss_c_objs)
deps += $(gloss_c_deps)
junk += $(gloss_c_deps) $(gloss_c_objs)

#-------------------------------------------------------------------------
# Build Object Files from Assembly Source
#-------------------------------------------------------------------------

gloss_asm_srcs = $(filter %.S, $(gloss_srcs))
gloss_asm_objs = $(patsubst %.S, %.o, $(notdir $(gloss_asm_srcs)))
gloss_asm_deps = $(patsubst %.S, %.d, $(notdir $(gloss_asm_srcs)))

$(gloss_asm_objs) : %.o : %.S
	$(COMPILE) -c -o $@ $<

gloss_objs += $(gloss_asm_objs)
deps += $(gloss_asm_deps)
junk += $(gloss_asm_deps) $(gloss_asm_objs)

#-------------------------------------------------------------------------
# Build libgloss.a
#-------------------------------------------------------------------------

gloss_lib  = libgloss.a
$(gloss_lib) : $(gloss_objs)
	$(AR) rcv $@ $^
	$(RANLIB) $@

junk += $(gloss_lib)

install_hdrs += $(gloss_hdrs)
install_libs += $(gloss_lib)
install_specs += $(gloss_specs)
install_bins += $(gloss_bins)

#-------------------------------------------------------------------------
# Autodependency files
#-------------------------------------------------------------------------

-include $(deps)

deps : $(deps)
.PHONY : deps

#-------------------------------------------------------------------------
# Installation
#-------------------------------------------------------------------------

install_hdrs_wdir += $(addprefix $(src_dir)/, $(install_hdrs))
install-hdrs : $(install_hdrs_wdir)
	test -d $(install_hdrs_dir) || mkdir -p $(install_hdrs_dir)
	for file in $^; do \
		$(INSTALL_DATA) $$file $(install_hdrs_dir)/; \
	done

install-libs : $(install_libs)
	test -d $(install_libs_dir) || mkdir -p $(install_libs_dir)
	for file in $^; do \
		$(INSTALL_DATA) $$file $(install_libs_dir)/$$file; \
	done

install-specs : $(install_specs)
	test -d $(install_libs_dir) || mkdir -p $(install_libs_dir)
	for file in $^; do \
		$(INSTALL_DATA) $$file $(install_libs_dir)/; \
	done

install-bins : $(install_bins)
	test -d $(install_bins_dir) || mkdir -p $(install_bins_dir)
	for file in $^; do \
		$(INSTALL) $$file $(install_bins_dir)/; \
	done

install : install-hdrs install-libs install-specs install-bins
.PHONY : install install-hdrs install-libs

#-------------------------------------------------------------------------
# Regenerate configure information
#-------------------------------------------------------------------------

configure_prereq = \
  $(src_dir)/configure.in \

$(src_dir)/configure : $(configure_prereq)
	cd $(src_dir) && autoconf

config.status : $(src_dir)/configure
	./config.status --recheck

Makefile : $(src_dir)/Makefile.in config.status
	./config.status

dist_junk += config.status Makefile config.log

#-------------------------------------------------------------------------
# Default
#-------------------------------------------------------------------------

all : $(install_libs) $(install_bins)
.PHONY : all

#-------------------------------------------------------------------------
# Clean up junk
#-------------------------------------------------------------------------

clean :
	rm -rf *~ \#* $(junk)

distclean :
	rm -rf *~ \#* $(junk) $(dist_junk)

.PHONY : clean distclean
