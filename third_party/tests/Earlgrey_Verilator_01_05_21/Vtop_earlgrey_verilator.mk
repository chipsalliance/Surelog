# Verilated -*- Makefile -*-
# DESCRIPTION: Verilator output: Makefile for building Verilated archive or executable
#
# Execute this makefile from the object directory:
#    make -f Vtop_earlgrey_verilator.mk

default: Vtop_earlgrey_verilator

### Constants...
# Perl executable (from $PERL)
PERL = perl
# Path to Verilator kit (from $VERILATOR_ROOT)
VERILATOR_ROOT = /usr/local/share/verilator
# SystemC include directory with systemc.h (from $SYSTEMC_INCLUDE)
SYSTEMC_INCLUDE ?= 
# SystemC library directory with libsystemc.a (from $SYSTEMC_LIBDIR)
SYSTEMC_LIBDIR ?= 

### Switches...
# SystemC output mode?  0/1 (from --sc)
VM_SC = 0
# Legacy or SystemC output mode?  0/1 (from --sc)
VM_SP_OR_SC = $(VM_SC)
# Deprecated
VM_PCLI = 1
# Deprecated: SystemC architecture to find link library path (from $SYSTEMC_ARCH)
VM_SC_TARGET_ARCH = linux

### Vars...
# Design prefix (from --prefix)
VM_PREFIX = Vtop_earlgrey_verilator
# Module prefix (from --prefix)
VM_MODPREFIX = Vtop_earlgrey_verilator
# User CFLAGS (from -CFLAGS on Verilator command line)
VM_USER_CFLAGS = \
	-I../src/lowrisc_dv_dpi_gpiodpi_0.1 \
	-I../src/lowrisc_dv_dpi_spidpi_0.1 \
	-I../src/lowrisc_dv_dpi_tcp_server_0.1 \
	-I../src/lowrisc_dv_dpi_uartdpi_0.1 \
	-I../src/lowrisc_dv_dpi_usbdpi_0.1 \
	-I../src/lowrisc_dv_dv_macros_0 \
	-I../src/lowrisc_dv_verilator_memutil_dpi_0/cpp \
	-I../src/lowrisc_dv_verilator_simutil_verilator_0/cpp \
	-I../src/lowrisc_prim_assert_0.1/rtl \
	-I../src/lowrisc_prim_util_memload_0/rtl \
	-I../src/lowrisc_dv_dpi_dmidpi_0.1 \
	-I../src/lowrisc_dv_dpi_jtagdpi_0.1 \
	-I../src/lowrisc_dv_verilator_memutil_verilator_0/cpp \
	-I../src/lowrisc_ip_otbn_tracer_0/cpp \
	-I../src/lowrisc_dv_otbn_model_0.1 \
	-std=c++11 -Wall -DVM_TRACE_FMT_FST -DVL_USER_STOP -DTOPLEVEL_NAME=top_earlgrey_verilator -g \

# User LDLIBS (from -LDFLAGS on Verilator command line)
VM_USER_LDLIBS = \
	-lz \
	-pthread -lutil -lelf \

# User .cpp files (from .cpp's on Verilator command line)
VM_USER_CLASSES = \
	dmidpi \
	gpiodpi \
	jtagdpi \
	monitor_spi \
	spidpi \
	tcp_server \
	uartdpi \
	monitor_usb \
	usb_crc \
	usbdpi \
	iss_wrapper \
	otbn_model \
	otbn_trace_checker \
	dpi_memutil \
	sv_scoped \
	verilator_memutil \
	verilated_toplevel \
	verilator_sim_ctrl \
	log_trace_listener \
	otbn_trace_source \
	top_earlgrey_verilator \

# User .cpp directories (from .cpp's on Verilator command line)
VM_USER_DIR = \
	../src/lowrisc_dv_dpi_dmidpi_0.1 \
	../src/lowrisc_dv_dpi_gpiodpi_0.1 \
	../src/lowrisc_dv_dpi_jtagdpi_0.1 \
	../src/lowrisc_dv_dpi_spidpi_0.1 \
	../src/lowrisc_dv_dpi_tcp_server_0.1 \
	../src/lowrisc_dv_dpi_uartdpi_0.1 \
	../src/lowrisc_dv_dpi_usbdpi_0.1 \
	../src/lowrisc_dv_otbn_model_0.1 \
	../src/lowrisc_dv_verilator_memutil_dpi_0/cpp \
	../src/lowrisc_dv_verilator_memutil_verilator_0/cpp \
	../src/lowrisc_dv_verilator_simutil_verilator_0/cpp \
	../src/lowrisc_ip_otbn_tracer_0/cpp \
	../src/lowrisc_systems_top_earlgrey_verilator_0.1 \


### Default rules...
# Include list of all generated classes
include Vtop_earlgrey_verilator_classes.mk
# Include global rules
include $(VERILATOR_ROOT)/include/verilated.mk

### Executable rules... (from --exe)
VPATH += $(VM_USER_DIR)

dmidpi.o: ../src/lowrisc_dv_dpi_dmidpi_0.1/dmidpi.c
	$(OBJCACHE) $(CXX) $(CXXFLAGS) $(CPPFLAGS) $(OPT_FAST) -c -o $@ $<
gpiodpi.o: ../src/lowrisc_dv_dpi_gpiodpi_0.1/gpiodpi.c
	$(OBJCACHE) $(CXX) $(CXXFLAGS) $(CPPFLAGS) $(OPT_FAST) -c -o $@ $<
jtagdpi.o: ../src/lowrisc_dv_dpi_jtagdpi_0.1/jtagdpi.c
	$(OBJCACHE) $(CXX) $(CXXFLAGS) $(CPPFLAGS) $(OPT_FAST) -c -o $@ $<
monitor_spi.o: ../src/lowrisc_dv_dpi_spidpi_0.1/monitor_spi.c
	$(OBJCACHE) $(CXX) $(CXXFLAGS) $(CPPFLAGS) $(OPT_FAST) -c -o $@ $<
spidpi.o: ../src/lowrisc_dv_dpi_spidpi_0.1/spidpi.c
	$(OBJCACHE) $(CXX) $(CXXFLAGS) $(CPPFLAGS) $(OPT_FAST) -c -o $@ $<
tcp_server.o: ../src/lowrisc_dv_dpi_tcp_server_0.1/tcp_server.c
	$(OBJCACHE) $(CXX) $(CXXFLAGS) $(CPPFLAGS) $(OPT_FAST) -c -o $@ $<
uartdpi.o: ../src/lowrisc_dv_dpi_uartdpi_0.1/uartdpi.c
	$(OBJCACHE) $(CXX) $(CXXFLAGS) $(CPPFLAGS) $(OPT_FAST) -c -o $@ $<
monitor_usb.o: ../src/lowrisc_dv_dpi_usbdpi_0.1/monitor_usb.c
	$(OBJCACHE) $(CXX) $(CXXFLAGS) $(CPPFLAGS) $(OPT_FAST) -c -o $@ $<
usb_crc.o: ../src/lowrisc_dv_dpi_usbdpi_0.1/usb_crc.c
	$(OBJCACHE) $(CXX) $(CXXFLAGS) $(CPPFLAGS) $(OPT_FAST) -c -o $@ $<
usbdpi.o: ../src/lowrisc_dv_dpi_usbdpi_0.1/usbdpi.c
	$(OBJCACHE) $(CXX) $(CXXFLAGS) $(CPPFLAGS) $(OPT_FAST) -c -o $@ $<
iss_wrapper.o: ../src/lowrisc_dv_otbn_model_0.1/iss_wrapper.cc
	$(OBJCACHE) $(CXX) $(CXXFLAGS) $(CPPFLAGS) $(OPT_FAST) -c -o $@ $<
otbn_model.o: ../src/lowrisc_dv_otbn_model_0.1/otbn_model.cc
	$(OBJCACHE) $(CXX) $(CXXFLAGS) $(CPPFLAGS) $(OPT_FAST) -c -o $@ $<
otbn_trace_checker.o: ../src/lowrisc_dv_otbn_model_0.1/otbn_trace_checker.cc
	$(OBJCACHE) $(CXX) $(CXXFLAGS) $(CPPFLAGS) $(OPT_FAST) -c -o $@ $<
dpi_memutil.o: ../src/lowrisc_dv_verilator_memutil_dpi_0/cpp/dpi_memutil.cc
	$(OBJCACHE) $(CXX) $(CXXFLAGS) $(CPPFLAGS) $(OPT_FAST) -c -o $@ $<
sv_scoped.o: ../src/lowrisc_dv_verilator_memutil_dpi_0/cpp/sv_scoped.cc
	$(OBJCACHE) $(CXX) $(CXXFLAGS) $(CPPFLAGS) $(OPT_FAST) -c -o $@ $<
verilator_memutil.o: ../src/lowrisc_dv_verilator_memutil_verilator_0/cpp/verilator_memutil.cc
	$(OBJCACHE) $(CXX) $(CXXFLAGS) $(CPPFLAGS) $(OPT_FAST) -c -o $@ $<
verilated_toplevel.o: ../src/lowrisc_dv_verilator_simutil_verilator_0/cpp/verilated_toplevel.cc
	$(OBJCACHE) $(CXX) $(CXXFLAGS) $(CPPFLAGS) $(OPT_FAST) -c -o $@ $<
verilator_sim_ctrl.o: ../src/lowrisc_dv_verilator_simutil_verilator_0/cpp/verilator_sim_ctrl.cc
	$(OBJCACHE) $(CXX) $(CXXFLAGS) $(CPPFLAGS) $(OPT_FAST) -c -o $@ $<
log_trace_listener.o: ../src/lowrisc_ip_otbn_tracer_0/cpp/log_trace_listener.cc
	$(OBJCACHE) $(CXX) $(CXXFLAGS) $(CPPFLAGS) $(OPT_FAST) -c -o $@ $<
otbn_trace_source.o: ../src/lowrisc_ip_otbn_tracer_0/cpp/otbn_trace_source.cc
	$(OBJCACHE) $(CXX) $(CXXFLAGS) $(CPPFLAGS) $(OPT_FAST) -c -o $@ $<
top_earlgrey_verilator.o: ../src/lowrisc_systems_top_earlgrey_verilator_0.1/top_earlgrey_verilator.cc
	$(OBJCACHE) $(CXX) $(CXXFLAGS) $(CPPFLAGS) $(OPT_FAST) -c -o $@ $<

### Link rules... (from --exe)
Vtop_earlgrey_verilator: $(VK_USER_OBJS) $(VK_GLOBAL_OBJS) $(VM_PREFIX)__ALL.a $(VM_HIER_LIBS)
	$(LINK) $(LDFLAGS) $^ $(LOADLIBES) $(LDLIBS) $(LIBS) $(SC_LIBS) -o $@


# Verilated -*- Makefile -*-
