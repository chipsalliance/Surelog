#-*-Makefile-*-

TSS_DIR = libstb/tss

SUBDIRS += $(TSS_DIR)

TSS_SRCS = trustedbootCmds.C trustedTypes.C trustedbootUtils.C \
	   tpmLogMgr.C
TSS_OBJS = $(TSS_SRCS:%.C=%.o)
TSS = $(TSS_DIR)/built-in.a

$(TSS): $(TSS_OBJS:%=$(TSS_DIR)/%)

