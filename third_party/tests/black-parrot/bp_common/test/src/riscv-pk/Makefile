TOP ?= $(shell git rev-parse --show-toplevel)

LINUX_DIR := $(TOP)/linux

.PHONY: all dtb initramfs clean

all: dtb initramfs

dtb:
	dtc blackparrot.dts -O dtb > machine/blackparrot.dtb

initramfs:
	mkdir -p root && cd root &&\
	mkdir -p bin etc dev lib mnt proc sbin sys tmp usr usr/bin usr/lib usr/sbin &&\
	cp $(EXTERNAL_DIR)/bin/busybox bin/. && \
	ln -sf bin/busybox init && \
	cp $(TOP)/inittab etc/. && \
	echo "\
		mknod dev/null c 1 3 && \
		mknod dev/tty c 5 0 && \
		mknod dev/zero c 1 5 && \
		mknod dev/console c 5 1 && \
		find . | cpio -H newc -o > $(LINUX_DIR)/initramfs.cpio" | fakeroot

clean:
	rm -rf root
	rm -rf build
	rm -rf machine/blackparrot.dtb
	$(MAKE) -C linux/ clean
