DTC=/usr/bin/dtc
OUT=p9-simics.dtb

all: $(OUT)

%.dtb: %.dts
	$(DTC) -I dts -O dtb $< -o $@

clean:
	$(RM) $(OUT)
