#!/usr/bin/python

from __future__ import division
from __future__ import print_function
import re

ihex_pattern = re.compile(':([0-9a-fA-F]{2})([0-9a-fA-F]{4})([0-9a-fA-F]{2})([0-9a-fA-F]*)([0-9a-fA-F]{2})')

while True:
	m = ihex_pattern.match(raw_input())
	if m:
		count = int(m.group(1), 16)
		address = int(m.group(2), 16)
		rectype = int(m.group(3), 16)
		data = [ int(m.group(4)[2*i:2*i+2], 16) for i in range(len(m.group(4))//2) ]
		checksum = int(m.group(5), 16)
		assert (checksum + count + address + address >> 8 + rectype + reduce(lambda x, y: x+y, data, 0)) & 0xff == 0
		if rectype == 0x00:
			for i in range(len(data)//2):
				waddr = address//2 + i + 0x400 - 0x8000;
				print("pmem[%4d] = 16'h%04x;" % (waddr, data[2*i] | data[2*i+1] << 8))
		elif rectype == 0x01:
			break
		elif rectype == 0x03:
			pass
		else:
			assert 0

