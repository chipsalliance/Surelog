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
		assert (checksum + count + address + (address >> 8) + rectype + reduce(lambda x, y: x+y, data, 0)) & 0xff == 0
		if rectype == 0x00:
			for i in range(len(data)//4):
				waddr = address//4 + i
				print("mem[%4d] = 32'h%08x;" % (waddr, data[4*i] | data[4*i+1] << 8 | data[4*i+2] << 16 | data[4*i+3] << 24))
		elif rectype == 0x01:
			break
		elif rectype == 0x03:
			pass
		else:
			assert 0

