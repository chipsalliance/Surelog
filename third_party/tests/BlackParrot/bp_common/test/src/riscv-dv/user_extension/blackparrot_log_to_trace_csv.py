
import argparse
import re
import sys

sys.path.insert(0, "./scripts")

from riscv_trace_csv import *
from lib import *

def process_blackparrot_sim_log(blackparrot_log, csv):
  with open(blackparrot_log, "r") as f, open(csv, "w") as csv_fd:
    trace_csv = RiscvInstructiontTraceCsv(csv_fd)
    trace_csv.start_new_trace()
    for line in f:
      fields = line.split()

      if len(fields) == 6:
        rv_instr_trace = RiscvInstructiontTraceEntry()
        rv_instr_trace.rd = gpr_to_abi("x%0s" % int(fields[4], 16))
        rv_instr_trace.rd_val = fields[5]
        rv_instr_trace.addr = fields[1]
        rv_instr_trace.binary = fields[2]

        trace_csv.write_trace_entry(rv_instr_trace)


def main():
  parser = argparse.ArgumentParser()
  parser.add_argument("--log", type=str, help="Input spike simulation log")
  parser.add_argument("--csv", type=str, help="Output trace csv_buf file")
  args = parser.parse_args()
  # Process spike log
  process_blackparrot_sim_log(args.log, args.csv)


if __name__ == "__main__":
  main()

