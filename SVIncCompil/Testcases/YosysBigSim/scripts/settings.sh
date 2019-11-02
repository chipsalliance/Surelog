
if [ $# -ne 1 -o ! -d "$1" ]; then
	echo "Usage: $0 <design>" >&2
	exit 1
fi

set -ex
design=${1%/}

YOSYS_COARSE=false
YOSYS_GLOBRST=false
YOSYS_SPLITNETS=false
TOP="" # must be set in settings.sh
RTL="" # must be set in settings.sh
SIM="" # must be set in settings.sh
source $design/sim/settings.sh

rtl_files=""
for src in $RTL; do
	rtl_files="$rtl_files $design/rtl/$src"
done

sim_files=""
for src in $SIM; do
	sim_files="$sim_files $design/sim/$src"
done

