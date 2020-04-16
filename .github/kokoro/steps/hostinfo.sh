#!/bin/bash

set -e

echo
echo "========================================"
echo "Host Environment"
echo "----------------------------------------"
export
echo "----------------------------------------"

echo
echo "========================================"
echo "Host CPU"
echo "----------------------------------------"
export CORES=$(nproc --all)
echo "Cores: $CORES"
echo
echo "Memory"
echo "----------------------------------------"
cat /proc/meminfo
echo "----------------------------------------"
export MEM_GB=$(($(awk '/MemTotal/ {print $2}' /proc/meminfo)/(1024*1024)))
echo "Total Memory (GB): $MEM_GB"
export MEM_PER_RUN=16
export MEM_CORES=$(($MEM_GB/$MEM_PER_RUN))
echo "Simultaneous runs ($MEM_PER_RUN GB each): $MEM_CORES"
export MAX_CORES_NO_MIN=$(($MEM_CORES>$CORES?$CORES:$MEM_CORES))
export MAX_CORES=$(($MAX_CORES_NO_MIN<1?1:$MAX_CORES_NO_MIN))
echo "Max cores: $MAX_CORES"
