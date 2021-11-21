#! /bin/bash -f
submodules=(
  rtl/bcm
  env/tue
  env/vip_common
  env/axi_vip
)

for submodule in ${submodules[@]} ; do
  git submodule update --init ${submodule}
done
