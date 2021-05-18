#!/bin/bash
builddir=`dirname "$0"`
GCONV_PATH="${builddir}/iconvdata"

usage () {
  echo "usage: $0 [--tool=strace] PROGRAM [ARGUMENTS...]" 2>&1
  echo "       $0 --tool=valgrind PROGRAM [ARGUMENTS...]" 2>&1
}

toolname=default
while test $# -gt 0 ; do
  case "$1" in
    --tool=*)
      toolname="${1:7}"
      shift
      ;;
    --*)
      usage
      ;;
    *)
      break
      ;;
  esac
done

if test $# -eq 0 ; then
  usage
fi

case "$toolname" in
  default)
    exec   env GCONV_PATH="${builddir}"/iconvdata LOCPATH="${builddir}"/localedata LC_ALL=C  "${builddir}"/elf/ld-linux-riscv64-lp64.so.1 --library-path "${builddir}":"${builddir}"/math:"${builddir}"/elf:"${builddir}"/dlfcn:"${builddir}"/nss:"${builddir}"/nis:"${builddir}"/rt:"${builddir}"/resolv:"${builddir}"/mathvec:"${builddir}"/support:"${builddir}"/crypt:"${builddir}"/nptl ${1+"$@"}
    ;;
  strace)
    exec strace  -EGCONV_PATH=/home/alain/black-parrot/sdk/riscv-gnu-toolchain/build-glibc-linux-rv64imafd-lp64/iconvdata  -ELOCPATH=/home/alain/black-parrot/sdk/riscv-gnu-toolchain/build-glibc-linux-rv64imafd-lp64/localedata  -ELC_ALL=C  /home/alain/black-parrot/sdk/riscv-gnu-toolchain/build-glibc-linux-rv64imafd-lp64/elf/ld-linux-riscv64-lp64.so.1 --library-path /home/alain/black-parrot/sdk/riscv-gnu-toolchain/build-glibc-linux-rv64imafd-lp64:/home/alain/black-parrot/sdk/riscv-gnu-toolchain/build-glibc-linux-rv64imafd-lp64/math:/home/alain/black-parrot/sdk/riscv-gnu-toolchain/build-glibc-linux-rv64imafd-lp64/elf:/home/alain/black-parrot/sdk/riscv-gnu-toolchain/build-glibc-linux-rv64imafd-lp64/dlfcn:/home/alain/black-parrot/sdk/riscv-gnu-toolchain/build-glibc-linux-rv64imafd-lp64/nss:/home/alain/black-parrot/sdk/riscv-gnu-toolchain/build-glibc-linux-rv64imafd-lp64/nis:/home/alain/black-parrot/sdk/riscv-gnu-toolchain/build-glibc-linux-rv64imafd-lp64/rt:/home/alain/black-parrot/sdk/riscv-gnu-toolchain/build-glibc-linux-rv64imafd-lp64/resolv:/home/alain/black-parrot/sdk/riscv-gnu-toolchain/build-glibc-linux-rv64imafd-lp64/mathvec:/home/alain/black-parrot/sdk/riscv-gnu-toolchain/build-glibc-linux-rv64imafd-lp64/support:/home/alain/black-parrot/sdk/riscv-gnu-toolchain/build-glibc-linux-rv64imafd-lp64/crypt:/home/alain/black-parrot/sdk/riscv-gnu-toolchain/build-glibc-linux-rv64imafd-lp64/nptl ${1+"$@"}
    ;;
  valgrind)
    exec env GCONV_PATH=/home/alain/black-parrot/sdk/riscv-gnu-toolchain/build-glibc-linux-rv64imafd-lp64/iconvdata LOCPATH=/home/alain/black-parrot/sdk/riscv-gnu-toolchain/build-glibc-linux-rv64imafd-lp64/localedata LC_ALL=C valgrind  /home/alain/black-parrot/sdk/riscv-gnu-toolchain/build-glibc-linux-rv64imafd-lp64/elf/ld-linux-riscv64-lp64.so.1 --library-path /home/alain/black-parrot/sdk/riscv-gnu-toolchain/build-glibc-linux-rv64imafd-lp64:/home/alain/black-parrot/sdk/riscv-gnu-toolchain/build-glibc-linux-rv64imafd-lp64/math:/home/alain/black-parrot/sdk/riscv-gnu-toolchain/build-glibc-linux-rv64imafd-lp64/elf:/home/alain/black-parrot/sdk/riscv-gnu-toolchain/build-glibc-linux-rv64imafd-lp64/dlfcn:/home/alain/black-parrot/sdk/riscv-gnu-toolchain/build-glibc-linux-rv64imafd-lp64/nss:/home/alain/black-parrot/sdk/riscv-gnu-toolchain/build-glibc-linux-rv64imafd-lp64/nis:/home/alain/black-parrot/sdk/riscv-gnu-toolchain/build-glibc-linux-rv64imafd-lp64/rt:/home/alain/black-parrot/sdk/riscv-gnu-toolchain/build-glibc-linux-rv64imafd-lp64/resolv:/home/alain/black-parrot/sdk/riscv-gnu-toolchain/build-glibc-linux-rv64imafd-lp64/mathvec:/home/alain/black-parrot/sdk/riscv-gnu-toolchain/build-glibc-linux-rv64imafd-lp64/support:/home/alain/black-parrot/sdk/riscv-gnu-toolchain/build-glibc-linux-rv64imafd-lp64/crypt:/home/alain/black-parrot/sdk/riscv-gnu-toolchain/build-glibc-linux-rv64imafd-lp64/nptl ${1+"$@"}
    ;;
  *)
    usage
    ;;
esac
