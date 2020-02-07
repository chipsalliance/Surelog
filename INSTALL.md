++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
## SURELOG project
++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
### Executable: surelog
++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++

### Development Environment Required:

* Linux (Ubuntu or Centos)

* Unlimit all limits, in your .cshrc or .bashrc put "ulimit -s"
  that will enable gcc to compile the very large Antlr generated C++ files

* Please install the following package updates:

   * sudo apt-get install build-essential cmake git pkg-config tclsh swig uuid-dev libgoogle-perftools-dev python3 python3-dev

   * If you don't intent to change the grammar:
     * sudo apt-get install default-jre
   * If you do intent to change the grammar:
     * sudo apt-get install default-jdk ant

* Surelog Source code
  * git clone https://github.com/alainmarcel/Surelog.git
  * cd Surelog
  * git submodule update --init --recursive
  * Remove capnproto limits:
  * sed -i 's/nestingLimit = 64/nestingLimit = 1024/g' third_party/UHDM/third_party/capnproto/c++/src/capnp/message.h
  * sed -i 's/8 \* 1024 \* 1024/64 \* 1024 \* 1024 \* 1024/g' third_party/UHDM/third_party/capnproto/c++/src/capnp/message.h 
* Build
  * make
  * or see [`src/README`](./src/README.md)
