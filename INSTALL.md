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

   * sudo apt-get install build-essential pkg-config tcsh swig uuid-dev libgoogle-perftools-dev python3 python3-dev

   * If you don't intent to change the grammar:
     * sudo apt-get install default-jre
   * If you do intent to change the grammar:
     * sudo apt-get install default-jdk ant

* Surelog Source code
  * git clone https://github.com/alainmarcel/Surelog.git
  * cd Surelog
  * git submodule update --init --recursive

* Build
  * make
  * or see [`src/README`](./src/README.md)
