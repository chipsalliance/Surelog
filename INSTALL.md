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
   * If you don't intent to change the grammar:
     * sudo apt-get install build-essential pkg-config default-jre ant tcsh swig google-perftools python3 python3-dev
   * If you intent to change the grammar:
     * sudo apt-get install build-essential pkg-config default-jdk ant tcsh swig google-perftools python3 python3-dev

* Surelog Source code
  * git clone https://github.com/alainmarcel/Surelog.git

* Build
  * make
  * or see [`SVIncCompil/README`](./SVIncCompil/README.md)
  