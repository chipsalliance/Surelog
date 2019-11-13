++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
## SURELOG project
++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
### Executable: surelog
++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++

### Development Environment Required:

* Linux (Ubuntu or Centos)

* Unlimit all limits, in your .cshrc or .bashrc put "ulimit -s"
  that will enable gcc to compile the very large Antlr generated C++ files

* The following tools need to be installed on your machine:
  * Java jdk (For Antlr generation)
  * Compiler: gcc with C11 support
    * gcc > 5.4
  * Python3.6
  * zlib (For Python install)
  * uuid
  * uuid-dev
  * cmake
  * tclsh
  * maven
  * git
  * swig
  * pkg-config
  * Java "ant" build system (For G4 directory)
  * IDE: >= netbeans8.2
  * ddd for core dump debug
  * valgrind --tool=memcheck to check for memory corruptions
  * tcmalloc

* We are suggesting the following package updates:
  * sudo apt-get install build-essentials
  * sudo apt-get install pkg-config
  * sudo apt-get install default-jdk
  * sudo add-apt-repository ppa:jonathonf/gcc-7.2
  * sudo apt-get update
  * sudo apt-get install gcc-7 g++-7	
  * sudo apt-get install ant
  * sudo apt-get install tclsh
  * sudo apt install default-jre
  * sudo apt-get install swig
  * sudo apt-get install google-perftools
  * sudo apt-get install libgoogle-perftools-dev
  * sudo add-apt-repository ppa:jonathonf/python-3.6 -y
  * sudo apt-get update -q
  * sudo apt-get install python3.6
  * sudo apt-get install python3.6-dev

* Surelog Source code
  * git clone https://github.com/alainmarcel/Surelog.git

* Build
  * make
  * or see [`SVIncCompil/README`](./SVIncCompil/README.md)
  