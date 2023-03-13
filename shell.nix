# This is a nix-shell for use with the nix package manager.
# If you have nix installed, you may simply run `nix-shell`
# in this repo, and have all dependencies ready in the new shell.

{ pkgs ? import <nixpkgs> {} }:
pkgs.mkShell {
  buildInputs = with pkgs;
    [
      cmake
      diffutils   # Used in regression tests.
      gperftools  # tcmalloc
      jdk11       # to run antlr jar

      # For generating code and make test/regression
      python310
      python310Packages.orderedmultidict
      python310Packages.psutil

      # Run regression scripts.
      tcl

      # If Python API is built.
      swig

      # Libraries for USE_HOST_* use
      flatbuffers
      capnproto
      gtest
      antlr4.runtime.cpp

      # Ease development
      ccache
      ninja
      clang-tools   # clang-format, clang-tidy
      lcov          # generate coverage
      git cacert
    ];
  shellHook = ''
    export CMAKE_CXX_COMPILER_LAUNCHER=ccache
    export ADDITIONAL_CMAKE_OPTIONS="-DSURELOG_USE_HOST_GTEST=On"
    export ADDITIONAL_CMAKE_OPTIONS="$ADDITIONAL_CMAKE_OPTIONS -DSURELOG_USE_HOST_FLATBUFFERS=On"

    # The following does not work yet: can't find ANTLR_JAR_LOCATION
    #export ADDITIONAL_CMAKE_OPTIONS="$ADDITIONAL_CMAKE_OPTIONS -DSURELOG_USE_HOST_ANTLR=On"
  '';
}
