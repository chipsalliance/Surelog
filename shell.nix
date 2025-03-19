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
      time

      # If Python API is built.
      swig

      # Libraries for USE_HOST_* use
      antlr4
      antlr4.runtime.cpp
      capnproto
      gtest
      nlohmann_json

      # Ease development
      ccache
      clang-tools_19 # for clang-tidy
      git cacert
      lcov          # generate coverage
      ninja
      pkg-config    # Testing install
    ];
  shellHook = ''
    export CMAKE_CXX_COMPILER_LAUNCHER=ccache
    export ADDITIONAL_CMAKE_OPTIONS="-DSURELOG_USE_HOST_GTEST=On -DSURELOG_USE_HOST_CAPNP=On -DSURELOG_USE_HOST_JSON=On -DSURELOG_USE_HOST_ANTLR=On -DANTLR_JAR_LOCATION=${pkgs.antlr4.jarLocation}"

    # Use latest clang-tidy
    export CLANG_TIDY=${pkgs.clang-tools_19}/bin/clang-tidy

    # There is too much volatility between even micro-versions of
    # clang-format 18. Let's use 17 for now.
    export CLANG_FORMAT=${pkgs.clang-tools_17}/bin/clang-format
  '';
}
