# This is a nix-shell for use with the nix package manager.
# If you have nix installed, you may simply run `nix-shell`
# in this repo, and have all dependencies ready in the new shell.

{ pkgs ? import <nixpkgs> {} }:
pkgs.mkShell {
  buildInputs = with pkgs;
    [
      stdenv

      antlr4
      cacert
      cmake
      diffutils
      git
      gperftools
      jdk11
      lcov
      #libunwind
      libuuid
      pkg-config
      python310
      python310Packages.orderedmultidict
      python310Packages.psutil
      swig
      tcl
      time
      zlib

      # Libraries for USE_HOST_* use
      flatbuffers
      capnproto

      # Ease development
      ccache
      ninja
      clang-tools
    ];
  shellHook =
  ''
    export CMAKE_CXX_COMPILER_LAUNCHER=ccache
  '';
}
