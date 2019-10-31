# Complete Surelog build script

echo "Generating Antlr parser"
cd ../G4
ant compile_cpp
ant copy_cpp
cd ../SVIncCompil

echo "Removing previous build"
rm -rf build;
chmod 777 -R dist; rm -rf dist;

echo "Generating caching scheme"
cd Cache; ./build_fbs.sh;
cd ..;

echo "Generating code"
SourceCompile/generate_parser_listener.tcl
API/generate_python_listener_api.tcl 
API/embed_python_api.tcl

echo "Make"
make -j  all;

echo "Run Tests"
./release.tcl ;
cd Testcases/ ;
./regression.tcl

echo "End build"
