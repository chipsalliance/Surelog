# Complete Surelog build script

echo "Generating Antlr parser"
cd ../G4
ant compile_cpp
ant copy_pp_cpp
cd ../SVIncCompil

#echo "Removing previous build"
#rm -rf build/Release;
#chmod 777 -Rf dist/Release; rm -rf dist/Release;

echo "Generating caching scheme"
cd Cache; ./build_fbs.sh;
cd ..;

echo "Generating code"
SourceCompile/generate_parser_listener.tcl
API/generate_python_listener_api.tcl 
API/embed_python_api.tcl

echo "Make"
make CONF=Release -j 4;

echo "Run Tests"
./release.tcl  "release tcmalloc" ;
cd Testcases/ ;
./regression.tcl

echo "End build"
