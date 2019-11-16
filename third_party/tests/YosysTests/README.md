

Running this tests with C++ coverage analysis
---------------------------------------------

```
git clone git@github.com:YosysHQ/yosys.git yosys-cover
cd yosys-cover

# Building Yosys
make config-gcov
make -j$(nproc)

# Running built-in tests
make -j$(nproc) test

# Running yosys-tests
make -j$(nproc) ystests

# Generate coverage report
make coverage

# Display coverage data
xdg-open coverage_html/index.html
```
