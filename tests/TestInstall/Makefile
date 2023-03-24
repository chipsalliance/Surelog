# Simple example how to utilize pkg-config to find the cflags and libraries
CXXFLAGS=--std=c++17
CXXFLAGS+=`pkg-config --cflags Surelog`
LDFLAGS+=`pkg-config --libs Surelog`

# TODO(hzeller): should the supporting libs be mentioned in the pkg-config ?
LDFLAGS+=-lpthread

# Let's build these out-of-tree
IN_DIR=src
OUT_DIR=tests/TestInstall/build

$(OUT_DIR)/%.o : $(IN_DIR)/%.cpp $(OUT_DIR)
	$(CXX) $(CXXFLAGS) -c $< -o $@

% : %.o
	$(CXX) $^ -o $@  $(LDFLAGS)

$(OUT_DIR):
	mkdir -p $(OUT_DIR)
