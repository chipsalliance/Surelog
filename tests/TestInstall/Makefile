# Simple example how to utilize pkg-config to find the cflags and libraries
CXXFLAGS+=`pkg-config --cflags Surelog`
LDFLAGS+=`pkg-config --libs Surelog`

# Let's build these out-of-tree
IN_DIR=src
OUT_DIR=build

$(OUT_DIR)/%.o : $(IN_DIR)/%.cpp
	$(CXX) $(CXXFLAGS) -c $^ -o $@

% : %.o
	$(CXX) $^ -o $@  $(LDFLAGS)
