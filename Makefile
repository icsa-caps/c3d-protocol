CXX = g++
MURPHIPATH = $(HOME)/local/murphi/cmurphi
MU = $(MURPHIPATH)/src/mu
INCLUDEPATH = $(MURPHIPATH)/include
CXXFLAGS = -std=c++11
OPTFLAGS = -O2

MODEL = C3D
MEM = 1024
RUN_FLAGS = -tv -m $(MEM)

.PHONY: all
all: $(MODEL)

$(MODEL): $(MODEL).cpp
	$(CXX) $(OPTFLAGS) $(CXXFLAGS) -I$(INCLUDEPATH) -o $@ $<

%.cpp: %.m
	$(MU) $<

.PHONY: check
check: $(MODEL)
	./$(MODEL) $(RUN_FLAGS)

.PHONY: clean
clean:
	$(RM) *.cpp
	$(RM) $(MODEL)
