.DEFAULT_GOAL := all
BUILD_DIR=build
BINARY_NAME=multicycle 
BSC_FLAGS=--aggressive-conditions --show-schedule -vdir $(BUILD_DIR) -bdir $(BUILD_DIR) -simdir $(BUILD_DIR) -o 

.PHONY: clean all $(BINARY_NAME)

$(BINARY_NAME):
	mkdir -p $(BUILD_DIR)
	#bsc $(BSC_FLAGS) $@ -verilog --ddumpLean -g mk$@ -u $@.bsv
	bsc $(BSC_FLAGS) $@ -verilog --ddumpLambdaCalculus -g mk$@ -u $@.bsv
	bsc $(BSC_FLAGS) $@ -sim -g mk$@ -u $@.bsv
	bsc $(BSC_FLAGS) $@ -sim -e mk$@

clean:
	rm -rf $(BUILD_DIR)
	rm -f $(BINARY_NAME)
	rm -f *.so
	rm -f *.sched

all: clean $(BINARY_NAME)

