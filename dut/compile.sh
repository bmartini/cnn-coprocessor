#!/usr/bin/env bash

#g++ -O3 -Wall -shared -std=c++11 -fPIC `python3 -m pybind11 --includes` -I. example.cpp -o example`python3-config --extension-suffix`

VERILATOR_ROOT=$(verilator -V | grep VERILATOR_ROOT | head -1 | sed -e "s/^.*=\s*//")
VINC="${VERILATOR_ROOT}/include"

verilator -CFLAGS "-fPIC -std=c++17" -I../hdl --trace -cc ../hdl/image_write.v

make -C obj_dir -f Vimage_write.mk

g++ -O3 -Wall -shared -std=c++17 -fPIC `python3 -m pybind11 --includes` -I. \
	-I${VINC} -Iobj_dir ${VINC}/verilated.cpp ${VINC}/verilated_vcd_c.cpp image_write.cc \
	obj_dir/Vimage_write__ALL.a -o testbench`python3-config --extension-suffix`
