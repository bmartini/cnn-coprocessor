#include <pybind11/pybind11.h>
#include <pybind11/stl.h>

#include <vector>

using namespace pybind11::literals;
namespace py = pybind11;

TB *dut;
VerilatedVcdC *wave;
vluint64_t timestamp;

void prep(const std::string, const std::vector<uint32_t> &);

py::dict update();

void init() {
  printf("Initialize DUT simulation\n");
  timestamp = 0;

  // Instantiate design
  dut = new TB;

  // Generate a trace
  Verilated::traceEverOn(true);
  wave = new VerilatedVcdC;
  dut->trace(wave, 99);
  wave->open("image_write.vcd");
}

void finish() {
  wave->close();

  delete dut;
  printf("Finish DUT simulation\n");
}

py::dict tick() {
  timestamp++;

  dut->eval();
  wave->dump(timestamp * 10 - 2);

  py::dict IO = update();

  dut->clk = 1;
  dut->eval();
  wave->dump(timestamp * 10);

  dut->clk = 0;
  dut->eval();
  wave->dump(timestamp * 10 + 5);
  wave->flush();

  return IO;
}

PYBIND11_MODULE(testbench, m) {
  m.doc() = "Python interface for a Verilator Design Under Test (dut)";

  m.def("init", &init, "Initialize DUT simulation");
  m.def("finish", &finish, "Finish DUT simulation");
  m.def("prep", &prep, "Prepare input values to be sampled on next posedge");
  m.def("tick", &tick,
        "Advances the clock one cycle and returns the port list state as it "
        "was on the posedge");
}
