#include <pybind11/pybind11.h>
#include <pybind11/stl.h>

#include <vector>

using namespace pybind11::literals;
namespace py = pybind11;

TB *dut;
VerilatedVcdC *wave;
vluint64_t timestamp;
bool trace_on;

void prep(const std::string, const std::vector<uint32_t> &);

py::dict update();

void init(const bool trace = true) {
  printf("Initialize DUT simulation\n");
  timestamp = 0;
  trace_on = trace;

  // Instantiate design
  dut = new TB;

  if (trace_on) {
    // Generate a trace
    Verilated::traceEverOn(true);
    wave = new VerilatedVcdC;
    dut->trace(wave, 99);
    wave->open("image_write.vcd");
  }
}

void finish() {
  if (trace_on) {
    wave->close();
  }

  delete dut;
  printf("Finish DUT simulation\n");
}

py::dict tick() {
  timestamp++;

  dut->eval();
  if (trace_on) {
    wave->dump(timestamp * 10 - 2);
  }

  py::dict IO = update();

  dut->clk = 1;
  dut->eval();
  if (trace_on) {
    wave->dump(timestamp * 10);
  }

  dut->clk = 0;
  dut->eval();
  if (trace_on) {
    wave->dump(timestamp * 10 + 5);
    wave->flush();
  }

  return IO;
}

PYBIND11_MODULE(testbench, m) {
  m.doc() = "Python interface for a Verilator Design Under Test (dut)";

  m.def("init", &init, "Initialize DUT simulation", py::arg("trace") = true);
  m.def("finish", &finish, "Finish DUT simulation");
  m.def("prep", &prep, "Prepare input values to be sampled on next posedge");
  m.def("tick", &tick,
        "Advances the clock one cycle and returns the port list state as it "
        "was on the posedge");
}
