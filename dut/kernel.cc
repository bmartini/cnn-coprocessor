#include "Vkernel.h"
#include "verilated.h"
#include "verilated_vcd_c.h"

typedef Vkernel TB;
#include "testbench.hh"

void prep(const std::string port, const std::vector<uint64_t> &value) {

  if ("rst" == port) {
    dut->rst = static_cast<uint8_t>(value[0]);
  } else if ("cfg_data" == port) {
    dut->cfg_data = static_cast<const uint32_t>(value[0]);
  } else if ("cfg_addr" == port) {
    dut->cfg_addr = static_cast<const uint8_t>(value[0]);
  } else if ("cfg_valid" == port) {
    dut->cfg_valid = static_cast<const uint8_t>(value[0]);
  } else if ("str_ker_bus" == port) {
    dut->str_ker_bus = static_cast<const uint64_t>(value[0]);
  } else if ("str_ker_val" == port) {
    dut->str_ker_val = static_cast<const uint8_t>(value[0]);
  } else if ("kernel_rdy" == port) {
    dut->kernel_rdy = static_cast<const uint8_t>(value[0]);
  } else {
    printf("WARNING: requested port \'%s\' not found.\n", port.c_str());
  }
}

py::dict update() {

  py::list bias_bus;
  for (auto &item : dut->bias_bus) {
    bias_bus.append(item);
  }

  py::list kernel_bus;
  for (auto &item : dut->kernel_bus) {
    kernel_bus.append(item);
  }

  return py::dict (
    "rst"_a = dut->rst,
    "cfg_data"_a = dut->cfg_data,
    "cfg_addr"_a = dut->cfg_addr,
    "cfg_valid"_a = dut->cfg_valid,
    "str_ker_bus"_a = dut->str_ker_bus,
    "str_ker_val"_a = dut->str_ker_val,
    "str_ker_rdy"_a = dut->str_ker_rdy,
    "bias_bus"_a = bias_bus,
    "kernel_bus"_a = kernel_bus,
    "kernel_rdy"_a = dut->kernel_rdy
  );
}
