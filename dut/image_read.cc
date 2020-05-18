#include "Vimage_read.h"
#include "verilated.h"
#include "verilated_vcd_c.h"

typedef Vimage_read TB;
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
  } else if ("next" == port) {
    dut->next = static_cast<const uint8_t>(value[0]);
  } else if ("rd_data" == port) {
    dut->rd_data = static_cast<const uint64_t>(value[0]);
  } else if ("image_rdy" == port) {
    dut->image_val = static_cast<const uint8_t>(value[0]);
  } else {
    printf("WARNING: requested port \'%s\' not found.\n", port.c_str());
  }
}

py::dict update() {

  return py::dict (
    "rst"_a = dut->rst,
    "cfg_data"_a = dut->cfg_data,
    "cfg_addr"_a = dut->cfg_addr,
    "cfg_valid"_a = dut->cfg_valid,
    "next"_a = dut->next,
    "next_rdy"_a = dut->next_rdy,
    "rd_val"_a = dut->rd_val,
    "rd_addr"_a = dut->rd_addr,
    "rd_data"_a = dut->rd_data,
    "image_bus"_a = dut->image_bus,
    "image_last"_a = dut->image_last,
    "image_val"_a = dut->image_val,
    "image_rdy"_a = dut->image_rdy
  );
}
