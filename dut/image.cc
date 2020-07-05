#include "Vimage.h"
#include "verilated.h"
#include "verilated_vcd_c.h"

typedef Vimage TB;
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
  } else if ("str_img_bus" == port) {
    dut->str_img_bus = static_cast<const uint64_t>(value[0]);
  } else if ("str_img_val" == port) {
    dut->str_img_val = static_cast<const uint8_t>(value[0]);
  } else if ("image_rdy" == port) {
    dut->image_rdy = static_cast<const uint8_t>(value[0]);
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
    "str_img_bus"_a = dut->str_img_bus,
    "str_img_val"_a = dut->str_img_val,
    "str_img_rdy"_a = dut->str_img_rdy,
    "image_bus"_a = dut->image_bus,
    "image_last"_a = dut->image_last,
    "image_val"_a = dut->image_val,
    "image_rdy"_a = dut->image_rdy
  );
}
