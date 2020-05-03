#include "Vimage_write.h"
#include "verilated.h"
#include "verilated_vcd_c.h"

#include <stdio.h>
#include <stdlib.h>

typedef Vimage_write TB;

uint32_t cfg_data = 0;
uint8_t cfg_addr = 0;
uint8_t cfg_valid = 0;

uint8_t next = 0;
uint8_t next_rdy = 0;

uint8_t str_img_val = 0;
uint8_t str_img_rdy = 0;
uint32_t str_img_bus[8] = {0};

uint8_t wr_val = 0;
uint16_t wr_addr = 0;
uint32_t wr_data[8] = {0};

TB *dut;
VerilatedVcdC *wave;
vluint64_t timestamp;

void prep(const std::string port, const void *value) {

  if ("rst" == port) {
    dut->rst = *(static_cast<const uint8_t *>(value));
  } else if ("cfg_data" == port) {
    dut->cfg_data = *(static_cast<const uint32_t *>(value));
  } else if ("cfg_addr" == port) {
    dut->cfg_addr = *(static_cast<const uint8_t *>(value));
  } else if ("cfg_valid" == port) {
    dut->cfg_valid = *(static_cast<const uint8_t *>(value));
  } else if ("next" == port) {
    dut->next = *(static_cast<const uint8_t *>(value));
  } else if ("str_img_val" == port) {
    dut->str_img_val = *(static_cast<const uint8_t *>(value));
  } else if ("str_img_bus" == port) {
    memcpy(dut->str_img_bus, value, sizeof(dut->str_img_bus));
  }
}

void update() {
  cfg_data = dut->cfg_data;
  cfg_addr = dut->cfg_addr;
  cfg_valid = dut->cfg_valid;

  next = dut->next;
  next_rdy = dut->next_rdy;

  str_img_val = dut->str_img_val;
  str_img_rdy = dut->str_img_rdy;
  memcpy(&str_img_bus[0], dut->str_img_bus, sizeof(str_img_bus));

  wr_val = dut->wr_val;
  wr_addr = dut->wr_addr;
  memcpy(&wr_data[0], dut->wr_data, sizeof(wr_data));
}

void tick() {
  timestamp++;

  dut->eval();
  wave->dump(timestamp * 10 - 2);

  update();

  dut->clk = 1;
  dut->eval();
  wave->dump(timestamp * 10);

  dut->clk = 0;
  dut->eval();
  wave->dump(timestamp * 10 + 5);
  wave->flush();
}

void set_rst(uint8_t rst) { prep("rst", &rst); }

void set_cfg(uint8_t valid, uint16_t addr, uint32_t data) {
  prep("cfg_addr", &addr);
  prep("cfg_data", &data);
  prep("cfg_valid", &valid);
}

void set_next(uint8_t next) { prep("next", &next); }

void set_str_img(uint8_t valid, uint32_t *data) {
  prep("str_img_bus", &data);
  prep("str_img_val", &valid);
}

int main(int argc, char **argv) {
  uint32_t cnt[8] = {0};
  timestamp = 0;

  // Initialize Verilators variables
  Verilated::commandArgs(argc, argv);

  // Instantiate design
  dut = new TB;

  // Generate a trace
  Verilated::traceEverOn(true);
  wave = new VerilatedVcdC;
  dut->trace(wave, 99);
  wave->open("image_write.vcd");

  set_rst(1);
  tick();
  set_rst(0);
  tick();
  tick();

  // CFG_IW_IMG_W
  set_cfg(1, 9, 0x00000009);
  tick();

  // CFG_IW_START
  set_cfg(1, 10, 0x00000004);
  tick();

  // CFG_IW_STEP
  set_cfg(1, 11, 0x00030009);
  tick();

  // release config bus
  set_cfg(0, 0, 0);
  tick();
  tick();
  tick();

  // register next configuration
  set_next(1);
  tick();

  while (!next_rdy) {
    // wait on next handshake if next_rdy is not high
    tick();
  }

  set_next(0);
  tick();

  for (int x = 0; x < 5; x++) {
    tick();
  }

  for (int x = 0; x < 8; x++) {
    cnt[x] += (x + 1);
  }

  for (int x = 0; x < 350; x++) {
    set_str_img(1, cnt);
    tick();

    if (str_img_rdy) {
      // sample the rdy to see if the data has been moved into the pipeline, if
      // both rdy & val are high we increment to the 'next' data

      for (int x = 0; x < 8; x++) {
        cnt[x]++;
      }
    }
  }

  wave->close();

  delete dut;
}
