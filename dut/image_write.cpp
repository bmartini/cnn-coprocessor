#include "Vimage_write.h"
#include "verilated.h"
#include "verilated_vcd_c.h"

#include <stdio.h>
#include <stdlib.h>

void tick(Vimage_write *dut, VerilatedVcdC *wave, vluint64_t timestamp) {
  dut->eval();
  wave->dump(timestamp * 10 - 2);

  dut->clk = 1;
  dut->eval();
  wave->dump(timestamp * 10);

  dut->clk = 0;
  dut->eval();
  wave->dump(timestamp * 10 + 5);
  wave->flush();
}

void reset(Vimage_write *dut, VerilatedVcdC *wave, vluint64_t timestamp) {
  dut->rst = 1;

  tick(dut, wave, timestamp);

  dut->rst = 0;
}

void set_cfg(Vimage_write *dut, uint8_t valid, uint16_t addr, uint32_t data) {
  dut->cfg_addr = addr;
  dut->cfg_data = data;
  dut->cfg_valid = valid;
}

void set_str_img(Vimage_write *dut, uint8_t valid, WData *data) {
  dut->str_img_bus[0] = data[0];
  dut->str_img_bus[1] = data[1];
  dut->str_img_bus[2] = data[2];
  dut->str_img_bus[3] = data[3];
  dut->str_img_bus[4] = data[4];
  dut->str_img_bus[5] = data[5];
  dut->str_img_bus[6] = data[6];
  dut->str_img_bus[7] = data[7];
  dut->str_img_val = valid;
}

int main(int argc, char **argv) {
  WData cnt[8] = {0};
  vluint64_t timestamp = 0;

  // Initialize Verilators variables
  Verilated::commandArgs(argc, argv);

  // Instantiate design
  Vimage_write *dut = new Vimage_write;

  // Generate a trace
  Verilated::traceEverOn(true);
  VerilatedVcdC *wave = new VerilatedVcdC;
  dut->trace(wave, 99);
  wave->open("image_write.vcd");

  reset(dut, wave, ++timestamp);

  tick(dut, wave, ++timestamp);

  // CFG_IW_IMG_W
  set_cfg(dut, 1, 9, 0x00000009);
  tick(dut, wave, ++timestamp);

  // CFG_IW_START
  set_cfg(dut, 1, 10, 0x00000004);
  tick(dut, wave, ++timestamp);

  // CFG_IW_STEP
  set_cfg(dut, 1, 11, 0x00030009);
  tick(dut, wave, ++timestamp);

  // release config bus
  set_cfg(dut, 0, 0, 0);
  tick(dut, wave, ++timestamp);
  tick(dut, wave, ++timestamp);
  tick(dut, wave, ++timestamp);

  // wait on next
  dut->next = 1;
  while (dut->next_rdy == 0) {
    // wait until next_rdy is high
    tick(dut, wave, ++timestamp);
  }
  tick(dut, wave, ++timestamp);

  dut->next = 0;
  tick(dut, wave, ++timestamp);

  for (int x = 0; x < 5; x++) {
    tick(dut, wave, ++timestamp);
  }

  for (int x = 0; x < 8; x++) {
    cnt[x] += (x + 1);
  }
  for (int x = 0; x < 350; x++) {
    set_str_img(dut, 1, cnt);

    if (dut->str_img_rdy) {
      // sample the rdy to see if the data will be moved into the pipeline, if
      // both rdy & val are high we increment to the 'next' data

      for (int x = 0; x < 8; x++) {
        cnt[x]++;
      }
    }

    tick(dut, wave, ++timestamp);
  }

  // memset(dut->str_img_bus, 0, sizeof(dut->str_img_bus));
  // dut->str_img_val = 0;
  // tick(dut, wave, ++timestamp);

  wave->close();

  delete dut;
}
