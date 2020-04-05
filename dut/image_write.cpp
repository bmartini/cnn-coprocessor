#include "Vimage_write.h"
#include "verilated.h"
#include "verilated_vcd_c.h"

#include <stdio.h>
#include <stdlib.h>

void tick(Vimage_write *dut, VerilatedVcdC *wave, vluint64_t timestamp) {
  printf("%lu\n", (timestamp * 10 - 2));

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

  dut->cfg_addr = 9; // CFG_IW_IMG_W
  dut->cfg_data = 0x00000009;
  dut->cfg_valid = 1;
  tick(dut, wave, ++timestamp);

  dut->cfg_addr = 10; // CFG_IW_START
  dut->cfg_data = 0x00000004;
  dut->cfg_valid = 1;
  tick(dut, wave, ++timestamp);

  dut->cfg_addr = 11; // CFG_IW_STEP
  dut->cfg_data = 0x00030009;
  dut->cfg_valid = 1;
  tick(dut, wave, ++timestamp);

  dut->cfg_addr = 0;
  dut->cfg_data = 0;
  dut->cfg_valid = 0;
  tick(dut, wave, ++timestamp);

  dut->next = 1;
  tick(dut, wave, ++timestamp);

  dut->next = 0;
  tick(dut, wave, ++timestamp);

  for (int x = 0; x < 5; x++) {
    tick(dut, wave, ++timestamp);
  }

  for (int x = 0; x < 5; x++) {
    cnt[0]++;
    // dut->str_img_bus = cnt;
    dut->str_img_val = 1;
    tick(dut, wave, ++timestamp);
  }

  printf("size: %lu\n", sizeof(dut->str_img_bus));

  memset(dut->str_img_bus, 0, sizeof(dut->str_img_bus));
  dut->str_img_val = 0;
  tick(dut, wave, ++timestamp);

  wave->close();

  delete dut;
}
