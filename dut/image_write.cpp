#include "Vimage_write.h"
#include "verilated.h"
#include "verilated_vcd_c.h"

#include <stdio.h>
#include <stdlib.h>

void tick(Vimage_write *dut, VerilatedVcdC* wave, vluint64_t timestamp) {
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

int main(int argc, char **argv) {
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

  for (int x = 0; x < 10; x++) {
    tick(dut, wave, ++timestamp);
  }


  wave->close();

  delete dut;
}
