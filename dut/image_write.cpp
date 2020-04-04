#include "Vimage_write.h"
#include "verilated.h"
#include "verilated_vcd_c.h"

#include <stdio.h>
#include <stdlib.h>

void tick(Vimage_write *dut) {
  dut->eval();
  dut->clk = 1;
  dut->eval();
  dut->clk = 0;
  dut->eval();
}

int main(int argc, char **argv) {

  // Initialize Verilators variables
  Verilated::commandArgs(argc, argv);

  // Instantiate design
  Vimage_write *dut = new Vimage_write;

  for (int x = 0; x < 10; x++) {
    tick(dut);
  }

  delete dut;
}
