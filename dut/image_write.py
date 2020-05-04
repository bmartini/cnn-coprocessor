#!/usr/bin/env python3
"""
Testbench for the image_write module.
"""

import testbench as dut


dut.init()

dut.prep("cfg_data", [0])
dut.prep("cfg_addr", [0])
dut.prep("cfg_valid", [0])
dut.prep("next", [0])
dut.prep("str_img_val", [0])
dut.prep("str_img_bus", [0, 0, 0, 0, 0, 0, 0, 0])

# reset module
dut.prep("rst", [1])
IO = dut.tick()

dut.prep("rst", [0])
for _ in range(2):
    IO = dut.tick()


# CFG_IW_IMG_W
dut.prep("cfg_data", [0x00000009])
dut.prep("cfg_addr", [9])
dut.prep("cfg_valid", [1])
IO = dut.tick()

# CFG_IW_START
dut.prep("cfg_data", [0x00000004])
dut.prep("cfg_addr", [10])
dut.prep("cfg_valid", [1])
IO = dut.tick()

# CFG_IW_STEP
dut.prep("cfg_data", [0x00030009])
dut.prep("cfg_addr", [11])
dut.prep("cfg_valid", [1])
IO = dut.tick()

dut.prep("cfg_data", [0])
dut.prep("cfg_addr", [0])
dut.prep("cfg_valid", [0])
for _ in range(3):
    IO = dut.tick()

# register next configuration
dut.prep("next", [1])
IO = dut.tick()

while not IO["next_rdy"]:
    # wait on next handshake if next_rdy is not high
    IO = dut.tick()

dut.prep("next", [0])
IO = dut.tick()

for _ in range(5):
    IO = dut.tick()


TEST_DATA = list(range(1, 9))
for _ in range(350):
    dut.prep("str_img_val", [1])
    dut.prep("str_img_bus", TEST_DATA)
    IO = dut.tick()

    if IO['str_img_rdy'] == 1:
        # sample the rdy to see if the data has been moved into the pipeline,
        # if both rdy & val are high we increment to the 'next' data
        TEST_DATA = [n+1 for n in TEST_DATA]


dut.finish()
