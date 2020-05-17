#!/usr/bin/env python3
"""
Testbench for the image_write module.
"""

from typing import Generator
import testbench as dut  # type: ignore


def concat_cfg2(left: int, right: int) -> int:
    shift_left = left << 16
    mask_right = right & 0x0000ffff

    return (shift_left | mask_right)


def model_write(start_addr: int, step_pixel: int, img_height: int,
                img_width: int, step_row: int) -> Generator[int, None, None]:
    """ Address calculation model """

    for depth in range(0, step_pixel):  # step over row
        for height in range(0, img_height):  # step over row
            for width in range(0, img_width):  # step over row
                addr = (start_addr + depth) \
                    + (height * step_pixel * step_row) \
                    + (width * step_pixel)

                yield addr


def setup():
    """ Set starting DUT values and reset module """

    dut.prep("cfg_data", [0])
    dut.prep("cfg_addr", [0])
    dut.prep("cfg_valid", [0])
    dut.prep("next", [0])
    dut.prep("str_img_val", [0])
    dut.prep("str_img_bus", [0, 0, 0, 0, 0, 0, 0, 0])

    # reset module
    dut.prep("rst", [1])
    dut.tick()

    dut.prep("rst", [0])
    for _ in range(2):
        dut.tick()


def config(start_addr: int, step_pixel: int, img_height: int,
           img_width: int, step_row: int) -> None:
    """ send configuration """

    # CFG_IW_IMG_W
    dut.prep("cfg_data", [(img_width-1)])
    dut.prep("cfg_addr", [9])
    dut.prep("cfg_valid", [1])
    io = dut.tick()

    # CFG_IW_START
    dut.prep("cfg_data", [concat_cfg2(start_addr, (img_height-1))])
    dut.prep("cfg_addr", [10])
    dut.prep("cfg_valid", [1])
    io = dut.tick()

    # CFG_IW_STEP
    dut.prep("cfg_data", [concat_cfg2((step_pixel-1), (step_row-1))])
    dut.prep("cfg_addr", [11])
    dut.prep("cfg_valid", [1])
    io = dut.tick()

    dut.prep("cfg_data", [0])
    dut.prep("cfg_addr", [0])
    dut.prep("cfg_valid", [0])
    for _ in range(3):
        io = dut.tick()

    # register next configuration
    dut.prep("next", [1])
    io = dut.tick()

    while not io["next_rdy"]:
        # wait on next handshake if next_rdy is not high
        io = dut.tick()

    dut.prep("next", [0])
    io = dut.tick()

    for _ in range(5):
        io = dut.tick()


# cfg values
img_width = 10  # image width
img_height = 5  # image height

start_addr = 0  # starting offset

step_pixel = 4  # distance to step to next pixel
step_row = 10   # distance to step to next row


model = model_write(start_addr, step_pixel, img_height, img_width, step_row)

dut.init()

setup()

config(start_addr, step_pixel, img_height, img_width, step_row)


str_data = list(range(1, 9))
wr_data = list(range(1, 9))
for _ in range(350):
    dut.prep("str_img_val", [1])
    dut.prep("str_img_bus", str_data)

    io = dut.tick()

    if io['str_img_rdy'] == 1:
        # sample the rdy to see if the data has been moved into the pipeline,
        # if both rdy & val are high we increment to the 'next' data
        str_data = [n+1 for n in str_data]

    if io['wr_val'] == 1:
        assert io['wr_addr'] == next(model)
        assert io['wr_data'] == wr_data
        wr_data = [n+1 for n in wr_data]

dut.finish()
