#!/usr/bin/env python3
"""
Testbench for the image_write module.
"""

from typing import Dict

import testbench as dut  # type: ignore


def concat_cfg1(arg0: int) -> int:
    return (arg0 & 0xffffffff)


def concat_cfg2(arg1: int, arg0: int) -> int:
    shift_arg0 = (arg0 & 0x0000ffff)
    shift_arg1 = (arg1 & 0x0000ffff) << 16

    return (shift_arg1 | shift_arg0)


def concat_cfg4(arg3: int, arg2: int, arg1: int, arg0: int) -> int:
    shift_arg0 = (arg0 & 0x000000ff)
    shift_arg1 = (arg1 & 0x000000ff) << 8
    shift_arg2 = (arg2 & 0x000000ff) << 16
    shift_arg3 = (arg3 & 0x000000ff) << 24

    return (shift_arg3 | shift_arg2 | shift_arg1 | shift_arg0)


def setup():
    """ Set starting DUT values and reset module """

    dut.prep("cfg_data", [0])
    dut.prep("cfg_addr", [0])
    dut.prep("cfg_valid", [0])
    dut.prep("str_img_bus", [0])
    dut.prep("str_img_val", [0])
    dut.prep("image_rdy", [0])

    # reset module
    dut.prep("rst", [1])
    dut.tick()

    dut.prep("rst", [0])
    for _ in range(2):
        dut.tick()


def config_write(start_addr: int, step_pixel: int, step_row: int,
                 img: Dict[str, int], mem_select: int) -> None:
    """ send write configuration """

    # CFG_IW_IMG_W
    dut.prep("cfg_data", [(img['width']-1)])
    dut.prep("cfg_addr", [9])
    dut.prep("cfg_valid", [1])
    dut.tick()

    # CFG_IW_START
    dut.prep("cfg_data", [concat_cfg2(start_addr, (img['height']-1))])
    dut.prep("cfg_addr", [10])
    dut.prep("cfg_valid", [1])
    dut.tick()

    # CFG_IW_STEP
    dut.prep("cfg_data", [concat_cfg2((step_pixel-1), (step_row-1))])
    dut.prep("cfg_addr", [11])
    dut.prep("cfg_valid", [1])
    dut.tick()

    # CFG_IMG_WR
    dut.prep("cfg_data", [mem_select])
    dut.prep("cfg_addr", [3])
    dut.prep("cfg_valid", [1])
    dut.tick()

    dut.prep("cfg_data", [0])
    dut.prep("cfg_addr", [0])
    dut.prep("cfg_valid", [0])
    for _ in range(3):
        dut.tick()


def config_read(img: Dict[str, int], pad: Dict[str, int],
                maxp_side: int, conv: Dict[str, int], mem_select: int) -> None:
    """ send read configuration """

    # CFG_IR_IMG_W
    dut.prep("cfg_data", [concat_cfg1(img['width']-1)])
    dut.prep("cfg_addr", [5])
    dut.prep("cfg_valid", [1])
    dut.tick()

    # CFG_IR_IMG_DH
    dut.prep("cfg_data", [concat_cfg2((img['depth']-1), (img['height']-1))])
    dut.prep("cfg_addr", [6])
    dut.prep("cfg_valid", [1])
    dut.tick()

    # CFG_IR_PAD
    dut.prep("cfg_data", [concat_cfg4(pad['left'], pad['right'],
                                      pad['top'], pad['bottom'])])
    dut.prep("cfg_addr", [7])
    dut.prep("cfg_valid", [1])
    dut.tick()

    # CFG_IR_CONV
    dut.prep("cfg_data", [concat_cfg4((maxp_side-1), (conv['side']-1),
                                      0, (conv['step']-1))])
    dut.prep("cfg_addr", [8])
    dut.prep("cfg_valid", [1])
    dut.tick()

    # CFG_IMG_RD
    dut.prep("cfg_data", [0])
    dut.prep("cfg_addr", [4])
    dut.prep("cfg_valid", [1])
    dut.tick()

    dut.prep("cfg_data", [0])
    dut.prep("cfg_addr", [0])
    dut.prep("cfg_valid", [0])
    for _ in range(3):
        dut.tick()


# parameters
param = {}
param['CFG_DWIDTH'] = 32
param['CFG_AWIDTH'] = 5
param['STR_IMG_WIDTH'] = 64
param['GROUP_NB'] = 4
param['IMG_WIDTH'] = 16
param['DEPTH_NB'] = 16
param['MEM_AWIDTH'] = 16

# cfg values
img_width = 10      # image width
img_height = 5      # image height
img_depth = 8       # image depth

start_addr = 0      # starting offset
step_pixel = 4      # distance to step to next pixel
step_row = 10       # distance to step to next row

pad_left = 1        # padding around left image
pad_right = 1       # padding around right image
pad_top = 1         # padding around top image
pad_bottom = 1      # padding around bottom image

maxp_side = 2       # maxp_side value of one will turn maxpooling off
conv_side = 3       # square side of conv e.g. 3x3
conv_step = 2       # distance to step for next conv volume

wr_mem_select = 0   # select the image_write buffer to activate
rd_mem_select = 0   # select the image_read buffer to activate

stream_nb = int(img_width * img_height * step_pixel *
                (param['IMG_WIDTH'] * param['DEPTH_NB'] / param['STR_IMG_WIDTH']))


dut.init()

setup()

config_write(
    start_addr, step_pixel, step_row,
    {'width': img_width, 'height': img_height, 'depth': img_depth},
    wr_mem_select)


cnt = 1
for _ in range(stream_nb):
    dut.prep("str_img_val", [1])
    dut.prep("str_img_bus", [cnt])

    io = dut.tick()

    if io['str_img_rdy'] == 1:
        # sample the rdy to see if the data has been moved into the pipeline,
        # if both rdy & val are high we increment to the 'next' data
        cnt = cnt + 1

dut.prep("str_img_val", [0])
dut.prep("str_img_bus", [0])


config_read(
    {'width': img_width, 'height': img_height, 'depth': img_depth},
    {'left': pad_left, 'right': pad_right, 'top': pad_top, 'bottom': pad_bottom},
    maxp_side,
    {'side': conv_side, 'step': conv_step},
    rd_mem_select)


dut.prep("image_rdy", [1])

io = dut.tick()
while io['image_last'] == 0:
    io = dut.tick()

for _ in range(100):
    io = dut.tick()


dut.finish()
