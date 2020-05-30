#!/usr/bin/env python3
"""
Testbench for the image_write module.
"""

from typing import Dict
from typing import Optional
from typing import Generator

import sys
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


def model_read(img: Dict[str, int],
               pad: Dict[str, int],
               maxp_side: int, conv: Dict[str, int]
               ) -> Generator[Optional[int], None, None]:
    """
    Create model of how the hardware generates image_read addresses
    """

    # total area of padded image
    area_w = pad['left'] + img['width'] + pad['right']
    area_h = pad['top'] + img['height'] + pad['bottom']

    def is_image(x_coor: int, y_coor: int) -> bool:
        """
        Test for when a coordinate pair is an image or padding pixel
        """
        result = True

        if x_coor < pad['left']:
            result = False

        if x_coor > (pad['left'] + img['width'] - 1):
            result = False

        if y_coor < pad['top']:
            result = False

        if y_coor > (pad['top'] + img['height'] - 1):
            result = False

        return result

    def xyz_address(x_addr: Dict[str, int],
                    y_addr: Dict[str, int],
                    z_depth: int) -> Optional[int]:
        """
        Calculates linear address when given the 3D coordinates
        """

        y_current = y_addr['area']+y_addr['maxp']+y_addr['conv']
        x_current = x_addr['area']+x_addr['maxp']+x_addr['conv']

        # check that x address is with valid range
        if x_current > area_w:
            print("Bad x addr")
            sys.exit()

        # check that y address is with valid range
        if y_current > area_h:
            print("Bad y addr")
            sys.exit()

        if not is_image(x_current, y_current):
            return None

        addr = ((y_current - pad['top']) * img['width'] * img['depth']) \
            + ((x_current - pad['left']) * img['depth']) \
            + z_depth

        return addr

    # last valid position within source image
    h_bound = (area_h - ((maxp_side - 1) * conv['step']) - (conv['side'] - 1))
    w_bound = (area_w - ((maxp_side - 1) * conv['step']) - (conv['side'] - 1))

    # conv volume for a given starting offset
    conv_volume = [{'y': y_conv, 'x': x_conv, 'z': z_depth}
                   for y_conv in range(0, conv['side'])
                   for x_conv in range(0, conv['side'])
                   for z_depth in range(0, img['depth'])]

    # maxpool area for a given starting offset
    maxp_plane = [{'y': y_maxp, 'x': x_maxp}
                  for y_maxp in range(0, (maxp_side * conv['step']), conv['step'])
                  for x_maxp in range(0, (maxp_side * conv['step']), conv['step'])]

    # area of input image
    area_plane = [{'y': y_area, 'x': x_area}
                  for y_area in range(0, h_bound, conv['step'])
                  for x_area in range(0, w_bound, conv['step'])]

    def addresses() -> Generator[Optional[int], None, None]:
        for i_addr in area_plane:
            for m_addr in maxp_plane:
                for c_addr in conv_volume:
                    yield xyz_address(
                        {'area': i_addr['x'],
                         'maxp': m_addr['x'],
                         'conv': c_addr['x']},
                        {'area': i_addr['y'],
                         'maxp': m_addr['y'],
                         'conv': c_addr['y']},
                        c_addr['z'])

    return addresses()


def setup():
    """ Set starting DUT values and reset module """

    dut.prep("cfg_data", [0])
    dut.prep("cfg_addr", [0])
    dut.prep("cfg_valid", [0])
    dut.prep("next", [0])
    dut.prep("rd_data", [0])
    dut.prep("image_rdy", [0])

    # reset module
    dut.prep("rst", [1])
    dut.tick()

    dut.prep("rst", [0])
    for _ in range(2):
        dut.tick()


def config(img: Dict[str, int],
           pad: Dict[str, int],
           maxp_side: int, conv: Dict[str, int]
           ) -> None:
    """ send configuration """

    # CFG_IR_IMG_W
    dut.prep("cfg_data", [concat_cfg1(img['width']-1)])
    dut.prep("cfg_addr", [5])
    dut.prep("cfg_valid", [1])
    io = dut.tick()

    # CFG_IR_IMG_DH
    dut.prep("cfg_data", [concat_cfg2((img['depth']-1), (img['height']-1))])
    dut.prep("cfg_addr", [6])
    dut.prep("cfg_valid", [1])
    io = dut.tick()

    # CFG_IR_PAD
    dut.prep("cfg_data", [concat_cfg4(pad['left'], pad['right'],
                                      pad['top'], pad['bottom'])])
    dut.prep("cfg_addr", [7])
    dut.prep("cfg_valid", [1])
    io = dut.tick()

    # CFG_IR_CONV
    dut.prep("cfg_data", [concat_cfg4((maxp_side-1), (conv['side']-1),
                                      0, (conv['step']-1))])
    dut.prep("cfg_addr", [8])
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


# cfg values
img_width = 10  # image width
img_height = 5  # image height
img_depth = 8   # image depth

pad_left = 1    # padding around left image
pad_right = 1   # padding around right image
pad_top = 1     # padding around top image
pad_bottom = 1  # padding around bottom image

maxp_side = 2   # maxp_side value of one will turn maxpooling off
conv_side = 3   # square side of conv e.g. 3x3
conv_step = 2   # distance to step for next conv volume


model = model_read(
    {'width': img_width, 'height': img_height, 'depth': img_depth},
    {'left': pad_left, 'right': pad_right, 'top': pad_top, 'bottom': pad_bottom},
    maxp_side,
    {'side': conv_side, 'step': conv_step})


dut.init()

setup()

config(
    {'width': img_width, 'height': img_height, 'depth': img_depth},
    {'left': pad_left, 'right': pad_right, 'top': pad_top, 'bottom': pad_bottom},
    maxp_side,
    {'side': conv_side, 'step': conv_step})


rd_data_2p = 1
rd_data_1p = 0
rd_data = 0

dut.prep("image_rdy", [1])

for _ in range(350):
    io = dut.tick()

    if io['rd_val'] == 0:
        dut.prep("rd_data", [0])
    else:
        rd_data = rd_data_1p
        rd_data_1p = rd_data_2p
        rd_data_2p = rd_data_2p + 1
        dut.prep("rd_data", [rd_data])


dut.finish()
