#!/usr/bin/env python3
"""
Testbench for the kernel module.
"""

from typing import Generator
import testbench as dut  # type: ignore


def concat_cfg2(arg1: int, arg0: int) -> int:
    shift_arg0 = (arg0 & 0x0000ffff)
    shift_arg1 = (arg1 & 0x0000ffff) << 16

    return (shift_arg1 | shift_arg0)


def setup() -> None:
    """ Set starting DUT values and reset module """

    dut.prep("cfg_data", [0])
    dut.prep("cfg_addr", [0])
    dut.prep("cfg_valid", [0])
    dut.prep("str_ker_val", [0])
    dut.prep("str_ker_bus", [0, 0, 0, 0, 0, 0, 0, 0])
    dut.prep("kernel_rdy", [0])

    # reset module
    dut.prep("rst", [1])
    dut.tick()

    dut.prep("rst", [0])
    for _ in range(2):
        dut.tick()


def config_wr(end: int) -> None:
    """ send write configuration """

    # CFG_KER_WR
    dut.prep("cfg_data", [end])
    dut.prep("cfg_addr", [1])
    dut.prep("cfg_valid", [1])
    dut.tick()

    dut.prep("cfg_data", [0])
    dut.prep("cfg_addr", [0])
    dut.prep("cfg_valid", [0])
    for _ in range(2):
        dut.tick()


def config_rd(end: int, start: int) -> None:
    """ send read configuration """

    # CFG_KER_RD
    dut.prep("cfg_data", [concat_cfg2(end, start)])
    dut.prep("cfg_addr", [2])
    dut.prep("cfg_valid", [1])
    dut.tick()

    dut.prep("cfg_data", [0])
    dut.prep("cfg_addr", [0])
    dut.prep("cfg_valid", [0])
    for _ in range(2):
        dut.tick()



dut.init()

setup()

config_wr(0)

str_data = list(range(1, 9))
for _ in range(16*(1+6)):
    dut.prep("str_ker_val", [1])
    dut.prep("str_ker_bus", str_data)

    io = dut.tick()

    if io['str_ker_rdy'] == 1:
        # sample the rdy to see if the data has been moved into the pipeline,
        # if both rdy & val are high we increment to the 'next' data
        str_data = [n+1 for n in str_data]

dut.prep("str_ker_val", [0])
dut.prep("str_ker_bus", [0, 0, 0, 0, 0, 0, 0, 0])
dut.tick()


config_rd(5, 0)


dut.prep("kernel_rdy", [1])
for _ in range(20):
    dut.tick()


dut.finish()
