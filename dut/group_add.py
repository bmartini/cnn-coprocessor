"""
Testbench for group_add module.
"""

import pytest
import random
import shutil
import tempfile
import vpw

from collections import deque
from enum import IntEnum
from typing import Deque, Dict, Generator


class Param(IntEnum):
    """Module parameter configuration.

    Attributes
    GROUP_NB: Number of MAC units in parallel
    NUM_WIDTH: Bus width of (up|dn)_data number
    """
    GROUP_NB = 4
    NUM_WIDTH = 16


def _twos(width: int, data: int) -> int:
    """Convert signed numbers into two's complement.

    If a number sent in as a negatively signed int it will be converted to a
    two's complement negative number with a defined bit width. Otherwise the
    number is masked to not extra bits are expressed in the returned number.

    Arguments
    width: Number of bits used to express the data value
    data: The number to be converted to two's complement
    """
    mask = (1 << width) - 1

    if data < 0:
        data = data + 2**width

    return data & mask


def _twos_extend(extend_width: int, data_width: int, data: int) -> int:
    """Extend signed bit of a two's complement number.

    Before performing an operation on a twos complement number its width must
    be extended to be the same as the finial operator.

    Arguments
    extend_width: Number of bits used to express the extended data value
    data_width: Number of bits used to express the data value
    data: The number to be converted to two's complement
    """
    mask_data = (1 << data_width) - 1
    mask_extend = (1 << extend_width) - 1
    negative = 1 << (data_width - 1)

    data = _twos(data_width, data)

    if bool(data & negative):
        data = (mask_extend ^ mask_data) | data

    return data


def _model_group_add(arg3: int, arg2: int, arg1: int, arg0: int) -> int:
    """Two's complement addition."""
    width_sum = Param.NUM_WIDTH + 2
    mask = (1 << Param.NUM_WIDTH) - 1

    arg0 = _twos_extend(width_sum, Param.NUM_WIDTH, arg0)
    arg1 = _twos_extend(width_sum, Param.NUM_WIDTH, arg1)
    arg2 = _twos_extend(width_sum, Param.NUM_WIDTH, arg2)
    arg3 = _twos_extend(width_sum, Param.NUM_WIDTH, arg3)

    return (arg3 + arg2 + arg1 + arg0) & mask


class Checker:
    def __init__(self) -> None:
        self._sum = 0
        self._up = vpw.Slice("up_data", Param.NUM_WIDTH, Param.GROUP_NB)

    def set(self, arg3: int, arg2: int, arg1: int, arg0: int) -> None:
        """Prep 4 addends for to send into module."""
        self._sum = _model_group_add(arg3, arg2, arg1, arg0)
        self._up[0] = arg0
        self._up[1] = arg1
        self._up[2] = arg2
        self._up[3] = arg3

    def init(self, dut) -> Generator:
        up = self._up.init(dut)
        next(up)
        sum_6p = 0
        sum_5p = 0
        sum_4p = 0
        sum_3p = 0
        sum_2p = 0
        sum_1p = 0
        self._sum = 0
        self._up[0] = 0
        self._up[1] = 0
        self._up[2] = 0
        self._up[3] = 0

        while True:
            io = yield
            up.send(io)
            sum_6p = sum_5p
            sum_5p = sum_4p
            sum_4p = sum_3p
            sum_3p = sum_2p
            sum_2p = sum_1p
            sum_1p = self._sum
            self._sum = 0
            self._up[0] = 0
            self._up[1] = 0
            self._up[2] = 0
            self._up[3] = 0

            assert io["dn_data"] == sum_6p


@pytest.fixture(scope="module")
def design():
    workspace = tempfile.mkdtemp()

    dut = vpw.create(module='group_add',
                     clock='clk',
                     include=['../hdl'],
                     parameter={'GROUP_NB': Param.GROUP_NB,
                                'NUM_WIDTH': Param.NUM_WIDTH},
                     workspace=workspace)
    yield dut

    shutil.rmtree(workspace)


@pytest.fixture
def context(design):
    vpw.init(design, trace=True)

    vpw.prep("up_data", vpw.pack(Param.GROUP_NB*Param.NUM_WIDTH, 0))
    vpw.idle(2)

    yield

    vpw.idle(10)
    vpw.finish()


def test_pipeline_depth(context):
    """Test that module pipeline depth is 4 clock cycles deep."""

    vpw.prep("up_data", vpw.pack(Param.NUM_WIDTH*Param.GROUP_NB, 5))
    vpw.tick()
    vpw.prep("up_data", vpw.pack(Param.NUM_WIDTH, 0))

    io = vpw.tick()
    assert io["dn_data"] == 0, "Module is 3 clock cycles deep instead of 4."

    io = vpw.idle(4)
    assert io["dn_data"] == _model_group_add(0, 0, 0, 5), "Module should be 4 clocks cycles deep."

    io = vpw.tick()
    assert io["dn_data"] == 0, "Module is 5 clock cycles deep instead of 4."


def test_numbers_positive(context):
    """Test when up stream numbers are positive values."""
    checker = Checker()
    vpw.register(checker)

    for x in range(10):
        checker.set(x+4, x+3, x+2, x+1)
        vpw.tick()

    vpw.idle(10)  # wait for longer then the pipelined depth of module


def test_numbers_positive_intermittent(context):
    """Test when up stream is intermittent and the numbers have positive values."""
    checker = Checker()
    vpw.register(checker)

    data = [x + 1 for x in range(10)]

    while data:
        if bool(random.getrandbits(1)):
            x = data.pop(0)
            checker.set(x+4, x+3, x+2, x+1)

        vpw.tick()

    vpw.idle(10)  # wait for longer then the pipelined depth of module


def test_number_negative(context):
    """Test when up stream numbers are negative values."""
    checker = Checker()
    vpw.register(checker)

    for x in range(-1, -11, -1):
        checker.set(x-4, x-3, x-2, x-1)
        vpw.tick()

    vpw.idle(10)  # wait for longer then the pipelined depth of module


def test_number_negative_intermittent(context):
    """Test when up stream is intermittent and the numbers have negative values."""
    checker = Checker()
    vpw.register(checker)

    data = [x + 1 for x in range(-1, -11, -1)]

    while data:
        if bool(random.getrandbits(1)):
            x = data.pop(0)
            checker.set(x-4, x-3, x-2, x-1)
        vpw.tick()

    vpw.idle(10)  # wait for longer then the pipelined depth of module


def test_bypass_random_numbers(context):
    """Test many random number values."""
    checker = Checker()
    vpw.register(checker)

    for _ in range(5000):
        checker.set(random.getrandbits(Param.NUM_WIDTH),
                    random.getrandbits(Param.NUM_WIDTH),
                    random.getrandbits(Param.NUM_WIDTH),
                    random.getrandbits(Param.NUM_WIDTH))
        vpw.tick()

    vpw.idle(10)  # wait for longer then the pipelined depth of module
