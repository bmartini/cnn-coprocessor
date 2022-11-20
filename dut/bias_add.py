"""
Testbench for bias_add module.
"""

import pytest
import random
import shutil
import tempfile
import vpw

from enum import IntEnum
from typing import Generator


class Param(IntEnum):
    """Module parameter configuration.

    Attributes
    NUM_WIDTH: Bus width of bias and (up|dn)_data number
    """
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


def _addition(arg1: int, arg0: int) -> int:
    """Two's complement addition."""
    width_sum = Param.NUM_WIDTH + 1
    mask = (1 << Param.NUM_WIDTH) - 1

    arg0 = _twos_extend(width_sum, Param.NUM_WIDTH, arg0)
    arg1 = _twos_extend(width_sum, Param.NUM_WIDTH, arg1)

    return (arg1 + arg0) & mask


class Checker:
    def __init__(self) -> None:
        self._bias = 0
        self._data = 0

    def bias(self, bias: int) -> None:
        """Prep 'bias' into module."""
        self._bias = bias

    def data(self, data: int) -> None:
        """Prep 'data' into module."""
        self._data = data

    def init(self, _) -> Generator:
        sum_2p = 0
        sum_1p = 0
        sum_0p = 0

        while True:
            io = yield
            sum_2p = sum_1p
            sum_1p = sum_0p
            sum_0p = _addition(self._bias, self._data)
            vpw.prep("bias", vpw.pack(Param.NUM_WIDTH, self._bias))
            vpw.prep("up_data", vpw.pack(Param.NUM_WIDTH, self._data))

            assert io["dn_data"] == sum_2p


@pytest.fixture(scope="module")
def design():
    workspace = tempfile.mkdtemp()

    dut = vpw.create(module='bias_add',
                     clock='clk',
                     include=['../hdl'],
                     parameter={'NUM_WIDTH': Param.NUM_WIDTH},
                     workspace=workspace)
    yield dut

    shutil.rmtree(workspace)


@pytest.fixture
def context(design):
    vpw.init(design, trace=False)

    vpw.prep("bias", vpw.pack(Param.NUM_WIDTH, 0))
    vpw.prep("up_data", vpw.pack(Param.NUM_WIDTH, 0))
    vpw.idle(2)

    yield

    vpw.idle(10)
    vpw.finish()


def test_pipeline_depth(context):
    """Test that module pipeline depth is 4 clock cycles deep."""
    vpw.prep("up_data", vpw.pack(Param.NUM_WIDTH, 5))
    vpw.tick()
    vpw.prep("up_data", vpw.pack(Param.NUM_WIDTH, 0))

    io = vpw.tick()
    assert io["dn_data"] == _addition(0, 5), "Module should be 1 clocks cycles deep."

    io = vpw.tick()
    assert io["dn_data"] == 0, "Module is 2 clock cycles deep instead of 1."


def test_numbers_positive_contiguous(context):
    """Test when up stream is contiguous and the numbers have positive values."""
    checker = Checker()
    vpw.register(checker)
    vpw.tick()

    checker.bias(1)

    for x in range(10):
        checker.data(x+1)
        vpw.tick()

    vpw.idle(10)  # wait for longer then the pipelined depth of module


def test_numbers_positive_intermittent(context):
    """Test when up stream is intermittent and the numbers have positive values."""
    checker = Checker()
    vpw.register(checker)
    vpw.tick()

    checker.bias(1)

    data = [x + 1 for x in range(10)]

    while data:
        if bool(random.getrandbits(1)):
            x = data.pop(0)
            checker.data(x)

        vpw.tick()

    vpw.idle(10)  # wait for longer then the pipelined depth of module


def test_numbers_positive_decreasing(context):
    """Test starting with positive number decreasing to negative."""
    checker = Checker()
    vpw.register(checker)
    vpw.tick()

    checker.bias(5)

    for x in range(-1, -11, -1):
        checker.data(x)
        vpw.tick()

    vpw.idle(10)  # wait for longer then the pipelined depth of module


def test_numbers_negative_contiguous(context):
    """Test when up stream is contiguous and the numbers have negative values."""
    checker = Checker()
    vpw.register(checker)
    vpw.tick()

    checker.bias(-1)

    for x in range(-1, -11, -1):
        checker.data(x)
        vpw.tick()

    vpw.idle(10)  # wait for longer then the pipelined depth of module


def test_numbers_negative_intermittent(context):
    """Test when up stream is intermittent and the numbers have negative values."""
    checker = Checker()
    vpw.register(checker)
    vpw.tick()

    checker.bias(-1)

    data = [x + 1 for x in range(-1, -11, -1)]

    while data:
        if bool(random.getrandbits(1)):
            x = data.pop(0)
            checker.data(x)
        vpw.tick()

    vpw.idle(10)  # wait for longer then the pipelined depth of module


def test_numbers_negative_increasing(context):
    """Test starting with negative number increasing to positive."""
    checker = Checker()
    vpw.register(checker)
    vpw.tick()

    checker.bias(-5)

    for x in range(10):
        checker.data(x+1)
        vpw.tick()

    vpw.idle(10)  # wait for longer then the pipelined depth of module


def test_random_numbers(context):
    """Test many random number values."""
    checker = Checker()
    vpw.register(checker)

    for _ in range(5000):
        checker.bias(random.getrandbits(Param.NUM_WIDTH))
        checker.data(random.getrandbits(Param.NUM_WIDTH))
        vpw.tick()

    vpw.idle(10)  # wait for longer then the pipelined depth of module
