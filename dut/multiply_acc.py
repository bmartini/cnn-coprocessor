"""
Testbench for multiply_acc module.
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
    IMG_WIDTH: Bus width of image data
    KER_WIDTH: Bus width of kernel data
    """
    IMG_WIDTH = 16
    KER_WIDTH = 16


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


def _mac_multiply(img: int, ker: int) -> int:
    """Two's complement multiply."""
    width = Param.IMG_WIDTH + Param.KER_WIDTH
    mask = (1 << width) - 1

    img = _twos_extend(width, Param.IMG_WIDTH, img)
    ker = _twos_extend(width, Param.KER_WIDTH, ker)

    return (img * ker) & mask


def _mac_addition(accumulate: int, product: int) -> int:
    """Two's complement addition."""
    width_accumulate = Param.IMG_WIDTH + Param.KER_WIDTH + 1
    width_product = Param.IMG_WIDTH + Param.KER_WIDTH
    mask_accumulate = (1 << width_accumulate) - 1

    accumulate = _twos(width_accumulate, accumulate)
    product = _twos_extend(width_accumulate, width_product, product)

    return (accumulate + product) & mask_accumulate


class Checker:
    def __init__(self) -> None:
        self._reset: int = 0
        self._product: int = 0
        self._result: int = 0

    def reset(self, state: bool) -> None:
        """Prep 'reset' module and model."""
        vpw.prep("rst", [int(state)])
        self._reset = state

    def set(self, img: int, ker: int) -> None:
        """Prep 'image' and 'kernel' in module and model."""
        vpw.prep("img", vpw.pack(Param.IMG_WIDTH, img))
        vpw.prep("ker", vpw.pack(Param.KER_WIDTH, ker))
        vpw.prep("val", [1])
        self._product = _mac_multiply(img, ker)

    def init(self, _) -> Generator:
        result_1m = 0
        result = 0
        product_5p = 0
        product_4p = 0
        product_3p = 0
        product_2p = 0
        product_1p = 0
        self._product = 0

        while True:
            io = yield
            assert io["result"] == result, f"{result_1m}, {product_5p}"

            result_1m = result
            result = _mac_addition(result, product_4p)
            product_5p = product_4p
            product_4p = product_3p
            product_3p = product_2p
            product_2p = product_1p
            product_1p = self._product
            self._product = 0
            vpw.prep("img", vpw.pack(Param.IMG_WIDTH, 0))
            vpw.prep("ker", vpw.pack(Param.KER_WIDTH, 0))
            vpw.prep("val", [0])

            if self._reset:
                result = 0
                product_5p = 0
                product_4p = 0
                product_3p = 0
                product_2p = 0
                product_1p = 0


@pytest.fixture(scope="module")
def design():
    workspace = tempfile.mkdtemp()

    dut = vpw.create(module='multiply_acc',
                     clock='clk',
                     include=['../hdl'],
                     parameter={'IMG_WIDTH': Param.IMG_WIDTH,
                                'KER_WIDTH': Param.KER_WIDTH},
                     workspace=workspace)
    yield dut

    shutil.rmtree(workspace)


@pytest.fixture
def context(design):
    vpw.init(design, trace=False)

    vpw.prep("rst", [1])
    vpw.prep("img", vpw.pack(Param.IMG_WIDTH, 0))
    vpw.prep("ker", vpw.pack(Param.KER_WIDTH, 0))
    vpw.prep("val", [0])
    vpw.idle(2)
    vpw.prep("rst", [0])
    vpw.idle(2)

    yield

    vpw.idle(10)
    vpw.finish()


def test_pipeline_depth(context):
    """Test that module pipeline depth is 5 clock cycles deep."""
    vpw.prep("img", vpw.pack(Param.IMG_WIDTH, 5))
    vpw.prep("ker", vpw.pack(Param.KER_WIDTH, 1))
    vpw.prep("val", [1])
    vpw.tick()
    vpw.prep("img", vpw.pack(Param.IMG_WIDTH, 0))
    vpw.prep("ker", vpw.pack(Param.KER_WIDTH, 0))
    vpw.prep("val", [0])

    io = vpw.idle(4)
    assert io["result"] == 0, "Module is 4 clock cycles deep instead of 5."

    io = vpw.tick()
    assert io["result"] == 5, "Module should be 5 clocks cycles deep."


def test_stream_contiguous_positive(context):
    """Test contiguous stream with both image and kernel positive numbers."""
    checker = Checker()
    vpw.register(checker)

    for x in range(10):
        checker.set(x + 1, 1)
        vpw.tick()

    vpw.idle(10)  # wait for longer then the pipelined depth of module


def test_stream_contiguous_negative(context):
    """Test contiguous stream with image positive and kernel negative numbers."""
    checker = Checker()
    vpw.register(checker)

    for x in range(10):
        checker.set(x + 1, -1)
        vpw.tick()

    vpw.idle(10)  # wait for longer then the pipelined depth of module


def test_stream_contiguous_negative_double(context):
    """Test contiguous stream with both image and kernel negative numbers."""
    checker = Checker()
    vpw.register(checker)

    for x in range(-1, -11, -1):
        checker.set(x, -1)
        vpw.tick()

    vpw.idle(10)  # wait for longer then the pipelined depth of module


def test_stream_intermittent(context):
    """Test intermittent stream."""
    checker = Checker()
    vpw.register(checker)

    data = [x + 1 for x in range(10)]

    while data:
        if bool(random.getrandbits(1)):
            image = data.pop(0)
            checker.set(image, 1)

        vpw.tick()

    vpw.idle(10)  # wait for longer then the pipelined depth of module


def test_stream_reset(context):
    """Test when a reset signal is sent during streaming."""
    checker = Checker()
    vpw.register(checker)

    for x in [1, 2, 3, 4, 5]:
        checker.set(x, 1)
        vpw.tick()

    checker.reset(True)
    checker.set(6, 1)
    vpw.tick()

    checker.reset(False)
    for x in [7, 8, 9, 10]:
        checker.set(x, 1)
        vpw.tick()

    vpw.idle(10)  # wait for longer then the pipelined depth of module


def test_stream_random(context):
    """Test many random numbers for both image and kernel."""
    checker = Checker()
    vpw.register(checker)

    for x in range(5000):
        checker.set(random.getrandbits(Param.IMG_WIDTH), random.getrandbits(Param.KER_WIDTH))
        vpw.tick()

    vpw.idle(10)  # wait for longer then the pipelined depth of module
