"""
Testbench for multiply_acc module.
"""

import pytest
import random
import shutil
import tempfile
import vpw

from enum import IntEnum
from typing import Final, Generator


class Param(IntEnum):
    """Module parameter configuration.

    Attributes
    GROUP_NB: Number of MAC units in parallel
    IMG_WIDTH: Bus width of image data
    KER_WIDTH: Bus width of kernel data
    """
    GROUP_NB = 4
    IMG_WIDTH = 16
    KER_WIDTH = 16


# Width of one result number
_RESULT_WIDTH: Final = Param.IMG_WIDTH + Param.KER_WIDTH + 1


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
    width_accumulate = _RESULT_WIDTH
    width_product = Param.IMG_WIDTH + Param.KER_WIDTH
    mask_accumulate = (1 << width_accumulate) - 1

    accumulate = _twos(width_accumulate, accumulate)
    product = _twos_extend(width_accumulate, width_product, product)

    return (accumulate + product) & mask_accumulate


class Checker:
    def __init__(self) -> None:
        self._reset: bool = False
        self._img = vpw.Slice("img", Param.IMG_WIDTH, Param.GROUP_NB)
        self._ker = vpw.Slice("ker", Param.KER_WIDTH, Param.GROUP_NB)
        self._result = vpw.Slice("result", _RESULT_WIDTH, Param.GROUP_NB)
        self._product = [0] * Param.GROUP_NB

    def reset(self, state: bool) -> None:
        """Prep 'reset' module and model."""
        vpw.prep("rst", [int(state)])
        self._reset = state

    def set(self, img: int, ker: int, *, position: int) -> None:
        """Prep 'image' and 'kernel' in module and model."""
        self._img[position] = img
        self._ker[position] = ker
        vpw.prep("val", [1])
        self._product[position] = _mac_multiply(img, ker)

    def init(self, dut) -> Generator:
        # init sub-tasks
        ports = []
        ports.append(self._img.init(dut))
        ports.append(self._ker.init(dut))
        ports.append(self._result.init(dut))
        for port in ports:
            next(port)

        result_1m = [0] * Param.GROUP_NB
        result = [0] * Param.GROUP_NB
        product_6p = [0] * Param.GROUP_NB
        product_5p = [0] * Param.GROUP_NB
        product_4p = [0] * Param.GROUP_NB
        product_3p = [0] * Param.GROUP_NB
        product_2p = [0] * Param.GROUP_NB
        product_1p = [0] * Param.GROUP_NB
        self._product = [0] * Param.GROUP_NB

        while True:
            io = yield
            # update sub-tasks
            for port in ports:
                port.send(io)

            for x in range(Param.GROUP_NB):
                assert self._result[x] == result[x], f"{result[x]} = {result_1m[x]} + {product_6p[x]}"

            result_1m = result
            for x in range(Param.GROUP_NB):
                result[x] = _mac_addition(result[x], product_5p[x])

            product_6p = product_5p
            product_5p = product_4p
            product_4p = product_3p
            product_3p = product_2p
            product_2p = product_1p
            product_1p = self._product
            self._product = [0] * Param.GROUP_NB

            vpw.prep("val", [0])
            for x in range(Param.GROUP_NB):
                self._img[x] = 0
                self._ker[x] = 0

            if self._reset:
                result = [0] * Param.GROUP_NB
                product_6p = [0] * Param.GROUP_NB
                product_5p = [0] * Param.GROUP_NB
                product_4p = [0] * Param.GROUP_NB
                product_3p = [0] * Param.GROUP_NB
                product_2p = [0] * Param.GROUP_NB
                product_1p = [0] * Param.GROUP_NB


@pytest.fixture(scope="module")
def design():
    workspace = tempfile.mkdtemp()

    dut = vpw.create(module='group_mac',
                     clock='clk',
                     include=['../hdl'],
                     parameter={'GROUP_NB': Param.GROUP_NB,
                                'IMG_WIDTH': Param.IMG_WIDTH,
                                'KER_WIDTH': Param.KER_WIDTH},
                     workspace=workspace)
    yield dut

    shutil.rmtree(workspace)


@pytest.fixture
def context(design):
    vpw.init(design, trace=False)

    vpw.prep("rst", [1])
    vpw.prep("img", vpw.pack(Param.GROUP_NB*Param.IMG_WIDTH, 0))
    vpw.prep("ker", vpw.pack(Param.GROUP_NB*Param.KER_WIDTH, 0))
    vpw.prep("val", [0])
    vpw.idle(2)
    vpw.prep("rst", [0])
    vpw.idle(2)

    yield

    vpw.idle(10)
    vpw.finish()


def test_pipeline_depth(context):
    """Test that module pipeline depth is 6 clock cycles deep."""
    img = vpw.Slice("img", Param.IMG_WIDTH, Param.GROUP_NB)
    vpw.register(img)

    ker = vpw.Slice("ker", Param.KER_WIDTH, Param.GROUP_NB)
    vpw.register(ker)

    result = vpw.Slice("result", _RESULT_WIDTH, Param.GROUP_NB)
    vpw.register(result)

    vpw.prep("val", [1])
    for x in range(Param.GROUP_NB):
        img[x] = 5 + x
        ker[x] = 1 + x

    vpw.tick()

    vpw.prep("val", [0])
    for x in range(Param.GROUP_NB):
        img[x] = 0
        ker[x] = 0

    vpw.idle(5)
    for x in range(Param.GROUP_NB):
        assert result[x] == 0, "Module is 5 clock cycles deep instead of 6."

    vpw.tick()
    for x in range(Param.GROUP_NB):
        assert result[x] == _mac_multiply((5 + x), (1 + x)), "Module should be 6 clocks cycles deep."


def test_stream_contiguous_positive(context):
    """Test contiguous stream with both image and kernel positive numbers."""
    checker = Checker()
    vpw.register(checker)

    for x in range(10):
        for p in range(Param.GROUP_NB):
            checker.set(x + 1, 1, position=p)
        vpw.tick()

    vpw.idle(10)  # wait for longer then the pipelined depth of module


def test_stream_contiguous_negative(context):
    """Test contiguous stream with image positive and kernel negative numbers."""
    checker = Checker()
    vpw.register(checker)

    for x in range(10):
        for p in range(Param.GROUP_NB):
            checker.set(x + 1, -1, position=p)
        vpw.tick()

    vpw.idle(10)  # wait for longer then the pipelined depth of module


def test_stream_contiguous_negative_double(context):
    """Test contiguous stream with both image and kernel negative numbers."""
    checker = Checker()
    vpw.register(checker)

    for x in range(-1, -11, -1):
        for p in range(Param.GROUP_NB):
            checker.set(x, -1, position=p)
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
            for p in range(Param.GROUP_NB):
                checker.set(image, 1, position=p)

        vpw.tick()

    vpw.idle(10)  # wait for longer then the pipelined depth of module


def test_stream_reset(context):
    """Test when a reset signal is sent during streaming."""
    checker = Checker()
    vpw.register(checker)

    for x in [1, 2, 3, 4, 5]:
        for p in range(Param.GROUP_NB):
            checker.set(x, 1, position=p)
        vpw.tick()

    checker.reset(True)
    for p in range(Param.GROUP_NB):
        checker.set(6, 1, position=p)
    vpw.tick()

    checker.reset(False)
    for x in [7, 8, 9, 10]:
        for p in range(Param.GROUP_NB):
            checker.set(x, 1, position=p)
        vpw.tick()

    vpw.idle(10)  # wait for longer then the pipelined depth of module


def test_stream_random(context):
    """Test many random numbers for both image and kernel."""
    checker = Checker()
    vpw.register(checker)

    for x in range(5000):
        for p in range(Param.GROUP_NB):
            checker.set(random.getrandbits(Param.IMG_WIDTH),
                        random.getrandbits(Param.KER_WIDTH),
                        position=p)
        vpw.tick()

    vpw.idle(10)  # wait for longer then the pipelined depth of module
