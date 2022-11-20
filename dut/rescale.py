"""
Testbench for rescale module.
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
    NUM_WIDTH: Bus width of up_data number
    IMG_WIDTH: Bus width of dn_data number
    """
    NUM_WIDTH = 33
    IMG_WIDTH = 16


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


def _model_rescale(number: int, shift: int) -> int:
    num_mask = (1 << Param.NUM_WIDTH) - 1
    negative = 1 << (Param.NUM_WIDTH - 1)
    img_max = int((1 << (Param.IMG_WIDTH - 1)) - 1)
    img_min = int((img_max + 1) * -1)

    # converts to twos complement of defined width
    number = _twos(Param.NUM_WIDTH, number)

    # convert number back into negative when down stream should be negative
    if (number & negative) != 0 and Param.NUM_WIDTH >= (Param.IMG_WIDTH + shift):
        number = int((num_mask - number + 1) * -1)

    # raw value of shifted number
    scaled = _twos(Param.IMG_WIDTH, (number >> shift))

    if int(number >> shift) > img_max:
        # shifted number greater than image max
        scaled = _twos(Param.IMG_WIDTH, img_max)

    if int(number >> shift) < img_min:
        # shifted number less than image min
        scaled = _twos(Param.IMG_WIDTH, img_min)

    return scaled


class Checker:
    def __init__(self) -> None:
        self._queue: Deque[Dict[str, int]] = deque()

    def empty(self) -> bool:
        return False if self._queue else True

    def send(self, data: int, shift: int) -> None:
        """Add 'data' and 'shift' to queue for sending into rescale module."""
        self._queue.append({"up_data": data, "shift": shift})

    def init(self, _) -> Generator:
        number_5p = {"up_data": 0, "shift": 0}
        number_4p = {"up_data": 0, "shift": 0}
        number_3p = {"up_data": 0, "shift": 0}
        number_2p = {"up_data": 0, "shift": 0}
        number_1p = {"up_data": 0, "shift": 0}
        number = {"up_data": 0, "shift": 0}
        vpw.prep("up_data", vpw.pack(Param.NUM_WIDTH, number["up_data"]))
        vpw.prep("shift", [number["shift"]])

        while True:
            io = yield
            number_5p = number_4p
            number_4p = number_3p
            number_3p = number_2p
            number_2p = number_1p
            number_1p = number
            number = {"up_data": 0, "shift": 0}
            if self._queue:
                number = self._queue.popleft()

            vpw.prep("up_data", vpw.pack(Param.NUM_WIDTH, number["up_data"]))
            vpw.prep("shift", [number["shift"]])

            assert io["dn_data"] == _model_rescale(number_5p["up_data"], number_5p["shift"])


@pytest.fixture(scope="module")
def design():
    workspace = tempfile.mkdtemp()

    dut = vpw.create(module='rescale',
                     clock='clk',
                     include=['../hdl'],
                     parameter={'NUM_WIDTH': Param.NUM_WIDTH,
                                'IMG_WIDTH': Param.IMG_WIDTH},
                     workspace=workspace)
    yield dut

    shutil.rmtree(workspace)


@pytest.fixture
def context(design):
    vpw.init(design, trace=False)

    vpw.prep("shift", [0])
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

    io = vpw.idle(3)
    assert io["dn_data"] == 0, "Module is 3 clock cycles deep instead of 4."

    io = vpw.tick()
    assert io["dn_data"] == _model_rescale(5, 0), "Module should be 4 clocks cycles deep."

    io = vpw.tick()
    assert io["dn_data"] == 0, "Module is 5 clock cycles deep instead of 4."


def test_image_maximum(context):
    """Test when up stream number is greater than what can be represented to by down stream."""
    vpw.prep("up_data", vpw.pack(Param.NUM_WIDTH, 75000))

    io = vpw.idle(10)  # wait for longer then the pipelined depth of module
    assert io["dn_data"] == _model_rescale(75000, 0), "Model max is different from modules max."


def test_image_minimum(context):
    """Test when up stream number is less than what can be represented to by down stream."""
    vpw.prep("up_data", vpw.pack(Param.NUM_WIDTH, -75000))

    io = vpw.idle(10)  # wait for longer then the pipelined depth of module
    assert io["dn_data"] == _model_rescale(-75000, 0), "Model min is different from modules min."


def test_dynamic_shift(context):
    """Test when up stream number is less than what can be represented to by down stream."""
    checker = Checker()
    vpw.register(checker)

    for x in range(18):
        checker.send(266240, x)

    # wait until all data has been sent into DUT
    while not checker.empty():
        vpw.tick()

    vpw.idle(10)  # wait for longer then the pipelined depth of module


def test_shift_random_number(context):
    """Test many random numbers for every valid shift value."""
    checker = Checker()
    vpw.register(checker)

    for shift in range(Param.NUM_WIDTH + 1):
        for _ in range(5000):
            checker.send(random.getrandbits(Param.IMG_WIDTH + shift), shift)

    # wait until all data has been sent into DUT
    while not checker.empty():
        vpw.tick()

    vpw.idle(10)  # wait for longer then the pipelined depth of module
