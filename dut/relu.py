"""
Testbench for relu module.
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
    NUM_WIDTH: Bus width of (up|dn)_data number
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


def _model_relu(number: int, bypass: bool) -> int:
    negative = 1 << (Param.NUM_WIDTH - 1)
    number = _twos(Param.NUM_WIDTH, number)

    return number if bypass or ((number & negative) == 0) else 0


class Checker:
    def __init__(self) -> None:
        self._queue: Deque[Dict[str, int]] = deque()

    def empty(self) -> bool:
        return False if self._queue else True

    def send(self, data: int, bypass: int) -> None:
        """Add 'data' and 'bypass' to queue for sending into relu module."""
        self._queue.append({"up_data": data, "bypass": bypass})

    def init(self, _) -> Generator:
        number_3p = {"up_data": 0, "bypass": 0}
        number_2p = {"up_data": 0, "bypass": 0}
        number_1p = {"up_data": 0, "bypass": 0}
        number = {"up_data": 0, "bypass": 0}
        vpw.prep("up_data", vpw.pack(Param.NUM_WIDTH, number["up_data"]))
        vpw.prep("bypass", [number["bypass"]])

        while True:
            io = yield
            number_3p = number_2p
            number_2p = number_1p
            number_1p = number
            number = {"up_data": 0, "bypass": 0}
            if self._queue:
                number = self._queue.popleft()

            vpw.prep("up_data", vpw.pack(Param.NUM_WIDTH, number["up_data"]))
            vpw.prep("bypass", [number["bypass"]])

            assert io["dn_data"] == _model_relu(number_3p["up_data"], number_3p["bypass"])


@pytest.fixture(scope="module")
def design():
    workspace = tempfile.mkdtemp()

    dut = vpw.create(module='relu',
                     clock='clk',
                     include=['../hdl'],
                     parameter={'NUM_WIDTH': Param.NUM_WIDTH},
                     workspace=workspace)
    yield dut

    shutil.rmtree(workspace)


@pytest.fixture
def context(design):
    vpw.init(design, trace=False)

    vpw.prep("bypass", [0])
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
    assert io["dn_data"] == 0, "Module is 1 clock cycles deep instead of 2."

    io = vpw.tick()
    assert io["dn_data"] == _model_relu(5, 0), "Module should be 2 clocks cycles deep."

    io = vpw.tick()
    assert io["dn_data"] == 0, "Module is 3 clock cycles deep instead of 2."


def test_number_positive_bypass_false(context):
    """Test when up stream number is positive value with no bypass requested."""
    vpw.prep("bypass", [0])
    vpw.prep("up_data", vpw.pack(Param.NUM_WIDTH, 500))

    io = vpw.idle(10)  # wait for longer then the pipelined depth of module
    assert io["dn_data"] == _model_relu(500, 0), "Model positive number behavior is different from modules."


def test_number_positive_bypass_true(context):
    """Test when up stream number is positive with bypass being requested."""
    vpw.prep("bypass", [1])
    vpw.prep("up_data", vpw.pack(Param.NUM_WIDTH, 700))

    io = vpw.idle(10)  # wait for longer then the pipelined depth of module
    assert io["dn_data"] == _model_relu(700, 1), "Model positive number behavior is different from modules."


def test_number_negative_bypass_false(context):
    """Test when up stream number is negative value with no bypass requested."""
    vpw.prep("bypass", [0])
    vpw.prep("up_data", vpw.pack(Param.NUM_WIDTH, -500))

    io = vpw.idle(10)  # wait for longer then the pipelined depth of module
    assert io["dn_data"] == _model_relu(-500, 0), "Model negative number behavior is different from modules."


def test_number_negative_bypass_true(context):
    """Test when up stream number is negative with bypass being requested."""
    vpw.prep("bypass", [1])
    vpw.prep("up_data", vpw.pack(Param.NUM_WIDTH, -700))

    io = vpw.idle(10)  # wait for longer then the pipelined depth of module
    assert io["dn_data"] == _model_relu(-700, 1), "Model negative number behavior is different from modules."


def test_bypass_random_number(context):
    """Test many random numbers with a random bypass value."""
    checker = Checker()
    vpw.register(checker)

    for _ in range(5000):
        checker.send(random.getrandbits(Param.NUM_WIDTH), random.getrandbits(1))

    # wait until all data has been sent into DUT
    while not checker.empty():
        vpw.tick()

    vpw.idle(10)  # wait for longer then the pipelined depth of module
