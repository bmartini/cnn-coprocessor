"""
Testbench for pool module.
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
    NUM_WIDTH: Bus width of (up|dn)_data number
    """
    NUM_WIDTH = 16


def _twos(width: int, data: int) -> int:
    """Convert signed numbers into two's complement.

    If a number sent in as a negatively signed int it will be converted to a
    two's complement negative number with a defined bit width. Otherwise the
    number is masked so no extra bits are expressed in the returned number.

    Arguments
    width: Number of bits used to express the data value
    data: The number to be converted to two's complement
    """
    mask = (1 << width) - 1

    if data < 0:
        data = data + 2**width

    return data & mask


def _real(width: int, data: int) -> int:
    """Convert a int (two's complement or not) into signed number

    If a number sent in as a negatively signed int it will be converted to a
    two's complement negative number with a defined bit width.

    Arguments
    width: Number of bits used to express the data value
    data: The number to be converted to two's complement
    """
    mask = (1 << width) - 1
    negative = 1 << (width - 1)

    # converts to twos complement of defined width
    data = _twos(width, data)

    # convert negative data into real negative number
    if (data & negative) != 0:
        data = int((mask - data + 1) * -1)

    return data


def _new_maximum(number: int, current: int) -> bool:
    """Test if new mumber is greater than the current maximum."""
    return _real(Param.NUM_WIDTH, number) > _real(Param.NUM_WIDTH, current)


class Checker:
    def __init__(self) -> None:
        self._restart: bool = False
        self._valid: bool = False
        self._data: int = 0

    def restart(self) -> None:
        """Prep 'restart' in module and model."""
        vpw.prep("restart", [1])
        self._restart = True

    def set(self, data: int) -> None:
        """Prep 'up_data' in module and model."""
        vpw.prep("up_valid", [1])
        vpw.prep("up_data", vpw.pack(Param.NUM_WIDTH, data))
        self._valid = True
        self._data = data

    def init(self, _) -> Generator:
        current_5p = 0
        current_4p = 0
        current_3p = 0
        current_2p = 0
        current_1p = 0
        current = 0
        self._valid = False
        self._data = 0

        while True:
            io = yield
            current_5p = current_4p
            current_4p = current_3p
            current_3p = current_2p
            current_2p = current_1p
            current_1p = current
            if self._valid and _new_maximum(self._data, current):
                current = self._data

            if self._valid and self._restart:
                current = self._data
                self._restart = False

            vpw.prep("restart", [0])
            vpw.prep("up_valid", [0])
            vpw.prep("up_data", vpw.pack(Param.NUM_WIDTH, 0))
            self._valid = False
            self._data = 0

            assert io["dn_data"] == current_4p


@pytest.fixture(scope="module")
def design():
    workspace = tempfile.mkdtemp()

    dut = vpw.create(module='pool',
                     clock='clk',
                     include=['../hdl'],
                     parameter={'NUM_WIDTH': Param.NUM_WIDTH},
                     workspace=workspace)
    yield dut

    shutil.rmtree(workspace)


@pytest.fixture
def context(design):
    vpw.init(design, trace=False)

    vpw.prep("restart", [0])
    vpw.prep("up_valid", [0])
    vpw.prep("up_data", vpw.pack(Param.NUM_WIDTH, 0))
    vpw.idle(2)

    yield

    vpw.idle(10)
    vpw.finish()


def test_pipeline_depth(context):
    """Test that module pipeline depth is 4 clock cycles deep."""
    vpw.prep("restart", [1])
    vpw.prep("up_valid", [1])
    vpw.prep("up_data", vpw.pack(Param.NUM_WIDTH, 5))
    vpw.tick()
    vpw.prep("restart", [0])
    vpw.prep("up_valid", [0])
    vpw.prep("up_data", vpw.pack(Param.NUM_WIDTH, 0))

    io = vpw.tick()
    assert io["dn_data"] == 0, "Module is 3 clock cycles deep instead of 4."

    io = vpw.idle(4)
    assert io["dn_data"] == 5, "Module should be 4 clocks cycles deep."

    io = vpw.tick()
    assert io["dn_data"] == 5, "Module needs to hold maximum number."


def test_pipeline_interrupted(context):
    """Test when up stream number is positive value with restart requested."""
    vpw.prep("restart", [1])
    vpw.prep("up_valid", [1])
    vpw.prep("up_data", vpw.pack(Param.NUM_WIDTH, 500))
    vpw.tick()
    vpw.prep("restart", [0])
    vpw.prep("up_valid", [0])
    vpw.prep("up_data", vpw.pack(Param.NUM_WIDTH, 0))

    io = vpw.idle(10)  # wait for longer then the pipelined depth of module
    assert io["dn_data"] == _twos(Param.NUM_WIDTH, 500), "Model positive number behavior is different from modules."

    vpw.prep("restart", [1])  # restart pool with next valid data
    io = vpw.tick()
    assert io["dn_data"] == _twos(Param.NUM_WIDTH, 500), "Model positive number behavior is different from modules."

    vpw.prep("restart", [0])
    io = vpw.tick()
    assert io["dn_data"] == _twos(Param.NUM_WIDTH, 500), "Model positive number behavior is different from modules."

    io = vpw.tick()
    assert io["dn_data"] == _twos(Param.NUM_WIDTH, 500), "Model positive number behavior is different from modules."

    vpw.prep("up_valid", [1])  # new data valid with lower value then current maximum
    vpw.prep("up_data", vpw.pack(Param.NUM_WIDTH, 100))
    io = vpw.tick()
    assert io["dn_data"] == _twos(Param.NUM_WIDTH, 500), "Model positive number behavior is different from modules."

    vpw.prep("up_valid", [0])
    vpw.prep("up_data", vpw.pack(Param.NUM_WIDTH, 0))
    io = vpw.tick()
    assert io["dn_data"] == _twos(Param.NUM_WIDTH, 500), "Model positive number behavior is different from modules."

    io = vpw.tick()
    assert io["dn_data"] == _twos(Param.NUM_WIDTH, 500), "Model positive number behavior is different from modules."

    io = vpw.tick()
    assert io["dn_data"] == _twos(Param.NUM_WIDTH, 500), "Model positive number behavior is different from modules."

    io = vpw.tick()
    assert io["dn_data"] == _twos(Param.NUM_WIDTH, 100), "Model positive number behavior is different from modules."


def test_number_positive_with_restart(context):
    """Test when up stream number is positive value with restart requested."""
    vpw.prep("restart", [1])
    vpw.prep("up_valid", [1])
    vpw.prep("up_data", vpw.pack(Param.NUM_WIDTH, 500))
    vpw.tick()
    vpw.prep("restart", [0])
    vpw.prep("up_valid", [0])
    vpw.prep("up_data", vpw.pack(Param.NUM_WIDTH, 0))

    io = vpw.idle(10)  # wait for longer then the pipelined depth of module
    assert io["dn_data"] == _twos(Param.NUM_WIDTH, 500), "Model positive number behavior is different from modules."


def test_number_positive_without_restart(context):
    """Test when up stream number is positive value without restart requested."""
    vpw.prep("restart", [0])
    vpw.prep("up_valid", [1])
    vpw.prep("up_data", vpw.pack(Param.NUM_WIDTH, 500))
    vpw.tick()
    vpw.prep("restart", [0])
    vpw.prep("up_valid", [0])
    vpw.prep("up_data", vpw.pack(Param.NUM_WIDTH, 0))

    io = vpw.idle(10)  # wait for longer then the pipelined depth of module
    assert io["dn_data"] == _twos(Param.NUM_WIDTH, 500), "Model positive number behavior is different from modules."


def test_number_negative_with_restart(context):
    """Test when up stream number is negative value with restart."""
    vpw.prep("restart", [1])
    vpw.prep("up_valid", [1])
    vpw.prep("up_data", vpw.pack(Param.NUM_WIDTH, _twos(Param.NUM_WIDTH, -500)))
    vpw.tick()
    vpw.prep("restart", [0])
    vpw.prep("up_valid", [0])
    vpw.prep("up_data", vpw.pack(Param.NUM_WIDTH, 0))

    io = vpw.idle(10)  # wait for longer then the pipelined depth of module
    assert io["dn_data"] == _twos(Param.NUM_WIDTH, -500), "Model negative number behavior is different from modules."


def test_number_negative_without_restart(context):
    """Test when up stream number is negative value without restart."""
    vpw.prep("restart", [0])
    vpw.prep("up_valid", [1])
    vpw.prep("up_data", vpw.pack(Param.NUM_WIDTH, _twos(Param.NUM_WIDTH, -500)))
    vpw.tick()
    vpw.prep("restart", [0])
    vpw.prep("up_valid", [0])
    vpw.prep("up_data", vpw.pack(Param.NUM_WIDTH, 0))

    io = vpw.idle(10)  # wait for longer then the pipelined depth of module
    assert io["dn_data"] == _twos(Param.NUM_WIDTH, 0), "Model negative number behavior is different from modules."


def test_random_number(context):
    """Test many random numbers with a restart sometimes."""
    checker = Checker()
    vpw.register(checker)
    vpw.tick()

    for _ in range(50):
        checker.restart()

        for _ in range(1000):
            checker.set(random.getrandbits(Param.NUM_WIDTH))
            vpw.tick()

    vpw.idle(10)  # wait for longer then the pipelined depth of module
