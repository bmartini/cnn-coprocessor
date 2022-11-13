# Testbench Validation of CNN SystemVerilog

Testbenchs are being written for the SystemVerilog modules by leveraging the
[VPW](https://github.com/bmartini/vpw-testbench) and pytest frameworks.

## Running Testbench

To run a single test, use the following command.

```bash
pytest -v relu.py
```

To run a single test within a testbench.

```bash
pytest -v relu.py -k test_pipeline_depth
```

And to run a every test within the current directory.

```bash
pytest -v *.py
```

If you want to generate a waveform to view for debug purposes you must edit the
following line within a testbench.

From:

```python
    vpw.init(design, trace=False)
```

To:

```python
    vpw.init(design, trace=True)
```

And then when you run a single test within that testbench, a waveform will be
created in the current directory.
