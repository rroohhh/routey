#!/usr/bin/env python3

import os
import shutil
import subprocess
import textwrap
from pathlib import Path
import inspect

from amaranth.back import rtlil
from amaranth._toolchain import require_tool

def assertFormal(spec, ports=None, mode="bmc", depth=1):
    # stack = traceback.extract_stack()
    # for frame in reversed(stack):
    #     if (os.path.dirname(__file__) not in frame.filename) or (frame.name == "<module>"):
    #         break
    #     caller = frame

    functions = []
    test_class = None
    caller_path = ""
    stack = inspect.stack()
    for frame in stack[1:]:
        if "unittest" in frame.filename or "<module>" in frame.function:
            filename = "__".join(reversed(functions))
            if "<module>" in frame.function:
                filename = Path(frame.filename).stem + "__" + filename
            if test_class:
                filename = f'{test_class}__{filename}'
            break
        functions.append(frame.function)
        try:
            test_class = frame.frame.f_locals['self'].__class__.__name__
        except:
            pass
        caller_path = frame.filename

    target_dir = Path(caller_path).parent / ".sim_results"
    target_dir.mkdir(exist_ok=True)
    if (target_dir / filename).exists():
        shutil.rmtree(target_dir / filename)
    print(target_dir, filename)
    engine = "smtbmc"
    if mode == "hybrid":
        # A mix of BMC and k-induction, as per personal communication with Claire Wolf.
        script = "setattr -unset init w:* a:amaranth.sample_reg %d"
        mode   = "bmc"
    elif mode == "prove":
        engine = "abc pdr"
        # engine = "aiger imctk-eqy-engine --rarity-sim-rounds=20 --window-max=20"
        script = ""
    elif mode == "bmc":
        engine = "smtbmc yices"
        script = ""
    else:
        script = ""


    # wait on
    # multiclock on
    config = textwrap.dedent("""\
    [options]
    mode {mode}
    depth {depth}

    [engines]
    {engine}

    [script]
    read_ilang top.il
    prep
    {script}

    [file top.il]
    {rtlil}
    """).format(
        engine=engine,
        mode=mode,
        depth=depth,
        script=script,
        rtlil=rtlil.convert(spec, ports=ports, platform="formal"),
    )
    with subprocess.Popen(
            [require_tool("sby"), "-f", "-d", filename],
            cwd=str(target_dir), env={**os.environ, "PYTHONWARNINGS":"ignore"},
            universal_newlines=True, stdin=subprocess.PIPE, stdout=subprocess.PIPE) as proc:
        stdout, stderr = proc.communicate(config)
        if proc.returncode != 0:
            assert False, "Formal verification failed:\n" + stdout
