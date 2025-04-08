import os
import shutil
import subprocess
import tempfile
import textwrap
from pathlib import Path
import inspect

from amaranth.back import rtlil
from amaranth._toolchain import require_tool

class FormalVerificationFailed(Exception):
    pass

def assertFormal(spec, ports=None, mode="bmc", depth=20, tmp = False):
    # stack = traceback.extract_stack()
    # for frame in reversed(stack):
    #     if (os.path.dirname(__file__) not in frame.filename) or (frame.name == "<module>"):
    #         break
    #     caller = frame

    if not tmp:
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

    with tempfile.TemporaryDirectory() as tmpdir:
        if tmp:
            target_dir = tmpdir
            filename = "tmp"

        # print(target_dir, filename)
        engine = "smtbmc"
        if mode == "prove":
            #engine = "abc pdr\naiger rIC3"
            # engine = "aiger rIC3"
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
        vcd off
        mode {mode}
        depth {depth}

        [engines]
        {engine}

        [script]
        read_rtlil top.il
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
                if "Status: FAILED" in stdout or "Status returned by engine: FAIL" in stdout:
                    raise FormalVerificationFailed(stdout)
                else:
                    assert False, "Formal verification failed:\n" + stdout

from amaranth import Assert, Module, Assume, Signal, ClockDomain, Cover, Mux, Print
from amaranth.lib.wiring import Component, In

class AssertEventually(Component):
    request: In(1)
    release: In(1)
    tick: In(1)

    def __init__(self, bound):
        super().__init__()
        self.bound = bound

    def elaborate(self, _):
        m = Module()

        timeout_counter = Signal(range(self.bound + 1))

        with m.If(self.tick):
            with m.FSM() as fsm:
                with m.State("IDLE"):
                    with m.If(self.request & ~self.release):
                        m.next = "WAITING"
                        m.d.sync += timeout_counter.eq(1)
                with m.State("WAITING"):
                    with m.If(~self.release):
                        with m.If(timeout_counter < self.bound):
                            m.d.sync += timeout_counter.eq(timeout_counter + 1)
                        with m.Else():
                            m.next = "TIMEOUT"
                    with m.Else():
                        m.next = "IDLE"
                with m.State("TIMEOUT"):
                    ...

        m.d.comb += Cover(fsm.ongoing("WAITING"))
        m.d.comb += Assert(~fsm.ongoing("TIMEOUT"))

        return m
