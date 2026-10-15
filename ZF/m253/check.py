#!/usr/bin/env python3
"""Rebuild and audit the exact ZF253 development with Coq 8.20.1.

Default: validate both table generators, compile the complete Audit253 closure
serially, check every Print Assumptions report, then recursively run matching
coqchk on every compiled logical module. --source-only performs no Coq calls.
The shared dependency resolver/load paths come from unchanged ../m254/check.py.
"""
from __future__ import annotations

import argparse
import contextlib
import hashlib
import importlib.util
import math
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile
import time

sys.dont_write_bytecode = True
if sys.flags.optimize:
    raise RuntimeError("Run with assertions enabled, not python -O")

HERE = Path(__file__).resolve().parent
M254 = HERE.parent / "m254"


def load_module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


BASE = load_module("m254_check", M254 / "check.py")
GEN = load_module("m253_candidate", HERE / "tools" / "generate_candidate.py")
ROOTS = dict(BASE.ROOTS)
ROOTS.update({"M254E": [M254 / "coq" / "e2e"],
              "M253": [HERE / "coq" / "tm"], "M253E": [HERE / "coq" / "e2e"]})
TOP = HERE / "coq" / "e2e" / "E2E253.v"
AUDIT = HERE / "coq" / "e2e" / "Audit253.v"
REQUIRED_ENDPOINTS = ("zf253_halts_iff_SIR", "zf253_halts_iff_ZF", "zf253_halts_iff_ZFC")
PROBES = re.compile(r"\bPrint\s+Assumptions\s+([\w.]+)\s*\.")
FORBIDDEN = re.compile(r"\b(?:Admitted|admit|Axiom|Parameter)\b|\bUnset\s+(?:Guard|Positivity|Universe)\s+Checking\b")
LOCKS = (Path("/tmp/mm0-native-mac.lock"), Path("/tmp/mm0_compile.lock"))


def clean_environment(environ=None):
    """Keep toolchain runtime variables, discard ambient Coq load-path overrides."""
    source = os.environ if environ is None else environ
    return {key: value for key, value in source.items()
            if not key.upper().startswith(("COQ", "ROCQ"))}


def audit_output(source, output):
    expected = len(PROBES.findall(BASE.strip_comments(source)))
    found = output.count("Closed under the global context")
    if re.search(r"(?m)^\s*Axioms\s*:", output):
        raise RuntimeError("Print Assumptions reported axioms")
    if found != expected:
        raise RuntimeError(f"Print Assumptions: {found}/{expected} closed reports")
    return found


def logical_name(path):
    candidates = []
    for prefix, directories in ROOTS.items():
        for directory in directories:
            try:
                relative = path.relative_to(directory)
            except ValueError:
                continue
            candidates.append((len(directory.parts), prefix + "." + ".".join(relative.with_suffix("").parts)))
    if not candidates:
        raise RuntimeError(f"no logical load path for {path}")
    return max(candidates)[1]


def source_checks():
    generated = GEN.generate_candidate()
    machine = HERE / "machine" / "zfc_253.tm"
    if machine.read_bytes() != generated:
        raise RuntimeError("zfc_253.tm differs from its exact four-row delta and explicit bijection")
    runtime_generator = HERE / "tools" / "gen_runtime253.py"
    table = HERE / "coq" / "tm" / "Table253.v"
    if not runtime_generator.is_file() or not table.is_file():
        raise RuntimeError("runtime table generator/Table253.v has not been integrated")
    result = subprocess.run([sys.executable, "-I", "-B", str(runtime_generator), "--check"],
                            cwd=HERE, env=clean_environment(), capture_output=True, text=True, timeout=30)
    if result.returncode:
        raise RuntimeError(f"generated Coq table/map check failed:\n{result.stdout}{result.stderr}")
    sites_generator = HERE / "tools" / "gen_sites253.py"
    sites_result = subprocess.run([sys.executable, "-I", "-B", str(sites_generator), "--check"],
                                  cwd=HERE, env=clean_environment(), capture_output=True, text=True, timeout=30)
    if sites_result.returncode:
        raise RuntimeError(f"generated instruction inventory check failed:\n{sites_result.stdout}{sites_result.stderr}")
    # Independent comparison of the actual compact literal rows, besides the
    # runtime author's complete byte check of maps and the old-label view.
    text = BASE.strip_comments(table.read_text(encoding="utf-8"))
    body = text.split("Definition table253", 1)[1].split("].", 1)[0]
    tuples = re.findall(r"\((true|false),\s*([LR]),\s*(\d+),\s*(true|false),\s*([LR]),\s*(\d+)\)", body)
    rows = GEN.candidate_rows()
    if len(tuples) != 253:
        raise RuntimeError(f"Table253.v contains {len(tuples)} compact rows, expected253")
    for q, (w0, d0, n0, w1, d1, n1) in enumerate(tuples):
        if (rows[q, 0], rows[q, 1]) != ((int(w0 == "true"), d0, int(n0)), (int(w1 == "true"), d1, int(n1))):
            raise RuntimeError(f"Table253.v compact row {q} differs from literal machine")
    if not TOP.is_file():
        raise RuntimeError("coq/e2e/E2E253.v has not been integrated")
    if not AUDIT.is_file():
        raise RuntimeError("mandatory coq/e2e/Audit253.v has not been integrated")
    files = BASE.closure(ROOTS, AUDIT)
    if TOP not in files:
        raise RuntimeError("Audit253.v must import E2E253.v")
    if AUDIT in BASE.closure(ROOTS, TOP):
        raise RuntimeError("E2E253.v must not import its final Audit253.v")
    own = sorted((HERE / "coq").rglob("*.v"))
    # Authored shared dependency sources are checked too; vendored theories
    # retain their original interfaces and are covered by the probe audit.
    authored = set(own) | {f for f in files if "vendor" not in f.parts}
    for file in sorted(authored):
        if FORBIDDEN.search(BASE.strip_comments(file.read_text(encoding="utf-8"))):
            raise RuntimeError(f"forbidden proof escape in {file.relative_to(HERE.parent)}")
    top_probes = {name.rsplit(".", 1)[-1] for name in PROBES.findall(BASE.strip_comments(TOP.read_text(encoding="utf-8")))}
    if not set(REQUIRED_ENDPOINTS) <= top_probes:
        raise RuntimeError("E2E253 must print assumptions for all SIR/ZF/ZFC endpoints")
    print(f"SOURCE PASS: exact {GEN.CANDIDATE_SHA256}; 253 states/506 rows; literal Coq table and maps agree", flush=True)
    return files


@contextlib.contextmanager
def build_locks():
    """Acquire existing lock inodes in their established order; never truncate."""
    if os.name != "posix":
        raise RuntimeError("this bounded serial build driver requires POSIX flock")
    import fcntl
    held = []
    try:
        for path in LOCKS:
            handle = path.open("a+b")
            try:
                fcntl.flock(handle, fcntl.LOCK_EX | fcntl.LOCK_NB)
            except BlockingIOError:
                handle.close()
                raise RuntimeError(f"native build lock is held: {path}; retry after its owner finishes")
            held.append(handle)
        yield
    finally:
        for handle in reversed(held):
            fcntl.flock(handle, fcntl.LOCK_UN)
            handle.close()


def run_bounded(command, *, seconds, memory_mib, label, environment):
    """Bound one direct Coq process by wall time, CPU, and monitored RSS."""
    import resource
    def limits():
        resource.setrlimit(resource.RLIMIT_CPU, (math.ceil(seconds), math.ceil(seconds) + 1))
        if sys.platform.startswith("linux"):
            maximum = memory_mib * 1024 * 1024
            resource.setrlimit(resource.RLIMIT_AS, (maximum, maximum))
    started = time.monotonic()
    peak, next_rss, next_progress, rss_failures = 0, 0.0, 25.0, 0
    failure = None
    with tempfile.TemporaryFile() as output:
        process = subprocess.Popen(command, cwd=HERE, env=environment, stdout=output,
                                   stderr=subprocess.STDOUT, preexec_fn=limits)
        try:
            while process.poll() is None:
                elapsed = time.monotonic() - started
                if elapsed > seconds:
                    failure = f"wall-time bound exceeded ({seconds}s)"
                    break
                if elapsed >= next_rss:
                    next_rss = elapsed + 0.5
                    try:
                        sample = subprocess.run(["ps", "-o", "rss=", "-p", str(process.pid)],
                                                capture_output=True, text=True, timeout=2)
                        if sample.returncode == 0 and sample.stdout.strip():
                            peak = max(peak, int(sample.stdout.strip()))
                            rss_failures = 0
                        elif process.poll() is None:
                            rss_failures += 1
                    except (OSError, ValueError, subprocess.TimeoutExpired):
                        rss_failures += 1
                    if peak > memory_mib * 1024:
                        failure = f"RSS bound exceeded ({memory_mib}MiB)"
                        break
                    if rss_failures >= 3:
                        failure = "cannot monitor child RSS"
                        break
                if elapsed >= next_progress:
                    print(f"running {label}: {elapsed:.0f}s, peak RSS {peak}KiB", flush=True)
                    next_progress += 25
                time.sleep(0.1)
            if failure:
                process.kill()
            code = process.wait()
        except BaseException:
            if process.poll() is None:
                process.kill()
            process.wait()
            raise
        output.seek(0)
        text = output.read().decode("utf-8", errors="replace")
    if failure or code:
        raise RuntimeError(f"{label}: {failure or f'exit {code}'}\n{text}")
    return text, time.monotonic() - started, peak


def toolchain(coqc, coqchk, environment):
    def locate(value):
        found = shutil.which(value)
        if found is None:
            raise RuntimeError(f"installed tool unavailable: {value}")
        return Path(found).resolve()
    compiler = locate(coqc)
    checker = locate(coqchk) if coqchk else compiler.with_name("coqchk")
    if not checker.is_file():
        raise RuntimeError(f"matching coqchk unavailable: {checker}")
    versions = []
    for tool in (compiler, checker):
        query = subprocess.run([str(tool), "--version"], env=environment, capture_output=True, text=True, timeout=10)
        # Coq 8.20 coqchk accepts -v rather than --version on some builds.
        if query.returncode and tool == checker:
            query = subprocess.run([str(tool), "-v"], env=environment, capture_output=True, text=True, timeout=10)
        version = query.stdout + query.stderr
        if query.returncode or not re.search(r"\b8\.20\.1\b", version):
            raise RuntimeError(f"Coq 8.20.1 required: {tool}\n{version}")
        versions.append(version.strip().splitlines()[0])
    # Resolving both tools to the same installed bin directory prevents
    # accidentally auditing new objects with another Coq distribution.
    if compiler.parent != checker.parent:
        raise RuntimeError("coqc and coqchk must come from the same resolved installation")
    print("; ".join(versions), flush=True)
    return compiler, checker


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--coqc", default=os.environ.get("COQC", "coqc"))
    parser.add_argument("--coqchk")
    parser.add_argument("--wall-seconds", type=int, default=240, help="per-source wall/CPU bound")
    parser.add_argument("--coqchk-seconds", type=int, default=900, help="separate recursive audit wall/CPU bound")
    parser.add_argument("--memory-mib", type=int, default=2048)
    parser.add_argument("--source-only", action="store_true", help="validate source/generators; no Coq calls and no kernel acceptance claim")
    parser.add_argument("--plan", action="store_true", help="print dependency modules after source checks; no Coq calls")
    args = parser.parse_args(argv)
    if min(args.wall_seconds, args.coqchk_seconds, args.memory_mib) <= 0:
        parser.error("resource bounds must be positive")
    files = source_checks()
    probes = sum(len(PROBES.findall(BASE.strip_comments(f.read_text(encoding="utf-8")))) for f in files)
    print(f"dependency closure: {len(files)} source files; {probes} Print Assumptions probes", flush=True)
    if args.plan:
        print("\n".join(logical_name(f) for f in files))
    if args.source_only or args.plan:
        print("SOURCE ONLY: no Coq compilation or recursive kernel audit performed")
        return 0
    environment = clean_environment()
    compiler, checker = toolchain(args.coqc, args.coqchk, environment)
    flags = [item for prefix, directories in ROOTS.items() for directory in directories
             for item in ("-Q", str(directory), prefix)]
    initial_hashes = {f: hashlib.sha256(f.read_bytes()).hexdigest() for f in files}
    closed, peak = 0, 0
    started = time.monotonic()
    with build_locks():
        for file in files:
            command = [str(compiler), "-q", *flags, *BASE.WARN,
                       *(BASE.LIBFLAGS if BASE.UNDEC in file.parents else []), str(file)]
            output, duration, rss = run_bounded(command, seconds=args.wall_seconds,
                                              memory_mib=args.memory_mib, label=logical_name(file), environment=environment)
            reports = audit_output(file.read_text(encoding="utf-8"), output)
            closed += reports
            peak = max(peak, rss)
            print(f"{duration:6.1f}s {logical_name(file)}; closed probes {reports}", flush=True)
            if file == TOP:
                print(output, end="" if output.endswith("\n") else "\n", flush=True)
        modules = [logical_name(file) for file in files]
        command = [str(checker), "-o", "-bytecode-compiler", "yes", *flags, *modules]
        _, duration, rss = run_bounded(command, seconds=args.coqchk_seconds,
                                      memory_mib=args.memory_mib, label="recursive coqchk", environment=environment)
        peak = max(peak, rss)
        if any(hashlib.sha256(file.read_bytes()).hexdigest() != digest for file, digest in initial_hashes.items()):
            raise RuntimeError("source files changed during verification")
    if closed != probes:
        raise RuntimeError(f"aggregate closed report count differs: {closed}/{probes}")
    print(f"recursive coqchk PASS: {len(modules)} module roots and all recursive dependencies; {duration:.1f}s", flush=True)
    print(f"CHECK PASS: {closed} closed reports; total {time.monotonic()-started:.1f}s; peak sampled RSS {peak}KiB", flush=True)
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (AssertionError, OSError, RuntimeError, subprocess.TimeoutExpired) as error:
        print(f"CHECK FAIL: {error}", file=sys.stderr)
        raise SystemExit(1)
