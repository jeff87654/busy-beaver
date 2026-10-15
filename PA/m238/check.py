#!/usr/bin/env python3
"""Check the PA238 sources; --source-only never claims kernel acceptance.

This original driver compiles only the dependency closure of currently
authored PA modules, under a trusted local Coq 8.20.1 installation. It does
not download packages or invoke upstream scripts. Endpoint proofs live in
the authored Coq modules.
"""
import argparse
import fcntl
import hashlib
import json
import os
from pathlib import Path
import re
import resource
import shutil
import subprocess
import sys
import tempfile
import time

HERE = Path(__file__).resolve().parent
REPO = HERE.parent.parent
TABLE_SHA = 'ffe370842d70bae96688ad5e290073edffe0bb213cf12fe562a75a74bec966de'
ROOTS = {
    'P238': HERE / 'coq',
    'Undecidability': HERE / 'vendor/undecidability/theories',
    'BusyCoq': REPO / 'ZF/stdzf_r3/vendor/busycoq',
}
REQ = re.compile(r'(?:From\s+([\w.]+)\s+)?Require\s+(?:Import\s+|Export\s+)?([\w.\s]+?)\.(?=\s|$)')
STDLIB_BARE = {'List', 'Lia', 'Arith', 'Bool', 'Setoid', 'Morphisms',
               'Vector', 'Cantor', 'FinFun', 'Relation_Definitions',
               'EqdepFacts', 'Eqdep_dec', 'Nat', 'PeanoNat', 'NArith',
               'PArith', 'ZArith', 'BinInt', 'BinNat', 'BinPos'}
ALIASES = {'Undecidability.Shared.Libs.PSL.Tactics':
           'Undecidability.Shared.Libs.PSL.Tactics.Tactics'}


def uncomment(text):
    result = []
    depth = i = 0
    quoted = False
    while i < len(text):
        if depth == 0 and text[i] == '"':
            if quoted and text.startswith('""', i):
                result.extend('  ')
                i += 2
                continue
            quoted = not quoted
            result.append(' ')
            i += 1
        elif quoted:
            result.append('\n' if text[i] == '\n' else ' ')
            i += 1
        elif text.startswith('(*', i):
            if depth == 0:
                result.append(' ')
            depth += 1
            i += 2
        elif depth and text.startswith('*)', i):
            depth -= 1
            i += 2
        else:
            if depth == 0:
                result.append(text[i])
            i += 1
    if depth:
        raise ValueError('unclosed comment')
    if quoted:
        raise ValueError('unclosed string')
    return ''.join(result)


def dependencies(path):
    text = uncomment(path.read_text(encoding='utf-8'))
    for prefix, names in REQ.findall(text):
        for name in names.split():
            full = (prefix + '.' if prefix else '') + name
            full = ALIASES.get(full, full)
            parts = full.split('.')
            if parts[0] in ('Coq', 'Stdlib') or full in STDLIB_BARE:
                continue
            if parts[0] not in ROOTS:
                raise ValueError(f'{path}: unknown logical import {full}')
            target = ROOTS[parts[0]].joinpath(*parts[1:]).with_suffix('.v')
            if not target.is_file():
                raise ValueError(f'{path}: missing imported source {full}')
            yield target


def closure(tops):
    result, seen, active = [], set(), set()
    def visit(path):
        if path in seen:
            return
        if path in active:
            raise ValueError(f'import cycle at {path}')
        active.add(path)
        for dependency in dependencies(path):
            visit(dependency)
        active.remove(path)
        seen.add(path)
        result.append(path)
    for top in tops:
        visit(top)
    return result


def vendor_pins():
    vendor = HERE / 'vendor/undecidability'
    manifest_path = vendor / 'MANIFEST.json'
    if not manifest_path.is_file():
        raise ValueError('missing pinned arithmetic library manifest')
    manifest = json.loads(manifest_path.read_text())
    if manifest['commit'] != '70dfc56f33a6e4835281044e68aa68279989047e':
        raise ValueError('incorrect arithmetic library pin')
    if manifest['license'] != 'MPL-2.0':
        raise ValueError('incorrect arithmetic library license notice')
    listed = set()
    for entry in manifest['files']:
        relative = Path(entry['path'])
        if relative.is_absolute() or '..' in relative.parts or relative in listed:
            raise ValueError('unsafe or duplicate vendor manifest path')
        listed.add(relative)
        data = (vendor / relative).read_bytes()
        blob = b'blob ' + str(len(data)).encode() + b'\0' + data
        if hashlib.sha256(data).hexdigest() != entry['sha256']:
            raise ValueError(f'vendor SHA256 mismatch: {relative}')
        if hashlib.sha1(blob).hexdigest() != entry['git_blob_sha1']:
            raise ValueError(f'vendor Git blob mismatch: {relative}')
    actual = {path.relative_to(vendor) for path in vendor.rglob('*.v')}
    actual.add(Path('LICENSE'))
    if listed != actual:
        raise ValueError('vendor source inventory differs from pinned manifest')


def child_limits(cpu_seconds):
    def limit():
        resource.setrlimit(resource.RLIMIT_CPU, (cpu_seconds, cpu_seconds))
    return limit


def run_compiler(command, wall_seconds, memory_bytes):
    """Bound the direct child; Darwin cannot enforce RLIMIT_AS here.

    ps observes only this compiler's PID. If that observation is unavailable,
    stop the compiler and fail, rather than silently running without the
    requested memory supervision. No process-group signal is used.
    """
    with tempfile.TemporaryFile(mode='w+', encoding='utf-8') as output:
        child = subprocess.Popen(command, cwd=REPO, stdout=output,
                                 stderr=subprocess.STDOUT,
                                 preexec_fn=child_limits(wall_seconds))
        start = time.monotonic()
        peak_kib = 0
        try:
            while child.poll() is None:
                if time.monotonic() - start > wall_seconds:
                    raise ValueError('compiler exceeded wall-time bound')
                observation = subprocess.run(
                    ['/bin/ps', '-o', 'rss=', '-p', str(child.pid)],
                    capture_output=True, text=True, timeout=3)
                rss = observation.stdout.strip()
                if child.poll() is not None:
                    break
                if observation.returncode != 0 or not rss.isdigit():
                    raise ValueError('compiler memory observation unavailable')
                peak_kib = max(peak_kib, int(rss))
                if int(rss) * 1024 > memory_bytes:
                    raise ValueError('compiler exceeded resident-memory bound')
                try:
                    child.wait(timeout=0.25)
                except subprocess.TimeoutExpired:
                    pass
        except BaseException:
            if child.poll() is None:
                child.kill()
                child.wait(timeout=5)
            output.seek(0)
            partial_output = output.read()
            print(f'Stopped compiler exit {child.returncode}; observed peak RSS {peak_kib} KiB.', flush=True)
            if partial_output:
                print(partial_output, end='' if partial_output.endswith('\n') else '\n', flush=True)
            raise
        output.seek(0)
        text = output.read()
        print(f'Compiler exit {child.returncode}; observed peak RSS {peak_kib} KiB.', flush=True)
        if text:
            print(text, end='' if text.endswith('\n') else '\n', flush=True)
        if child.returncode != 0:
            raise subprocess.CalledProcessError(child.returncode, command, output=text)
        return text


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source-only', action='store_true')
    parser.add_argument('--coqc', default=os.environ.get('COQC', 'coqc'))
    parser.add_argument('--wall-seconds', type=int, default=300)
    parser.add_argument('--memory-mib', type=int, default=2048)
    parser.add_argument('--check-file', type=Path, action='append', default=[],
                        help='repair iteration: rebuild selected PA files and missing/outdated dependencies; partial check only')
    parser.add_argument('--coq-time', action='store_true',
                        help='diagnose failed/slow proof commands with Coq timing output')
    args = parser.parse_args()
    if args.wall_seconds <= 0 or args.memory_mib <= 0:
        raise ValueError('resource limits must be positive')
    table = HERE / 'machine/pa_238.tm'
    if hashlib.sha256(table.read_bytes()).hexdigest() != TABLE_SHA:
        raise ValueError('selected table hash mismatch')
    vendor_pins()
    tops = sorted((HERE / 'coq').rglob('*.v'))
    if not tops:
        raise ValueError('no authored Coq modules')
    for source in tops:
        body = uncomment(source.read_text(encoding='utf-8'))
        if re.search(r'\b(?:Admitted|admit|Axiom|Parameter)\b', body):
            raise ValueError(f'{source}: unresolved proof or added assumption')
    order = closure(tops)
    print(f'Exact PA238 hash matched; {len(tops)} PA modules, {len(order)} dependency sources.', flush=True)
    if args.source_only:
        print('SOURCE CHECK PASS; kernel compilation NOT RUN.')
        return
    if args.check_file:
        selected = set()
        for path in args.check_file:
            target = path.resolve()
            if target not in set(tops):
                raise ValueError('repair target must be an authored PA source in this checkout')
            selected.add(target)
        # Rebuild importers whenever a dependency was selected for repair or
        # its compiled object is newer. Source-only freshness misses Coq's
        # recorded dependency digests after a prerequisite is recompiled.
        order, rebuilding = [], set()
        for source in closure(sorted(selected)):
            product = source.with_suffix('.vo')
            imported = list(dependencies(source))
            stale = (source in selected or not product.is_file()
                     or product.stat().st_mtime_ns < source.stat().st_mtime_ns)
            if not stale:
                stale = any(dependency in rebuilding
                            or not dependency.with_suffix('.vo').is_file()
                            or dependency.with_suffix('.vo').stat().st_mtime_ns
                               > product.stat().st_mtime_ns
                            for dependency in imported)
            if stale:
                rebuilding.add(source)
                order.append(source)
    executable = shutil.which(args.coqc)
    if executable is None:
        raise ValueError('trusted Coq 8.20.1 + matching Stdlib not installed; compilation pending')
    version = subprocess.run([executable, '--version'], check=True, capture_output=True, text=True, timeout=15)
    if not re.search(r'\b8\.20\.1\b', version.stdout):
        raise ValueError('this pinned development requires Coq 8.20.1')
    flags = []
    for logical, root in ROOTS.items():
        flags.extend(['-Q', str(root), logical])
    locks = []
    try:
        # Existing inode only: no creation, replacement, truncation or deletion.
        for lock_path in ('/tmp/mm0-native-mac.lock', '/tmp/mm0_compile.lock'):
            lock = open(lock_path, 'r+b')
            locks.append(lock)
            fcntl.flock(lock.fileno(), fcntl.LOCK_EX | fcntl.LOCK_NB)
        for source in order:
            command = [executable, *flags, '-set', 'Default Proof Using = Type']
            if args.coq_time:
                command.append('-time')
            command.append(str(source))
            print('Compiling ' + str(source.relative_to(REPO)), flush=True)
            output = run_compiler(command, args.wall_seconds,
                                  args.memory_mib * 1024 * 1024)
            probes = len(re.findall(r'\bPrint\s+Assumptions\b',
                                    uncomment(source.read_text(encoding='utf-8'))))
            if probes and (output.count('Closed under the global context') != probes
                           or 'Axioms:' in output):
                raise ValueError(f'{source}: closed-assumption probe failed')
    finally:
        for lock in reversed(locks):
            lock.close()
    if args.check_file:
        print('SELECTED DEPENDENCY CLOSURE COMPILED; closed-assumption probes passed.')
    else:
        print('AUTHORED MODULES COMPILED; closed-assumption probes passed.')


if __name__ == '__main__':
    try:
        main()
    except (OSError, ValueError, subprocess.SubprocessError) as error:
        print('CHECK BLOCKED: ' + str(error), file=sys.stderr)
        sys.exit(1)
