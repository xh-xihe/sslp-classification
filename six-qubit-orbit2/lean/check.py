#!/usr/bin/env python3
"""Check with this package's Lake environment or a preinstalled Mathlib project.
The latter is read-only; build artifacts are written beneath this package.
"""
import argparse
import os
import re
from pathlib import Path
import subprocess
import time
from concurrent.futures import ThreadPoolExecutor

ROOT = Path(__file__).resolve().parent
p = argparse.ArgumentParser()
p.add_argument('--mathlib-project', type=Path, default=ROOT)
p.add_argument('--jobs', type=int, default=2)
p.add_argument('--coefficients-only', action='store_true')
p.add_argument('--module', help='Check just one module, e.g. Orbit2.Certificate')
p.add_argument('--target', default='Orbit2', help='Rebuild a module and every local dependency')
p.add_argument('--incremental', action='store_true', help='Reuse oleans newer than source and all local dependencies')
p.add_argument('--stack-kb', type=int, default=65536, help='Lean thread stack size for finite kernel checks')
args = p.parse_args()
if args.incremental and args.module:
    p.error('--incremental requires a dependency rebuild, not --module')
env = os.environ.copy()
paths = subprocess.check_output(['lake', 'env', 'printenv', 'LEAN_PATH'],
    cwd=args.mathlib_project, text=True).strip()
# Lake can emit relative search paths: resolve them against its project directory.
paths = ':'.join(str((args.mathlib_project / x).resolve()) if not x.startswith('/') else x
                 for x in paths.split(':'))
build = ROOT / '.lake' / 'build' / 'lib' / 'lean'
build.mkdir(parents=True, exist_ok=True)
env['LEAN_PATH'] = str(build) + ':' + paths
start = time.monotonic()
dependencies = {}
def check(module):
    rel = Path(*module.split('.'))
    output = build / rel.with_suffix('.olean')
    output.parent.mkdir(parents=True, exist_ok=True)
    source = ROOT / rel.with_suffix('.lean')
    if args.incremental and output.is_file():
        inputs = [source] + [build / Path(*name.split('.')).with_suffix('.olean')
                             for name in dependencies[module]]
        if all(path.is_file() and path.stat().st_mtime_ns <= output.stat().st_mtime_ns
               for path in inputs):
            print(f'PASS {module} (cached kernel-checked olean)', flush=True)
            return
    result = subprocess.run(['lean', '-s', str(args.stack_kb), '-o', str(output), str(rel.with_suffix('.lean'))],
        cwd=ROOT, env=env, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    if result.stdout:
        print(result.stdout, end='', flush=True)
    result.check_returncode()
    if "declaration uses 'sorry'" in result.stdout:
        raise RuntimeError(f'Unproved declaration in {module}')
    allowed_axioms = {'propext', 'Classical.choice', 'Quot.sound'}
    for audit in re.findall(r'depends on axioms:\s*\[(.*?)\]', result.stdout, re.DOTALL):
        unexpected = {name.strip() for name in audit.split(',') if name.strip()} - allowed_axioms
        if unexpected:
            raise RuntimeError(f'Unexpected axiom dependencies in {module}: {sorted(unexpected)}')
    print(f'PASS {module}', flush=True)

if args.module:
    check(args.module)
    count = 1
else:
    # Discover local imports, so a successful full run cannot silently omit a
    # newly added obligation. External Mathlib modules use the installed cache.
    def discover(module):
        if module in dependencies:
            return
        source = ROOT / Path(*module.split('.')).with_suffix('.lean')
        if not source.is_file():
            return
        imports = re.findall(r'^import\s+(\S+)', source.read_text(), re.MULTILINE)
        local = {name for name in imports
                 if (ROOT / Path(*name.split('.')).with_suffix('.lean')).is_file()}
        dependencies[module] = local
        for name in sorted(local):
            discover(name)
    discover('Orbit2.Coefficients' if args.coefficients_only else args.target)
    pending = set(dependencies)
    completed = set()
    with ThreadPoolExecutor(max_workers=args.jobs) as pool:
        while pending:
            ready = sorted(name for name in pending if dependencies[name] <= completed)
            if not ready:
                raise RuntimeError(f'Local import cycle: {sorted(pending)}')
            list(pool.map(check, ready))
            completed.update(ready)
            pending.difference_update(ready)
    count = len(completed)
print(f'LEAN CHECKS PASSED ({count} modules, {time.monotonic()-start:.1f}s)', flush=True)
