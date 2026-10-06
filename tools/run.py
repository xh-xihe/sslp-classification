"""Run any preserved tool with the right import path.

    python tools/run.py verification/feas2.py
    python tools/run.py core/kl.py

The scripts import each other by bare module name (`from orbit import fiber`),
so `core/`, `orbits/` and `verification/` have to be on sys.path.  Doing that
here means the preserved scripts are byte-identical to the ones that produced
the results.

`verification/` matters because the acceptance gate runs its scripts through
this runner while they import each other directly -- `orbit_table_kernel.py`
does `from mkmanifest import ...`.  Running such a script directly works,
because Python puts its own directory on the path; running it through here did
not, so `verify.py --only table-kernel` failed with ModuleNotFoundError while
the same check passed standalone.
"""
import os
import runpy
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path[:0] = [os.path.join(HERE, 'core'), os.path.join(HERE, 'orbits'),
                os.path.join(HERE, 'verification')]

if len(sys.argv) < 2:
    print(__doc__)
    raise SystemExit(2)

target = os.path.join(HERE, sys.argv[1])
if not os.path.exists(target):
    target = sys.argv[1]
sys.argv = sys.argv[1:]
runpy.run_path(target, run_name='__main__')
