"""Run any preserved tool with the right import path.

    python tools/run.py verification/feas2.py
    python tools/run.py core/kl.py

The scripts import each other by bare module name (`from orbit import fiber`),
so `core/` and `orbits/` have to be on sys.path.  Doing that here means the
preserved scripts are byte-identical to the ones that produced the results.
"""
import os
import runpy
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path[:0] = [os.path.join(HERE, 'core'), os.path.join(HERE, 'orbits')]

if len(sys.argv) < 2:
    print(__doc__)
    raise SystemExit(2)

target = os.path.join(HERE, sys.argv[1])
if not os.path.exists(target):
    target = sys.argv[1]
sys.argv = sys.argv[1:]
runpy.run_path(target, run_name='__main__')
