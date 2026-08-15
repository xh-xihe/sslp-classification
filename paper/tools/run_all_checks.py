"""Run every numeric verification behind the manuscript; exit nonzero on failure.

    python tools/run_all_checks.py

Each script asserts the figures the paper prints and returns a nonzero exit code
if any of them no longer holds.
"""

import os
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))

SCRIPTS = [
    ('check_bell_table.py', 'Bell-pair Pauli table, all sixteen Paulis'),
    ('check_rung1.py', 'the rung-1 code of the explicit seed'),
    ('check_exact_distance.py', 'the weight-three witness at rungs 0-4'),
    ('check_witness_detail.py', 'the rung-0 detail in the exactness proof'),
    ('check_sweep.py', 'every number in the theorem-hypothesis sweep'),
    ('prose_audit.py', 'prose tics and repeated disclaimers'),
]

failed = []
for script, what in SCRIPTS:
    path = os.path.join(HERE, script)
    if not os.path.exists(path):
        print('MISSING  %s' % script)
        failed.append(script)
        continue
    print('=' * 74)
    print('%s  --  %s' % (script, what))
    print('=' * 74)
    rc = subprocess.call([sys.executable, path], cwd=os.path.dirname(HERE))
    if rc != 0:
        failed.append(script)
    print()

print('=' * 74)
if failed:
    print('FAILED: %s' % ', '.join(failed))
    sys.exit(1)
print('all %d verification scripts passed' % len(SCRIPTS))
sys.exit(0)
