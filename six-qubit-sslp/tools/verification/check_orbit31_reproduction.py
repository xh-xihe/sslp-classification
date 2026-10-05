"""Reproduce the orbit-31, literal orbit-32 and orbit-33 proof-source candidates.

This checks source provenance only. Ordinary Lean elaboration and a fresh
transitive axiom audit are separately required for proof acceptance.
"""
import argparse
from concurrent.futures import ThreadPoolExecutor
import hashlib
import json
from pathlib import Path
import subprocess
import sys
from prepare_orbit31_audit_20261005 import modules

ROOT=Path(__file__).resolve().parents[2]
GENERATORS=[
    'emit_orbit31_support_arithmetic.py','emit_orbit31_support_coverage.py',
    'emit_orbit31_cross_rows.py','emit_orbit31_cross_consequences.py',
    'emit_orbit31_no_singleton_counts.py','emit_orbit31_phase_coverage.py',
    'emit_orbit31_symmetry_base.py','emit_orbit31_printed_orbits.py',
    'emit_orbit31_affine_table_group.py','emit_orbit31_vertex_reconstructions.py',
    'emit_orbit31_direct_triangles.py','emit_orbit31_final_cross.py',
    'emit_orbit31_balanced_moment_iff.py','generate_orbit31_printed_minor.py',
    'generate_orbit32_printed_normal.py','generate_orbit32_printed_minor.py',
    'generate_orbit33_printed_blocks.py','generate_orbit33_scalar_reflection.py',
    'generate_order_five_grid_remaining.py','generate_order_four_walsh_remaining.py',
    'generate_order_three_printed_moments.py','generate_order_three_cross_rows.py',
    'generate_order_three_printed_ranks.py',
    'generate_orbit49_printed_rows.py',
    'generate_orbit50_printed_rows.py','generate_orbit51_printed_rows.py',
    'generate_order_two_printed_moments.py','generate_order_two_printed_walsh.py',
    'generate_order_two_printed_ranks.py','generate_order_two_shell_projectors.py',
    'generate_orbit45_affine_gauge.py','generate_orbit45_cross_factors.py',
    'generate_standard_five_joint_space.py',
    'generate_orbit29_face_audit.py','generate_orbit29_pair_balance.py',
    'generate_orbit29_physical_pair_reduction.py','generate_orbit29_printed_simplex.py',
    'generate_orbit29_physical_ratios.py','generate_orbit29_printed_eta.py',
    'generate_orbit29_moment_rank.py',
]

def sha(path,lf=False):
    raw=path.read_bytes()
    return hashlib.sha256(raw.replace(b'\r\n',b'\n') if lf else raw).hexdigest()

def check(name):
    path=ROOT/'tools/verification'/name
    result=subprocess.run([sys.executable,'-X','utf8',str(path),'--check'],
                          cwd=ROOT,capture_output=True,encoding='utf8')
    return {'tool':path.relative_to(ROOT).as_posix(),'sha256_lf':sha(path,True),
            'exit_code':result.returncode,'output':result.stdout+result.stderr}

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path)
    args=parser.parse_args()
    before={p.relative_to(ROOT).as_posix():sha(p,True) for p in modules()}
    with ThreadPoolExecutor(max_workers=2) as executor:
        checks=list(executor.map(check,GENERATORS))
    after={p.relative_to(ROOT).as_posix():sha(p,True) for p in modules()}
    if before != after:
        raise ValueError('Proof-source snapshot changed during reproduction checks')
    passed=all(row['exit_code']==0 for row in checks)
    record={'schema':1,'passed':passed,
        'scope':'Source reproduction only; candidate inputs do not replace Lean kernel semantics.',
        'candidate_data':{'path':'results/orbit31-support-candidates-20261005.json',
                          'sha256':sha(ROOT/'results/orbit31-support-candidates-20261005.json')},
        'source_hashes_lf':after,'checks':checks}
    if args.output:
        if args.output.exists():
            raise ValueError('Refusing to overwrite a reproduction record')
        args.output.parent.mkdir(parents=True,exist_ok=True)
        args.output.write_text(json.dumps(record,indent=2)+'\n',encoding='utf8')
    for row in checks:
        print(('PASS' if row['exit_code']==0 else 'FAIL')+': '+row['tool'])
        if row['exit_code']:
            print(row['output'])
    print(f'{len(checks)} reproduction checks; {len(after)} source bindings; '+('PASS' if passed else 'FAIL'))
    return 0 if passed else 1

if __name__=='__main__':
    raise SystemExit(main())
