"""Check literal parity-frame and shell sources and bind ten anchor proofs."""
import argparse, hashlib, json, subprocess, sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--output', type=Path)
args = parser.parse_args()
checks = []
for name in ('generate_orbit19_shell_displays.py', 'generate_parity_frame_displays.py'):
    result = subprocess.run([sys.executable, str(ROOT / 'tools/verification' / name), '--check'],
                            cwd=ROOT, capture_output=True, encoding='utf8')
    checks.append({'generator': name, 'passed': result.returncode == 0,
                   'output': result.stdout + result.stderr})
    print(('PASS' if result.returncode == 0 else 'FAIL') + ': ' + name)
names = ('Orbit19ShellDisplays', 'Orbit26PhysicalNorms', 'Orbit26PhysicalDependentAnchors',
         'Orbit26OrthogonalGram', 'Orbit26NormalizedRows', 'Orbit26NonmatchingPhysical',
         'Orbit26MatchingRows', 'Orbit14ParityFrames', 'Orbit15ParityFrames', 'Orbit24ParityFrames')
hashes = {f'MainTheory/{n}.lean': hashlib.sha256((ROOT / 'MainTheory' / (n + '.lean'))
           .read_bytes().replace(b'\r\n', b'\n')).hexdigest() for n in names}
passed = all(row['passed'] for row in checks)
if args.output:
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps({'schema': 1, 'passed': passed, 'checks': checks,
        'source_hashes_lf': hashes,
        'scope': 'Exact-source reconstruction and hashes; separate whole kernel build and audit required.'},
        ensure_ascii=False, indent=2) + '\n', encoding='utf8', newline='\n')
raise SystemExit(0 if passed else 1)
