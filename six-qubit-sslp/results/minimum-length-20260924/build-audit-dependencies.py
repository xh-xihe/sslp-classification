import json
import sys
from pathlib import Path

root = Path.cwd()
sys.path.insert(0, str(root / 'tools'))
import build_lean
import verify

# Build every current audit import, not the expensive individual #print commands.
# The subsequent shared-state kernel harness reads the current Audit source.
_, modules, _ = verify.axiom_inventory(paper_version='20260924')
args = [arg for name in modules for arg in ('--module', name)]
code = build_lean.main(args)
if code == 0:
    target = root / 'results/minimum-length-20260924/build.json'
    target.write_bytes((root / '.lake/build/certification/success.json').read_bytes())
sys.exit(code)
