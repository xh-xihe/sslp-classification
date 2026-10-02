"""Build the current audit import closure, without the repeated print wrappers."""
import sys
from pathlib import Path

root = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(root / 'tools'))
import build_lean
import verify

_, modules, _ = verify.axiom_inventory(paper_version='20260924')
code = build_lean.main([arg for name in modules for arg in ('--module', name)])
if code == 0:
    (Path(__file__).parent / 'build.json').write_bytes(
        (root / '.lake/build/certification/success.json').read_bytes())
sys.exit(code)
