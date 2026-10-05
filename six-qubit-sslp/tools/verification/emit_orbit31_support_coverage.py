"""Emit kernel-checkable primal/dual coverage for all 65536 support masks.

Candidate selection is untrusted. Each mask is checked by ordinary Lean
kernel reduction, and the aggregate theorem has arbitrary-real semantics.
"""
import argparse
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
BLOCKS = 16
BLOCK_SIZE = 4096


def certificate(data, mask):
    vertices = data['primal_selectors'][mask]
    if vertices is not None:
        assert vertices
        union = 0
        for vertex in vertices:
            union |= data['primals'][vertex]['mask']
        assert union == mask
        return '.primal [' + ','.join(map(str, vertices)) + ']'
    profile = data['dual_selectors'][mask]
    assert profile is not None
    dual = data['duals'][profile]
    assert dual['negative_mask'] & mask == 0
    if dual['rhs_twice'] < 0:
        coordinate = 0
    else:
        assert dual['rhs_twice'] == 0
        positive = dual['positive_mask'] & mask
        assert positive
        coordinate = (positive & -positive).bit_length() - 1
    return f'.dual {profile} {coordinate}'


def generate(data):
    files = {}
    for block in range(BLOCKS):
        name = f'Shard{block:03d}'
        witnesses = [certificate(data, BLOCK_SIZE * block + j) for j in range(BLOCK_SIZE)]
        count = sum(data['primal_selectors'][BLOCK_SIZE * block + j] is not None
                    for j in range(BLOCK_SIZE))
        files[f'MainTheory/Generated/Orbit31SupportCoverage/{name}.lean'] = f'''import MainTheory.Orbit31SupportCoverageBase
import MainTheory.FiniteListCertificateCounts

/-! Exact support coverage for masks {BLOCK_SIZE * block} through {BLOCK_SIZE * (block + 1) - 1}.
Every primal union or strict-support dual witness is reduced by the kernel.
-/
set_option autoImplicit false
set_option maxHeartbeats 64000000
set_option maxRecDepth 1000000
namespace MainTheory.Generated.Orbit31SupportCoverage.{name}
open MainTheory.Orbit31SupportCoverageBase

def records : List Certificate := [
  ''' + ',\n  '.join(witnesses) + f''']

theorem length : records.length = {BLOCK_SIZE} := by decide +kernel

def certificates (j : Fin {BLOCK_SIZE}) : Certificate :=
  records[j.val]'(by rw [length]; exact j.isLt)

theorem checked : (records.zipIdx {BLOCK_SIZE * block}).all
    (fun pair => decide (Valid pair.2 pair.1)) = true := by decide +kernel

theorem valid : ∀ j : Fin {BLOCK_SIZE},
    Valid ({BLOCK_SIZE * block} + j.val) (certificates j) := by
  have h : ∀ pair ∈ records.zipIdx {BLOCK_SIZE * block}, Valid pair.2 pair.1 := by
    simpa only [decide_eq_true_eq] using List.all_eq_true.mp checked
  intro j
  exact List.forall_mem_zipIdx.mp h j.val (by rw [length]; exact j.isLt)

theorem count_records : (records.filter isPrimal).length = {count} := by decide +kernel

theorem count : (Finset.univ.filter fun j : Fin {BLOCK_SIZE} =>
    isPrimal (certificates j) = true).card = {count} := by
  have h := MainTheory.FiniteListCertificateCounts.indexed_filter_card records isPrimal
  rw [count_records] at h
  simpa only [length,certificates] using h

end MainTheory.Generated.Orbit31SupportCoverage.{name}
'''
    imports = '\n'.join(f'import MainTheory.Generated.Orbit31SupportCoverage.Shard{i:03d}'
                        for i in range(BLOCKS))
    functions = ',\n  '.join(f'Shard{i:03d}.certificates' for i in range(BLOCKS))
    valid_cases = '\n'.join(f'  · exact Shard{i:03d}.valid' for i in range(BLOCKS))
    counts = [sum(data['primal_selectors'][BLOCK_SIZE * i + j] is not None
                  for j in range(BLOCK_SIZE)) for i in range(BLOCKS)]
    count_cases = '\n'.join(f'  · exact Shard{i:03d}.count' for i in range(BLOCKS))
    files['MainTheory/Generated/Orbit31SupportCoverage/Aggregate.lean'] = f'''{imports}

/-! All support masks, including boundary faces, have a checked certificate. -/
set_option autoImplicit false
set_option maxHeartbeats 64000000
set_option maxRecDepth 1000000
namespace MainTheory.Generated.Orbit31SupportCoverage.Aggregate
open MainTheory.Orbit31SupportCoverageBase

def certificates : Fin {BLOCKS} → Fin {BLOCK_SIZE} → Certificate := ![
  {functions}]
def counts : Fin {BLOCKS} → ℕ := ![{','.join(map(str, counts))}]

theorem valid (i : Fin {BLOCKS}) : ∀ j : Fin {BLOCK_SIZE},
    Valid ({BLOCK_SIZE} * i.val + j.val) (certificates i j) := by
  fin_cases i
{valid_cases}

theorem count (i : Fin {BLOCKS}) : (Finset.univ.filter fun j : Fin {BLOCK_SIZE} =>
    isPrimal (certificates i j) = true).card = counts i := by
  fin_cases i
{count_cases}

theorem count_total : (∑ i, counts i) = 15603 := by decide +kernel

end MainTheory.Generated.Orbit31SupportCoverage.Aggregate
'''
    return files


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--candidates', type=Path,
                        default=ROOT / 'results/orbit31-support-candidates-20261005.json')
    parser.add_argument('--output-dir', type=Path, default=ROOT)
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    data = json.loads(args.candidates.read_text(encoding='utf8'))
    files = generate(data)
    shard_dir = args.output_dir / 'MainTheory/Generated/Orbit31SupportCoverage'
    expected = {args.output_dir / relative for relative in files}
    for stale in shard_dir.glob('Shard*.lean'):
        if stale not in expected:
            if args.check:
                raise SystemExit('Stale generated source: ' + str(stale))
            if stale.resolve().parent != shard_dir.resolve() or not stale.name[5:8].isdigit():
                raise SystemExit('Refusing an unexpected generated path')
            stale.unlink()
    for relative, content in files.items():
        path = args.output_dir / relative
        if args.check:
            if path.read_text(encoding='utf8') != content:
                raise SystemExit('Generated source differs: ' + relative)
        else:
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(content, encoding='utf8', newline='\n')
    print('Prepared', len(files), 'kernel-only coverage modules; Lean acceptance remains required.')


if __name__ == '__main__':
    main()
