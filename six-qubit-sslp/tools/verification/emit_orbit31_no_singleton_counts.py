"""Emit exact kernel counts for the necessary orbit-31 no-singleton filter."""
import argparse
import json
from pathlib import Path

from emit_orbit31_support_coverage import BLOCKS, BLOCK_SIZE

ROOT = Path(__file__).resolve().parents[2]


def generate(data):
    stage = set(data['no_singleton_masks'])
    counts = [sum(BLOCK_SIZE*i+j in stage for j in range(BLOCK_SIZE)) for i in range(BLOCKS)]
    assert sum(counts)==2903
    text = '''import MainTheory.Generated.Orbit31SupportCoverage.Aggregate
import MainTheory.Orbit31SignedSupport

/-! Counts bind the actual support certificates and literal overlap predicate. -/
set_option autoImplicit false
set_option maxHeartbeats 256000000
set_option maxRecDepth 1000000
namespace MainTheory.Generated.Orbit31NoSingletonCounts
open MainTheory.Orbit31SupportCoverageBase
open MainTheory.Orbit31SignedSupport
open MainTheory.Generated.Orbit31SupportCoverage
'''
    for i,count in enumerate(counts):
        shard = f'Shard{i:03d}'
        text += f'''
theorem count{i}_records : (({shard}.records.zipIdx {BLOCK_SIZE*i}).filter
    (fun pair => isPrimal pair.1 && noSingleton pair.2)).length = {count} := by decide +kernel

theorem count{i} : (Finset.univ.filter fun j : Fin {BLOCK_SIZE} =>
    isPrimal ({shard}.certificates j) = true ∧ noSingleton ({BLOCK_SIZE*i}+j.val) = true).card = {count} := by
  have h := MainTheory.FiniteListCertificateCounts.indexed_filter_card
    ({shard}.records.zipIdx {BLOCK_SIZE*i}) (fun pair => isPrimal pair.1 && noSingleton pair.2)
  rw [count{i}_records] at h
  simpa only [List.length_zipIdx,{shard}.length,List.getElem_zipIdx,
    {shard}.certificates,Bool.and_eq_true] using h
'''
    text += f'''
def counts : Fin {BLOCKS} → ℕ := ![{','.join(map(str,counts))}]

theorem count (i : Fin {BLOCKS}) : (Finset.univ.filter fun j : Fin {BLOCK_SIZE} =>
    isPrimal (Aggregate.certificates i j) = true ∧
      noSingleton ({BLOCK_SIZE}*i.val+j.val) = true).card = counts i := by
  fin_cases i
'''
    text += '\n'.join(f'  · exact count{i}' for i in range(BLOCKS))
    text += '''

theorem count_total : (∑ i, counts i) = 2903 := by decide +kernel

end MainTheory.Generated.Orbit31NoSingletonCounts
'''
    return text


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check',action='store_true')
    args = parser.parse_args()
    data = json.loads((ROOT/'results/orbit31-support-candidates-20261005.json').read_text(encoding='utf8'))
    text = generate(data)
    path = ROOT/'MainTheory/Generated/Orbit31NoSingletonCounts.lean'
    if args.check:
        if path.read_text(encoding='utf8') != text:
            raise SystemExit('Generated no-singleton counts differ')
    else:
        path.write_text(text,encoding='utf8',newline='\n')
    print('Prepared kernel counts for the no-singleton filter; Lean acceptance remains required.')
