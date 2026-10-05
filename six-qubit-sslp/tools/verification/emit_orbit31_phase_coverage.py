"""Emit explicit colourings or odd closed walks for all 2903 audit masks.

Each record additionally has a real moment witness and the no-singleton
predicate. Python only chooses input records; Lean checks every record.
"""
import argparse
from itertools import combinations
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
SIZE = 192


def graph(mask):
    edges = []
    active = lambda j: bool(mask & (1 << j))
    for i in range(3):
        for e in range(4):
            b = 4 + 4*i + e
            if active(e) and active(b):
                edges.append((e,b,False))
    for i,j in combinations(range(3),2):
        for e,f in combinations(range(4),2):
            a,b,c,d = 4+4*i+e,4+4*j+f,4+4*i+f,4+4*j+e
            if active(a) and active(b) and not (active(c) and active(d)):
                edges.append((a,b,True))
            if active(c) and active(d) and not (active(a) and active(b)):
                edges.append((c,d,True))
    return edges


def fin(i):
    return f'⟨{i},by decide⟩'


def phase_certificate(data,mask):
    candidate = data['phase_candidates'][str(mask)]
    if 'colors' in candidate:
        colors = candidate['colors']
        assert len(colors)==16
        assert all((colors[a]^colors[b])==int(s) for a,b,s in graph(mask))
        return '.coloring ![' + ','.join('true' if c else 'false' for c in colors) + ']'
    edges = graph(mask)
    indices = candidate['odd_cycle_edges']
    for start in edges[indices[0]][:2]:
        current = start
        walk = []
        for k in indices:
            a,b,negative = edges[k]
            if current==a:
                current=b
            elif current==b:
                current=a
            else:
                break
            walk.append((negative,current))
        else:
            if current==start and sum(negative for negative,_ in walk)%2==1:
                assert mask & (1<<start)
                return '.oddWalk '+fin(start)+' ['+','.join(
                    f'({str(negative).lower()},{fin(v)})' for negative,v in walk)+']'
    raise ValueError(('No closed signed walk',mask,indices))


def generate(data):
    masks = data['no_singleton_masks']
    assert len(masks)==2903 and masks==sorted(set(masks))
    files = {}
    names = []
    for start in range(0,len(masks),SIZE):
        selected = masks[start:start+SIZE]
        name = f'Shard{start//SIZE:03d}'
        names.append(name)
        records = []
        for mask in selected:
            vertices = data['primal_selectors'][mask]
            assert vertices
            records.append('{mask:='+fin(mask)+',vertices:=['+','.join(map(str,vertices))+
                           '],phase:='+phase_certificate(data,mask)+'}')
        count = sum('colors' in data['phase_candidates'][str(mask)] for mask in selected)
        files[f'MainTheory/Generated/Orbit31PhaseCoverage/{name}.lean'] = f'''import MainTheory.Orbit31PhaseCoverageBase

/-! Every listed support has a checked primal witness and phase certificate. -/
set_option autoImplicit false
set_option maxHeartbeats 128000000
set_option maxRecDepth 1000000
namespace MainTheory.Generated.Orbit31PhaseCoverage.{name}
open MainTheory.Orbit31PhaseCoverageBase
open MainTheory.Orbit31SignedSupport (isColoring)

def records : List Entry := [
  '''+',\n  '.join(records)+f''']

theorem checked : records.all (fun entry => decide (Valid entry)) = true := by decide +kernel
theorem valid : ∀ entry ∈ records, Valid entry := by
  simpa only [decide_eq_true_eq] using List.all_eq_true.mp checked
theorem length : records.length = {len(selected)} := by decide +kernel
theorem color_count : (records.filter (fun entry => isColoring entry.phase)).length = {count} := by decide +kernel

end MainTheory.Generated.Orbit31PhaseCoverage.{name}
'''
    imports = '\n'.join('import MainTheory.Generated.Orbit31PhaseCoverage.'+n for n in names)
    joined = ' ++ '.join(n+'.records' for n in names)
    checks = ','.join(n+'.checked' for n in names)
    lengths = ','.join(n+'.length' for n in names)
    counts = ','.join(n+'.color_count' for n in names)
    files['MainTheory/Generated/Orbit31PhaseCoverage/Aggregate.lean'] = f'''{imports}

/-! Complete record set for the no-singleton supports, with exact graph checks. -/
set_option autoImplicit false
set_option maxHeartbeats 256000000
set_option maxRecDepth 1000000
namespace MainTheory.Generated.Orbit31PhaseCoverage.Aggregate
open MainTheory.Orbit31PhaseCoverageBase
open MainTheory.Orbit31SignedSupport (isColoring)

def records : List Entry := {joined}

theorem checked : records.all (fun entry => decide (Valid entry)) = true := by
  simp only [records,List.all_append,{checks},Bool.true_and]
theorem valid : ∀ entry ∈ records, Valid entry := by
  simpa only [decide_eq_true_eq] using List.all_eq_true.mp checked
theorem length : records.length = 2903 := by
  norm_num [records,List.length_append,{lengths}]
theorem color_count : (records.filter (fun entry => isColoring entry.phase)).length = 311 := by
  norm_num [records,List.filter_append,List.length_append,{counts}]
theorem masks_increasing : (records.map Entry.mask).IsChain (· < ·) := by decide +kernel
theorem masks_nodup : (records.map Entry.mask).Nodup :=
  masks_increasing.pairwise.imp (fun h => ne_of_lt h)

end MainTheory.Generated.Orbit31PhaseCoverage.Aggregate
'''
    return files


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check',action='store_true')
    args = parser.parse_args()
    data = json.loads((ROOT/'results/orbit31-support-candidates-20261005.json').read_text(encoding='utf8'))
    files = generate(data)
    for relative,text in files.items():
        path = ROOT/relative
        if args.check:
            if path.read_text(encoding='utf8') != text:
                raise SystemExit('Generated phase coverage differs: '+relative)
        else:
            path.parent.mkdir(parents=True,exist_ok=True)
            path.write_text(text,encoding='utf8',newline='\n')
    print('Prepared',len(files),'kernel-only signed-graph coverage modules; Lean acceptance remains required.')
