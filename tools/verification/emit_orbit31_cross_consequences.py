"""Emit literal reciprocal, sum and rectangle consequences of physical KL.

Only checked cross-row normal forms are used; no impossibility theorem is used.
"""
import argparse
from itertools import combinations
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]


def fin(i):
    return f'⟨{i},by decide⟩'


def context(name):
    return f'''theorem {name} (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x = 0) (hd : ∀ x, x ∉ S1 → d x = 0)
    (hkl : SS.HasDistance ![c,d] 3)'''


def generate():
    data = json.loads((ROOT/'results/orbit31-support-candidates-20261005.json').read_text(encoding='utf8'))
    words = [int(''.join(map(str,w)),2) for w in data['words']]
    index = {w:j for j,w in enumerate(words)}
    text = '''import MainTheory.Orbit31CrossRows
import MainTheory.Orbit31PhaseRatios
import MainTheory.Orbit31SignedSupport

/-! Canonical cross-KL equations in the actual A/B table coordinates. -/
set_option autoImplicit false
set_option maxHeartbeats 16000000
namespace MainTheory.Orbit31CrossConsequences
open MainTheory.Generated.Orbit31CrossRows
open MainTheory.Orbit31PhaseRatios
open MainTheory.Orbit31SignedSupport (A B)
open SixQubit.Orbit31
open scoped BigOperators
noncomputable section
'''
    for i in range(3):
        flip = 'Flip'+str(i+1)
        text += f'''
theorem pair{i} (t : Fin 8 → ℂ) (h : {flip}.W.mulVec t = 0) (e : Fin 4) :
    t ⟨2*e.val,by omega⟩ = t ⟨2*e.val+1,by omega⟩ := by
  rw [({flip}.kernel_iff t).mp h]
  fin_cases e <;> norm_num [{flip}.pattern]

theorem sum{i} (t : Fin 8 → ℂ) (h : {flip}.W.mulVec t = 0) :
    (∑ e : Fin 4, t ⟨2*e.val,by omega⟩) = 0 := by
  rw [({flip}.kernel_iff t).mp h]
  norm_num [{flip}.pattern,Fin.sum_univ_succ,Fin.succ]
  ring
'''
    text += '\n'+context('physical_reciprocal')+''' :
    ∀ i : Fin 3, ∀ e : Fin 4,
      star (C c (A e)) * D d (B i e) = star (C c (B i e)) * D d (A e) := by
  intro i e
  fin_cases i
'''
    for i in range(3):
        flip = 'Flip'+str(i+1)
        text += f'''  · have h := pair{i} ({flip}.products c d) ({flip}.physical c d hc hd hkl) e
    fin_cases e <;> simpa [{flip}.products,{flip}.src,{flip}.dst,C,D,top,A,B,Fin.succ] using h
'''
    text += '\n'+context('physical_weight_one_sum')+''' :
    ∀ i : Fin 3, (∑ e : Fin 4, star (C c (A e)) * D d (B i e)) = 0 := by
  intro i
  fin_cases i
'''
    for i in range(3):
        flip = 'Flip'+str(i+1)
        text += f'''  · simpa [{flip}.products,{flip}.src,{flip}.dst,C,D,top,A,B,
      Fin.sum_univ_succ,Fin.succ] using
      sum{i} ({flip}.products c d) ({flip}.physical c d hc hd hkl)
'''
    names = []
    for i,j in combinations(range(3),2):
        for e,f in combinations(range(4),2):
            cells = [(4+4*i+e,4+4*j+f),(4+4*j+f,4+4*i+e),
                     (4+4*i+f,4+4*j+e),(4+4*j+e,4+4*i+f)]
            flip_value = (63 ^ words[cells[0][0]]) ^ words[cells[0][1]]
            physical = [k for k in range(6) if flip_value & (1 << (5-k))]
            assert len(physical)==2
            flip = 'Flip'+''.join(str(k+1) for k in physical)
            pairs = []
            for a,w in enumerate(words):
                b=index.get((63 ^ w) ^ flip_value)
                if b is not None and a<=b:
                    pairs.extend([(a,b),(b,a)])
            slots = [pairs.index(cell) for cell in cells]
            name = f'rectangle_{i}{j}_{e}{f}'
            names.append((i,j,e,f,name))
            term = ' + '.join(f'star (C c {fin(a)}) * D d {fin(b)}' for a,b in cells)
            poly = ' + '.join(f'{flip}.products c d {fin(k)}' for k in slots)
            text += '\n'+context(name)+f''' :
    {term} = 0 := by
  have ht := ({flip}.kernel_iff _).mp ({flip}.physical c d hc hd hkl)
  have h : {poly} = 0 := by
    rw [ht]
    norm_num [{flip}.pattern,{flip}.freeIndices]
    ring
  simpa [{flip}.products,{flip}.src,{flip}.dst,C,D,top] using h
'''
    text += '\n'+context('physical_rectangles')+''' :
    ∀ r : Fin 3, ∀ k : Fin 6,
      let i := (MainTheory.Orbit31SignedSupport.rowPairs r).1
      let j := (MainTheory.Orbit31SignedSupport.rowPairs r).2
      let e := (MainTheory.Orbit31SignedSupport.colPairs k).1
      let f := (MainTheory.Orbit31SignedSupport.colPairs k).2
      star (C c (B i e)) * D d (B j f) + star (C c (B j f)) * D d (B i e) +
        star (C c (B i f)) * D d (B j e) + star (C c (B j e)) * D d (B i f) = 0 := by
  intro r k
  fin_cases r <;> fin_cases k
'''
    for i,j,e,f,name in names:
        text += f'  · exact {name} c d hc hd hkl\n'
    text += '\nend\nend MainTheory.Orbit31CrossConsequences\n'
    return text


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check',action='store_true')
    args = parser.parse_args()
    path = ROOT/'MainTheory/Orbit31CrossConsequences.lean'
    content = generate()
    if args.check:
        if path.read_text(encoding='utf8') != content:
            raise SystemExit('Generated cross consequences differ')
    else:
        path.write_text(content,encoding='utf8',newline='\n')
    print('Prepared canonical physical reciprocal, sum and eighteen rectangle equations; Lean acceptance remains required.')
