"""Emit actual Pauli cross rows and exact row-space normal forms for orbit 31.

The generator supplies only algebraic candidates. Lean checks the physical
incidences, all dressing signs, both directions of the row-space normal form,
the rank, and the bridge from distance-three KL.
"""
import argparse
from itertools import combinations
import json
from pathlib import Path
import re
import sympy as s

ROOT = Path(__file__).resolve().parents[2]


def vec(items):
    return '![' + ','.join(map(str, items)) + ']'


def number(x):
    return str(x) if x.q == 1 else f'({x.p}/{x.q})'


def fin(i):
    return f'⟨{i},by decide⟩'


def generate(data):
    words = [int(''.join(map(str, w)), 2) for w in data['words']]
    index = {w: j for j, w in enumerate(words)}
    files = {}
    for physical in list(combinations(range(3), 1)) + list(combinations(range(6), 2)):
        flip = sum(1 << (5-i) for i in physical)
        pairs = []
        for j, w in enumerate(words):
            partner = index.get((63 ^ w) ^ flip)
            if partner is not None and j <= partner:
                pairs.append((j, partner))
        if not pairs:
            continue
        assert len(pairs) == 4
        directed = [v for a, b in pairs for v in [(a, b), (b, a)]]
        dressings = [z for z in range(64) if (flip | z).bit_count() <= 2]
        rows = s.Matrix([[-1 if (z & (63 ^ words[b])).bit_count() % 2 else 1
                          for a, b in directed] for z in dressings])
        reduced, pivots = rows.rref()
        free = [j for j in range(8) if j not in pivots]
        assert len(pivots) == (5 if len(physical) == 1 else 2)
        name = 'Flip' + ''.join(str(i+1) for i in physical)
        pattern = []
        for j in range(8):
            if j in free:
                pattern.append(f'p {free.index(j)}')
            else:
                r = pivots.index(j)
                pattern.append(' + '.join(f'{number(-reduced[r, k])} * p {free.index(k)}'
                                          for k in free if reduced[r, k]) or '0')
        source = f'''import MainTheory.Orbit31SupportBase

/-! Actual orbit-31 cross-Pauli rows for physical flip {physical}.
The support incidences, signs and complete row-space normal form are checked.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 1000000
namespace MainTheory.Generated.Orbit31CrossRows.{name}
open MainTheory.Orbit31SupportBase
open MainTheory.OrderEightSupportDisplays (bits)
open SixQubit.Orbit31
open scoped BigOperators
noncomputable section

def top (j : Fin 16) : SS.BitString 6 := fun k => !(bottom j k)
def src : Fin 8 → Fin 16 := {vec(fin(a) for a,b in directed)}
def dst : Fin 8 → Fin 16 := {vec(fin(b) for a,b in directed)}
def flip : SS.BitString 6 := bits {flip}
def dressing : Fin {len(dressings)} → SS.BitString 6 := fun r => bits ({vec(dressings)} r)
def rows : Matrix (Fin {len(dressings)}) (Fin 8) ℤ := {vec(vec(row) for row in rows.tolist())}
def W : Matrix (Fin {len(dressings)}) (Fin 8) ℂ := fun i j => rows i j
def products (c d : SS.State 6 ℂ) : Fin 8 → ℂ := fun j =>
  star (c (bottom (src j))) * d (top (dst j))

theorem incidences : S1.filter (fun y => SS.bxor y flip ∈ S0) =
    ({{{','.join('top '+str(b) for a,b in directed)}}} : Finset (SS.BitString 6)) := by decide +kernel

theorem source_incidence : ∀ j, SS.bxor (top (dst j)) flip = bottom (src j) := by decide +kernel
theorem dressing_weight : ∀ r, (⟨flip,dressing r⟩ : SS.PauliString 6).wt ≤ 2 := by decide +kernel
theorem actual_signs : ∀ r j,
    (if SS.bdot (dressing r) (top (dst j)) then (-1 : ℤ) else 1) = rows r j := by decide +kernel
'''
        for r, z in enumerate(dressings):
            source += f'''
theorem row{r} (c d : SS.State 6 ℂ) :
    SixQubit.offSumOn S0 S1 c d flip (dressing {r}) = W.mulVec (products c d) {r} := by
  unfold SixQubit.offSumOn
  rw [incidences,
    ''' + ',\n    '.join(['Finset.sum_insert (by decide +kernel)'] * 7) + ''',
    Finset.sum_singleton]
'''
            for a, b in directed:
                sign = 'true' if (z & (63 ^ words[b])).bit_count() % 2 else 'false'
                source += f'  rw [show SS.bxor (top {b}) flip = bottom {a} by decide +kernel]\n'
                source += f'  rw [show SS.bdot (dressing {r}) (top {b}) = {sign} by decide +kernel]\n'
            source += f'''  conv_rhs => norm_num [W,rows,products,src,dst,
    Matrix.mulVec,dotProduct,Fin.sum_univ_succ,Fin.succ]
  conv_lhs => norm_num [SixQubit.signMul]
'''
        source += f'''
theorem physical (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x = 0) (hd : ∀ x, x ∉ S1 → d x = 0)
    (hkl : SS.HasDistance ![c,d] 3) : W.mulVec (products c d) = 0 := by
  ext r
  fin_cases r
'''
        for r in range(len(dressings)):
            source += f'''  · simpa only [Pi.zero_apply] using (row{r} c d).symm.trans
      (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl
        flip (dressing {r}) (dressing_weight {r}))
'''
        source += f'''
def freeIndices : Fin {len(free)} → Fin 8 := {vec(fin(j) for j in free)}
def pattern (p : Fin {len(free)} → ℂ) : Fin 8 → ℂ := {vec(pattern)}

theorem kernel_iff (t : Fin 8 → ℂ) :
    W.mulVec t = 0 ↔ t = pattern (fun j => t (freeIndices j)) := by
  constructor
  · intro h
'''
        for r in range(len(dressings)):
            source += f'    have h{r} := congrFun h {r}\n'
        source += '    norm_num [W,rows,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,Fin.succ] at ' + ' '.join(f'h{r}' for r in range(len(dressings))) + '\n'
        for r, pivot in enumerate(pivots):
            coefficients = rows.T.gauss_jordan_solve(reduced.row(r).T)[0]
            extra = set().union(*(v.free_symbols for v in coefficients))
            coefficients = coefficients.subs({x: 0 for x in extra})
            rhs = ' + '.join(f'{number(-reduced[r,k])} * t {k}'
                             for k in free if reduced[r,k]) or '0'
            proof = ' + '.join(f'{number(v)} * h{k}' for k, v in enumerate(coefficients) if v)
            source += f'    have e{pivot} : t {pivot} = {rhs} := by\n      norm_num\n      linear_combination {proof}\n'
        source += '    funext j\n    fin_cases j\n'
        for j in range(8):
            source += f'    · exact e{j}\n' if j in pivots else '    · rfl\n'
        source += '''  · intro h
    rw [h]
    ext r
    fin_cases r <;> norm_num [W,rows,pattern,Matrix.mulVec,dotProduct,
      Fin.sum_univ_succ,Fin.succ] <;> ring

def parameters : (Fin ''' + str(len(free)) + ''' → ℂ) ≃ₗ[ℂ] LinearMap.ker W.mulVecLin where
  toFun p := ⟨pattern p,(kernel_iff _).mpr (by funext j; fin_cases j <;> rfl)⟩
  invFun t := fun j => t.1 (freeIndices j)
  left_inv p := by funext j; fin_cases j <;> rfl
  right_inv t := by apply Subtype.ext; exact ((kernel_iff _).mp t.2).symm
  map_add' p q := by apply Subtype.ext; funext j; fin_cases j <;> norm_num [pattern] <;> ring
  map_smul' a p := by apply Subtype.ext; funext j; fin_cases j <;> norm_num [pattern] <;> ring

theorem kernel_dimension : Module.finrank ℂ (LinearMap.ker W.mulVecLin) = ''' + str(len(free)) + ''' := by
  simpa using (LinearEquiv.finrank_eq parameters).symm

theorem rank : W.rank = ''' + str(len(pivots)) + ''' := by
  have h := LinearMap.finrank_range_add_finrank_ker W.mulVecLin
  rw [kernel_dimension] at h
  change W.rank + ''' + str(len(free)) + ''' = Module.finrank ℂ (Fin 8 → ℂ) at h
  norm_num at h
  omega

end
end MainTheory.Generated.Orbit31CrossRows.''' + name + '\n'
        source = re.sub(r'\b(bottom|top|dressing|dressing_weight|congrFun h|t|p) (\d+)\b',
                        lambda m: m[1] + ' ' + fin(int(m[2])), source)
        source = re.sub(r'\(products c d\) (\d+)\b',
                        lambda m: '(products c d) ' + fin(int(m[1])), source)
        files[f'MainTheory/Generated/Orbit31CrossRows/{name}.lean'] = source
    assert len(files) == 12
    return files


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output-dir', type=Path, default=ROOT)
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    data = json.loads((ROOT / 'results/orbit31-support-candidates-20261005.json').read_text(encoding='utf8'))
    files = generate(data)
    for relative, text in files.items():
        path = args.output_dir / relative
        if args.check:
            if path.read_text(encoding='utf8') != text:
                raise SystemExit('Generated source differs: ' + relative)
        else:
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(text, encoding='utf8', newline='\n')
    print('Prepared 12 actual cross-row modules; strict Lean acceptance remains required.')
