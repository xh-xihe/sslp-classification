"""Emit kernel-checkable exact aggregate moment algebra for SI orbit 26.

SymPy supplies only candidate row combinations. Lean checks the literal
physical tail-bit matrix, the complete affine solution, and its rational rank.
"""
from itertools import combinations
from pathlib import Path
import argparse
import sympy as s

ROOT = Path(__file__).resolve().parents[2]
WORDS = [0, 6, 17, 23, 9, 15, 26, 28]
TOP = [31-x for x in WORDS]
PAIRS = list(combinations(range(5), 2))
features = [lambda x, j=j: (x >> (4-j)) & 1 for j in range(5)] + [
    lambda x, j=j, k=k: ((x >> (4-j)) & 1)*((x >> (4-k)) & 1)
    for j, k in PAIRS]
A = s.Matrix([[1]*8+[0]*8, [0]*8+[1]*8] + [
    [f(x) for x in WORDS]+[-f(x) for x in TOP] for f in features])
ROWS = list(A.T.rref()[1])
assert len(ROWS) == 14
P = s.Matrix([[1, 1], [-1, -1], [-1, 0], [1, 0], [0, -1], [0, 1],
              [0, 0], [0, 0]]*2)
particular = s.Matrix([s.Rational(-1, 8), s.Rational(3, 8), s.Rational(1, 4),
                      0, s.Rational(1, 4), 0, s.Rational(1, 8), s.Rational(1, 8)]*2)
rhs = s.Matrix([1, 1]+[0]*15)
assert A*P == s.zeros(17, 2) and A*particular == rhs


def num(v):
    return str(v) if v.q == 1 else f'({v.p}/{v.q})'


def generate():
    parts = ['''import MainTheory.OrderFour26Support
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic

/-! The literal seventeen-by-sixteen tail moment system for SI orbit 26.
The integer entries are checked against the actual fibre tail coordinates.
The complete rational affine solution and rank fourteen are kernel proofs;
they do not depend on the final no-code theorem.
-/

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace MainTheory.Orbit26PrintedMoments
open MainTheory.OrderFour26Support

''']
    parts.append(f'''def pairs : Fin 10 → Fin 5 × Fin 5 := ![{','.join(f'({j},{k})' for j,k in PAIRS)}]
def values : List (List ℤ) := [{','.join('['+','.join(str(v) for v in A.row(i))+']' for i in range(17))}]
def rows : Matrix (Fin 17) (Fin 16) ℤ := fun i j => (values.getD i.val []).getD j.val 0
def actual : Matrix (Fin 17) (Fin 16) ℤ := fun i j =>
  if i.val = 0 then (if j.val < 8 then 1 else 0) else
  if i.val = 1 then (if j.val < 8 then 0 else 1) else
    let x := if h : j.val < 8 then bottomAt false ⟨j.val,h⟩
      else topAt false ⟨j.val-8,by omega⟩
    let sign : ℤ := if j.val < 8 then 1 else -1
    if h : i.val < 7 then
      sign * (if x (⟨i.val-2,by omega⟩ : Fin 5).succ then 1 else 0)
    else sign * (if x (pairs ⟨i.val-7,by omega⟩).1.succ then 1 else 0) *
      (if x (pairs ⟨i.val-7,by omega⟩).2.succ then 1 else 0)

theorem actual_rows : actual = rows := by decide +kernel

def M : Matrix (Fin 17) (Fin 16) ℚ := fun i j => rows i j
def homogeneous (a b : ℚ) : Fin 16 → ℚ :=
  ![a+b,-a-b,-a,a,-b,b,0,0,a+b,-a-b,-a,a,-b,b,0,0]

theorem kernel_iff (u : Fin 16 → ℚ) :
    M.mulVec u = 0 ↔ u = homogeneous (u 3) (u 5) := by
  constructor
  · intro h
''')
    for i in ROWS:
        index = '(0 : Fin 17)' if i == 0 else f'(0 : Fin {17-i})'+'.succ'*i
        parts.append(f'    have h{i} := congrFun h ({index})\n')
    parts.append('    norm_num [M,rows,values,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,Fin.succ] at '+
                 ' '.join(f'h{i}' for i in ROWS)+'\n')
    for i in ROWS:
        terms = [f'u {j}' if v == 1 else f'-u {j}' for j, v in enumerate(A.row(i)) if v]
        expr = terms[-1]
        for term in reversed(terms[:-1]):
            expr = f'{term}+({expr})'
        parts.append(f'    change {expr}=0 at h{i}\n')
    expressions = ['u 3+u 5', '-u 3-u 5', '-u 3', 'u 3', '-u 5', 'u 5', '0', '0']
    for i in range(16):
        if i in (3, 5):
            continue
        target = s.zeros(1, 16)
        target[0, i] = 1
        for j, v in zip((3, 5), P.row(i)):
            target[0, j] -= v
        coefs = A.extract(ROWS, list(range(16))).T.gauss_jordan_solve(target.T)[0]
        expr = ' + '.join(f'{num(v)} * h{r}' for v, r in zip(coefs, ROWS) if v)
        parts.append(f'    have hu{i} : u {i} = {expressions[i%8]} := by linear_combination {expr}\n')
    parts.append('    funext i\n    fin_cases i <;> simp [homogeneous,'+
                 ','.join(f'hu{i}' for i in range(16) if i not in (3, 5))+''']
  · intro h
    rw [h]
    ext i
    fin_cases i <;> norm_num [M,rows,values,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,homogeneous] <;> ring

def particular : Fin 16 → ℚ :=
  ![-1/8,3/8,1/4,0,1/4,0,1/8,1/8,-1/8,3/8,1/4,0,1/4,0,1/8,1/8]
def target : Fin 17 → ℚ := ![1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def affine (a b : ℚ) : Fin 16 → ℚ :=
  ![a+b-1/8,3/8-a-b,1/4-a,a,1/4-b,b,1/8,1/8,
    a+b-1/8,3/8-a-b,1/4-a,a,1/4-b,b,1/8,1/8]

theorem particular_solution : M.mulVec particular = target := by
  ext i
  fin_cases i <;> norm_num [M,rows,values,Matrix.mulVec,dotProduct,
    Fin.sum_univ_succ,particular,target]

theorem affine_iff (u : Fin 16 → ℚ) :
    M.mulVec u = target ↔ u = affine (u 3) (u 5) := by
  constructor
  · intro h
    have hz : M.mulVec (u-particular) = 0 := by
      rw [Matrix.mulVec_sub,h,particular_solution,sub_self]
    have hu := (kernel_iff (u-particular)).1 hz
    have ha : (u-particular) 3 = u 3 := by
      change u 3-particular ⟨3,by decide⟩ = u 3
      norm_num [particular]
    have hb : (u-particular) 5 = u 5 := by
      change u 5-particular ⟨5,by decide⟩ = u 5
      norm_num [particular]
    rw [ha,hb] at hu
    funext i
    have hi := congrFun hu i
    fin_cases i <;> norm_num [Pi.sub_apply,homogeneous,particular,affine,Fin.succ] at hi ⊢ <;> linarith
  · intro h
    rw [h]
    ext i
    fin_cases i <;> norm_num [M,rows,values,Matrix.mulVec,dotProduct,
      Fin.sum_univ_succ,affine,target] <;> ring

noncomputable def parameters : (Fin 2 → ℚ) ≃ₗ[ℚ] LinearMap.ker M.mulVecLin where
  toFun p := ⟨homogeneous (p 0) (p 1), by
    change M.mulVec (homogeneous (p 0) (p 1)) = 0
    exact (kernel_iff _).2 rfl⟩
  invFun u := ![u.1 3,u.1 5]
  left_inv p := by funext i; fin_cases i <;> rfl
  right_inv u := by apply Subtype.ext; exact ((kernel_iff u.1).1 u.2).symm
  map_add' p q := by
    apply Subtype.ext
    funext i
    fin_cases i <;> simp [homogeneous] <;> ring
  map_smul' a p := by
    apply Subtype.ext
    funext i
    fin_cases i <;> simp [homogeneous] <;> ring

theorem kernel_dimension : Module.finrank ℚ (LinearMap.ker M.mulVecLin) = 2 := by
  simpa using (LinearEquiv.finrank_eq parameters).symm

theorem rank_fourteen : M.rank = 14 := by
  have h := LinearMap.finrank_range_add_finrank_ker M.mulVecLin
  rw [kernel_dimension] at h
  change M.rank+2 = Module.finrank ℚ (Fin 16 → ℚ) at h
  norm_num at h
  omega

end MainTheory.Orbit26PrintedMoments
''')
    return ''.join(parts)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true')
    parser.add_argument('--output', type=Path, default=ROOT/'MainTheory/Orbit26PrintedMoments.lean')
    args = parser.parse_args()
    text = generate()
    if args.check:
        if args.output.read_text(encoding='utf8') != text:
            raise SystemExit('Generated orbit-26 moment source differs')
        print('PASS exact orbit-26 rational moment regeneration')
    else:
        args.output.write_text(text, encoding='utf8', newline='\n')
        print('Generated actual 17-by-16 moment matrix and complete rational affine solution')
