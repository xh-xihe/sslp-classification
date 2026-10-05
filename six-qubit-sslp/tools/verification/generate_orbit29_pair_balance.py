"""Generate the four-pair parallelism argument, retaining checked algebra."""
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2]
WORK=Path(__file__).resolve().parent
def fin(i): return f'⟨{i},by decide⟩'
cases=[]
for i in range(4):
    for j in range(4):
        if i==j:
            cases.append('  · ring')
        else:
            k,l=[n for n in range(4) if n not in (i,j)]
            cases.append(f'''  · exact SixQubit.Pair29.par_edge (Q {fin(i)}) (Q {fin(j)}) (Q {fin(k)}) (Q {fin(l)})
      (s {fin(i)}) (t {fin(i)}) (s {fin(j)}) (t {fin(j)}) (s {fin(k)}) (t {fin(k)})
      (by linarith) (hle _) (hle _) (hn _) (hn _) (hm _) (hm _) (hm _)
      (hd _ _) (hd _ _) (hd _ _)''')
source='''import SixQubit.Pair29

/-! Pair probabilities and the non-diagonal orthogonality consequences,
without using the final orbit-29 impossibility theorem. -/
set_option autoImplicit false
namespace MainTheory.Orbit29PairBalance
open scoped BigOperators
noncomputable section

theorem parallel_all (s t : Fin 4 → ℂ) (Q : Fin 4 → ℝ)
    (hs : (∑ i, Q i)=3/4) (hle : ∀ i, Q i≤1/4) (hn : ∀ i, 0≤Q i)
    (hm : ∀ i, s i*star (s i)+t i*star (t i)=(Q i : ℂ))
    (hd : ∀ i j, ((Q i+Q j-1/4 : ℝ) : ℂ)*(s i*t j-s j*t i)=0) :
    ∀ i j, s i*t j-s j*t i=0 := by
  norm_num [Fin.sum_univ_succ,Fin.succ] at hs
  change Q ⟨0,by decide⟩+(Q ⟨1,by decide⟩+(Q ⟨2,by decide⟩+Q ⟨3,by decide⟩))=3/4 at hs
  intro i j
  fin_cases i <;> fin_cases j
'''+ '\n'.join(cases)+'''

theorem balanced_high (s t : Fin 4 → ℂ)
    (hm : (∑ i, Complex.normSq (s i))+(∑ i, Complex.normSq (t i))=3/4)
    (he : (∑ i, Complex.normSq (s i))=(∑ i, Complex.normSq (t i)))
    (hp : ∀ i j, s i*t j-s j*t i=0) :
    ∀ i, Complex.normSq (s i)=Complex.normSq (t i) := by
  have hs : (∑ i, Complex.normSq (s i))=3/8 := by linarith
  have ht : (∑ i, Complex.normSq (t i))=3/8 := by linarith
  intro i
  have hprod (j : Fin 4) : Complex.normSq (s i)*Complex.normSq (t j)=
      Complex.normSq (s j)*Complex.normSq (t i) := by
    have h := congrArg Complex.normSq (sub_eq_zero.mp (hp i j))
    simpa only [Complex.normSq_mul] using h
  have key : Complex.normSq (s i)*(∑ j, Complex.normSq (t j))=
      Complex.normSq (t i)*(∑ j, Complex.normSq (s j)) := by
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    simpa only [mul_comm] using hprod j
  rw [hs,ht] at key
  nlinarith

theorem perpendicular_balance (c0 c1 s t : ℂ)
    (ho : star c0*s+star c1*t=0)
    (hb : Complex.normSq s=Complex.normSq t)
    (hp : 0 < Complex.normSq s+Complex.normSq t) :
    Complex.normSq c0=Complex.normSq c1 := by
  have he : star c0*s=-(star c1*t) := by linear_combination ho
  have hn := congrArg Complex.normSq he
  simp only [Complex.normSq_mul,Complex.normSq_neg,Complex.star_def,
    Complex.normSq_conj] at hn
  have ht : 0 < Complex.normSq t := by linarith
  rw [hb] at hn
  exact mul_right_cancel₀ (ne_of_gt ht) hn

end
end MainTheory.Orbit29PairBalance
'''
import argparse
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--check',action='store_true')
args=parser.parse_args()
generated=source
target=ROOT/'MainTheory/Orbit29PairBalance.lean'
if args.check:
    if target.read_text(encoding='utf8') != generated:
        raise SystemExit('FAIL: regenerate '+str(target.relative_to(ROOT)))
else:
    target.write_text(generated,encoding='utf8',newline='\n')
