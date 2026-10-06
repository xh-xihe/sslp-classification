"""Untrusted rational coefficients; all physical rows are checked in Lean."""
from pathlib import Path
import re
import sympy as s

ROOT=Path(__file__).resolve().parents[2]
WORK=Path(__file__).resolve().parent
pieces=['''import SixQubit.CodeOrbit27
import SixQubit.CodeOrbit62
import MainTheory.FlipCharacterObstruction

/-! The literal six-edge matrix and the particular odd triangle printed
in the current SI. Intermediate statements use diagonal moments and actual
physical cross rows, independently of the pre-existing no-code theorems.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
namespace MainTheory.OrderFourWalshRemainingDisplays
open scoped BigOperators Matrix
noncomputable section
''']
for orbit,n,m in ((27,16,12),(62,7,7)):
    q=s.symbols(' '.join('q'+str(i) for i in range(n)))
    r=s.symbols(' '.join('r'+str(i) for i in range(m)))
    variables=q+r
    source=(ROOT/f'SixQubit/Orbit{orbit}.lean').read_text(encoding='utf8')
    fields=re.findall(r'^  (n[01]|m[1-6]|c[1-6][1-6]) : (.+) = (.+)$',source,re.M)
    differences=[s.expand(s.sympify(a,locals={str(v):v for v in variables})-
                          s.sympify(b,locals={str(v):v for v in variables})) for _,a,b in fields]
    A=s.Matrix([[d.coeff(v) for v in variables] for d in differences])
    rhs=s.Matrix([-d.subs({v:0 for v in variables}) for d in differences])
    independent=list(A.T.rref()[1])
    targets=[(q[0],s.Rational(3,8)),(r[0]+r[1]+r[2]+r[3]+r[4]+r[6],s.Rational(5,8))] if orbit==27 else [
        (v,s.Rational(1,4) if v in (q[0],r[6]) else s.Rational(1,8)) for v in variables]
    names=' '.join(str(v) for v in variables)
    pieces.append(f'\nnamespace Orbit{orbit}\nopen SixQubit.Orbit{orbit}\n\n')
    def num(v):return str(v) if v.q==1 else f'({v.p}/{v.q})'
    for k,(expr,value) in enumerate(targets):
        coeff=A.extract(independent,list(range(n+m))).T.gauss_jordan_solve(s.Matrix([expr.coeff(v) for v in variables]))[0]
        assert (coeff.T*rhs.extract(independent,[0]))[0]==value
        terms=' + '.join(f'{num(v)} * hm.{fields[j][0]}' for v,j in zip(coeff,independent) if v)
        pieces.append(f'''theorem consequence{k} {{{names} : ℝ}}
    (hm : MomentSystem {names}) : {expr}={num(value)} := by
  linear_combination {terms}

''')
    def physical(expr):
        text=str(expr)
        for i in range(n-1,-1,-1): text=re.sub(r'\bq'+str(i)+r'\b',f'(Complex.normSq (c y{i}))',text)
        for i in range(m-1,-1,-1): text=re.sub(r'\br'+str(i)+r'\b',f'(Complex.normSq (d z{i}))',text)
        return text
    conclusion=' ∧\n    '.join(physical(expr)+'='+num(value) for expr,value in targets)
    proofs=','.join(f'consequence{k} hm' for k in range(len(targets)))
    pieces.append(f'''theorem physical_probabilities (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x=0) (hd : ∀ x, x ∉ S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
    (hkl : SS.HasDistance ![c,d] 3) :
    {conclusion} := by
  have hm := moments c d hc hd hnc hnd hkl
  exact ⟨{proofs}⟩

''')
    if orbit==27:
        pieces.append('''def sources : Fin 6 → SS.BitString 6 := ![z6,z7,z8,z9,z10,z11]
def destinations : Fin 6 → SS.BitString 6 := ![y0,y1,y2,y3,y4,y5]
def characters : Fin 6 → SS.BitString 6 := ![w0_0,w0_1,w0_2,w0_3,w0_4,w0_5]
def W : Matrix (Fin 6) (Fin 6) ℚ :=
  !![1,1,1,1,1,1;1,1,-1,-1,-1,-1;1,-1,1,-1,-1,-1;
    1,-1,-1,1,-1,-1;1,-1,-1,-1,1,-1;1,-1,-1,-1,-1,1]
def WC : Matrix (Fin 6) (Fin 6) ℂ := fun i j => W i j
def products (c d : SS.State 6 ℂ) : Fin 6 → ℂ :=
  fun j => star (c (destinations j))*d (sources j)
theorem actual_characters : ∀ i j,
    W i j=if SS.bdot (characters i) (sources j) then -1 else 1 := by decide +kernel
theorem actual_incidence : S1.filter (fun y => SS.bxor y ef0 ∈ S0)=
    Finset.univ.image sources := by decide +kernel
theorem actual_images : ∀ j, SS.bxor (sources j) ef0=destinations j := by decide +kernel
theorem weights : ∀ i, (⟨ef0,characters i⟩ : SS.PauliString 6).wt≤2 := by decide +kernel
theorem determinant : W.det= -128 := by decide +kernel
theorem determinant_complex : WC.det= -128 := by
  have he : WC.det=(W.det : ℂ) := ((algebraMap ℚ ℂ).map_det W).symm
  rw [he,determinant]
  norm_num
theorem expansion (c d : SS.State 6 ℂ) : ∀ i,
    offSum c d ef0 (characters i)=(WC.mulVec (products c d)) i := by
  intro i
  fin_cases i
''')
        for k in range(6):
            pieces.append(f'''  · rw [show characters ⟨{k},by decide⟩=w0_{k} from rfl,ex0_{k}]
    norm_num [WC,W,products,sources,destinations,Matrix.mulVec,dotProduct,Fin.sum_univ_succ]
    ring
''')
        pieces.append('''theorem physical_matrix_rows (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x=0) (hd : ∀ x, x ∉ S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) : WC.mulVec (products c d)=0 := by
  ext i
  rw [← expansion]
  exact SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl _ _ (weights i)
theorem physical_all_edges_zero (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x=0) (hd : ∀ x, x ∉ S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) : products c d=0 := by
  have hdW : IsUnit WC.det := by rw [determinant_complex]; norm_num
  calc products c d=(WC⁻¹*WC).mulVec (products c d) := by rw [Matrix.nonsing_inv_mul _ hdW,Matrix.one_mulVec]
    _=WC⁻¹ *ᵥ (WC *ᵥ products c d) := by rw [Matrix.mulVec_mulVec]
    _=0 := by rw [physical_matrix_rows c d hc hd hkl,Matrix.mulVec_zero]

namespace AllCoordinates
def sources (i : Fin 6) : Fin 6 → SS.BitString 6 :=
  Fin.cases (SS.stdBasis i) (fun j : Fin 5 => SS.complement (SS.stdBasis (i.succAbove j)))
def characters (i : Fin 6) : Fin 6 → SS.BitString 6 :=
  Fin.cases (fun _ => false) (fun j : Fin 5 => SS.stdBasis (i.succAbove j))
theorem injective : ∀ i, Function.Injective (sources i) := by decide +kernel
theorem incidence : ∀ i, Finset.univ.image (sources i)=
    S1.filter (fun y => SS.bxor y (SS.stdBasis i) ∈ S0) := by decide +kernel
theorem characters_checked : ∀ i j k,
    W j k=if SS.bdot (characters i j) (sources i k) then -1 else 1 := by decide +kernel
theorem weight_checked : ∀ i j, (⟨SS.stdBasis i,characters i j⟩ : SS.PauliString 6).wt≤2 := by decide +kernel
theorem matrix_checked (i : Fin 6) :
    MainTheory.FlipCharacter.restrictedCharacterMatrix (characters i) (sources i)=WC := by
  ext j k
  change (if SS.bdot (characters i j) (sources i k) then (-1 : ℂ) else 1)=(W j k : ℂ)
  rw [characters_checked i j k]
  split <;> norm_num
theorem first_source : ∀ i, sources i 0=SS.stdBasis i ∧
    SS.bxor (sources i 0) (SS.stdBasis i)=y0 := by decide +kernel
theorem physical_products_zero (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x=0) (hd : ∀ x, x ∉ S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) (i : Fin 6) : ∀ j,
    star (c (SS.bxor (sources i j) (SS.stdBasis i)))*d (sources i j)=0 := by
  apply MainTheory.FlipCharacter.monomials_zero_of_det_ne_zero S0 S1 c d hc hd hkl
    (SS.stdBasis i) (characters i) (sources i) (injective i) (incidence i) (weight_checked i)
  rw [matrix_checked,determinant_complex]
  norm_num
theorem physical_weight_one_zero (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x=0) (hd : ∀ x, x ∉ S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
    (hkl : SS.HasDistance ![c,d] 3) : ∀ i, d (SS.stdBasis i)=0 := by
  have hp := (physical_probabilities c d hc hd hnc hnd hkl).1
  have hn : c y0≠0 := by intro he; rw [he,Complex.normSq_zero] at hp; norm_num at hp
  intro i
  have he := physical_products_zero c d hc hd hkl i 0
  rw [(first_source i).2,(first_source i).1] at he
  exact (mul_eq_zero.1 he).resolve_left (star_ne_zero.2 hn)
end AllCoordinates
''')
    else:
        pieces.append('''def bottom : Fin 7 → SS.BitString 6 := ![y0,y1,y2,y3,y4,y5,y6]
def top : Fin 7 → SS.BitString 6 := ![z6,z5,z4,z3,z2,z1,z0]
def triangle : Fin 3 → SS.BitString 6 := ![y0,y6,y2]
def next : Fin 3 → Fin 3 := ![1,2,0]
def flips : Fin 3 → SS.BitString 6 :=
  ![bs false false false false true true,bs false true false true false false,bs true false true false false false]
def zero : SS.BitString 6 := fun _ => false
def rho (c d : SS.State 6 ℂ) (x : SS.BitString 6) : ℂ := d (SS.complement x)/star (c x)
theorem actual_complements : ∀ i, top i=SS.complement (bottom i) := by decide +kernel
theorem actual_incidence : ∀ k,
    S1.filter (fun y => SS.bxor y (flips k) ∈ S0)=
    {SS.complement (triangle k),SS.complement (triangle (next k))} := by decide +kernel
theorem pairs_ne : ∀ k, SS.complement (triangle k)≠SS.complement (triangle (next k)) := by decide +kernel
theorem actual_images : ∀ k,
    SS.bxor (SS.complement (triangle k)) (flips k)=triangle (next k) ∧
    SS.bxor (SS.complement (triangle (next k))) (flips k)=triangle k := by decide +kernel
theorem zero_signs : ∀ k, SS.bdot zero (SS.complement (triangle k))=false ∧
    SS.bdot zero (SS.complement (triangle (next k)))=false := by decide +kernel
theorem weights : ∀ k, (⟨flips k,zero⟩ : SS.PauliString 6).wt≤2 := by decide +kernel
theorem expansion (c d : SS.State 6 ℂ) (k : Fin 3) :
    offSum c d (flips k) zero=
    star (c (triangle k))*d (SS.complement (triangle (next k)))+
    star (c (triangle (next k)))*d (SS.complement (triangle k)) := by
  unfold offSum
  rw [actual_incidence,Finset.sum_pair (pairs_ne k),(actual_images k).1,(actual_images k).2]
  simp only [(zero_signs k).1,(zero_signs k).2,SixQubit.signMul_false]
  ring
theorem reciprocal_opposition (a b da db : ℂ) (ha : a≠0) (hb : b≠0)
    (he : star a*db+star b*da=0) : db/star b= -(da/star a) := by
  apply (div_eq_iff (star_ne_zero.2 hb)).2
  field_simp [ha] at he ⊢
  linear_combination he
theorem physical_triangle_rows (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x=0) (hd : ∀ x, x ∉ S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) : ∀ k,
    star (c (triangle k))*d (SS.complement (triangle (next k)))+
    star (c (triangle (next k)))*d (SS.complement (triangle k))=0 := by
  intro k
  rw [← expansion]
  exact SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl _ _ (weights k)
theorem physical_all_nonzero (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x=0) (hd : ∀ x, x ∉ S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
    (hkl : SS.HasDistance ![c,d] 3) : ∀ i, c (bottom i)≠0 ∧ d (top i)≠0 := by
  have hm := moments c d hc hd hnc hnd hkl
  intro i
  fin_cases i
''')
        for i in range(7):
            topi=6-i
            pieces.append(f'''  · constructor
    · intro he
      have hp := consequence{i} hm
      norm_num [bottom] at he
      rw [he,Complex.normSq_zero] at hp
      norm_num at hp
    · intro he
      have hp := consequence{7+topi} hm
      norm_num [top] at he
      rw [he,Complex.normSq_zero] at hp
      norm_num at hp
''')
        pieces.append('''theorem triangle_mem : ∀ k, ∃ i, triangle k=bottom i := by decide +kernel
theorem physical_phase_triangle (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x=0) (hd : ∀ x, x ∉ S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
    (hkl : SS.HasDistance ![c,d] 3) : ∀ k,
    rho c d (triangle (next k))= -rho c d (triangle k) := by
  have hn := physical_all_nonzero c d hc hd hnc hnd hkl
  have ht : ∀ k, c (triangle k)≠0 := by
    intro k
    obtain ⟨i,hi⟩ := triangle_mem k
    rw [hi]
    exact (hn i).1
  intro k
  exact reciprocal_opposition _ _ _ _ (ht k) (ht (next k))
    (physical_triangle_rows c d hc hd hkl k)
''')
    pieces.append(f'\nend Orbit{orbit}\n')
pieces.append('\nend\nend MainTheory.OrderFourWalshRemainingDisplays\n')
lean=''.join(pieces)
import argparse
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--check',action='store_true')
args=parser.parse_args()
generated=lean
target=ROOT/'MainTheory/OrderFourWalshRemainingDisplays.lean'
if args.check:
    if target.read_text(encoding='utf8') != generated:
        raise SystemExit('FAIL: regenerate '+str(target.relative_to(ROOT)))
else:
    target.write_text(generated,encoding='utf8',newline='\n')
print('Generated literal orbit-27 and orbit-62 physical derivations')
