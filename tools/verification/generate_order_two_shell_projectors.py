"""Generate the actual orbit-18/41 shell systems and anchor projectors."""
from pathlib import Path
import re
import sympy as s
ROOT=Path(__file__).resolve().parents[2]
WORK=Path(__file__).resolve().parent
def idx(i):return f'⟨{i},by decide⟩'
def vec(xs):return '!['+','.join(map(str,xs))+']'
def mat(M):return vec(vec('('+str(x)+')' for x in row) for row in M.tolist())
parts=['''import MainTheory.RectangularFlipCharacters
import SixQubit.CodeOrbit18
import SixQubit.CodeOrbit41
import MainTheory.FlipCharacterObstruction

/-! Exact displayed shell systems on the actual fibers and the literal
restricted-Walsh projectors isolating their forced positive anchors. -/
set_option autoImplicit false
set_option maxHeartbeats 16000000
namespace MainTheory.OrderTwoShellProjectors
open scoped BigOperators Matrix
noncomputable section
def characterQ (z x : SS.BitString 6) : ℚ := if SS.bdot z x then -1 else 1
''']
for orbit in (18,41):
    source=(ROOT/f'SixQubit/Orbit{orbit}.lean').read_text(encoding='utf8')
    wordrows=re.findall(r'^def ([yz])(\d+) : SS.BitString 6 := bs (.+?)\s*--\s*([01]{6})',source,re.M)
    words={p:[list(map(int,w)) for _,_,_,w in sorted([row for row in wordrows if row[0]==p],key=lambda row:int(row[1]))] for p in ('y','z')}
    n=len(words['y']);k=3 if orbit==18 else 4
    def coords(w):return (sum(w[:5]),w[5]) if orbit==18 else (sum(w[:4]),w[4],w[5])
    btypes=[(0,0),(4,0),(2,1)] if orbit==18 else [(0,0,0),(1,1,1),(3,0,1),(4,1,0)]
    ttypes=[(2,0),(0,1),(4,1)] if orbit==18 else [(0,0,1),(1,1,0),(3,0,0),(4,1,1)]
    buckets=[[ [j for j,w in enumerate(words[p]) if coords(w)==typ] for typ in types] for p,types in [('y',btypes),('z',ttypes)]]
    q=s.symbols(' '.join('q'+str(i) for i in range(n)));r=s.symbols(' '.join('r'+str(i) for i in range(n)))
    v=q+r;local={str(x):x for x in v}
    masses=[[sum(var[j] for j in bucket) for bucket in bs] for var,bs in zip((q,r),buckets)]
    if orbit==18:
        A,B,C=masses[0];D,E,F=masses[1]
        eqs=[(A+B+C,1),(D+E+F,1),(C,E+F),(2*C,4*F),(4*B+2*C,2*D+4*F),(6*B+C,D+6*F)]
        args='A B C D E F';system='A+B+C=1 ∧ D+E+F=1 ∧ C=E+F ∧ 2*C=4*F ∧ 4*B+2*C=2*D+4*F ∧ 6*B+C=D+6*F'
        values=['1/4','1/4','1/2','1/2','1/4','1/4']
        charindices=[[],[5],[0],[1],[2],[3],[4]];lam=[s.Rational(1,8),s.Rational(-1,4)]+[s.Rational(1,8)]*5
        coordtype='ℕ × ℕ';coordslean='((∑ j : Fin 5, if x ⟨j.val,by omega⟩ then 1 else 0),if x ⟨5,by decide⟩ then 1 else 0)'
    else:
        A,B,C,D=masses[0];E,F,G,H=masses[1]
        eqs=[(A+B+C+D,1),(E+F+G+H,1),(B,H),(B+3*C,4*H),(3*C+6*D,3*G+6*H),(B+C,E+H),(B+D,F+H),(B+3*C+4*D,F+3*G+4*H)]
        args='A B C D E F G H';system='A+B+C+D=1 ∧ E+F+G+H=1 ∧ B=H ∧ B+3*C=4*H ∧ 3*C+6*D=3*G+6*H ∧ B+C=E+H ∧ B+D=F+H ∧ B+3*C+4*D=F+3*G+4*H'
        values=['1/4']*8;charindices=[[],[5],[0],[0,5]];lam=[s.Rational(1,4),s.Rational(-1,4),s.Rational(1,4),s.Rational(-1,4)]
        coordtype='ℕ × ℕ × ℕ';coordslean='((∑ j : Fin 4, if x ⟨j.val,by omega⟩ then 1 else 0),if x ⟨4,by decide⟩ then 1 else 0,if x ⟨5,by decide⟩ then 1 else 0)'
    fields=re.findall(r'^  (n[01]|m[1-6](?:[1-6])?) : (.+) = (.+)$',source,re.M)
    dif=[s.expand(s.sympify(a,locals=local)-s.sympify(b,locals=local)) for _,a,b in fields]
    matrix=s.Matrix([[e.coeff(x) for x in v] for e in dif]);constants=s.Matrix([-e.subs(dict.fromkeys(v,0)) for e in dif])
    independent=list(matrix.T.rref()[1])
    def expression(p,bucket):return '+'.join(f'{p} {idx(j)}' for j in bucket)
    def massvec(p,bs):return vec('('+expression(p,bucket)+')' for bucket in bs)
    nativeargs=' '.join(f'(p {idx(j)})' for j in range(n))+' '+' '.join(f'(q {idx(j)})' for j in range(n))
    normalizedargs=' '.join(f'({p} {str(j) if j<2 else idx(j)})' for p in ('p','q') for j in range(n))
    systemargs=' '.join(f'(bottomMass p {idx(j)})' for j in range(k))+' '+' '.join(f'(topMass q {idx(j)})' for j in range(k))
    point_formula=('(1-2*characterQ (SS.stdBasis ⟨5,by decide⟩) x+'
        '(∑ j : Fin 5, characterQ (SS.stdBasis ⟨j.val,by omega⟩) x))/8' if orbit==18 else
        '(1-characterQ (SS.stdBasis ⟨5,by decide⟩) x+'
        'characterQ (SS.stdBasis 0) x-characterQ (SS.bxor (SS.stdBasis 0) (SS.stdBasis ⟨5,by decide⟩)) x)/4')
    tupletypes=lambda types:vec('('+','.join(map(str,t))+')' for t in types)
    chars=lambda row:'(fun _ => false)' if not row else ('SS.stdBasis '+idx(row[0]) if len(row)==1 else f'SS.bxor (SS.stdBasis {idx(row[0])}) (SS.stdBasis {idx(row[1])})')
    W=s.Matrix([[(-1)**sum(w[j] for j in row) for w in words['z']] for row in charindices]);m=len(charindices)
    assert s.Matrix([lam])*W==s.Matrix([[1]+[0]*(n-1)])
    parts.append(f'''
namespace Orbit{orbit}
open SixQubit.Orbit{orbit}
def bottom : Fin {n} → SS.BitString 6 := {vec('y'+str(j) for j in range(n))}
def top : Fin {n} → SS.BitString 6 := {vec('z'+str(j) for j in range(n))}
def coordinates (x : SS.BitString 6) : {coordtype} := {coordslean}
def bottomTypes : Fin {k} → {coordtype} := {tupletypes(btypes)}
def topTypes : Fin {k} → {coordtype} := {tupletypes(ttypes)}
theorem actual_coordinates :
    (∀ i, coordinates (bottom i)={tupletypes([coords(w) for w in words['y']])} i) ∧
    (∀ i, coordinates (top i)={tupletypes([coords(w) for w in words['z']])} i) := by decide +kernel
theorem shell_types : (∀ x, x ∈ S0 ↔ ∃ j, coordinates x=bottomTypes j) ∧
    (∀ x, x ∈ S1 ↔ ∃ j, coordinates x=topTypes j) := by decide +kernel
theorem point_projector : ∀ x ∈ S1,
    {point_formula}=(if x=z0 then 1 else 0) := by decide +kernel
def bottomMass (p : Fin {n} → ℝ) : Fin {k} → ℝ := {massvec('p',buckets[0])}
def topMass (q : Fin {n} → ℝ) : Fin {k} → ℝ := {massvec('q',buckets[1])}
theorem actual_shell_masses (p q : Fin {n} → ℝ) :
    (∀ j, bottomMass p j=∑ i : Fin {n}, if coordinates (bottom i)=bottomTypes j then p i else 0) ∧
    (∀ j, topMass q j=∑ i : Fin {n}, if coordinates (top i)=topTypes j then q i else 0) := by
  constructor
  · intro j
    simp_rw [actual_coordinates.1]
    fin_cases j <;> norm_num [bottomMass,bottomTypes,
      Fin.sum_univ_succ,Fin.succ] <;> ring
  · intro j
    simp_rw [actual_coordinates.2]
    fin_cases j <;> norm_num [topMass,topTypes,
      Fin.sum_univ_succ,Fin.succ] <;> ring
def Moment (p q : Fin {n} → ℝ) := MomentSystem {nativeargs}
def ShellSystem ({args} : ℝ) : Prop := {system}
theorem shell_system (p q : Fin {n} → ℝ) (hm : Moment p q) : ShellSystem {systemargs} := by
  change MomentSystem {normalizedargs} at hm
  unfold ShellSystem
  refine ⟨{','.join('?_' for _ in eqs)}⟩
''')
    for lhs,rhs in eqs:
        difference=s.expand(lhs-rhs)
        coeff=matrix.extract(independent,list(range(2*n))).T.gauss_jordan_solve(s.Matrix([difference.coeff(x) for x in v]))[0]
        assert (coeff.T*constants.extract(independent,[0]))[0]==-difference.subs(dict.fromkeys(v,0))
        terms=' + '.join(f'({c} : ℝ)*hm.{fields[j][0]}' for c,j in zip(coeff,independent) if c)
        parts.append('  · norm_num [bottomMass,topMass]\n    linear_combination '+terms+'\n')
    eqvars=','.join('h'+str(j) for j in range(len(eqs)))
    if orbit==18:
        parts.append('''theorem character_sum : ∀ x : SS.BitString 6,
    (∑ j : Fin 5, characterQ (SS.stdBasis ⟨j.val,by omega⟩) x)=5-2*(coordinates x).1 := by decide +kernel
''')
    else:
        parts.append(f'''theorem shell_chain ({args} : ℝ) (h : ShellSystem {args}) :
    C=B ∧ E=B ∧ F=D ∧ G=D ∧ D=B := by
  obtain ⟨{eqvars}⟩ := h
  refine ⟨?_,?_,?_,?_,?_⟩ <;> linarith only [{eqvars}]
''')
    parts.append(f'''theorem shell_solution ({args} : ℝ) (h : ShellSystem {args}) :
    {' ∧ '.join(f'{x}={y}' for x,y in zip(args.split(),values))} := by
  obtain ⟨{eqvars}⟩ := h
  refine ⟨{','.join('?_' for _ in args.split())}⟩ <;> linarith only [{eqvars}]
theorem physical_moment (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x=0) (hd : ∀ x, x ∉ S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
    (hkl : SS.HasDistance ![c,d] 3) :
    Moment (fun i => Complex.normSq (c (bottom i))) (fun i => Complex.normSq (d (top i))) :=
  SixQubit.Orbit{orbit}.moments c d hc hd hnc hnd hkl
theorem physical_shell_system (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x=0) (hd : ∀ x, x ∉ S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
    (hkl : SS.HasDistance ![c,d] 3) :
    ShellSystem {' '.join(f'(bottomMass (fun i => Complex.normSq (c (bottom i))) {idx(j)})' for j in range(k))}
      {' '.join(f'(topMass (fun i => Complex.normSq (d (top i))) {idx(j)})' for j in range(k))} :=
  shell_system (fun i => Complex.normSq (c (bottom i))) (fun i => Complex.normSq (d (top i)))
    (physical_moment c d hc hd hnc hnd hkl)
def flip : SS.BitString 6 := SS.stdBasis ⟨5,by decide⟩
def characters : Fin {m} → SS.BitString 6 := {vec(chars(row) for row in charindices)}
def W : Matrix (Fin {m}) (Fin {n}) ℚ := {mat(W)}
def WC : Matrix (Fin {m}) (Fin {n}) ℂ := W.map (Rat.castHom ℂ)
def coefficients : Matrix (Fin 1) (Fin {m}) ℚ := {mat(s.Matrix([lam]))}
def coefficientsC : Matrix (Fin 1) (Fin {m}) ℂ := coefficients.map (Rat.castHom ℂ)
def anchorRow : Matrix (Fin 1) (Fin {n}) ℚ := {mat(s.Matrix([[1]+[0]*(n-1)]))}
def anchorRowC : Matrix (Fin 1) (Fin {n}) ℂ := anchorRow.map (Rat.castHom ℂ)
theorem actual_incidence : Finset.univ.image top=S1.filter (fun y => SS.bxor y flip ∈ S0) := by decide +kernel
theorem sources_injective : Function.Injective top := by decide +kernel
theorem actual_images : ∀ j, SS.bxor (top j) flip=bottom j := by decide +kernel
theorem actual_characters : ∀ i j, W i j=characterQ (characters i) (top j) := by decide +kernel
theorem weights : ∀ i, (⟨flip,characters i⟩ : SS.PauliString 6).wt ≤ 2 := by decide +kernel
theorem matrix_checked : MainTheory.RectangularFlipCharacters.matrix characters top=WC := by
  ext i j
  change (if SS.bdot (characters i) (top j) then (-1 : ℂ) else 1)=(W i j : ℂ)
  rw [actual_characters i j]
  unfold characterQ
  split <;> norm_num
theorem projector_checked : coefficients*W=anchorRow := by
  have he : ∀ i j, (coefficients*W) i j=anchorRow i j := by decide +kernel
  exact Matrix.ext he
theorem complex_projector : coefficientsC*WC=anchorRowC := by
  rw [coefficientsC,WC,anchorRowC,← Matrix.map_mul,projector_checked]
theorem anchor_extraction (v : Fin {n} → ℂ) : anchorRowC *ᵥ v=(fun _ => v 0) := by
  ext i
  fin_cases i
  norm_num [anchorRowC,anchorRow,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,Fin.succ]
def products (c d : SS.State 6 ℂ) : Fin {n} → ℂ :=
  fun j => MainTheory.FlipCharacter.incidenceMonomial c d flip (top j)
theorem physical_rows (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x=0) (hd : ∀ x, x ∉ S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) : WC *ᵥ products c d=0 := by
  rw [← matrix_checked]
  exact MainTheory.RectangularFlipCharacters.physical_rows _ _ c d hc hd hkl
    flip characters top sources_injective actual_incidence weights
theorem physical_anchor_zero (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x=0) (hd : ∀ x, x ∉ S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) : products c d 0=0 := by
  have he : anchorRowC *ᵥ products c d=0 := by
    rw [← complex_projector,← Matrix.mulVec_mulVec,physical_rows c d hc hd hkl,Matrix.mulVec_zero]
  rw [anchor_extraction] at he
  exact congrFun he 0
theorem physical_anchor_norm (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x=0) (hd : ∀ x, x ∉ S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
    (hkl : SS.HasDistance ![c,d] 3) : Complex.normSq (products c d 0)=1/16 := by
  obtain ⟨hp,hq⟩ := (physical_moment c d hc hd hnc hnd hkl).endpoints
  change Complex.normSq (c (bottom 0))=1/4 at hp
  change Complex.normSq (d (top 0))=1/4 at hq
  unfold products
  rw [MainTheory.FlipCharacter.normSq_incidenceMonomial,actual_images,hp,hq]
  norm_num
theorem physical_no_go (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x=0) (hd : ∀ x, x ∉ S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
    (hkl : SS.HasDistance ![c,d] 3) : False := by
  have he := physical_anchor_norm c d hc hd hnc hnd hkl
  rw [physical_anchor_zero c d hc hd hkl,Complex.normSq_zero] at he
  norm_num at he
end Orbit{orbit}
''')
parts.append('\nend\nend MainTheory.OrderTwoShellProjectors\n')
import argparse
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--check',action='store_true')
args=parser.parse_args()
generated=''.join(parts)
target=ROOT/'MainTheory/OrderTwoShellProjectors.lean'
if args.check:
    if target.read_text(encoding='utf8') != generated:
        raise SystemExit('FAIL: regenerate '+str(target.relative_to(ROOT)))
else:
    target.write_text(generated,encoding='utf8',newline='\n')
print('Generated actual shell masses, complete displayed systems and exact physical anchor projectors')
