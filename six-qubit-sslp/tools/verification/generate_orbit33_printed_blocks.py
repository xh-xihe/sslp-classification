"""Discover rational row combinations; the emitted Lean checks each identity."""
from pathlib import Path
import re
import sympy as s

ROOT=Path(__file__).resolve().parents[2]
native=(ROOT/'SixQubit/Orbit33.lean').read_text(encoding='utf8')
fields=re.findall(r'^  (n[01]|m[1-6]|c[1-6][1-6]) : (.+) = (.+)$',native,re.M)
assert len(fields)==23
variables=s.symbols(' '.join('q'+str(j) for j in range(12))+' '+' '.join('r'+str(j) for j in range(12)))
local={str(v):v for v in variables}
expressions=[s.sympify(a,locals=local)-s.sympify(b,locals=local) for _,a,b in fields]
q,r=variables[:12],variables[12:]
R=list(map(s.Rational,['3/10','1/5','1/5','1/10','1/10','1/10']))
C=s.Matrix([[1,1,1,1,1,1],[1,1,-1,-1,-1,-1],[1,-1,1,-1,-1,-1],
            [1,-1,-1,1,1,-1],[1,-1,-1,1,-1,1],[1,-1,-1,-1,1,1]])
inverse=C.inv()

def affine_matrix(xs):
    return s.Matrix([[s.expand(x).coeff(v) for v in variables]+[s.expand(x).subs({v:0 for v in variables})] for x in xs])
A=affine_matrix(expressions)
def multipliers(x):
    solution=A.T.gauss_jordan_solve(affine_matrix([x]).T)[0]
    return solution.subs({v:0 for term in solution for v in term.free_symbols})
def number(x):
    return str(x) if x.q==1 else f'({x.p}/{x.q})'
def expression(x):
    text=s.sstr(s.expand(x))
    for v in sorted(variables,key=lambda x:-len(str(x))):
        text=re.sub(r'\b'+str(v)+r'\b',f'({str(v)[0]} ⟨{str(v)[1:]},by decide⟩)',text)
    return text
def combination(x):
    return ' + '.join(number(v)+' * hm.'+name for v,(name,_,_) in zip(multipliers(x),fields) if v)
system='MomentSystem '+' '.join(f'({str(v)[0]} ⟨{str(v)[1:]},by decide⟩)' for v in variables)
lean='''import SixQubit.CodeOrbit33
import MainTheory.Orbit33PrintedReflection

/-! Every printed block norm and matrix reflection in actual physical coordinates.
The rational row combinations are checked by Lean, independently of no-code.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
namespace MainTheory.Orbit33PrintedBlocks
open SixQubit.Orbit33
open scoped BigOperators
noncomputable section

def VectorMoments (q r : Fin 12 → ℝ) : Prop := '''+system+'\n\n'
for tag,vec in [('bottom',q),('top',r)]:
    for i in range(6):
        j=i if tag=='bottom' else 5-i
        x=vec[j]+vec[j+6]-R[i]
        lean+=f'theorem norm_{tag}_{i} (q r : Fin 12 → ℝ) (hm : VectorMoments q r) : {expression(x)}=0 := by\n'
        lean+='  change '+system+' at hm\n  linear_combination '+combination(x)+'\n\n'
for bit in range(2):
    for i in range(6):
        x=q[6*bit+i]+r[6*bit+5-i]-2*R[i]*sum(q[6*bit:6*bit+6])
        lean+=f'theorem diagonal_{bit}_{i} (q r : Fin 12 → ℝ) (hm : VectorMoments q r) : {expression(x)}=0 := by\n'
        lean+='  change '+system+' at hm\n  linear_combination '+combination(x)+'\n\n'
dresses=[0,6,5,11,4,10,3,9,2,8,1,7]
for i in range(6):
    lean+=f'theorem off_diagonal_{i} (c d : SS.State 6 ℂ)\n'
    for w in dresses:
        lean+=f'    (Dg_w{w} : diagBot c ef0 w{w}=diagTop d ef0 w{w})\n'
    lean+=f'    : c y{i} * star (c y{i+6}) + d z{5-i} * star (d z{11-i})\n'
    lean+='      = '+number(2*R[i])+' * ('+' + '.join(f'c y{j} * star (c y{j+6})' for j in range(6))+') := by\n'
    for w in dresses:
        lean+=f'  rw [dbot_w{w},dtop_w{w}] at Dg_w{w}\n'
    lean+='  linear_combination '+' + '.join(f'({number(-inverse[i,k]*(1 if k==0 else -1)/2)} : ℂ) * Dg_w{w}'
       for k,(w0,w1) in enumerate([(0,6),(5,11),(4,10),(3,9),(2,8),(1,7)]) for w in (w0,w1))+'\n\n'
lean+='''
def bottom (i : Fin 6) (r : Fin 2) : SS.BitString 6 :=
  ![![y0,y1,y2,y3,y4,y5],![y6,y7,y8,y9,y10,y11]] r i
def top (i : Fin 6) (r : Fin 2) : SS.BitString 6 :=
  ![![z5,z4,z3,z2,z1,z0],![z11,z10,z9,z8,z7,z6]] r i
def CBlock (c : SS.State 6 ℂ) (i : Fin 6) : Fin 2 → ℂ := fun r => c (bottom i r)
def DBlock (d : SS.State 6 ℂ) (i : Fin 6) : Fin 2 → ℂ := fun r => d (top i r)
def outer (v : Fin 2 → ℂ) : Matrix (Fin 2) (Fin 2) ℂ := fun r s => v r * star (v s)
def rho (c : SS.State 6 ℂ) : Matrix (Fin 2) (Fin 2) ℂ := ∑ i, outer (CBlock c i)
def R : Fin 6 → ℝ := ![3/10,1/5,1/5,1/10,1/10,1/10]
def nativeBottom : Fin 12 → SS.BitString 6 := ![y0,y1,y2,y3,y4,y5,y6,y7,y8,y9,y10,y11]
def nativeTop : Fin 12 → SS.BitString 6 := ![z0,z1,z2,z3,z4,z5,z6,z7,z8,z9,z10,z11]
def ActualMoments (c d : SS.State 6 ℂ) : Prop :=
  VectorMoments (fun j => Complex.normSq (c (nativeBottom j)))
    (fun j => Complex.normSq (d (nativeTop j)))

theorem actual_bottom : ∀ i r, bottom i r=![r=1,y0 1,y0 2,y0 3,y0 4,y0 5] ∨ True := by
  intros; trivial

theorem block_norms (c d : SS.State 6 ℂ) (hm : ActualMoments c d) (i : Fin 6) :
    (∑ r : Fin 2, Complex.normSq (CBlock c i r))=R i ∧
    (∑ r : Fin 2, Complex.normSq (DBlock d i r))=R i := by
  fin_cases i
'''
# The literal word bridge replaces this placeholder before any draft compilation.
lean=lean.replace('theorem actual_bottom : ∀ i r, bottom i r=![r=1,y0 1,y0 2,y0 3,y0 4,y0 5] ∨ True := by\n  intros; trivial\n', '''def tail : Fin 6 → SS.BitString 5 :=
  ![![false,false,false,false,false],![false,true,true,true,true],
    ![true,false,true,true,true],![true,true,false,false,true],
    ![true,true,false,true,false],![true,true,true,false,false]]
def embed (r : Fin 2) (t : SS.BitString 5) : SS.BitString 6 :=
  ![r=1,t 0,t 1,t 2,t 3,t 4]
theorem actual_words : ∀ i r,
    bottom i r=embed r (tail i) ∧ top i r=embed r (fun j => !(tail i j)) := by decide +kernel
theorem actual_fibers :
    Finset.univ.image (fun p : Fin 6 × Fin 2 => bottom p.1 p.2)=S0 ∧
    Finset.univ.image (fun p : Fin 6 × Fin 2 => top p.1 p.2)=S1 := by decide +kernel
def character (i j : Fin 6) : ℚ := if i=0 then 1 else
  if tail j ⟨i.val-1,by have := i.isLt; omega⟩ then -1 else 1
theorem actual_characters : MainTheory.Orbit33PrintedReflection.C=character := by decide +kernel
''')
for i in range(6):
    lean+=f'  · have hb := norm_bottom_{i} _ _ hm\n    have ht := norm_top_{i} _ _ hm\n'
    lean+='    norm_num [nativeBottom,nativeTop] at hb ht\n'
    lean+='    norm_num [CBlock,DBlock,bottom,top,R,Fin.sum_univ_succ,Fin.succ]\n'
    lean+='    exact ⟨by linear_combination hb,by linear_combination ht⟩\n'
lean+='''
theorem matrix_reflection (c d : SS.State 6 ℂ) (hm : ActualMoments c d)
'''
for w in dresses:
    lean+=f'    (Dg_w{w} : diagBot c ef0 w{w}=diagTop d ef0 w{w})\n'
lean+='    (i : Fin 6) : outer (CBlock c i)+outer (DBlock d i)=(2*(R i : ℂ)) • rho c := by\n'
lean+='  ext r s\n  fin_cases i\n'
for i in range(6):
    lean+='  · fin_cases r <;> fin_cases s\n'
    for rr,ss in ((0,0),(0,1),(1,0),(1,1)):
        if rr==ss:
            lean+=f'    · have h := diagonal_{rr}_{i} _ _ hm\n'
            lean+='      norm_num [nativeBottom,nativeTop] at h\n'
            lean+='      have hc := congrArg (fun x : ℝ => (x : ℂ)) h\n      push_cast at hc\n'
            lean+='      simp only [Complex.normSq_eq_conj_mul_self] at hc\n'
        else:
            lean+=f'    · have hc := off_diagonal_{i} c d '+' '.join(f'Dg_w{w}' for w in dresses)+'\n'
            if rr==1:
                lean+='      have hc := congrArg star hc\n      simp only [star_add,star_mul\',star_star,star_div₀,star_ofNat] at hc\n'
        if rr!=ss:
            lean+='      norm_num at hc\n'
        lean+='      norm_num [outer,CBlock,DBlock,bottom,top,rho,R,Fin.sum_univ_succ,Fin.succ]\n'
        lean+='      linear_combination hc\n'
lean+='''
theorem physical_norms_and_reflection (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x=0) (hd : ∀ x, x ∉ S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
    (hkl : SS.HasDistance ![c,d] 3) :
    (∀ i, (∑ r : Fin 2, Complex.normSq (CBlock c i r))=R i ∧
      (∑ r : Fin 2, Complex.normSq (DBlock d i r))=R i) ∧
    (∀ i, outer (CBlock c i)+outer (DBlock d i)=(2*(R i : ℂ)) • rho c) := by
  have hm : ActualMoments c d := moments c d hc hd hnc hnd hkl
  refine ⟨block_norms c d hm,?_⟩
  intro i
  exact matrix_reflection c d hm
'''
for w in dresses:
    lean+=f'    (SixQubit.diagOn_eq_of_hasDistance S0 S1 c d hc hd hkl ef0 w{w} (by decide))\n'
lean+='    i\n\n'
lean+='''theorem positive_R : ∀ i, 0<R i := by intro i; fin_cases i <;> norm_num [R]

theorem physical_blocks_nonzero (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x=0) (hd : ∀ x, x ∉ S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
    (hkl : SS.HasDistance ![c,d] 3) (i : Fin 6) : CBlock c i≠0 ∧ DBlock d i≠0 := by
  have hn := (physical_norms_and_reflection c d hc hd hnc hnd hkl).1 i
  constructor
  · intro he
    have hx := hn.1
    rw [he] at hx
    norm_num at hx
    exact (ne_of_gt (positive_R i)) hx.symm
  · intro he
    have hx := hn.2
    rw [he] at hx
    norm_num at hx
    exact (ne_of_gt (positive_R i)) hx.symm

def near (i : Fin 3) : Fin 6 := ⟨i.val,by omega⟩
def far (j : Fin 3) : Fin 6 := ⟨j.val+3,by omega⟩
def crossFlip (i j : Fin 3) : SS.BitString 6 := SS.bxor (bottom (near i) 0) (top (far j) 0)

theorem cross_weight : ∀ i j, (⟨crossFlip i j,w0⟩ : SS.PauliString 6).wt≤2 := by decide +kernel
theorem zero_dressing : ∀ x : SS.BitString 6, SS.bdot w0 x=false := by decide +kernel
theorem cross_incidence : ∀ i j,
    S1.filter (fun y => SS.bxor y (crossFlip i j) ∈ S0)=
      {top (near i) 0,top (near i) 1,top (far j) 0,top (far j) 1} := by decide +kernel
'''
def fin(j):
    return f'⟨{j},by decide⟩'
for i in range(3):
    for j in range(3):
        fi,fj=fin(i),fin(j)
        lean+=f'\ntheorem cross_scalar_{i}_{j} (c d : SS.State 6 ℂ) :\n'
        lean+=f'    offSum c d (crossFlip {fi} {fj}) w0=\n'
        lean+=f'      (∑ r : Fin 2, (star (CBlock c (far {fj}) r) * DBlock d (near {fi}) r +\n'
        lean+=f'        star (CBlock c (near {fi}) r) * DBlock d (far {fj}) r)) := by\n'
        lean+='  unfold offSum\n'
        lean+=f'  rw [cross_incidence {fi} {fj}]\n'
        lean+='  rw [Finset.sum_insert (by decide),Finset.sum_insert (by decide),Finset.sum_insert (by decide),Finset.sum_singleton]\n'
        for source,target in [('near '+fi,'far '+fj),('far '+fj,'near '+fi)]:
            for bit in range(2):
                lean+=f'  rw [show SS.bxor (top ({source}) {bit}) (crossFlip {fi} {fj})=bottom ({target}) {bit} by decide]\n'
        lean+='  simp only [zero_dressing,SixQubit.signMul_false]\n'
        lean+='  norm_num [CBlock,DBlock,bottom,top,near,far,Fin.sum_univ_succ,Fin.succ]\n  ring\n'
lean+='''
theorem physical_complete_cross (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x=0) (hd : ∀ x, x ∉ S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) (i j : Fin 3) :
    (∑ r : Fin 2, (star (CBlock c (far j) r) * DBlock d (near i) r +
      star (CBlock c (near i) r) * DBlock d (far j) r))=0 := by
  have h : offSum c d (crossFlip i j) w0=0 :=
    SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl (crossFlip i j) w0 (cross_weight i j)
  fin_cases i <;> fin_cases j
'''
for i in range(3):
    for j in range(3):
        lean+=f'  · rw [cross_scalar_{i}_{j}] at h\n    exact h\n'
lean+='''
def mixed (v w : Fin 2 → ℂ) : Matrix (Fin 2) (Fin 2) ℂ := fun r s => v r * star (w s)
def pairIndex (i : Fin 2) : Fin 6 := ⟨i.val+1,by omega⟩
theorem physical_rankone_pairs (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x=0) (hd : ∀ x, x ∉ S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) (i : Fin 2) :
    mixed (DBlock d 0) (CBlock c (pairIndex i))+
      mixed (DBlock d (pairIndex i)) (CBlock c 0)=0 := by
  ext r s
  fin_cases i <;> fin_cases r <;> fin_cases s
'''
for i in range(2):
    for rr,ss in ((0,0),(0,1),(1,0),(1,1)):
        flip=2*i+1+(rr!=ss)
        lean+=f'  · have h := xr{i+1}_{rr}{ss} c d\n'
        for w in (0,6):
            lean+=f'      (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl ef{flip} w{w} (by decide))\n'
        lean+='    simpa [mixed,CBlock,DBlock,bottom,top,pairIndex,add_comm] using h\n'
for i in (1,2):
    e=2*i-1
    lean+=f'\ndef RankOneRows{i} (c d : SS.State 6 ℂ) : Prop :=\n'
    lean+=f'  offSum c d ef{e} w0=0 ∧ offSum c d ef{e} w6=0 ∧\n'
    lean+=f'  offSum c d ef{e+1} w0=0 ∧ offSum c d ef{e+1} w6=0\n'
    lean+=f'\ntheorem rankone_rows_iff_{i} (c d : SS.State 6 ℂ) : RankOneRows{i} c d ↔\n'
    lean+=f'    mixed (DBlock d 0) (CBlock c ⟨{i},by decide⟩)+\n'
    lean+=f'      mixed (DBlock d ⟨{i},by decide⟩) (CBlock c 0)=0 := by\n'
    lean+='  constructor\n  · rintro ⟨h0,h6,k0,k6⟩\n    ext r s\n    fin_cases r <;> fin_cases s\n'
    for rr,ss in ((0,0),(0,1),(1,0),(1,1)):
        names='k0 k6' if rr!=ss else 'h0 h6'
        lean+=f'    · have he := xr{i}_{rr}{ss} c d {names}\n'
        lean+='      simpa [mixed,CBlock,DBlock,bottom,top,add_comm] using he\n'
    lean+='  · intro h\n'
    for rr,ss in ((0,0),(0,1),(1,0),(1,1)):
        lean+=f'    have h{rr}{ss} := congrFun (congrFun h {rr}) {ss}\n'
    lean+='    norm_num [mixed,CBlock,DBlock,bottom,top] at h00 h01 h10 h11\n'
    lean+=f'    unfold RankOneRows{i}\n    refine ⟨?_,?_,?_,?_⟩\n'
    for ix,(flip,w,comb) in enumerate(((e,0,'h00+h11'),(e,6,'h00-h11'),(e+1,0,'h01+h10'),(e+1,6,'h01-h10'))):
        prefix='    · '
        indent='      '
        lean+=prefix+f'rw [ex{flip}_w{w}]\n'+indent+'norm_num\n'+indent+'linear_combination '+comb+'\n'
lean+='''
def evaluation (F : Matrix (Fin 2) (Fin 2) ℂ) (v : Fin 2 → ℂ) : ℂ := Matrix.trace (F*outer v)

theorem evaluation_formula (F : Matrix (Fin 2) (Fin 2) ℂ) (v : Fin 2 → ℂ) :
    evaluation F v=(∑ r : Fin 2, ∑ s : Fin 2, star (v r)*F r s*v s) := by
  simp only [evaluation,Matrix.trace,Matrix.diag,Matrix.mul_apply,outer]
  simp only [Fin.sum_univ_two]
  ring

theorem scalar_reflection_of_matrix (c d : SS.State 6 ℂ)
    (h : ∀ i, outer (CBlock c i)+outer (DBlock d i)=(2*(R i : ℂ)) • rho c)
    (F : Matrix (Fin 2) (Fin 2) ℂ) (i : Fin 6) :
    evaluation F (CBlock c i)+evaluation F (DBlock d i)=
      2*(R i : ℂ)*(∑ j, evaluation F (CBlock c j)) := by
  have he := congrArg (fun A => Matrix.trace (F*A)) (h i)
  simpa [evaluation,rho,Matrix.mul_add,Matrix.mul_sum,Matrix.mul_smul,
    Matrix.trace_add,Matrix.trace_sum,Matrix.trace_smul] using he

def entryMatrix (r s : Fin 2) : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j => if i=s ∧ j=r then 1 else 0

theorem matrix_pairings_iff (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    A=B ↔ ∀ F : Matrix (Fin 2) (Fin 2) ℂ, Matrix.trace (F*A)=Matrix.trace (F*B) := by
  constructor
  · intro h F; rw [h]
  · intro h
    ext r s
    have he := h (entryMatrix r s)
    fin_cases r <;> fin_cases s <;>
      norm_num [entryMatrix,Matrix.trace,Matrix.diag,Matrix.mul_apply,Fin.sum_univ_succ,Fin.succ] at he ⊢ <;> exact he

theorem matrix_reflection_iff (c d : SS.State 6 ℂ) :
    (∀ i, outer (CBlock c i)+outer (DBlock d i)=(2*(R i : ℂ)) • rho c) ↔
    (∀ F : Matrix (Fin 2) (Fin 2) ℂ, ∀ i,
      evaluation F (CBlock c i)+evaluation F (DBlock d i)=
        2*(R i : ℂ)*(∑ j, evaluation F (CBlock c j))) := by
  constructor
  · intro h F i
    exact scalar_reflection_of_matrix c d h F i
  · intro h i
    apply (matrix_pairings_iff _ _).2
    intro F
    simpa [evaluation,rho,Matrix.mul_add,Matrix.mul_sum,Matrix.mul_smul,
      Matrix.trace_add,Matrix.trace_sum,Matrix.trace_smul] using h F i

end
end MainTheory.Orbit33PrintedBlocks
'''
import argparse
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--check',action='store_true')
args=parser.parse_args()
generated=lean
target=ROOT/'MainTheory/Orbit33PrintedBlocks.lean'
if args.check:
    if target.read_text(encoding='utf8') != generated:
        raise SystemExit('FAIL: regenerate '+str(target.relative_to(ROOT)))
else:
    target.write_text(generated,encoding='utf8',newline='\n')
print('Emitted all twelve norms and all twenty-four matrix-reflection entries')
