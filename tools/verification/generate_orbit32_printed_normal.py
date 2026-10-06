"""Candidate rational row combinations for the literal SI normal form."""
from pathlib import Path
import re
import sympy as s

ROOT=Path(__file__).resolve().parents[2]
native=(ROOT/'SixQubit/Orbit32.lean').read_text(encoding='utf8')
fields=re.findall(r'^  (n[01]|m[1-6]|c[1-6][1-6]) : (.+) = (.+)$',native,re.M)
assert len(fields)==23
variables=s.symbols(' '.join('q'+str(j) for j in range(16))+' '+' '.join('r'+str(j) for j in range(16)))
local={str(v):v for v in variables}
native_expr=[s.sympify(a,locals=local)-s.sympify(b,locals=local) for _,a,b in fields]
q,r=variables[:16],variables[16:]
rows=[]
for e in range(4):
    E,F,G=r[4+e],r[8+e],r[12+e]
    for row,rhs in enumerate(((2*E+2*F-G)/3,(2*E-F+2*G)/3,(-E+2*F+2*G)/3)):
        rows.append((f'reflection{row}_{e}',q[4*row+e]-rhs))
    rhs=s.Rational(1,8)-(E+F+G)/3
    rows.append((f'oddBottom{e}',q[15-e]-rhs))
    rows.append((f'oddTop{e}',r[3-e]-rhs))
for row in range(3):
    rows.append((f'row{row}',sum(r[4+4*row:8+4*row])-s.Rational(1,4)))

def affine_matrix(expressions):
    return s.Matrix([[s.expand(x).coeff(v) for v in variables]+[s.expand(x).subs({v:0 for v in variables})]
                     for x in expressions])
A=affine_matrix(native_expr)
B=affine_matrix([x for _,x in rows])
assert A.rank()==B.rank()==23

def multipliers(matrix,expr):
    h=matrix.T.gauss_jordan_solve(affine_matrix([expr]).T)[0]
    return h.subs({v:0 for x in h for v in x.free_symbols})

def number(v):
    return str(v) if v.q==1 else f'({v.p}/{v.q})'

def expression(expr):
    text=s.sstr(s.expand(expr))
    for v in sorted(variables,key=lambda v:-len(str(v))):
        text=re.sub(r'\b'+str(v)+r'\b',f'({str(v)[0]} ⟨{str(v)[1:]},by decide⟩)',text)
    return text

def proof(coefs,names,prefix):
    return ' + '.join(number(v)+' * '+prefix+name for v,name in zip(coefs,names) if v)

system='MomentSystem '+' '.join(f'({str(v)[0]} ⟨{str(v)[1:]},by decide⟩)' for v in variables)
lean='''import SixQubit.CodeOrbit32

/-! The complete real moment normal form in the SI table coordinates.
All row combinations are kernel checked, with nonnegative boundaries retained.
No final no-code theorem is used to discharge an intermediate equation. -/
set_option autoImplicit false
set_option maxHeartbeats 16000000
namespace MainTheory.Orbit32PrintedMomentNormal
noncomputable section
open SixQubit.Orbit32
open scoped BigOperators

def VectorMoments (q r : Fin 16 → ℝ) : Prop := '''+system+'\n\n'
lean+='structure PrintedNormalForm (q r : Fin 16 → ℝ) : Prop where\n'
for name,x in rows:
    lean+='  '+name+' : '+expression(x)+'=0\n'
lean+='  nonnegQ : ∀ j, 0 ≤ q j\n  nonnegR : ∀ j, 0 ≤ r j\n\n'
lean+='theorem normal_of_moments (q r : Fin 16 → ℝ) (hm : VectorMoments q r) : PrintedNormalForm q r := by\n'
lean+='  change '+system+' at hm\n  constructor\n'
for name,x in rows:
    lean+='  · linear_combination '+proof(multipliers(A,x),[f[0] for f in fields],'hm.')+'\n'
for tag in ('q','r'):
    lean+='  · intro j\n    fin_cases j\n'
    for j in range(16):
        lean+=f'    · exact hm.n{tag}{j}\n'
lean+='\ntheorem moments_of_normal (q r : Fin 16 → ℝ) (hm : PrintedNormalForm q r) : VectorMoments q r := by\n'
lean+='  change '+system+'\n  constructor\n'
for _,x in zip(fields,native_expr):
    lean+='  · linear_combination '+proof(multipliers(B,x),[f[0] for f in rows],'hm.')+'\n'
for tag in ('Q','R'):
    for j in range(16):
        lean+=f'  · exact hm.nonneg{tag} ⟨{j},by decide⟩\n'
lean+='''
theorem complete_normal_form (q r : Fin 16 → ℝ) :
    VectorMoments q r ↔ PrintedNormalForm q r :=
  ⟨normal_of_moments q r,moments_of_normal q r⟩

def bottom : Fin 16 → SS.BitString 6 :=
  ![y0,y1,y2,y3,y4,y5,y6,y7,y8,y9,y10,y11,y12,y13,y14,y15]
def top : Fin 16 → SS.BitString 6 :=
  ![z0,z1,z2,z3,z4,z5,z6,z7,z8,z9,z10,z11,z12,z13,z14,z15]

theorem physical_normal_form (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x=0) (hd : ∀ x, x ∉ S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
    (hkl : SS.HasDistance ![c,d] 3) :
    PrintedNormalForm (fun j => Complex.normSq (c (bottom j)))
      (fun j => Complex.normSq (d (top j))) := by
  apply normal_of_moments
  exact moments c d hc hd hnc hnd hkl

def middle : Fin 4 → Fin 3 → Bool := ![![false,false,false],![false,true,true],![true,false,true],![true,true,false]]
def embed (o u : Fin 3 → Bool) : SS.BitString 6 := ![o 0,o 1,u 0,u 1,u 2,o 2]
def AIndex (e : Fin 4) : Fin 16 := ⟨e.val,by omega⟩
def BIndex (e : Fin 4) : Fin 16 := ⟨4+e.val,by omega⟩
def CIndex (e : Fin 4) : Fin 16 := ⟨8+e.val,by omega⟩
def EIndex (e : Fin 4) : Fin 16 := ⟨4+e.val,by omega⟩
def FIndex (e : Fin 4) : Fin 16 := ⟨8+e.val,by omega⟩
def GIndex (e : Fin 4) : Fin 16 := ⟨12+e.val,by omega⟩
def RIndex (e : Fin 4) : Fin 16 := ⟨15-e.val,by omega⟩
def SIndex (e : Fin 4) : Fin 16 := ⟨3-e.val,by omega⟩
theorem actual_bottom_groups : ∀ e,
    bottom (AIndex e)=embed ![false,false,false] (middle e) ∧
    bottom (BIndex e)=embed ![false,true,true] (middle e) ∧
    bottom (CIndex e)=embed ![true,false,true] (middle e) ∧
    bottom (RIndex e)=embed ![true,true,false] (fun j => !(middle e j)) := by decide +kernel
theorem actual_top_groups : ∀ e,
    top (EIndex e)=embed ![false,true,false] (middle e) ∧
    top (FIndex e)=embed ![true,false,false] (middle e) ∧
    top (GIndex e)=embed ![true,true,true] (middle e) ∧
    top (SIndex e)=embed ![false,false,true] (fun j => !(middle e j)) := by decide +kernel

'''
lean+='theorem reflected (q r : Fin 16 → ℝ) (hm : PrintedNormalForm q r) (e : Fin 4) :\n'
lean+='  q (AIndex e)=(2*r (EIndex e)+2*r (FIndex e)-r (GIndex e))/3 ∧\n'
lean+='  q (BIndex e)=(2*r (EIndex e)-r (FIndex e)+2*r (GIndex e))/3 ∧\n'
lean+='  q (CIndex e)=(-r (EIndex e)+2*r (FIndex e)+2*r (GIndex e))/3 := by\n  fin_cases e\n'
for e in range(4):
    lean+='  · constructor\n'
    for row in range(3):
        if row==1:
            lean+='    · constructor\n'
        indent='    · ' if row==0 else '      · '
        lean+=indent+f'have he := hm.reflection{row}_{e}\n'
        indent='      ' if row==0 else '        '
        lean+=indent+'norm_num at he\n'+indent+'norm_num [AIndex,BIndex,CIndex,EIndex,FIndex,GIndex,Fin.succ]\n'+indent+'linear_combination he\n'
lean+='''
theorem rowsums (q r : Fin 16 → ℝ) (hm : PrintedNormalForm q r) :
    (∑ e : Fin 4, r (EIndex e))=1/4 ∧ (∑ e : Fin 4, r (FIndex e))=1/4 ∧
      (∑ e : Fin 4, r (GIndex e))=1/4 := by
  have h0 := hm.row0
  have h1 := hm.row1
  have h2 := hm.row2
  norm_num at h0 h1 h2
  norm_num [Fin.sum_univ_succ,Fin.succ,EIndex,FIndex,GIndex]
  exact ⟨by linear_combination h0,by linear_combination h1,by linear_combination h2⟩
'''
lean+='theorem oddweights (q r : Fin 16 → ℝ) (hm : PrintedNormalForm q r) (e : Fin 4) :\n'
lean+='  q (RIndex e)=1/8-(r (EIndex e)+r (FIndex e)+r (GIndex e))/3 ∧\n'
lean+='  r (SIndex e)=1/8-(r (EIndex e)+r (FIndex e)+r (GIndex e))/3 := by\n  fin_cases e\n'
for e in range(4):
    lean+=f'  · have h0 := hm.oddBottom{e}\n    have h1 := hm.oddTop{e}\n'
    lean+='    norm_num at h0 h1\n    norm_num [RIndex,SIndex,EIndex,FIndex,GIndex,Fin.succ]\n'
    lean+='    exact ⟨by linear_combination h0,by linear_combination h1⟩\n'
lean+='''
def parameters (r : Fin 16 → ℝ) : Fin 12 → ℝ := fun j => r ⟨4+j.val,by omega⟩
theorem parameter_injectivity (q r q' r' : Fin 16 → ℝ)
    (hm : PrintedNormalForm q r) (hn : PrintedNormalForm q' r')
    (he : parameters r=parameters r') : q=q' ∧ r=r' := by
'''
for j in range(12):
    lean+=f'  have h{j} := congrFun he (⟨{j},by decide⟩ : Fin 12)\n'
    lean+=f"  change r ⟨{j+4},by decide⟩=r' ⟨{j+4},by decide⟩ at h{j}\n"
projection=s.zeros(12,32)
for j in range(12):
    projection[j,20+j]=1
homogeneous=B[:,:32].col_join(projection)
lean+='  constructor\n'
for offset,name in [(0,'q'),(16,'r')]:
    lean+='  · funext j\n    fin_cases j\n'
    for j in range(16):
        target=s.zeros(32,1)
        target[offset+j]=1
        coeff=homogeneous.T.gauss_jordan_solve(target)[0]
        coeff=coeff.subs({v:0 for x in coeff for v in x.free_symbols})
        terms=[]
        for c,(field,_) in zip(coeff[:len(rows)],rows):
            if c:
                terms += [number(c)+' * hm.'+field,number(-c)+' * hn.'+field]
        terms += [number(c)+' * h'+str(k) for k,c in enumerate(coeff[len(rows):]) if c]
        lean+=f"    · change {name} ⟨{j},by decide⟩={name}' ⟨{j},by decide⟩\n"
        lean+='      linear_combination '+' + '.join(terms)+'\n'
lean+='\nend\nend MainTheory.Orbit32PrintedMomentNormal\n'
import argparse
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--check',action='store_true')
args=parser.parse_args()
generated=lean
target=ROOT/'MainTheory/Orbit32PrintedMomentNormal.lean'
if args.check:
    if target.read_text(encoding='utf8') != generated:
        raise SystemExit('FAIL: regenerate '+str(target.relative_to(ROOT)))
else:
    target.write_text(generated,encoding='utf8',newline='\n')
print('Generated 23 independent printed normal equations, both directions')
