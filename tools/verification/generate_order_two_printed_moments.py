"""Literal real normal forms; SymPy supplies coefficients only, never proofs."""
from pathlib import Path
import re
import sympy as s

ROOT=Path(__file__).resolve().parents[2]
WORK=Path(__file__).resolve().parent
a,b,g,t=s.symbols('a b g t')
R=s.Rational
DATA={
42:([R(1,4),R(1,4),R(1,4)-a-b-g,R(1,4)-a-b-g,a,a,b,b,g,g],
    None,[a,b,g],['q4','q6','q8'],[a,b,g,R(1,4)-a-b-g]),
43:([R(1,4),R(1,4),R(1,4)-a-b-g,R(1,4)-a-b-g,a,a,b,b,g,g],
    None,[a,b,g],['q4','q6','q8'],[a,b,g,R(1,4)-a-b-g]),
44:([R(1,4)-a-g,R(1,4)-a-g,a,a,R(1,4)-b,R(1,4)-b,b,b,g,g],
    None,[a,b,g],['q2','q6','q8'],[a,b,g,R(1,4)-a-g,R(1,4)-b]),
46:([R(1,4)-a,R(1,4)-a,a,a,R(1,4)-b-g,R(1,4)-b-g,b,b,g,g],
    None,[a,b,g],['q2','q6','q8'],[a,b,g,R(1,4)-a,R(1,4)-b-g]),
}

def text(v):return str(s.expand(v)).replace('**','^')
def num(v):return str(v) if v.q==1 else f'({v.p}/{v.q})'
pieces=['\n'.join(f'import SixQubit.CodeOrbit{o}' for o in DATA)+'''
import MainTheory.OrderEightSupportDisplays

/-! Both directions of the literal SI probability normal forms, over ℝ.
The rational row combinations are checked against the actual native moments.
The source words and both probability boundaries are retained explicitly.
No final no-code theorem is used to derive any normal form.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
namespace MainTheory.OrderTwoPrintedMoments
noncomputable section
''']
for orbit,(bp,tp,params,extract,domain) in DATA.items():
    if tp is None:tp=bp[::-1] if orbit==50 else bp
    n,m=len(bp),len(tp)
    q=s.symbols(' '.join('q'+str(i) for i in range(n)))
    r=s.symbols(' '.join('r'+str(i) for i in range(m)))
    variables=q+r
    local={str(v):v for v in variables}
    subst=dict(zip(params,[local[v] for v in extract]))
    source=(ROOT/f'SixQubit/Orbit{orbit}.lean').read_text(encoding='utf8')
    fields=re.findall(r'^  (n[01]|m[1-6](?:[1-6])?|c[1-6][1-6]) : (.+) = (.+)$',source,re.M)
    assert len(fields)==23,(orbit,len(fields))
    differences=[s.expand(s.sympify(lhs,locals=local)-s.sympify(rhs,locals=local)) for _,lhs,rhs in fields]
    A=s.Matrix([[d.coeff(v) for v in variables] for d in differences])
    constants=s.Matrix([-d.subs({v:0 for v in variables}) for d in differences])
    independent=list(A.T.rref()[1])
    words=[]
    for prefix,size in [('y',n),('z',m)]:
        wordrows=re.findall(r'^def '+prefix+r'(\d+) : SS.BitString 6 := bs (.+?)\s*--\s*([01]{6})',source,re.M)
        assert len(wordrows)==size,(orbit,prefix,len(wordrows))
        words.append([int(w,2) for _,_,w in sorted(wordrows,key=lambda row:int(row[0]))])
    if orbit in (49,50,51):assert all(x^y==63 for x,y in zip(words[0],words[1][::-1] if orbit==50 else words[1])),orbit
    assert all(x^y==(1 if orbit!=44 else 2) for x,y in zip(*words)),orbit
    names=' '.join(str(v) for v in variables)
    pnames=' '.join(map(str,params))
    bottomvec='!['+','.join(f'y{i}' for i in range(n))+']'
    topvec='!['+','.join(f'z{i}' for i in range(m))+']'
    nativeargs=' '.join(f'(p ⟨{i},by decide⟩)' for i in range(n))+' '+\
               ' '.join(f'(q ⟨{i},by decide⟩)' for i in range(m))
    vectorbp='!['+','.join(text(v) for v in bp)+']'
    vectortp='!['+','.join(text(v) for v in tp)+']'
    domaintext=' ∧ '.join('0≤'+f'({text(v)})' for v in domain)
    pieces.append(f'''
namespace Orbit{orbit}
open SixQubit.Orbit{orbit}
def bottom : Fin {n} → SS.BitString 6 := {bottomvec}
def top : Fin {m} → SS.BitString 6 := {topvec}
def bottomProb ({pnames} : ℝ) : Fin {n} → ℝ := {vectorbp}
def topProb ({pnames} : ℝ) : Fin {m} → ℝ := {vectortp}
def Domain ({pnames} : ℝ) : Prop := {domaintext}
def Moment (p : Fin {n} → ℝ) (q : Fin {m} → ℝ) := MomentSystem {nativeargs}
theorem actual_words :
    (∀ i, bottom i=MainTheory.OrderEightSupportDisplays.bits (![{','.join(map(str,words[0]))}] i)) ∧
    (∀ i, top i=MainTheory.OrderEightSupportDisplays.bits (![{','.join(map(str,words[1]))}] i)) ∧
    S0=Finset.univ.image bottom ∧ S1=Finset.univ.image top := by decide +kernel

''')
    if orbit in (49,50,51):
        perm=list(range(n-1,-1,-1)) if orbit==50 else list(range(n))
        pieces.append(f'def complementIndex : Fin {n} → Fin {n} := ![{",".join(map(str,perm))}]\n')
        pieces.append('theorem actual_complements : ∀ i, top (complementIndex i)=SS.complement (bottom i) := by decide +kernel\n\n')
    for k,(v,expected) in enumerate(zip(variables,bp+tp)):
        expr=s.expand(v-s.sympify(expected).subs(subst))
        coefs=A.extract(independent,list(range(n+m))).T.gauss_jordan_solve(s.Matrix([expr.coeff(v) for v in variables]))[0]
        assert (coefs.T*constants.extract(independent,[0]))[0]== -expr.subs({v:0 for v in variables}),(orbit,k)
        terms=' + '.join(f'{num(c)} * hm.{fields[j][0]}' for c,j in zip(coefs,independent) if c)
        proof='ring' if not terms else 'linear_combination '+terms
        pieces.append(f'''theorem consequence{k} {{{names} : ℝ}}
    ({'hm' if terms else '_hm'} : MomentSystem {names}) : {v}={text(s.sympify(expected).subs(subst))} := by
  {proof}

''')
    # Completeness is a theorem on arbitrary real probabilities, not merely
    # squared magnitudes of an already impossible distance-three code.
    selected=[]
    for v in extract:
        prefix,index=v[0],int(v[1:])
        selected.append(f'({"p" if prefix=="q" else "q"} ⟨{index},by decide⟩)')
    chosen=' '.join(selected)
    eqs=','.join('h'+str(i) for i in range(n+m))
    nonnegative=','.join('hm.n'+str(v) for v in variables)
    pieces.append(f'''theorem normal_coordinates (p : Fin {n} → ℝ) (q : Fin {m} → ℝ) (hm : Moment p q) :
    p=bottomProb {chosen} ∧ q=topProb {chosen} := by
''')
    for k in range(n+m):pieces.append(f'  have h{k} := consequence{k} hm\n')
    pieces.append(f'''  constructor
  · ext i
    fin_cases i <;> norm_num [bottomProb,Fin.succ] at * <;> linarith only [{eqs}]
  · ext i
    fin_cases i <;> norm_num [topProb,Fin.succ] at * <;> linarith only [{eqs}]

theorem domain_of_moment (p : Fin {n} → ℝ) (q : Fin {m} → ℝ) (hm : Moment p q) : Domain {chosen} := by
''')
    for k in range(n+m):pieces.append(f'  have h{k} := consequence{k} hm\n')
    pieces.append('  unfold Domain\n  refine ⟨'+','.join('?_ ' for _ in domain).strip()+'⟩ <;>\n')
    pieces.append(f'    linarith only [{nonnegative},{eqs}]\n\n')
    # Each native projection has an explicit sign inequality; no existential
    # reconstruction is accepted just from a final impossibility theorem.
    domhyp=','.join('h'+str(k) for k in range(len(domain)))
    parsaffine=' '.join(f'(bottomProb {pnames} ⟨{i},by decide⟩)' for i in range(n))+' '+\
               ' '.join(f'(topProb {pnames} ⟨{i},by decide⟩)' for i in range(m))
    pieces.append(f'''theorem reconstruct ({pnames} : ℝ) (h : Domain {pnames}) :
    Moment (bottomProb {pnames}) (topProb {pnames}) := by
  obtain ⟨{domhyp}⟩ := h
  change MomentSystem {parsaffine}
  constructor <;> norm_num [bottomProb,topProb] <;> linarith only [{domhyp}]

theorem complete_iff (p : Fin {n} → ℝ) (q : Fin {m} → ℝ) :
    Moment p q ↔ ∃ {pnames} : ℝ, Domain {pnames} ∧ p=bottomProb {pnames} ∧ q=topProb {pnames} := by
  constructor
  · intro hm
    exact ⟨{','.join(selected)},domain_of_moment p q hm,normal_coordinates p q hm⟩
  · rintro ⟨{','.join(map(str,params))},hd,hp,hq⟩
    rw [hp,hq]
    exact reconstruct {pnames} hd

''')
    if orbit==49:
        pieces.append('''theorem key_masses (p q : Fin 10 → ℝ) (hm : Moment p q) :
    (∀ i : Fin 4, p ⟨2*i.val,by omega⟩+p ⟨2*i.val+1,by omega⟩=1/6) ∧
    p ⟨8,by decide⟩=1/6 ∧ p ⟨9,by decide⟩=1/6 := by
  obtain ⟨a,b,g,_hd,hp,_hq⟩ := (complete_iff p q).1 hm
  rw [hp]
  refine ⟨?_,?_,?_⟩
  · intro i
    fin_cases i <;> norm_num [bottomProb]
    ring
  · norm_num [bottomProb]
  · norm_num [bottomProb]

''')
    if orbit==50:
        pieces.append('''theorem key_masses (p q : Fin 11 → ℝ) (hm : Moment p q) :
    p ⟨0,by decide⟩=1/6 ∧ p ⟨10,by decide⟩=1/6 ∧
    p ⟨1,by decide⟩+p ⟨2,by decide⟩+p ⟨5,by decide⟩=1/3 := by
  obtain ⟨a,b,g,t,_hd,hp,_hq⟩ := (complete_iff p q).1 hm
  rw [hp]
  refine ⟨?_,?_,?_⟩ <;> norm_num [bottomProb]
  ring

''')
    pieces.append(f'''theorem actual_matched_flip : ∀ i,
    top i=SS.bxor (bottom i) (SS.stdBasis ⟨{4 if orbit==44 else 5},by decide⟩) := by decide +kernel

theorem matched_probabilities (p q : Fin 10 → ℝ) (hm : Moment p q) : p=q := by
  obtain ⟨hp,hq⟩ := normal_coordinates p q hm
  exact hp.trans hq.symm

''')
    pieces.append(f'''theorem physical_normal_form (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x=0) (hd : ∀ x, x ∉ S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
    (hkl : SS.HasDistance ![c,d] 3) :
    ∃ {pnames} : ℝ, Domain {pnames} ∧
      (fun i => Complex.normSq (c (bottom i)))=bottomProb {pnames} ∧
      (fun i => Complex.normSq (d (top i)))=topProb {pnames} := by
  apply (complete_iff _ _).1
  exact moments c d hc hd hnc hnd hkl
end Orbit{orbit}
''')
pieces.append('\nend\nend MainTheory.OrderTwoPrintedMoments\n')
import argparse
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--check',action='store_true')
args=parser.parse_args()
generated=''.join(pieces)
target=ROOT/'MainTheory/OrderTwoPrintedMoments.lean'
if args.check:
    if target.read_text(encoding='utf8') != generated:
        raise SystemExit('FAIL: regenerate '+str(target.relative_to(ROOT)))
else:
    target.write_text(generated,encoding='utf8',newline='\n')
print('Generated complete real SI moment normal forms for orbits 42,43,44,46')
