#!/usr/bin/env python3
"""Construct a stabilizer seed; Lean checks its full finite KL certificate.
No search or numerical optimization is used.
"""
from pathlib import Path

ROOT=Path(__file__).resolve().parent
def add(a,b):return (a[0]+b[0],a[1]+b[1])
def mul(a,b):return (a[0]*b[0]-a[1]*b[1],a[0]*b[1]+a[1]*b[0])
def bits(k):return [(k>>(4-i))&1 for i in range(5)]
def number(s):return sum(x<<(4-i) for i,x in enumerate(s))
def act(label,v):
    out=[(0,0)]*32
    for k,z in enumerate(v):
        s=bits(k);c=(1,0)
        for i,p in enumerate(label):
            if p=='Z':c=mul(c,(-1 if s[i] else 1,0))
            if p=='Y':c=mul(c,(0,-1 if s[i] else 1))
            if p in 'XY':s[i]^=1
        out[number(s)]=add(out[number(s)],mul(c,z))
    return out
def rotate(v,site):
    # sqrt(2) H S^dagger, so both rotations remove their denominators.
    out=[(0,0)]*32
    for k,z in enumerate(v):
        s=bits(k);r=s[site]
        z=mul(z,(0,-1) if r else (1,0))
        for t in (0,1):
            s[site]=t
            out[number(s)]=add(out[number(s)],mul(z,(-1 if r*t else 1,0)))
    return out
def permute(v):
    out=[(0,0)]*32
    for k,z in enumerate(v):out[number([bits(k)[i] for i in [0,3,4,1,2]])]=z
    return out
def lit(z):return f'⟨{z[0]}, {z[1]}⟩'
def table(v,depth=0):
    if len(v)==1:return lit(v[0])
    m=len(v)//2
    return f'![{table(v[:m],depth+1)}, {table(v[m:],depth+1)}]'
def main():
    c0=[(0,0)]*32;c0[0]=(1,0)
    for g in ['XZZXI','IXZZX','XIXZZ','ZXIXZ']:
        c0=[add(a,b) for a,b in zip(c0,act(g,c0))]
    c1=act('XXXXX',c0)
    seed=[permute(rotate(rotate(c,0),3)) for c in [c1,c0]]
    assert all(sum(a*a+b*b for a,b in c)==64 for c in seed)
    source='''import Orbit2.TensorPauli

namespace Orbit2.FiveQubit
open scoped BigOperators
open Orbit2.TensorPauli
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def flipSite (p : Fin 4) (s : Fin 2) : Fin 2 :=
  if p = 1 ∨ p = 2 then (if s = 0 then 1 else 0) else s
def flip (p : Label 5) (s : Fin 5 → Fin 2) : Fin 5 → Fin 2 :=
  fun i => flipSite (p i) (s i)
def amplitude (p : Label 5) (s : Fin 5 → Fin 2) : GaussianInt :=
  ∏ i, localG (p i) (s i) (flip p s i)
def act (p : Label 5) (v : (Fin 5 → Fin 2) → GaussianInt) (s : Fin 5 → Fin 2) : GaussianInt :=
  amplitude p s * v (flip p s)
def weight (p : Label 5) : ℕ := ∑ i, if p i = 0 then 0 else 1

def seed (j : Fin 2) (s : Fin 5 → Fin 2) : GaussianInt :=
'''+f'  ![{table(seed[0])}, {table(seed[1])}] j (s 0) (s 1) (s 2) (s 3) (s 4)\n'+'''
/-- Every Pauli of weight at most two has exactly zero compression, except I.
The normalization is 64 because the logical columns are seed/8. -/
theorem pure_KL_G : ∀ p : Label 5, weight p ≤ 2 → ∀ j k : Fin 2,
    (∑ s, star (seed j s) * act p (seed k) s) =
      if p = (fun _ => 0) ∧ j = k then 64 else 0 := by
  decide +kernel

theorem logical_G : ∀ j s, act ![3,3,3,0,0] (seed j) s =
    (if j = 0 then 1 else -1) * seed j s := by
  decide +kernel

end Orbit2.FiveQubit
'''
    (ROOT/'Orbit2/FiveQubit.lean').write_text(source)
    print('Generated explicit five-qubit seed and exact KL obligations.')
if __name__=='__main__':main()
