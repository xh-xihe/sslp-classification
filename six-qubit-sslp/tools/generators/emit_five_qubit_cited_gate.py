"""Exact proposals for auditing the gate convention in arXiv:2504.20847 B.1.

The generated identities are independently checked by Lean kernel reduction.
Coordinates represent Z[sqrt(3),i], embedded into the existing ZQ ring.
"""
from pathlib import Path
from itertools import product

ROOT=Path(__file__).resolve().parents[2]
ZERO=(0,0,0,0)
ONE=(1,0,0,0)
def add(a,b): return tuple(x+y for x,y in zip(a,b))
def neg(a): return tuple(-x for x in a)
def conj(a): return (a[0],a[1],-a[2],-a[3])
def mul(a,b):
    p=lambda x,y:(x[0]*y[0]+3*x[1]*y[1],x[0]*y[1]+x[1]*y[0])
    rr,ii,ri,ir=p(a[:2],b[:2]),p(a[2:],b[2:]),p(a[:2],b[2:]),p(a[2:],b[:2])
    return (rr[0]-ii[0],rr[1]-ii[1],ri[0]+ir[0],ri[1]+ir[1])
def isum(xs):
    t=ZERO
    for x in xs:t=add(t,x)
    return t
def iprod(xs):
    t=ONE
    for x in xs:t=mul(t,x)
    return t
I=(0,0,1,0)
T=[[neg(I),neg(ONE)],[I,neg(ONE)]]
D=[[(1,0,0,-1),ZERO],[ZERO,(1,0,0,1)]]
W=[[(-2,0,0,0),(-1,1,1,-1)],[(-1,1,-1,1),(2,0,0,0)]]
R=[
 [1,0,0,-1,0,1,-1,0,0,1,1,0,-1,0,0,-1,0,-1,1,0,1,0,0,-1,-1,0,0,-1,0,-1,-1,0],
 [0,1,1,0,1,0,0,1,1,0,0,-1,0,-1,1,0,1,0,0,1,0,-1,-1,0,0,1,-1,0,1,0,0,-1]]
bits=lambda x:[(x>>(4-j))&1 for j in range(5)]
RW=[[isum(mul(W[x&1][b],(R[i][(x//2)*2+b],0,0,0)) for b in range(2))
     for x in range(32)] for i in range(2)]
K=[[mul(iprod(T[a][b] for a,b in zip(bits(x)[:4],bits(y)[:4])),D[x&1][y&1])
    for y in range(32)] for x in range(32)]
IMG=[[isum(mul(K[x][y],RW[i][y]) for y in range(32)) for x in range(32)] for i in range(2)]
for i,j in product(range(2),repeat=2):
    assert isum(mul(conj(RW[i][x]),IMG[j][x]) for x in range(32))==ZERO
    assert isum(mul(conj(RW[i][x]),RW[j][x]) for x in range(32))==((192,-64,0,0) if i==j else ZERO)
    assert isum(mul(conj(IMG[i][x]),IMG[j][x]) for x in range(32))==((12288,-4096,0,0) if i==j else ZERO)
def q(a):return 'z8 '+' '.join(str(x) if x>=0 else f'({x})' for x in (a[0],0,a[1],0,a[2],0,a[3],0))
def vec(xs):return '!['+',\n    '.join(q(x) for x in xs)+']'
body='''import MainTheory.FiveQubitPerfectCore
import MainTheory.ExactZQFinite

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace MainTheory.FiveQubitCitedGateData

open SixQubit.Realize MainTheory.FiveQubitPerfectCore
open MainTheory.ExactZQFinite

def W : Fin 2 → Fin 2 → ZQ :=
  !![z8 (-2) 0 0 0 0 0 0 0, z8 (-1) 0 1 0 1 0 (-1) 0;
     z8 (-1) 0 1 0 (-1) 0 1 0, z8 2 0 0 0 0 0 0 0]
def T : Fin 2 → Fin 2 → ZQ :=
  !![z8 0 0 0 0 (-1) 0 0 0, z8 (-1) 0 0 0 0 0 0 0;
     z8 0 0 0 0 1 0 0 0, z8 (-1) 0 0 0 0 0 0 0]
def D : Fin 2 → Fin 2 → ZQ :=
  !![z8 1 0 0 0 0 0 (-1) 0, ZQ.zero;
     ZQ.zero, z8 1 0 0 0 0 0 1 0]
def index (b : Bool) : Fin 2 := if b then 1 else 0
def kernel (x y : Fin 32) : ZQ := ZQ.mul
  (prod 4 (fun j => T (index (bits x j.castSucc)) (index (bits y j.castSucc))))
  (D (index (bits x 4)) (index (bits y 4)))
'''
body+='\ndef rawWord : Fin 2 → Fin 32 → ZQ :=\n  !['+',\n  '.join(vec(xs) for xs in RW)+']\n'
body+='\ndef imageWord : Fin 2 → Fin 32 → ZQ :=\n  !['+',\n  '.join(vec(xs) for xs in IMG)+']\n'
body+='''
theorem rawWord_checked : ∀ i x, rawWord i x = sum 2 (fun b => ZQ.mul
    (W (index (bits x 4)) b)
    (z8 (raw i (Fin.snoc (fun j : Fin 4 => bits x j.castSucc) (decide (b=1)))) 0 0 0 0 0 0 0)) := by
  decide

theorem imageWord_checked : ∀ i x, imageWord i x =
    sum 32 (fun y => ZQ.mul (kernel x y) (rawWord i y)) := by decide

theorem orthogonal_checked : ∀ i j, sum 32 (fun x =>
    ZQ.mul (ZQ.conj (rawWord i x)) (imageWord j x)) = ZQ.zero := by decide

theorem gram_checked : ∀ i j, sum 32 (fun x =>
    ZQ.mul (ZQ.conj (rawWord i x)) (rawWord j x)) =
    if i=j then z8 192 0 (-64) 0 0 0 0 0 else ZQ.zero := by decide

theorem image_gram_checked : ∀ i j, sum 32 (fun x =>
    ZQ.mul (ZQ.conj (imageWord i x)) (imageWord j x)) =
    if i=j then z8 12288 0 (-4096) 0 0 0 0 0 else ZQ.zero := by decide

end MainTheory.FiveQubitCitedGateData
'''
p=ROOT/'MainTheory/FiveQubitCitedGateData.lean'
if not p.exists() or p.read_text(encoding='utf-8')!=body:
    p.write_text(body,encoding='utf-8')
print('Wrote',p.relative_to(ROOT))

TC=[[neg(I),ONE],[I,ONE]]
KC=[[mul(iprod(TC[a][b] for a,b in zip(bits(x)[:4],bits(y)[:4])),D[x&1][y&1])
     for y in range(32)] for x in range(32)]
F5=[[iprod(TC[a][b] for a,b in zip(bits(x),bits(y))) for y in range(32)] for x in range(32)]
LC=[[isum(mul((R[i][x]*R[j][y],0,0,0),F5[x][y]) for x,y in product(range(32),repeat=2))
     for j in range(2)] for i in range(2)]
assert all(t%16==0 for row in LC for z in row for t in z)
LC=[[mul((1,0,1,0),tuple(t//16 for t in z)) for z in row] for row in LC]
CIMG=[[isum(mul(KC[x][y],RW[i][y]) for y in range(32)) for x in range(32)] for i in range(2)]
assert all(CIMG[i][x]==isum(mul(LC[j][i],RW[j][x]) for j in range(2))
           for i,x in product(range(2),range(32)))
fixed='''import MainTheory.FiveQubitCitedGateData

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace MainTheory.FiveQubitCorrectedGateData

open SixQubit.Realize MainTheory.FiveQubitPerfectCore
open MainTheory.ExactZQFinite MainTheory.FiveQubitCitedGateData

def Tcorrected : Fin 2 → Fin 2 → ZQ :=
  !![z8 0 0 0 0 (-1) 0 0 0, z8 1 0 0 0 0 0 0 0;
     z8 0 0 0 0 1 0 0 0, z8 1 0 0 0 0 0 0 0]
def correctedKernel (x y : Fin 32) : ZQ := ZQ.mul
  (prod 4 (fun j => Tcorrected (index (bits x j.castSucc)) (index (bits y j.castSucc))))
  (D (index (bits x 4)) (index (bits y 4)))
'''
fixed+='\ndef logical : Fin 2 → Fin 2 → ZQ :=\n  !['+',\n  '.join(vec(xs) for xs in LC)+']\n'
fixed+='''
theorem corrected_checked : ∀ i x,
    sum 32 (fun y => ZQ.mul (correctedKernel x y) (rawWord i y)) =
    sum 2 (fun j => ZQ.mul (logical j i) (rawWord j x)) := by decide

end MainTheory.FiveQubitCorrectedGateData
'''
p=ROOT/'MainTheory/FiveQubitCorrectedGateData.lean'
if not p.exists() or p.read_text(encoding='utf-8')!=fixed:
    p.write_text(fixed,encoding='utf-8')
print('Wrote',p.relative_to(ROOT),'logical matrix',LC)
