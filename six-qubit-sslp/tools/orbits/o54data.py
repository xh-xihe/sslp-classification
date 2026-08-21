import sys; sys.path.insert(0,'.')
import sympy as sp
from itertools import combinations
from orbit import fiber, ind
from scan import bits, xor, dot, dressings
from quad import linear_system, kernels, solve_orbit
from kercycle import kernel_relations
from oddcycle import find_cycle

a,q,delta=[1,1,2,2,2,5],6,1
S0,S1=fiber(a,q,0),fiber(a,q,delta); n0,n1=len(S0),len(S1)
A,b=linear_system(S0,S1); sol,_=A.gauss_jordan_solve(b)
Q=sp.symbols('q0:%d'%n0); R=sp.symbols('r0:%d'%n1); V=list(Q)+list(R)
# moment equations as polynomials (lhs - rhs)
L=[]
names=['n0','n1']+['m%d'%(i+1) for i in range(6)]+['c%d%d'%(i+1,j+1) for i,j in combinations(range(6),2)]
L.append(sum(Q)-1); L.append(sum(R)-1)
for i in range(6):
    L.append(sum(Q[k] for k in range(n0) if ind(S0[k],i)) - sum(R[k] for k in range(n1) if ind(S1[k],i)))
for i,j in combinations(range(6),2):
    L.append(sum(Q[k] for k in range(n0) if ind(S0[k],i)*ind(S0[k],j))
             - sum(R[k] for k in range(n1) if ind(S1[k],i)*ind(S1[k],j)))
# quadratic identities
ker=kernels(S0,S1); seen=set(); quads=[]
for e,inc,v in ker:
    base=None
    for t,(i,j,y) in enumerate(inc):
        if v[t]==0: continue
        if base is None: base=(i,j,t); continue
        i0,j0,t0=base
        red=sp.simplify(sp.expand(sol[i0]*sol[n0+j0]-sol[i]*sol[n0+j]))
        if red==0: continue
        key=(i0,j0,i,j)
        if key in seen: continue
        seen.add(key); quads.append((e,i0,j0,i,j,Q[i0]*R[j0]-Q[i]*R[j]))
print('== 二次恒等式 =='); 
for k,(e,i0,j0,i,j,p) in enumerate(quads): print('  hq%d (mask %s): q%d*r%d = q%d*r%d'%(k,e,i0,j0,i,j))
# pinning certificates
pt = solve_orbit(54,a,q,delta)[5][0]
print(); print('== 固定值证书 ==')
certs=[]
for k in range(n0+n1):
    tgt = V[k] - pt[k]
    quo, rem = sp.reduced(tgt, [p for *_,p in quads]+L, *V, order='lex')
    assert rem==0, 'no certificate for %d'%k
    nz=[(t,sp.nsimplify(quo[t])) for t in range(len(quo)) if quo[t]!=0]
    certs.append((k,pt[k],nz))
    lbl=('q%d'%k) if k<n0 else ('r%d'%(k-n0))
    terms=' + '.join(('(%s)*hq%d'%(c,t) if t<len(quads) else '(%s)*%s'%(c,names[t-len(quads)])) for t,c in nz)
    print('  %-4s = %-6s   <=  %s'%(lbl,pt[k],terms[:110]))
# odd cycle
st=[('pos',x) if x>0 else ('zero',sp.Rational(0)) for x in pt]
rels=kernel_relations(S0,S1,st)
combo,coef = find_cycle(rels,3)
print(); print('== 奇环 ==')
for t,ridx in enumerate(combo):
    w,sbit,(e,src),(i,j,k,l,sigma) = rels[ridx]
    print('  R%d (mask %s): q%d..  star(c y%d)*d z%d = %s star(c y%d)*d z%d   系数 %d'
          %(t,e,i,i,j,'+' if sigma>0 else '-',k,l,coef[t]))
