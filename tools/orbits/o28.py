import sys
sys.path.insert(0, r'C:/Users/richa/AppData/Local/Temp/claude/D--UTD-Project-purdue/e2435927-3651-49b0-acfb-31f3430ee257/scratchpad')
from orbit import fiber, ind
from sympy import Matrix
from itertools import combinations

a, q = [1,1,1,1,1,2], 4
for d1 in range(q):
    S0, S1 = fiber(a,q,0), fiber(a,q,d1)
    if not S0 or not S1: continue
    rows, rhs = [], []
    rows.append([1]*len(S0)+[0]*len(S1)); rhs.append(1)
    rows.append([0]*len(S0)+[1]*len(S1)); rhs.append(1)
    for i in range(6):
        rows.append([ind(x,i) for x in S0]+[-ind(y,i) for y in S1]); rhs.append(0)
    for i,j in combinations(range(6),2):
        rows.append([ind(x,i)*ind(x,j) for x in S0]+[-ind(y,i)*ind(y,j) for y in S1]); rhs.append(0)
    M, b = Matrix(rows), Matrix(rhs)
    try:
        part, params = M.gauss_jordan_solve(b)[:2]
    except ValueError:
        print('delta=%d  |S0|=%2d |S1|=%2d   矩系统无解' % (d1,len(S0),len(S1))); continue
    ns = M.nullspace()
    sub = {p:0 for p in part.free_symbols}
    v = [part[k].subs(sub) if part.free_symbols else part[k] for k in range(M.shape[1])]
    print('delta=%d  |S0|=%2d |S1|=%2d  dLP=%d' % (d1,len(S0),len(S1),len(ns)))
    if len(ns)==0:
        nz0=[(S0[k],v[k]) for k in range(len(S0)) if v[k]!=0]
        nz1=[(S1[k],v[len(S0)+k]) for k in range(len(S1)) if v[len(S0)+k]!=0]
        print('   T0(%d)= %s' % (len(nz0), ', '.join('%s:%s'%t for t in nz0)))
        print('   T1(%d)= %s' % (len(nz1), ', '.join('%s:%s'%t for t in nz1)))
        print('   全部非负:', all(x>=0 for x in v))
