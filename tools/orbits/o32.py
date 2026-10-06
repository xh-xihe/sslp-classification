import sys; sys.path.insert(0,'.')
import sympy as sp
from itertools import combinations
from orbit import fiber, ind
from scan import bits, xor, dot, dressings
from cert import build, reduce_mod_linear
from propagate import pdim, DLP

a,q=[1,1,2,2,2,3],4
S0f=fiber(a,q,0)
for delta in (1,3):
    S1f=fiber(a,q,delta)
    print('delta=%d  |S0|=%d |S1|=%d  dim=%s (表 %d)'%(delta,len(S0f),len(S1f),pdim(S0f,S1f),DLP[32]))
# 论文的坐标: 串 = (o1,o2,u1,u2,u3,o3)
E=['000','011','101','110']; O=['001','010','100','111']
OUT={'A':'000','B':'011','C':'101','D':'110','E':'010','F':'100','G':'111','H':'001'}
def mk(o,u): return o[0]+o[1]+u[0]+u[1]+u[2]+o[2]
for delta in (1,3):
    S1f=fiber(a,q,delta)
    bot=[mk(OUT[L],u) for L in 'ABC' for u in E]+[mk(OUT['D'],v) for v in O]
    top=[mk(OUT[L],u) for L in 'EFG' for u in E]+[mk(OUT['H'],v) for v in O]
    print('delta=%d  底=纤维0? %s   顶=纤维%d? %s'%(delta,sorted(bot)==sorted(S0f),delta,sorted(top)==sorted(S1f)))

print()
delta=1; S0=fiber(a,q,0); S1=fiber(a,q,delta)
Q,R,V,A,b,enames=build(S0,S1)
def qi(L,u): return Q[S0.index(mk(OUT[L],u))]
def ri(L,u): return R[S1.index(mk(OUT[L],u))]
ok=True
for u in E:
    for L,expr in (('A',(2*ri('E',u)+2*ri('F',u)-ri('G',u))/3),
                   ('B',(2*ri('E',u)-ri('F',u)+2*ri('G',u))/3),
                   ('C',(-ri('E',u)+2*ri('F',u)+2*ri('G',u))/3)):
        cof,rem = reduce_mod_linear(qi(L,u)-expr, V, A, b)
        if rem!=0: ok=False; print('  矩反射 %s_%s 失败, 余式 %s'%(L,u,rem))
print('矩反射 A/B/C = T(E,F,G):', '全部成立' if ok else '有失败')
for L in 'EFG':
    cof,rem = reduce_mod_linear(sum(ri(L,u) for u in E)-sp.Rational(1,4), V, A, b)
    print('  行和 sum_u %s_u = 1/4 :'%L, '成立' if rem==0 else ('余式 %s'%rem))
# 关联集
for nm,e,pairs in (('X_1','100000',[('A','F'),('B','G')]),
                   ('X_2','010000',[('A','E'),('C','G')]),
                   ('X_6','000001',[('B','E'),('C','F')])):
    inc=[(S0.index(xor(y,e)),j) for j,y in enumerate(S1) if xor(y,e) in S0]
    want=set()
    for lb,lt in pairs:
        for u in E: want.add((S0.index(mk(OUT[lb],u)), S1.index(mk(OUT[lt],u))))
    print('  %s 关联数 %d, 与论文一致: %s'%(nm,len(inc),set(inc)==want))
# 4x4 Walsh over E with dressings I,Z3,Z4,Z5
zs=['000000','001000','000100','000010']
W=sp.Matrix([[(-1)**dot(z, '00'+u+'0') for u in E] for z in zs])
print('  4x4 Walsh det =', W.det())
