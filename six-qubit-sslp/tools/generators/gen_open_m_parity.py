"""Exact SO(5) circle family with a full-support logical Pauli.

The shell code uses w=(C,S/sqrt(2),S/sqrt(2),0,0),
u=(-S,C/sqrt(2),C/sqrt(2),0,0), v=(0,1/sqrt(2),-1/sqrt(2),0,0).
Multiplying logical Z_anc Z_4 Z_5 by the scalar X^tensor5 produces a
full-support Pauli. Local Cliffords put its eigenvectors in parity fibers.
This script proposes exact coefficients; generated Lean proofs certify them.
"""
import hashlib
import json
from pathlib import Path
import sys
import sympy as sp

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / 'tools/generators'))
from genreal import ZERO, zadd, zneg, zconj, zmul
from gen_open_l_families import lean_zq

C, S = sp.symbols('C S', real=True)
EXPONENTS = [(0,0),(1,0),(0,1),(2,0),(1,1),(0,2)]


def coefficient(value):
    value = sp.expand(value)
    re, im = sp.expand(sp.re(value)), sp.expand(sp.im(value))
    out = [0]*8
    for part, offset in ((re,0),(im,4)):
        poly = sp.Poly(part, sp.sqrt(2))
        for (power,), number in poly.terms():
            assert power <= 1 and number.q == 1, (value, poly)
            out[offset+power] = int(number)
    return tuple(out)


def make_tables():
    u = [-S,C/sp.sqrt(2),C/sp.sqrt(2),0,0]
    v = [0,1/sp.sqrt(2),-1/sp.sqrt(2),0,0]
    words = [[sp.S.Zero]*64 for _ in range(2)]
    for j in range(5):
        for shell in (1<<j,31^(1<<j)):
            words[0][shell<<1] = (u[j]+sp.I*v[j])/(2*sp.sqrt(2))
            words[0][(shell<<1)|1] = ((1 if j==3 else 0)+sp.I*(1 if j==4 else 0))/(2*sp.sqrt(2))
            words[1][shell<<1] = ((1 if j==3 else 0)-sp.I*(1 if j==4 else 0))/(2*sp.sqrt(2))
            words[1][(shell<<1)|1] = (-u[j]+sp.I*v[j])/(2*sp.sqrt(2))
    for i in range(2):
        a = words[i]
        for j in range(1,6):
            if j in (4,5):
                a = [(-sp.I if (y>>j)&1 else 1)*value for y,value in enumerate(a)]
            a = [sp.expand((a[y&~(1<<j)] + (-1 if (y>>j)&1 else 1)*a[y|(1<<j)])/sp.sqrt(2))
                 for y in range(64)]
        words[i] = a
    denominator = 32
    tables = [[[coefficient(sp.Poly(sp.expand(value*denominator), C,S).coeff_monomial(m))
                for m in (1,C,S)] for value in a] for a in words]
    parity = [{y.bit_count()%2 for y,row in enumerate(a) if any(x!=ZERO for x in row)} for a in tables]
    assert parity == [{1},{0}], parity
    return denominator,list(reversed(tables))


def qmat(a,b,x,z):
    result = [ZERO]*6
    for y in range(64):
        left,right = a[y^x],b[y]
        for l,le in enumerate(EXPONENTS[:3]):
            if left[l] == ZERO:
                continue
            for r,re in enumerate(EXPONENTS[:3]):
                if right[r] == ZERO:
                    continue
                value = zmul(zconj(left[l]),right[r])
                if (y&z).bit_count()%2:
                    value = zneg(value)
                index = EXPONENTS.index((le[0]+re[0],le[1]+re[1]))
                result[index] = zadd(result[index],value)
    return result


def circle_zero(q):
    return q[1]==q[2]==q[4]==ZERO and q[3]==q[5] and q[0]==zneg(q[5])


def symbolic(q):
    def zexpr(z):
        return sum(a*b for a,b in zip(z,(1,sp.sqrt(2),sp.sqrt(3),sp.sqrt(6),sp.I,sp.I*sp.sqrt(2),sp.I*sp.sqrt(3),sp.I*sp.sqrt(6))))
    return sp.expand(sum(zexpr(a)*C**i*S**j for a,(i,j) in zip(q,EXPONENTS)))


def generate():
    denominator,(a,b) = make_tables()
    traces = []
    for x in range(64):
        for z in range(64):
            wt=(x|z).bit_count()
            if wt>3:
                continue
            aa,bb=qmat(a,a,x,z),qmat(b,b,x,z)
            if wt<=2:
                assert circle_zero([zadd(v,zneg(w)) for v,w in zip(aa,bb)]),(x,z,'diag')
                assert circle_zero(qmat(a,b,x,z)),(x,z,'cross')
            trace=[zadd(v,w) for v,w in zip(aa,bb)]
            if not circle_zero(trace):
                traces.append(dict(x=x,z=z,weight=wt,quad=trace))
    for word in (a,b):
        q=qmat(word,word,0,0)
        q[0]=zadd(q[0],(-denominator**2,0,0,0,0,0,0,0))
        assert circle_zero(q),q
    for wt in range(4):
        value=sp.expand(sum(sp.expand_complex(symbolic(row['quad'])*sp.conjugate(symbolic(row['quad'])))
                            for row in traces if row['weight']==wt)/(4*denominator**4))
        reduced=sp.rem(sp.Poly(value,C,S),sp.Poly(S**2+C**2-1,C,S), S) if False else sp.expand(value.subs(S**4,(1-C**2)**2).subs(S**2,1-C**2))
        print('A',wt,':',sp.factor(reduced),'traces',sum(row['weight']==wt for row in traces))
    data=dict(denominator=denominator,tables=[a,b],traces=traces)
    target=ROOT/'tmp/open-m-parity-candidate.json'
    target.write_text(json.dumps(data,indent=2)+'\n',encoding='utf-8')
    return data


def emit_lean(data):
    directory=ROOT/'SixQubit/Generated/OpenMParity'
    directory.mkdir(parents=True,exist_ok=True)
    lines=['import SixQubit.ParityMomentFamily','','/- Exact proposed coefficients; all identities receive kernel proofs. -/',
           'namespace SixQubit.OpenMParity','','open SixQubit.Realize SixQubit.Orbit8Family',
           'open SixQubit.ParityCircleFamily SixQubit.ParityMomentFamily','','set_option maxRecDepth 100000',
           'set_option maxHeartbeats 20000000','','def angle : Fin 6 → ZMod 2 := ![1,1,1,1,1,1]','']
    for k,word in enumerate(data['tables']):
        support=[y for y,row in enumerate(word) if any(tuple(v)!=ZERO for v in row)]
        lines += [f'def L{k} : List (SS.BitString 6) :=',
                  '  ['+', '.join('nbit '+str(y) for y in support)+']','',
                  f'def c{k} (x : SS.BitString 6) : LinZ :=']
        def tree(bit, prefix, indent):
            values=[word[y] for y in range(64) if y % (1<<bit)==prefix]
            if all(all(tuple(z)==ZERO for z in row) for row in values):
                return [indent+'LinZ.zero']
            if bit==6:
                return [indent+'⟨'+', '.join(lean_zq(v) for v in word[prefix])+'⟩']
            return ([indent+f'if x {bit} then']+tree(bit+1,prefix+(1<<bit),indent+'  ')+
                    [indent+'else']+tree(bit+1,prefix,indent+'  '))
        lines += tree(0,0,'  ')+['']
    lines += ['def traceModel (P : SS.PauliString 6) : QuadZ :=']
    for index,row in enumerate(data['traces']):
        lines.append('  '+('if' if index==0 else 'else if')+
                     f' num P.x = {row["x"]} ∧ num P.z = {row["z"]} then '+
                     '⟨'+', '.join(lean_zq(v) for v in row['quad'])+'⟩')
    lines += ['  else QuadZ.zero','',
        'def klCheck (P : SS.PauliString 6) : Prop :=',
        '  CircleZero (QuadZ.sub (qmat c0 c0 L0 P.x P.z) (qmat c1 c1 L1 P.x P.z)) ∧',
        '    CircleZero (qmat c0 c1 L1 P.x P.z) ∧ CircleZero (qmat c1 c0 L0 P.x P.z)','',
        'instance (P : SS.PauliString 6) : Decidable (klCheck P) := by unfold klCheck; infer_instance','',
        'def rowCheck (P : SS.PauliString 6) : Prop :=',
        '  (P.wt ≤ 2 → klCheck P) ∧',
        '    (P.wt ≤ 3 → CircleZero (QuadZ.sub (qtrace c0 c1 L0 L1 P) (traceModel P)))','',
        'instance (P : SS.PauliString 6) : Decidable (rowCheck P) := by unfold rowCheck; infer_instance','']
    support_lines=['import SixQubit.Generated.OpenMParity.Data', '',
                   'namespace SixQubit.OpenMParity', '',
                   'open SixQubit.Realize SixQubit.Orbit8Family', '',
                   'set_option maxRecDepth 100000', 'set_option maxHeartbeats 20000000', '']
    for wt in (1,2,3):
        rows=[row for row in data['traces'] if row['weight']==wt]
        lines += [f'def traceList{wt} : List (SS.PauliString 6) :=',
                  '  ['+', '.join(f'⟨nbit {r["x"]}, nbit {r["z"]}⟩' for r in rows)+']','',
                  f'theorem traceList{wt}_nodup : traceList{wt}.Nodup := by decide',
                  f'theorem traceList{wt}_weight : ∀ P ∈ traceList{wt}, P.wt = {wt} := by',
                  '  intro P hP']
        if rows:
            lines += [f'  simp only [traceList{wt}, List.mem_cons, List.not_mem_nil, or_false] at hP',
                      '  rcases hP with '+' | '.join(['rfl']*len(rows)),
                      '  all_goals decide', '']
        else:
            lines += [f'  simp [traceList{wt}] at hP', '']
        lines += [f'def modelList{wt} : List QuadZ :=',
                  '  ['+', '.join('⟨'+', '.join(lean_zq(v) for v in row['quad'])+'⟩' for row in rows)+']',
                  f'theorem modelList{wt}_correct : traceList{wt}.map traceModel = modelList{wt} := by decide','']
        support_lines += [
                  f'theorem traceList{wt}_support_masks : ∀ m < 64, ∀ k < 64,',
                  f'    let P : SS.PauliString 6 := ⟨nbit m, nbit k⟩',
                  f'    P.wt = {wt} → P ∉ traceList{wt} → traceModel P = QuadZ.zero := by',
                  '  intro m hm', '  interval_cases m <;> decide', '',
                  f'theorem traceList{wt}_support (P : SS.PauliString 6) (hw : P.wt = {wt})',
                  f'    (hn : P ∉ traceList{wt}) : traceModel P = QuadZ.zero := by',
                  '  have he : (⟨nbit (num P.x), nbit (num P.z)⟩ : SS.PauliString 6) = P := by',
                  '    cases P; simp only [nbit_num]',
                  f'  have h := traceList{wt}_support_masks (num P.x) (num_lt _) (num P.z) (num_lt _)',
                  '  dsimp only at h', '  rw [he] at h', '  exact h hw hn','']
    lines += ['end SixQubit.OpenMParity','']
    (directory/'Data.lean').write_text('\n'.join(lines),encoding='utf-8')
    support_lines += ['end SixQubit.OpenMParity','']
    (directory/'Support.lean').write_text('\n'.join(support_lines),encoding='utf-8')
    for block in range(8):
        lines=['import SixQubit.Generated.OpenMParity.Data','',
               'namespace SixQubit.OpenMParity','','open SixQubit.Realize','',
               'set_option maxRecDepth 100000','set_option maxHeartbeats 20000000','']
        for mask in range(8*block,8*block+8):
            lines += [f'theorem row_{mask} : ∀ k < 64,',
                      f'    rowCheck (⟨nbit {mask}, nbit k⟩ : SS.PauliString 6) := by decide','']
        lines += [
               f'theorem rows{block} : ∀ j < 8, ∀ k < 64,',
               f'    rowCheck (⟨nbit ({8*block} + j), nbit k⟩ : SS.PauliString 6) := by',
               '  intro j hj', '  interval_cases j']
        for mask in range(8*block,8*block+8):
            lines += [f'  · exact row_{mask}']
        lines += ['', 'end SixQubit.OpenMParity','']
        (directory/f'Rows{block}.lean').write_text('\n'.join(lines),encoding='utf-8')
    lines=[f'import SixQubit.Generated.OpenMParity.Rows{block}' for block in range(8)]
    lines += ['', 'namespace SixQubit.OpenMParity','','open SixQubit.Realize SixQubit.Orbit8Family',
              'open SixQubit.ParityCircleFamily SixQubit.ParityMomentFamily','',
              'theorem all_rows (P : SS.PauliString 6) : rowCheck P := by',
              '  have hx := num_lt P.x', '  have hz := num_lt P.z',
              '  have he : (⟨nbit (num P.x), nbit (num P.z)⟩ : SS.PauliString 6) = P := by',
              '    cases P; simp only [nbit_num]', '  rw [← he]',
              '  have hblock : num P.x / 8 < 8 := by omega',
              '  interval_cases hb : num P.x / 8']
    for block in range(8):
        lines += [f'  · have h := rows{block} (num P.x - {8*block}) (by omega) (num P.z) hz',
                  '    convert h using 1', '    congr 2', '    omega']
    lines += ['', 'set_option maxHeartbeats 20000000', 'set_option maxRecDepth 100000','',
              'def certificate : SixQubit.ParityMomentFamily.Certificate where',
              '  angle := angle', '  c0 := c0', '  c1 := c1', '  L0 := L0', '  L1 := L1',
              f'  denominator := {data["denominator"]}', '  denominator_pos := by decide',
              '  L0_nodup := by decide', '  L1_nodup := by decide',
              '  vanishes0 := by decide', '  vanishes1 := by decide',
              '  fiber0 := by decide', '  fiber1 := by decide',
              '  kl := fun P hP => (all_rows P).1 hP',
              '  norm0 := by decide', '  norm1 := by decide','',
              'end SixQubit.OpenMParity','']
    (directory/'Certificate.lean').write_text('\n'.join(lines),encoding='utf-8')
    order = ['Data', *(f'Rows{i}' for i in range(8)), 'Support', 'Certificate']
    modules = ['SixQubit.Generated.OpenMParity.' + leaf for leaf in order]
    (directory/'serial-build-order.txt').write_text('\n'.join(modules)+'\n',encoding='utf-8')
    manifest = ['# lean_files=' + str(len(order))]
    manifest += [hashlib.sha256((directory/(leaf+'.lean')).read_bytes()).hexdigest() + '  ' + module
                 for leaf, module in zip(order, modules)]
    (directory/'generation-manifest.sha256').write_text('\n'.join(manifest)+'\n',encoding='utf-8')


if __name__=='__main__':
    emit_lean(generate())
