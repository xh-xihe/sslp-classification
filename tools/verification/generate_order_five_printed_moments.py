"""Generate exact SI moment consequences without using orbit no-go results.

Each rational multiplier is an untrusted candidate. The emitted Lean proof
checks it against the physical MomentSystem supplied by CodeOrbit35/37/38.
"""
import argparse
from pathlib import Path
import re
import sympy as s

ROOT = Path(__file__).resolve().parents[2]


def num(v):
    return str(v) if v.q == 1 else f'({v.p}/{v.q})'


def targets(orbit, n):
    q = s.symbols(' '.join('q'+str(i) for i in range(n)))
    r = s.symbols(' '.join('r'+str(i) for i in range(13)))
    if orbit == 35:
        rows = [(q[5]+r[10]+r[11], s.Rational(2, 5)),
                (q[7]-r[10], 0), (q[8]-r[11], 0), (r[12], s.Rational(3, 10))]
    elif orbit == 37:
        rows = [(q[12], s.Rational(1, 10))]
        rows += [(sum(q[3+3*i:6+3*i]), s.Rational(1, 5)) for i in range(3)]
        rows += [(q[2-j]-sum(q[3+j+3*i] for i in range(3)), s.Rational(-1, 10))
                 for j in range(3)]
        rows += [(sum(q[:3]), s.Rational(3, 10))]
        rows += [(q[i]-r[12-i], 0) for i in range(13)]
    else:
        rows = [(q[12], s.Rational(1, 5))]
        rows += [(sum(q[4+4*i:8+4*i]), s.Rational(3, 10)) for i in range(2)]
        rows += [(q[3-j]-q[4+j]-q[8+j], s.Rational(-1, 10)) for j in range(4)]
        rows += [(q[i]-r[12-i], 0) for i in range(13)]
    return q, r, rows


def generate():
    parts = ['''import SixQubit.CodeOrbit35
import SixQubit.CodeOrbit37
import SixQubit.CodeOrbit38
import MainTheory.OrderEightSupportDisplays

/-! Literal SI order-five moment consequences of actual physical codewords.
Only normalization and degree-two diagonal moments are used. Every rational
constraint multiplier is checked by the Lean kernel, independently of all
phase exclusions and final no-code theorems. Zero amplitudes are allowed.
-/

set_option autoImplicit false
set_option maxHeartbeats 8000000

namespace MainTheory.OrderFivePrintedMoments
noncomputable section
open scoped BigOperators
''']
    for orbit in (35, 37, 38):
        n = 12 if orbit == 35 else 13
        q, r, consequences = targets(orbit, n)
        variables = q+r
        local = {str(v): v for v in variables}
        source = (ROOT/f'SixQubit/Orbit{orbit}.lean').read_text(encoding='utf8')
        fields = re.findall(r'^  (n[01]|m[1-6]|c[1-6][1-6]) : (.+) = (.+)$', source, re.M)
        assert len(fields) == 23
        differences = [s.expand(s.sympify(lhs, locals=local)-s.sympify(rhs, locals=local))
                       for _, lhs, rhs in fields]
        A = s.Matrix([[d.coeff(v) for v in variables] for d in differences])
        b = s.Matrix([-d.subs({v: 0 for v in variables}) for d in differences])
        independent = list(A.T.rref()[1])
        parts.append(f'\nnamespace Orbit{orbit}\nopen SixQubit.Orbit{orbit}\n\n')
        if orbit in (37, 38):
            cols = 3 if orbit == 37 else 4
            nrows = 3 if orbit == 37 else 2
            first = 3 if orbit == 37 else 4
            avec = ','.join(f'y{i}' for i in range(cols-1, -1, -1))
            bvec = ','.join('!['+','.join(f'y{first+cols*i+j}' for j in range(cols))+']'
                            for i in range(nrows))
            awords = [6, 5, 0] if orbit == 37 else [9, 5, 3, 0]
            bwords = [[25, 26, 31], [41, 42, 47], [49, 50, 55]] if orbit == 37 else [
                [22, 26, 28, 31], [38, 42, 44, 47]]
            words = ','.join('!['+','.join(str(w) for w in row)+']' for row in bwords)
            parts.append(f'''def A : Fin {cols} → SS.BitString 6 := ![{avec}]
def B : Fin {nrows} → Fin {cols} → SS.BitString 6 := ![{bvec}]

theorem printed_labels :
    (∀ j, A j = MainTheory.OrderEightSupportDisplays.bits (![{','.join(map(str,awords))}] j)) ∧
    (∀ i j, B i j = MainTheory.OrderEightSupportDisplays.bits (![{words}] i j)) ∧
    y12 = MainTheory.OrderEightSupportDisplays.bits {60 if orbit == 37 else 49} := by
  decide +kernel

''')
        names = ' '.join(str(v) for v in variables)
        arguments = ' '.join(str(v) for v in variables)
        for k, (expr, constant) in enumerate(consequences):
            expr = s.expand(expr)
            row = s.Matrix([expr.coeff(v) for v in variables])
            coefs = A.extract(independent, list(range(n+13))).T.gauss_jordan_solve(row)[0]
            assert (coefs.T*b.extract(independent, [0]))[0] == constant
            terms = ' + '.join(f'{num(v)} * hm.{fields[i][0]}'
                               for v, i in zip(coefs, independent) if v)
            lhs = str(expr).replace('**', '^')
            parts.append(f'''theorem consequence{k} {{{names} : ℝ}}
    (hm : MomentSystem {arguments}) : {lhs} = {num(s.Rational(constant))} := by
  linear_combination {terms}

''')
        if orbit != 35:
            C = s.Matrix([[s.expand(expr).coeff(v) for v in variables]
                          for expr, _ in consequences])
            constants = s.Matrix([value for _, value in consequences])
            for i in range(23):
                coefs, parameters = C.T.gauss_jordan_solve(A.row(i).T)
                coefs = coefs.subs({v: 0 for v in parameters})
                assert (coefs.T*constants)[0] == b[i]
            nonnegative = '\n'.join(f'    (hn{v} : 0 ≤ {v})' for v in variables)
            indices = [k for k in range(len(consequences)) if not (orbit == 37 and k == 7)]
            equations = '\n'.join(f'    (h{k} : {str(s.expand(consequences[k][0]))} = {num(s.Rational(consequences[k][1]))})'
                                  for k in indices)
            hypotheses = ','.join([f'hn{v}' for v in variables]+
                                   [f'h{k}' for k in indices])
            parts.append(f'''theorem reconstruct {{{names} : ℝ}}
{nonnegative}
{equations} : MomentSystem {arguments} := by
  constructor <;> linarith only [{hypotheses}]

''')
        if orbit == 38:
            clauses = ' ∧\n    '.join(f'(1/10 ≤ q{4+j}+q{8+j} ∧ 0 < q{4+j}+q{8+j})'
                                     for j in range(4))
            parts.append(f'''theorem column_positive {{{names} : ℝ}}
    (hm : MomentSystem {arguments}) :
    {clauses} := by
  refine ⟨⟨?_,?_⟩,⟨?_,?_⟩,⟨?_,?_⟩,⟨?_,?_⟩⟩
''')
            for j in range(4):
                parts.append(f'  · linarith only [consequence{3+j} hm,hm.nq{3-j}]\n')
                parts.append(f'  · linarith only [consequence{3+j} hm,hm.nq{3-j}]\n')
            parts.append('\n')
        def physical(expr):
            text = str(s.expand(expr))
            for i in range(n-1, -1, -1):
                text = re.sub(r'\bq'+str(i)+r'\b', f'(Complex.normSq (c y{i}))', text)
            for i in range(12, -1, -1):
                text = re.sub(r'\br'+str(i)+r'\b', f'(Complex.normSq (d z{i}))', text)
            return text
        conclusion = ' ∧\n    '.join(physical(expr)+' = '+num(s.Rational(constant))
                                     for expr, constant in consequences)
        proofs = ','.join(f'consequence{k} hm' for k in range(len(consequences)))
        parts.append(f'''theorem physical_consequences (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x = 0) (hd : ∀ x, x ∉ S1 → d x = 0)
    (hnc : SS.innerC c c = 1) (hnd : SS.innerC d d = 1)
    (hkl : SS.HasDistance ![c,d] 3) :
    {conclusion} := by
  have hm := SixQubit.Orbit{orbit}.moments c d hc hd hnc hnd hkl
  exact ⟨{proofs}⟩
''')
        if orbit in (37, 38):
            star = '1/10' if orbit == 37 else '1/5'
            rowsum = '1/5' if orbit == 37 else '3/10'
            low = 4 if orbit == 37 else 3
            parts.append(f'''
theorem physical_display (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x = 0) (hd : ∀ x, x ∉ S1 → d x = 0)
    (hnc : SS.innerC c c = 1) (hnd : SS.innerC d d = 1)
    (hkl : SS.HasDistance ![c,d] 3) :
    Complex.normSq (c y12) = {star} ∧
    (∀ i : Fin {nrows}, ∑ j : Fin {cols}, Complex.normSq (c (B i j)) = {rowsum}) ∧
    (∀ j : Fin {cols}, Complex.normSq (c (A j)) =
      (∑ i : Fin {nrows}, Complex.normSq (c (B i j)))-1/10) := by
  have hm := SixQubit.Orbit{orbit}.moments c d hc hd hnc hnd hkl
  refine ⟨consequence0 hm,?_,?_⟩
  · intro i
    fin_cases i <;> norm_num [B,Fin.sum_univ_succ,Fin.succ] <;>
      linarith only [{','.join(f'consequence{k} hm' for k in range(1,1+nrows))}]
  · intro j
    fin_cases j <;> norm_num [A,B,Fin.sum_univ_succ,Fin.succ] <;>
      linarith only [{','.join(f'consequence{k} hm' for k in range(low,low+cols))}]
''')
            if orbit == 38:
                parts.append('''
theorem physical_column_positive (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x = 0) (hd : ∀ x, x ∉ S1 → d x = 0)
    (hnc : SS.innerC c c = 1) (hnd : SS.innerC d d = 1)
    (hkl : SS.HasDistance ![c,d] 3) :
    ∀ j : Fin 4, 1/10 ≤ Complex.normSq (c (B 0 j))+Complex.normSq (c (B 1 j)) ∧
      0 < Complex.normSq (c (B 0 j))+Complex.normSq (c (B 1 j)) := by
  have hm := SixQubit.Orbit38.moments c d hc hd hnc hnd hkl
  have hp := column_positive hm
  intro j
  fin_cases j <;> norm_num [B,Fin.succ] <;> tauto
''')
        parts.append(f'\nend Orbit{orbit}\n')
    parts.append('\nend\nend MainTheory.OrderFivePrintedMoments\n')
    return ''.join(parts)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true')
    parser.add_argument('--output', type=Path, default=ROOT/'MainTheory/OrderFivePrintedMoments.lean')
    args = parser.parse_args()
    text = generate()
    if args.check:
        if args.output.read_text(encoding='utf8') != text:
            raise SystemExit('Generated order-five moment source differs')
        print('PASS exact order-five printed moment regeneration')
    else:
        args.output.write_text(text, encoding='utf8', newline='\n')
        print('Generated physical moment consequences for orbits 35, 37 and 38')
