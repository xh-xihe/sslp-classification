"""Generate `SixQubit/Flip5.lean`: the two-qubit flip-kernel dichotomy.

Everything algebraic is produced here rather than typed by hand: the entries of
the intertwiner `G X - X H`, the distinguished vector `w` spanning the flip
kernel line, and the `linear_combination` certificates that push each of them
through `ring`.
"""
import io
import os

import sympy as sp

u = [sp.Symbol('u%d' % i) for i in range(4)]
U = [sp.Symbol('U%d' % i) for i in range(4)]
x = [sp.Symbol('x%d' % i) for i in range(4)]

Um = sp.Matrix([[u[0], u[1]], [u[2], u[3]]])
Ud = sp.Matrix([[U[0], U[2]], [U[1], U[3]]])
G = Um * Ud
H = Ud * Um
X = sp.Matrix([[x[0], x[1]], [x[2], x[3]]])

dl = u[0] * u[3] - u[1] * u[2]
dlb = U[0] * U[3] - U[1] * U[2]
th = sum(u[i] * U[i] for i in range(4))
DD = sp.expand(th ** 2 - 4 * dl * dlb)
Wv = [sp.expand(th * U[3] - 2 * dlb * u[0]),
      sp.expand(-th * U[2] - 2 * dlb * u[1]),
      sp.expand(-th * U[1] - 2 * dlb * u[2]),
      sp.expand(th * U[0] - 2 * dlb * u[3])]
tau = u[3] * x[0] - u[2] * x[1] - u[1] * x[2] + u[0] * x[3]

C = sp.expand(G * X - X * H)
CROW = [C[0, 0], C[0, 1], C[1, 0], C[1, 1]]
SIG = sum(U[i] * x[i] for i in range(4))


def lean(e):
    """render a sympy polynomial in u,U,x as a Lean term"""
    e = sp.expand(e)
    if e == 0:
        return '0'
    out = []
    d = e.as_coefficients_dict()
    items = sorted(d.items(), key=lambda kv: sp.default_sort_key(kv[0]))
    for mon, co in items:
        co = sp.Rational(co)
        fac = []
        if abs(co) != 1:
            fac.append(str(abs(co)))
        pw = mon.as_powers_dict() if mon != 1 else {}
        for s in sorted(pw, key=sp.default_sort_key):
            n = int(pw[s])
            nm = str(s)
            if nm.startswith('U'):
                t = 'star (u %s)' % nm[1:]
            elif nm.startswith('u'):
                t = 'u %s' % nm[1:]
            else:
                t = 'x %s' % nm[1:]
            fac.extend([t] * n)
        term = ' * '.join(fac) if fac else '1'
        out.append(('-' if co < 0 else '+', term))
    s = ''
    for k, (sg, t) in enumerate(out):
        if k == 0:
            s += ('-' + t) if sg == '-' else t
        else:
            s += (' - ' if sg == '-' else ' + ') + t
    return s


def wrapped(prefix, body, cont, width=100):
    """break a Lean sum across lines"""
    toks = body.replace(' - ', ' \x00- ').replace(' + ', ' \x00+ ').split('\x00')
    line = prefix + toks[0].rstrip()
    out = []
    for t in toks[1:]:
        t = t.strip()
        if len(line) + len(t) + 1 > width:
            out.append(line)
            line = cont + t
        else:
            line = line + ' ' + t
    out.append(line)
    return out


# ---------------------------------------------------------------- certificates
ms = sp.symbols('m0:3')
COMBO = {0: (0, 1), 1: (0, 1), 2: (0, 2), 3: (1, 3)}
CERT = {}
for i in range(4):
    t = [sp.expand(DD * (1 if i == j else 0) - Wv[i] * sp.diff(tau, x[j])) for j in range(4)]
    r0, r1 = COMBO[i]
    M = [[sp.expand(sp.diff(CROW[r0], v)) for v in x],
         [sp.expand(sp.diff(CROW[r1], v)) for v in x],
         [U[0], U[1], U[2], U[3]]]
    eqs = [sp.expand(sum(ms[r] * M[r][j] for r in range(3)) - t[j]) for j in range(4)]
    sol = sp.solve(eqs, ms, dict=True)
    assert sol, i
    vals = [sp.cancel(sol[0].get(k, 0)) for k in ms]
    assert all(sp.denom(v) == 1 for v in vals), (i, vals)
    CERT[i] = (r0, r1, [sp.expand(v) for v in vals])

L = []
w = L.append

w('import Mathlib')
w('')
w('import SS.FullKL')
w('import SixQubit.Common')
w('import SixQubit.Trace5')
w('import SixQubit.Triangle')
w('')
w('set_option maxHeartbeats 4000000')
w('')
w('/-!')
w('# The two-qubit flip-kernel dichotomy of orbit 5')
w('')
w('Orbit 5 has two zero-angle qubits, so a tail amplitude is a vector of `ℂ⁴`,')
w('which we read as the `2 × 2` coefficient matrix `X` with `X r s = x (2*r+s)`.')
w('For the anchor `u` write `G = U U†` and `H = U† U`.')
w('')
w('For a one-qubit operator `F` on either factor the error `F Xᵢ` has weight two,')
w('so the Knill--Laflamme rows for all such `F` say exactly that both one-qubit')
w('partial traces of `|u⟩⟨bᵢ| + |aᵢ⟩⟨u|` vanish, i.e.')
w('')
w('```')
w('Bᵢ U† + U Aᵢ† = 0 ,      U† Bᵢ + Aᵢ† U = 0 .')
w('```')
w('')
w('Eliminating between the two gives the *intertwining relations*')
w('')
w('```')
w('G Bᵢ = Bᵢ H ,     G Aᵢ = Aᵢ H ,')
w('```')
w('whose solution space `S` is two-dimensional as soon as the two singular values')
w('of `U` are distinct.  The discriminant that decides this is')
w('')
w('```')
w('dsc u = (u†u)² - 4 |det U|²   ( = (s² - t²)²/9 for the Schmidt values s,t ) ,')
w('```')
w('')
w('and the whole dichotomy is run off it, with no local-unitary normalisation:')
w('')
w('* `line_key` -- if `dsc u ≠ 0` then every `X ∈ S` orthogonal to `u` satisfies')
w('  `dsc u • X = τ(u,X) • w`, where `w = (u†u) (adj U)† - 2 conj(det U) U` is a')
w('  fixed vector of `u^⊥`.  So all `aᵢ` and `bᵢ` lie on one line and the')
w('  two-flip relations become the odd triangle of `SixQubit.Triangle`.')
w('* `bell_pair` -- if `dsc u = 0` then `G = H = (1/6) I`, whence `Bᵢ = -6 U Aᵢ† U`')
w('  and `aᵢ† bⱼ = aⱼ† bᵢ`; with the two-flip relations that gives the twelve')
w('  cross orthogonalities wanted by `SixQubit.Trace5.bell_contradiction`.')
w('')
w('Nothing here mentions bit strings; `native_decide` and `sorry` do not occur.')
w('-/')
w('')
w('namespace SixQubit.Flip5')
w('')
w('open scoped ComplexConjugate')
w('open SixQubit.Trace5')
w('')
w('noncomputable section')
w('')
w('/-! ## The invariants of the anchor -/')
w('')
w('/-- `conj (det U)`. -/')
w('def dcj (u : Fin 4 → ℂ) : ℂ := star (u 0) * star (u 3) - star (u 1) * star (u 2)')
w('')
w('/-- `det U`. -/')
w('def dtu (u : Fin 4 → ℂ) : ℂ := u 0 * u 3 - u 1 * u 2')
w('')
w('/-- The discriminant `(u†u)² - 4 |det U|²` separating the two branches. -/')
w('def dsc (u : Fin 4 → ℂ) : ℂ := ip u u * ip u u - 4 * dcj u * dtu u')
w('')
w('/-- The bilinear pairing `Tr (adj U · X)`. -/')
w('def tau (u x : Fin 4 → ℂ) : ℂ := u 3 * x 0 - u 2 * x 1 - u 1 * x 2 + u 0 * x 3')
w('')
w('/-- The vector `w = (u†u) (adj U)† - 2 conj(det U) U`, which spans the flip')
w('kernel line inside `u^⊥` whenever `dsc u ≠ 0`. -/')
w('def ww (u : Fin 4 → ℂ) : Fin 4 → ℂ :=')
w('  ![ip u u * star (u 3) - 2 * dcj u * u 0, -(ip u u * star (u 2)) - 2 * dcj u * u 1,')
w('    -(ip u u * star (u 1)) - 2 * dcj u * u 2, ip u u * star (u 0) - 2 * dcj u * u 3]')
w('')
WW = ['ip u u * star (u 3) - 2 * dcj u * u 0', '-(ip u u * star (u 2)) - 2 * dcj u * u 1',
      '-(ip u u * star (u 1)) - 2 * dcj u * u 2', 'ip u u * star (u 0) - 2 * dcj u * u 3']
for k in range(4):
    w('@[simp] theorem ww_%d (u : Fin 4 → ℂ) : ww u %d = %s := rfl' % (k, k, WW[k]))
w('')
w('/-- The four entries of the intertwiner `G X - X H`. -/')
w('def cin (u x : Fin 4 → ℂ) : Fin 4 → ℂ :=')
for k in range(4):
    pre = '  ![' if k == 0 else '    '
    tail = ',' if k < 3 else ']'
    for ln in wrapped(pre, lean(CROW[k]), '      '):
        w(ln)
    L[-1] = L[-1] + tail
w('')
for k in range(4):
    w('@[simp] theorem cin_%d (u x : Fin 4 → ℂ) :' % k)
    for ln in wrapped('    cin u x %d = ' % k, lean(CROW[k]), '      '):
        w(ln)
    L[-1] = L[-1] + ' := rfl'
w('')
w('/-! ## The discriminant is real -/')
w('')
w('theorem dsc_star (u : Fin 4 → ℂ) : star (dsc u) = dsc u := by')
w('  simp only [dsc, dcj, dtu, ip, star_sub, star_mul\', star_add, star_star, star_ofNat]')
w('  ring')
w('')
w('/-! ## The line branch -/')
w('')
w('/-- **The flip-kernel line.**  A vector of the intertwiner kernel that is')
w('orthogonal to the anchor is carried onto the fixed vector `w` by the')
w('discriminant. -/')
w('theorem line_key (u x : Fin 4 → ℂ)')
w('    (h0 : cin u x 0 = 0) (h1 : cin u x 1 = 0) (h2 : cin u x 2 = 0) (h3 : cin u x 3 = 0)')
w('    (hs : ip u x = 0) :')
w('    dsc u * x 0 = tau u x * ww u 0 ∧ dsc u * x 1 = tau u x * ww u 1 ∧')
w('      dsc u * x 2 = tau u x * ww u 2 ∧ dsc u * x 3 = tau u x * ww u 3 := by')
w('  simp only [cin_0, cin_1, cin_2, cin_3] at h0 h1 h2 h3')
w('  simp only [ip] at hs')
w('  refine ⟨?_, ?_, ?_, ?_⟩ <;>')
w('    simp only [dsc, dcj, dtu, tau, ww_0, ww_1, ww_2, ww_3, ip]')
for i in range(4):
    r0, r1, vals = CERT[i]
    parts = []
    for nm, v in zip(['h%d' % r0, 'h%d' % r1, 'hs'], vals):
        parts.append('(%s) * %s' % (lean(v), nm))
    for ln in wrapped('  · linear_combination ', ' + '.join(parts), '      '):
        w(ln)
w('')
w('/-- Transporting the line identity through an inner product. -/')
w('theorem line_ip (u x y : Fin 4 → ℂ)')
w('    (e0 : dsc u * x 0 = tau u x * ww u 0) (e1 : dsc u * x 1 = tau u x * ww u 1)')
w('    (e2 : dsc u * x 2 = tau u x * ww u 2) (e3 : dsc u * x 3 = tau u x * ww u 3) :')
w('    dsc u * ip x y = star (tau u x) * ip (ww u) y := by')
w('  have d0 := congrArg star e0')
w('  have d1 := congrArg star e1')
w('  have d2 := congrArg star e2')
w('  have d3 := congrArg star e3')
w('  simp only [star_mul\', dsc_star] at d0 d1 d2 d3')
w('  simp only [ip]')
w('  linear_combination (y 0) * d0 + (y 1) * d1 + (y 2) * d2 + (y 3) * d3')
w('')

ROOT = os.path.normpath(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..'))
OUT = os.path.join(ROOT, 'build_zh', 'flip5_part1.lean')
io.open(OUT, 'w', encoding='utf-8', newline='\n').write('\n'.join(L) + '\n')
print('flip5 part 1: %d lines -> %s' % (len(L), OUT))
