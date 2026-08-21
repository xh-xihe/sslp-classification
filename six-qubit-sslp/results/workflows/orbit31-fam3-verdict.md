# Workflow record: orbit31-fam3

division-free form of the orbit 31 family-three relation

Run id `wx15lqd6o`; 313617 subagent tokens, 67 tool calls.

---

## summary

## 1. Blocker resolved?

Yes — your guessed rebalancing `t_ef * star a_f * a_e = star v_f * v_e - star a_f * a_e` is correct, and there is now a fully division-free, kernel-verified statement that does not mention `rho` at all.

## 2. What is machine-verified

**The identity (unconditional, no nonvanishing hypotheses):**

```
((be1*star bf1 + be2*star bf2 + be3*star bf3) - star ve * vf) * (ve * star vf - ae * star af) = 0
```

i.e. `(M_ef - conj(v_e) v_f) * (v_e conj(v_f) - a_e conj(a_f)) = 0`. The second factor is literally your `T_ef` (up to the bar-symmetric rewriting `star vf * ve - star af * ae`, which is the same object — verified).

**Hypotheses it needs, all polynomial:**

1. `hFam` — family three for the pair `{e,f}` in raw form: **b-Gram + conjugate a-Gram = u-Gram + conjugate v-Gram**, where `u_ie := conj(d at complement of B_{i,e})`. Not an extra assumption: verified in sympy to be the combination `(1/4, -1/4, -1/4, 1/4)` of the four diagonal KL conditions of Klein mask `e xor f` (and `(1/4,-1/4,1/4,-1/4)` for the second pair carried by that mask); residual 0 for all six pairs, and the span of the six pair equations + conjugates equals the span of the twelve raw conditions (rank 12 = 12 = 12).
2. `hColE i`, `hColF i` — column relations cross-multiplied: `u_ie * a_e = v_e * b_ie`. Verified to lie in the row space of the weight-one off-diagonal KL conditions for all 12 `(i,e)`. This is the division-free replacement for "rho constant along columns".
3. `hKe`, `hKf` — the moment facts at the two A rows, multiplicatively: `v_e * star v_e = a_e * star a_e`. Your existing `kernel_norm` produces exactly this.
4. **For the corollary `M_ef = star v_e * v_f` only:** `ve * star vf - ae * star af ≠ 0`. Nothing else. This single condition is `t_ef * N_ef`, so it silently encodes `a_e ≠ 0` AND `a_f ≠ 0` AND `rho_e ≠ rho_f`. It cannot be weakened to `t_ef ≠ 0` while staying inside `(a, v, M)` — see §4.

Not needed anywhere: any `rho` object, any inverse, the conjugate family-three relation, any hypothesis on `|M_ef|`.

Sharpness (verified): no cofactor of degree ≤ 1 works; none of `a_e`, `star a_f`, `N_ef`, `star v_f * v_e`, `|a_e|²`, or `1` can replace `T_ef`; and **the orientation matters** — `(M - star v_e * v_f) * star T_ef` is NOT in the ideal.

## 3. Lean source — compiles

Verified just now, not merely in isolation: I spliced this block into your actual `SixQubit/Table31.lean` (a copy, before `end SixQubit.Table31`) and compiled the whole merged file.

```
$ cd D:/UTD/Project_purdue/Lean_certification
$ lake env lean .../T31test.lean      exit=0, zero bytes of output (0 errors, 0 warnings)
$ lake env lean .../T31axioms.lean    all nine: [propext, Classical.choice, Quot.sound]
```

No `native_decide`. Names are `fam3_`-prefixed and collide with nothing already in the file. Paste verbatim before the final `end SixQubit.Table31`; the file's existing `import Mathlib` and `open scoped ComplexConjugate` are all it needs.

```lean
/-! ## Family three: a division-free pin for `M_ef = conj (v_e) * v_f`

Everything below is polynomial in the amplitudes: no `rho`, no inverses, and no
nonvanishing side condition except in the extraction corollaries.

Notation for the column pair `{e, f}` of the `4 x 4` table:

* `ae`, `af`        bottom amplitudes at the `A` row of columns `e`, `f`;
* `be1 be2 be3`     bottom amplitudes at the `B` rows of column `e`, likewise `bf`;
* `ve`, `vf`        `conj (d at the complement of A_e)`, resp. of `A_f`;
* `ue1 ue2 ue3`     `conj (d at the complement of B_{i,e})`, likewise `uf`;
* `M_ef = be1 * star bf1 + be2 * star bf2 + be3 * star bf3`, the `B`-column Gram.
-/

/-- **The family-three identity**, one bottom row chosen in each column.

`p, q` are the bottom and top amplitude at *any* chosen position of column `e`
(so `(p, q) = (ae, ve)` on the `A` row and `(p, q) = (b_ie, u_ie)` on a `B` row),
and `p', q'` likewise for column `f`.

* `hFam` is the raw family-three relation for the pair `{e, f}`: "b-Gram plus
  conjugate a-Gram equals u-Gram plus conjugate v-Gram".  It is the combination
  `(1/4, -1/4, -1/4, 1/4)` of the four diagonal Knill-Laflamme conditions of the
  Klein mask `e xor f`.
* `hColE i`, `hColF i` are the column relations (`rho` constant along a column)
  in cross-multiplied form, anchored at the chosen position.
* `hPe`, `hPf` are the phase-transfer facts at the chosen positions; on the `A`
  rows they are literally the moment facts `|v| = |a|`.

The conclusion carries the factor `q * star q' - p * star p'` and is
unconditionally true; it degenerates to `0 = 0` exactly when that factor
vanishes, which is where `M_ef` genuinely is not determined. -/
theorem fam3_row_key
    (ae af ve vf p q p' q' be1 be2 be3 bf1 bf2 bf3 ue1 ue2 ue3 uf1 uf2 uf3 : ℂ)
    (hFam : (be1 * star bf1 + be2 * star bf2 + be3 * star bf3) + star ae * af
              = (ue1 * star uf1 + ue2 * star uf2 + ue3 * star uf3) + star ve * vf)
    (hColE1 : ue1 * p = q * be1)
    (hColE2 : ue2 * p = q * be2)
    (hColE3 : ue3 * p = q * be3)
    (hColF1 : uf1 * p' = q' * bf1)
    (hColF2 : uf2 * p' = q' * bf2)
    (hColF3 : uf3 * p' = q' * bf3)
    (hPe : star ve * q = star ae * p)
    (hPf : vf * star q' = af * star p') :
    ((be1 * star bf1 + be2 * star bf2 + be3 * star bf3) - star ve * vf)
      * (q * star q' - p * star p') = 0 := by
  have hC1 : star uf1 * star p' = star q' * star bf1 := by
    rw [← star_mul', ← star_mul', hColF1]
  have hC2 : star uf2 * star p' = star q' * star bf2 := by
    rw [← star_mul', ← star_mul', hColF2]
  have hC3 : star uf3 * star p' = star q' * star bf3 := by
    rw [← star_mul', ← star_mul', hColF3]
  linear_combination
    (-(p * star p')) * hFam
      - (star bf1 * star q') * hColE1 - (star bf2 * star q') * hColE2
      - (star bf3 * star q') * hColE3
      - (ue1 * p) * hC1 - (ue2 * p) * hC2 - (ue3 * p) * hC3
      - (star ae * p) * hPf - (vf * star q') * hPe

/-- The `A`-row case of `fam3_row_key`.  Here the phase-transfer hypotheses are
exactly the moment facts `p_1 (v-bar) = p_0 (v)` at `A_e` and `A_f`, stated
multiplicatively so that they stay division free (see `kernel_norm`). -/
theorem fam3_key_of_raw
    (ae af ve vf be1 be2 be3 bf1 bf2 bf3 ue1 ue2 ue3 uf1 uf2 uf3 : ℂ)
    (hFam : (be1 * star bf1 + be2 * star bf2 + be3 * star bf3) + star ae * af
              = (ue1 * star uf1 + ue2 * star uf2 + ue3 * star uf3) + star ve * vf)
    (hColE1 : ue1 * ae = ve * be1)
    (hColE2 : ue2 * ae = ve * be2)
    (hColE3 : ue3 * ae = ve * be3)
    (hColF1 : uf1 * af = vf * bf1)
    (hColF2 : uf2 * af = vf * bf2)
    (hColF3 : uf3 * af = vf * bf3)
    (hKe : ve * star ve = ae * star ae)
    (hKf : vf * star vf = af * star af) :
    ((be1 * star bf1 + be2 * star bf2 + be3 * star bf3) - star ve * vf)
      * (ve * star vf - ae * star af) = 0 :=
  fam3_row_key ae af ve vf ae ve af vf be1 be2 be3 bf1 bf2 bf3
    ue1 ue2 ue3 uf1 uf2 uf3
    hFam hColE1 hColE2 hColE3 hColF1 hColF2 hColF3
    (by linear_combination hKe) hKf

/-- Extraction of `M_ef` from the `A`-row identity.  The single division-free
side condition `ve * star vf ≠ ae * star af` packages all three nondegeneracy
requirements at once: `ae ≠ 0`, `af ≠ 0` and `rho_e ≠ rho_f`. -/
theorem fam3_M_eq_of_raw
    (ae af ve vf be1 be2 be3 bf1 bf2 bf3 ue1 ue2 ue3 uf1 uf2 uf3 : ℂ)
    (hFam : (be1 * star bf1 + be2 * star bf2 + be3 * star bf3) + star ae * af
              = (ue1 * star uf1 + ue2 * star uf2 + ue3 * star uf3) + star ve * vf)
    (hColE1 : ue1 * ae = ve * be1)
    (hColE2 : ue2 * ae = ve * be2)
    (hColE3 : ue3 * ae = ve * be3)
    (hColF1 : uf1 * af = vf * bf1)
    (hColF2 : uf2 * af = vf * bf2)
    (hColF3 : uf3 * af = vf * bf3)
    (hKe : ve * star ve = ae * star ae)
    (hKf : vf * star vf = af * star af)
    (hT : ve * star vf - ae * star af ≠ 0) :
    be1 * star bf1 + be2 * star bf2 + be3 * star bf3 = star ve * vf := by
  rcases mul_eq_zero.mp
      (fam3_key_of_raw ae af ve vf be1 be2 be3 bf1 bf2 bf3
        ue1 ue2 ue3 uf1 uf2 uf3
        hFam hColE1 hColE2 hColE3 hColF1 hColF2 hColF3 hKe hKf) with h | h
  · exact sub_eq_zero.mp h
  · exact absurd h hT

/-- The bridge: the raw family-three relation together with the column relations
already implies the *cleared* relation `hH3`, which is the original
`M_ef * t_ef = - star (N_ef * t_ef)` multiplied through by `N_ef = ae * star af`.
No moment fact and no nonvanishing hypothesis is needed here. -/
theorem fam3_hH3_of_raw
    (ae af ve vf be1 be2 be3 bf1 bf2 bf3 ue1 ue2 ue3 uf1 uf2 uf3 : ℂ)
    (hFam : (be1 * star bf1 + be2 * star bf2 + be3 * star bf3) + star ae * af
              = (ue1 * star uf1 + ue2 * star uf2 + ue3 * star uf3) + star ve * vf)
    (hColE1 : ue1 * ae = ve * be1)
    (hColE2 : ue2 * ae = ve * be2)
    (hColE3 : ue3 * ae = ve * be3)
    (hColF1 : uf1 * af = vf * bf1)
    (hColF2 : uf2 * af = vf * bf2)
    (hColF3 : uf3 * af = vf * bf3) :
    (be1 * star bf1 + be2 * star bf2 + be3 * star bf3)
        * (star vf * ve - star af * ae)
      = -(ae * star af) * (vf * star ve - af * star ae) := by
  have hC1 : star uf1 * star af = star vf * star bf1 := by
    rw [← star_mul', ← star_mul', hColF1]
  have hC2 : star uf2 * star af = star vf * star bf2 := by
    rw [← star_mul', ← star_mul', hColF2]
  have hC3 : star uf3 * star af = star vf * star bf3 := by
    rw [← star_mul', ← star_mul', hColF3]
  linear_combination
    (-(ae * star af)) * hFam
      - (star bf1 * star vf) * hColE1 - (star bf2 * star vf) * hColE2
      - (star bf3 * star vf) * hColE3
      - (ue1 * ae) * hC1 - (ue2 * ae) * hC2 - (ue3 * ae) * hC3

/-- The `(a, v, M)`-only identity.  Division free: no `rho`, no inverses, no side
conditions.  `star vf * ve - star af * ae` is the division-free stand-in for
`t_ef * star af * ae`. -/
theorem fam3_key (ae af ve vf M : ℂ)
    (hKe : ve * star ve = ae * star ae)
    (hKf : vf * star vf = af * star af)
    (hH3 : M * (star vf * ve - star af * ae)
             = -(ae * star af) * (vf * star ve - af * star ae)) :
    (M - star ve * vf) * (star vf * ve - star af * ae) = 0 := by
  linear_combination hH3 - (star vf * vf) * hKe - (ae * star ae) * hKf

/-- The usable corollary of `fam3_key`. -/
theorem fam3_M_eq (ae af ve vf M : ℂ)
    (hKe : ve * star ve = ae * star ae)
    (hKf : vf * star vf = af * star af)
    (hH3 : M * (star vf * ve - star af * ae)
             = -(ae * star af) * (vf * star ve - af * star ae))
    (hT : star vf * ve - star af * ae ≠ 0) :
    M = star ve * vf := by
  rcases mul_eq_zero.mp (fam3_key ae af ve vf M hKe hKf hH3) with h | h
  · exact sub_eq_zero.mp h
  · exact absurd h hT

/-- On a `B` row the phase-transfer hypothesis of `fam3_row_key` is itself a
consequence of that row's column relation and moment fact, provided the bottom
amplitude there is nonzero.  This is what rescues the `ae = 0` branch, at the
price of assuming `b ≠ 0` instead. -/
theorem fam3_phase_transfer (ae ve b u : ℂ)
    (hCol : u * ae = ve * b)
    (hMom : u * star u = b * star b)
    (hb : b ≠ 0) :
    star ve * u = star ae * b := by
  have hCb : star u * star ae = star ve * star b := by
    rw [← star_mul', ← star_mul', hCol]
  have h : (star ve * u - star ae * b) * star b = 0 := by
    linear_combination (-u) * hCb + (star ae) * hMom
  rcases mul_eq_zero.mp h with h' | h'
  · exact sub_eq_zero.mp h'
  · exact absurd (star_eq_zero.mp h') hb

/-- If `ae = 0` then the moment fact forces the whole `A`-row factor to vanish,
so the `A`-row identity is vacuous and `M_ef` is genuinely undetermined by it. -/
theorem fam3_T_zero_of_ae (ae af ve vf : ℂ) (h0 : ae = 0)
    (hKe : ve * star ve = ae * star ae) :
    star vf * ve - star af * ae = 0 := by
  have hv : ve = 0 := by
    rcases mul_eq_zero.mp (by rw [hKe, h0]; ring : ve * star ve = 0) with h | h
    · exact h
    · exact star_eq_zero.mp h
  rw [hv, h0]; simp

/-- Symmetrically for `af = 0`. -/
theorem fam3_T_zero_of_af (ae af ve vf : ℂ) (h0 : af = 0)
    (hKf : vf * star vf = af * star af) :
    star vf * ve - star af * ae = 0 := by
  have hv : vf = 0 := by
    rcases mul_eq_zero.mp (by rw [hKf, h0]; ring : vf * star vf = 0) with h | h
    · exact h
    · exact star_eq_zero.mp h
  rw [hv, h0]; simp
```

Test files, if you want to re-run the check yourself:
`C:\Users\richa\AppData\Local\Temp\claude\D--UTD-Project-purdue\e2435927-3651-49b0-acfb-31f3430ee257\scratchpad\T31test.lean` (merged file) and `...\T31axioms.lean` (same + the nine `#print axioms`), and `...\fam3_block.lean` (just the block above).

**One correction to what was claimed earlier, and it matters.** The general `(k,l)` row identity is *not* in the ideal generated by family three + column relations + moments alone. `fam3_row_key` exposes two extra hypotheses `hPe`, `hPf` (phase transfer at the chosen row). On the A rows those *are* the moment facts, so `fam3_key_of_raw` is unconditional. On a B row they are not automatic — `fam3_phase_transfer` derives them, and that derivation genuinely needs `b ≠ 0` (the cofactor certificate is `(star v_e * u - star a_e * b) * star b = -u*hCb + star a_e * hMom`; the `b` factor cannot be removed). Net side condition is the same as previously claimed, but the honest statement is two lemmas, not one.

## 4. Degenerate cases

The identity never degenerates — it is `0 = 0` there. What fails is the *extraction* of `M_ef`, and it fails **truly**, not just unprovably. Numeric counterexamples (independently reproduced twice): `rho ≡ 1` on all four columns, i.e. `d = star(c)` everywhere with random `c`, satisfies all twelve family-three conditions (residual 1.8e-15), all twelve column relations exactly, all sixteen moment facts exactly — and has `|M_01 - star(v_0) v_1| = 3.45`. So there is no unconditional version; `hT` is mandatory.

- **`t_ef = 0` (columns share a phase), `a_e, a_f ≠ 0`.** `T_ef = 0`, `M_ef` genuinely free. Nothing in this block closes it. Caller must branch on `SamePhase` (you already have that `def`) and handle it by a different argument.
- **`a_e = 0`** (hence `v_e = 0` by the moment fact): `fam3_T_zero_of_ae` shows `T_ef = 0` identically, so the A-row identity is vacuous whatever `rho` does. Two sub-branches:
  - `a_e = 0` and `rho_e = rho_f`: conclusion is **false** (counterexample (B2), residual 1.8e-15, `|M_01 - star(v_0) v_1| = 2.21`).
  - `a_e = 0` and `rho_e ≠ rho_f`: conclusion is **true** (`M_ef = 0`), but the A-row statement cannot see it — with `a_e = v_e = 0` all trace of column `e`'s phase has left the `(a, v, M)` data. **No hypothesis stated in `a, v, M` alone can cover this branch.** The fix is `fam3_row_key` on a B row, fed by `fam3_phase_transfer`, with side condition `b_ke ≠ 0`, `b_lf ≠ 0` instead of `a_e ≠ 0`, `a_f ≠ 0`. Still division-free; it just drags the `u` amplitudes into the statement.
- **`a_f = 0`**: symmetric, `fam3_T_zero_of_af`.
- **This branching is not hypothetical.** Your moment facts admit `alpha_0 = 0`: `beta_i0 = 1/24`, `beta_ie = 5/72` for `e = 1,2,3` gives row sums `1/4`, `alpha = (0, 1/12, 1/12, 1/12)`, sum `1/4`, all `≥ 0`. So `a_e ≠ 0` is not free from the polytope. Either branch on it or use the B-row identity uniformly.

## 5. Next step

The Lean is done for this layer; the remaining work is transcription, and there is exactly one trust boundary left.

1. **Discharge `hFam` inside Lean.** This is the trust boundary: the claim "family three = `(1/4, -1/4, -1/4, 1/4)` of the four diagonal KL conditions of Klein mask `e xor f`" (and `(1/4, -1/4, 1/4, -1/4)` for the second pair on each mask) is **verified in sympy but not yet in Lean**. Concretely: derive `hFam` for each of the six pairs from the twelve diagonal KL conditions by `linear_combination` with those exact coefficients. Cheap, mechanical, but do it — it is the only step between the raw KL conditions and `fam3_M_eq_of_raw` that is still on paper.
2. **Discharge `hColE i` / `hColF i`** likewise from the weight-one off-diagonal KL conditions (masks `100000/010000/001000`); verified in sympy to lie in that row space for all 12 `(i,e)`. Same shape of work as (1).
3. **Discharge `hKe`, `hKf`** with the existing `kernel_norm` — already the right statement, no work.
4. **Then instantiate `fam3_M_eq_of_raw` for the six column pairs** and feed the resulting `M_ef = star v_e * v_f` into `kernel_identity` / `all_distinct` / `partition31`, which is where it was always headed. In the `all_distinct` branch every `t_ef ≠ 0`, so `hT` reduces to `a_e ≠ 0` for all four columns; discharge that from the polytope where you can and fall back to `fam3_row_key` + `fam3_phase_transfer` on a B row where you cannot.
5. **The `(4)`, `(2,2)`, `(2,1,1)` branches still need the `t_ef = 0` argument, which does not exist yet in any form.** That is the real remaining mathematical hole, unchanged by today's work.

Practical note for whoever does (1) and (2): the Groebner route dies in the 32-variable setting (2-minute timeout), and sympy's `reduced` against a non-Groebner generator list returns a nonzero remainder even when the polynomial *is* in the ideal, so it is useless as a membership test here. Derive the cofactors by hand from the mechanism and confirm with a single `sp.expand(goal - cert) == 0` — instant, and it transcribes directly into `linear_combination`.

## derivations

## statement

Write T_ef := star v_f * v_e - star a_f * a_e   (this is the division-free stand-in for t_ef * star a_f * a_e; the user's guessed rebalancing is CORRECT).

THE IDENTITY (Lean, over ℂ, all hypotheses and the goal division-free):

theorem orbit31_family3_key (a_e a_f v_e v_f M : ℂ)
    (hve : v_e * star v_e = a_e * star a_e)
    (hvf : v_f * star v_f = a_f * star a_f)
    (hH3 : M * (star v_f * v_e - star a_f * a_e)
             = -(a_e * star a_f) * (v_f * star v_e - a_f * star a_e)) :
    (M - star v_e * v_f) * (star v_f * v_e - star a_f * a_e) = 0 := by
  linear_combination hH3 - (star v_f * v_f) * hve - (a_e * star a_e) * hvf

and the usable corollary

theorem orbit31_M_eq (a_e a_f v_e v_f M : ℂ)
    (hve : v_e * star v_e = a_e * star a_e)
    (hvf : v_f * star v_f = a_f * star a_f)
    (hH3 : M * (star v_f * v_e - star a_f * a_e)
             = -(a_e * star a_f) * (v_f * star v_e - a_f * star a_e))
    (hT : star v_f * v_e - star a_f * a_e ≠ 0) :
    M = star v_e * v_f := by
  rcases mul_eq_zero.mp (orbit31_family3_key a_e a_f v_e v_f M hve hvf hH3) with h | h
  · exact sub_eq_zero.mp h
  · exact absurd h hT

Key structural facts established:
  * REBALANCING (verified): t_ef * star a_f * a_e = star v_f * v_e - star a_f * a_e = T_ef,
    and its bar  conj(t_ef) * a_f * star a_e = star T_ef = v_f * star v_e - a_f * star a_e.
  * CLEARING (verified): M*T_ef + N_ef*star T_ef  =  N_ef * ( M*t_ef + star(N_ef*t_ef) )
    exactly, with N_ef = a_e * star a_f. So hH3 is the ORIGINAL family-three relation
    multiplied by N_ef. Deriving hH3 from the raw relation is always legitimate (it is a
    multiplication); going back needs a_e ≠ 0 and a_f ≠ 0.
  * SHARPNESS (verified): no cofactor of degree ≤ 1, and none of a_e, star a_f, N_ef,
    star v_f * v_e, |a_e|^2, nor 1, can replace T_ef. T_ef is the minimal legal cofactor.
  * ORIENTATION WARNING (verified): (M - star v_e * v_f) * star T_ef is NOT in the ideal.
    Using conj(T) in place of T is wrong. The orientation T_ef = star v_f * v_e - star a_f * a_e
    (indices f-bar times e) is forced.

## hypotheses

hve : v_e * star v_e = a_e * star a_e   (i.e. |v_e| = |a_e|, stated multiplicatively so it is division-free)

hvf : v_f * star v_f = a_f * star a_f   (i.e. |v_f| = |a_f|)

hH3 : M * (star v_f * v_e - star a_f * a_e) = -(a_e * star a_f) * (v_f * star v_e - a_f * star a_e)   — the family-three relation M_ef t_ef = -star(N_ef t_ef) after multiplying through by N_ef = a_e * star a_f. Verified to equal N_ef times the original, so it is implied by the original with no nonvanishing side condition.

hT : star v_f * v_e - star a_f * a_e ≠ 0   — needed ONLY for the corollary M = star v_e * v_f, not for the identity itself. Over ℂ this is equivalent to (a_e ≠ 0 and a_f ≠ 0 and t_ef ≠ 0, i.e. rho_e ≠ rho_f).

NOT needed: a_e ≠ 0, a_f ≠ 0, any existence or definition of rho, the conjugate family-three relation (star M * star t = -N t), and any hypothesis on M's modulus. Verified: the conjugate relation is not used by the certificate.

## verified_how

Four independent machine checks.

(1) SYMPY, explicit ideal-membership certificate. Conjugates treated as independent symbols (ae,aeb,af,afb,ve,veb,vf,vfb,M) with a formal bar involution. With g1 = ve*veb - ae*aeb, g2 = vf*vfb - af*afb, g3 = M*T + (ae*afb)*Tbar and goal P = (M - veb*vf)*T, expanded P - (g3 - (vfb*vf)*g1 - (ae*aeb)*g2) to exactly 0. This certificate is what becomes the Lean linear_combination.

(2) SYMPY, Groebner reduction. Lex and grevlex Groebner bases of <g1,g2,g3> in the 10 variables reduce P to remainder 0. Negative control: M - veb*vf alone reduces to itself (nonzero), confirming the T factor is genuinely necessary and M is unconstrained when T = 0. Further controls showed (M - veb*vf)*star T is NOT in the ideal, and no degree-<=1 or degree-2 monomial cofactor works.

(3) SYMPY, rho-parametrisation substitution (the check requested in the task). Imposed |rho| = 1 exactly by writing conj(rho_e) = 1/rho_e, set v_e = conj(rho_e) a_e, conj(v_e) = rho_e conj(a_e), same for f. Confirmed g1, g2 vanish identically; confirmed the rebalancing T = t*afb*ae; solved g3 for M and got exactly conj(v_e) v_f; and confirmed P minus the certificate is 0 with M left free.

(4) EXACT NUMERICS. 200 random trials over Gaussian rationals (rho drawn on the unit circle as z/conj(z) to stay exact), checking: the certificate holds unconditionally, the goal vanishes whenever the hypothesis does with M arbitrary, and M = conj(v_e) v_f satisfies the hypothesis. Zero failures.

(5) LEAN KERNEL — the decisive check. Wrote the theorem in the actual project and compiled it with `lake env lean` against the pinned Mathlib (toolchain leanprover/lean4:v4.27.0). File: C:\Users\richa\AppData\Local\Temp\claude\D--UTD-Project-purdue\e2435927-3651-49b0-acfb-31f3430ee257\scratchpad\O31DivFree.lean. It compiles with ZERO errors and ZERO warnings, no native_decide, and #print axioms reports exactly [propext, Classical.choice, Quot.sound] for all four theorems (key, M_eq, and both degenerate lemmas). The one-line `linear_combination hH3 - (star v_f * v_f) * hve - (a_e * star a_e) * hvf` closes the main goal.

Supporting files: o31_divfree.py, o31_divfree.out, o31_opt.py in the scratchpad.

## verification_output

=== SYMPY (o31_divfree.py) ===

STEP 1.  rho-parametrisation, and the rebalancing  t_ef * conj(a_f) * a_e = T_ef
rho-param:  v_e = ae/rho_e   conj(v_e) = aeb*rho_e
            v_f = af/rho_f   conj(v_f) = afb*rho_f
t_ef = -1 + rho_f/rho_e    conj(t_ef) = rho_e/rho_f - 1

  T_ef - t_ef*conj(a_f)*a_e   under rho-param  --> 0
  [VERIFIED]  t_ef * conj(a_f) * a_e = conj(v_f) v_e - conj(a_f) a_e = T_ef
  conj(T_ef) - conj(t_ef)*a_f*conj(a_e) under rho-param --> 0
  [VERIFIED]  conj(t_ef) * a_f * conj(a_e) = conj(T_ef)   (the bar of the above)

STEP 2.  Clearing denominators in the family-three relation
division-free candidate g3 :=  M*T_ef + N_ef*conj(T_ef) =
    -M*ae*afb + M*ve*vfb - ae*aeb*af*afb + ae*afb*veb*vf

  ( M*T + N*conj(T) ) / ( M*t + conj(N)*conj(t) )  = ae*afb
  [VERIFIED]  M*T_ef + N_ef*conj(T_ef)  =  N_ef * ( M*t_ef + conj(N_ef)*conj(t_ef) )
  => the two relations are EQUIVALENT exactly when N_ef = a_e*conj(a_f) != 0,
     i.e. when a_e != 0 AND a_f != 0.

  original relation at M = conj(v_e)*v_f, under rho-param  --> 0
  [VERIFIED]  M = conj(v_e) v_f solves the original rho-form relation.

STEP 3.  THE IDENTITY   (M - conj(v_e) v_f) * T_ef = 0   and its certificate
goal   P := (M - conj(v_e)*v_f) * T_ef =
    -M*ae*afb + M*ve*vfb + ae*afb*veb*vf - ve*veb*vf*vfb

hypotheses (each must vanish):
   g1 =  -ae*aeb + ve*veb
   g2 =  -af*afb + vf*vfb
   g3 =  -M*ae*afb + M*ve*vfb - ae*aeb*af*afb + ae*afb*veb*vf

EXPLICIT CERTIFICATE:
   P  ==  1*g3  -  (conj(v_f)*v_f)*g1  -  (a_e*conj(a_e))*g2
   P - certificate  = 0
   [VERIFIED]  exact polynomial identity, no division anywhere.

independent check: Groebner reduction of P modulo <g1,g2,g3>
   remainder = 0
   [VERIFIED]  P lies in the ideal generated by the three hypotheses.

negative control: is  M - conj(v_e)*v_f  ITSELF in the ideal (no T factor)?
   remainder = M - veb*vf
   [as expected] NO -- the factor T_ef is genuinely necessary;
   M is unconstrained when T_ef = 0.

STEP 4.  Substitute the rho-parametrisation v = conj(rho) a, |rho| = 1
  g1 under rho-param = 0
  g2 under rho-param = 0
  g3 under rho-param = (-M*ae*afb*rho_e*rho_f + M*ae*afb*rho_f**2 + ae*aeb*af*afb*rho_e**2 - ae*aeb*af*afb*rho_e*rho_f)/(rho_e*rho_f)
  solving g3 for M   =>  M = [aeb*af*rho_e/rho_f]
  conj(v_e)*v_f      = aeb*af*rho_e/rho_f
  difference         = 0
  [VERIFIED]  the rho-form relation forces M = conj(v_e) v_f (when rho_e != rho_f).

  P - certificate, under rho-param, M free  --> 0
  [VERIFIED]  identity reduces to zero symbolically under the parametrisation.

STEP 5.  Random numerical check over C
  200 random Gaussian-rational trials, exact arithmetic:  failures = 0
  [VERIFIED] numerically.

STEP 6.  Degenerate cases
  a_e = 0  =>  (via |v_e|=|a_e|) v_e = 0  =>  T_ef = 0
  a_f = 0  =>  (via |v_f|=|a_f|) v_f = 0  =>  T_ef = 0
  t_ef = 0 (rho_e = rho_f) with a_e,a_f != 0: hypothesis is vacuous, M free.
  check: g3 at rho_e = rho_f, M free  --> 0

STEP 7.  Lean linear_combination cofactors
  hve  : v_e * star v_e = a_e * star a_e   ->  l-r = -ae*aeb + ve*veb
  hvf  : v_f * star v_f = a_f * star a_f   ->  l-r = -af*afb + vf*vfb
  hH3  : M*T = -(a_e * star a_f) * star T  ->  l-r = -M*ae*afb + M*ve*vfb - ae*aeb*af*afb + ae*afb*veb*vf
  goal : (M - star v_e * v_f) * T = 0      ->  l-r = -M*ae*afb + M*ve*vfb + ae*afb*veb*vf - ve*veb*vf*vfb
  certificate:  goal = (1)*hH3 + (-(star v_f * v_f))*hve + (-(a_e * star a_e))*hvf
  residual = 0
ALL CHECKS PASSED

=== SYMPY SHARPNESS / ORIENTATION (o31_opt.py) ===
is (M - conj(ve)vf) * T           in ideal?  True
is (M - conj(ve)vf) * conj(T)     in ideal?  False
   cofactor 1                  -> False
   cofactor a_e                -> False
   cofactor conj(a_f)          -> False
   cofactor a_e*conj(a_f)=N    -> False
   cofactor conj(v_f)v_e       -> False
   cofactor |a_e|^2            -> False
   cofactor |T|^2              -> True
   cofactor T*conj(a_f)a_e     -> True
search for any lower-degree cofactor c with c*D in the ideal:
   degree<=1 cofactors that work: []
   degree-2 monomial cofactors that work: []

=== LEAN KERNEL (lake env lean, Mathlib pinned, lean4 v4.27.0) ===
$ lake env lean .../O31DivFree.lean
'Orbit31DivFree.key' depends on axioms: [propext, Classical.choice, Quot.sound]
'Orbit31DivFree.M_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'Orbit31DivFree.T_eq_zero_of_ae' depends on axioms: [propext, Classical.choice, Quot.sound]
'Orbit31DivFree.T_eq_zero_of_af' depends on axioms: [propext, Classical.choice, Quot.sound]
(no errors, no warnings)

## degenerate_cases

All three degenerate cases collapse into one clean statement: they all force T_ef = 0, in which case the identity reads 0 = 0 and M_ef is genuinely NOT determined. This is why the conclusion must carry the T_ef factor rather than being an equation for M.

a_e = 0. Then hve gives v_e * star v_e = 0, hence v_e = 0 over ℂ. So T_ef = star v_f * 0 - star a_f * 0 = 0. Both terms of the hypothesis vanish and hH3 is vacuous; M is arbitrary. Machine-checked as Lean theorem T_eq_zero_of_ae. Note NO nonvanishing hypothesis on a_e is needed for the identity — the identity is unconditionally true, it just becomes vacuous.

a_f = 0. Symmetrically hvf gives v_f = 0, so T_ef = 0 * v_e - 0 * a_e = 0. Same conclusion. Machine-checked as Lean theorem T_eq_zero_of_af.

t_ef = 0 (i.e. rho_e = rho_f, the columns share a phase) with a_e, a_f both nonzero. Then T_ef = t_ef * star a_f * a_e = 0. Verified in sympy: g3 evaluated at rho_f = rho_e with M free reduces to 0, so the family-three relation imposes nothing and M_ef is free. This is the substantive degenerate case and it is not removable — it is a real gap in the column-pair argument that must be handled elsewhere (e.g. by a separate argument when two columns are in phase).

Conversely, over ℂ, T_ef ≠ 0 holds iff a_e ≠ 0 AND a_f ≠ 0 AND t_ef ≠ 0. So the single division-free side condition `star v_f * v_e - star a_f * a_e ≠ 0` packages all three nondegeneracy requirements at once, which is exactly what makes it a usable Lean hypothesis — one can discharge it without ever mentioning rho.

One further caution, machine-verified: the equivalence of hH3 with the original rho-form relation M_ef t_ef = -star(N_ef t_ef) is only two-way when N_ef = a_e * star a_f ≠ 0. The direction actually needed (original ⟹ hH3) is just multiplication by N_ef and is unconditionally valid, so nothing is lost. But do not try to recover the original relation from hH3 when a_e or a_f can vanish.

## confidence

machine-verified

## statement

Headline (the form you asked for, in a_e, a_f, v_e, v_f, M_ef only):

    (M_ef - star (v e) * v f) * (v e * star (v f) - a e * star (a f)) = 0

Lean-style, spelled out:

    theorem fam3_pin (e f : Fin 4) (hef : e ≠ f) :
        (M e f - star (v e) * v f) * (v e * star (v f) - a e * star (a f)) = 0

Corollary: if  v e * star (v f) ≠ a e * star (a f)  then  M e f = star (v e) * v f.

There is a strictly stronger MODULUS-FREE form, which is the one I actually
certified first and from which the headline follows by rewriting with the two
moment facts.  It uses no unimodularity at all:

    (M e f - star (v e) * v f) * (v e * star (v f) - a e * star (a f))
      = a e * star (a e) * (a f * star (a f)) - v e * star (v e) * (v f * star (v f))

and equivalently, in the shape that is closest to the raw conditions,

    M e f * (a e * star (a f) - v e * star (v f))
      + a e * star (a f) * (star (a e) * a f - star (v e) * v f) = 0.

ROUTE (independent of the rho-rebalancing guess).  Recomputing the twelve Klein
diagonal KL conditions from the definition and taking the ±1/4 combinations
listed below shows that family three is EXACTLY, with no rho and no division,
the six complex equations (one per unordered column pair)

    (F1)   sum_i b_ie * star (b_if) + star (a e) * a f
             = sum_i u_ie * star (u_if) + star (v e) * v f

where u_ie := star (d at the complement of B_{i,e}) is the B-row analogue of v_e.
That is: "b-Gram + conjugate a-Gram = u-Gram + conjugate v-Gram".  rho never
appears; it is only the elimination of the u-Gram that costs anything.

MORE GENERAL LEMMA (certified for all 16 row choices).  For any bottom position
k in column e and l in column f, writing (c^e_0,...,c^e_3) = (a_e,b_1e,b_2e,b_3e)
and (T^e_0,...,T^e_3) = (v_e,u_1e,u_2e,u_3e),

    (M e f - star (v e) * v f) * (T^e_k * star (T^f_l) - c^e_k * star (c^f_l)) = 0.

The headline is the case k = l = 0 (A-row).  Taking k or l on a B row is what
rescues the a_e = 0 branch (see degenerate_cases).

## hypotheses

(H1) FAMILY THREE for the pair {e,f}, in its rho-free raw form:  sum_i b_ie * star (b_if) + star (a e) * a f = sum_i u_ie * star (u_if) + star (v e) * v f,  where u_ie := star (d at the complement of B_{i,e}).  This is not an extra assumption: it is exactly the combination (1/4)D(m,000000) - (1/4)D(m,z1) - (1/4)D(m,z2) + (1/4)D(m,m) of the four raw diagonal KL conditions of the Klein mask m = e xor f, with the sign of the last two terms flipped for the second pair carried by that mask (exact coefficients printed in verification_output for all six pairs; residual 0). Division-free.

(H2) COLUMN RELATIONS in cross-multiplied form, for i = 1,2,3:  u_ie * a e = v e * b_ie  (column e)  and  star (u_if) * star (a f) = star (v f) * star (b_if)  (column f).  In raw amplitudes: star (c_{A_e}) * d_{Bbar_{i,e}} = star (c_{B_{i,e}}) * d_{Abar_e}.  I machine-checked that each of these lies in the row space of the raw weight-one OFF-diagonal KL conditions (masks 100000 / 010000 / 001000, 12 dressings each), so this is the division-free replacement for 'rho is constant along columns' and needs no rho object. Division-free.

(H3) The two MOMENT FACTS at the A row of the two columns:  v e * star (v e) = a e * star (a e)  and  v f * star (v f) = a f * star (a f).  These are p_1(vbar) = p_0(v) at positions A_e and A_f, which you have already verified. Division-free.  Needed ONLY to pass from the modulus-free form to the '= 0' headline; the modulus-free identity follows from (H1)+(H2) alone.

(H4) FOR THE COROLLARY ONLY, the nonvanishing  v e * star (v f) - a e * star (a f) ≠ 0.  Nothing else. This is division-free and is exactly t_ef * N_ef, so it is STRICTLY STRONGER than t_ef ≠ 0: it additionally forces a e ≠ 0 and a f ≠ 0.  It is unavoidable in a statement written in a, v, M alone (see degenerate_cases).

## verified_how

Four sympy scripts, all exact (rational/integer arithmetic, no floating point in the certificates); every check is an sp.expand(...) == 0 or an exact rank/solve over Q.

1. C:\Users\richa\AppData\Local\Temp\claude\D--UTD-Project-purdue\e2435927-3651-49b0-acfb-31f3430ee257\scratchpad\fam3raw.py
   Rebuilds the twelve Klein-mask DIAGONAL conditions straight from the KL
   definition (P = X^e Z^z, P|x> = (-1)^{z.x}|x xor e>; sum over S0 = sum over S1)
   on the real orbit-31 fibers from relgen.setup(31), with 32 independent formal
   amplitudes and 32 formal conjugates.  NO substitution of any kind is made.
   Then it compares the C-span of those 12 polynomials with the span of the six
   pair equations (F1) together with their formal conjugates: ranks 12, 12, 12
   for raw / new / stacked, i.e. the spans coincide.  It also solves exactly for
   the coefficients writing each (F1) in terms of the four raw conditions of its
   mask (residual 0 in every case).

2. ...\scratchpad\fam3elim.py
   Part 1: checks that the raw column relation star(c_A) d_Bbar - star(c_B) d_Abar
   lies in the row space of the weight-one off-diagonal KL conditions, for all
   12 (i,e) pairs -> the column hypothesis is itself a KL consequence.
   Part 2: the cofactor certificate in free commuting symbols, expand()-checked.
   Part 3: the identical check after substituting the real orbit-31 symbols.
   Part 4: floating-point confirmation on random genuine phase data.

3. ...\scratchpad\fam3deg.py
   Certifies the general (k,l) identity for all 16 row choices, and builds
   explicit numerical configurations for the degenerate branches, checking all
   twelve family-three residuals, all column relations and all moduli on each.

4. ...\scratchpad\fam3final.py  (and fam3all.py, the same file looped over pairs)
   Assembles the END-TO-END certificate: the target expressed as an explicit
   polynomial combination of RAW KL conditions plus the two moment facts, in the
   actual orbit-31 amplitude symbols, verified by expand() == 0 for all six
   column pairs.  Every cofactor is a monomial in the amplitudes, so this
   transcribes directly into a Lean `linear_combination`.

The certificate, exactly as verified (F1, C_ie, Cb_if, K_e, K_f denote the
left-minus-right of hypotheses H1, H2, H3):

  (M_ef - star(v_e) v_f) * (v_e star(v_f) - a_e star(a_f))
    = - F1 * (a_e star(a_f))
      - sum_i [ C_ie * (star(u_if) star(a_f)) + v_e b_ie * Cb_if ]
      - K_e * (a_f star(a_f)) - K_f * (v_e star(v_e))

with C_ie = u_ie a_e - v_e b_ie, Cb_if = star(u_if) star(a_f) - star(v_f) star(b_if),
K_e = v_e star(v_e) - a_e star(a_e), K_f = v_f star(v_f) - a_f star(a_f).

Cross-check (not the route, reported for completeness): your guessed rebalancing
t_ef * star(a_f) * a_e = star(v_f) v_e - star(a_f) a_e is CORRECT — verified
symbolically, and it needs no unimodularity.  My second factor
v_e star(v_f) - a_e star(a_f) is literally the same object, so the two routes
land on the same identity.

## verification_output

$ python fam3raw.py
Klein masks: ['000011', '000101', '000110']
each Klein mask stabilises both fibers: OK
raw diagonal conditions: 12  (all nonzero: True)
rank(raw 12)      = 12
rank(new 12)      = 12
rank(stacked 24)  = 12
SPANS EQUAL       = True

each pair equation as a combination of the four raw conditions of its mask:
  pair (0,1) mask 000011 : coeffs [1/4, -1/4, -1/4, 1/4]   residual 0
  pair (2,3) mask 000011 : coeffs [1/4, -1/4, 1/4, -1/4]   residual 0
  pair (0,2) mask 000101 : coeffs [1/4, -1/4, -1/4, 1/4]   residual 0
  pair (1,3) mask 000101 : coeffs [1/4, -1/4, 1/4, -1/4]   residual 0
  pair (0,3) mask 000110 : coeffs [1/4, -1/4, -1/4, 1/4]   residual 0
  pair (1,2) mask 000110 : coeffs [1/4, -1/4, 1/4, -1/4]   residual 0

$ python fam3elim.py
PART 1  the column relation is a two-term off-diagonal KL consequence
  i=1 e=0  mask 100000  conj(c_A)d_Bbar - conj(c_B)d_Abar in row space: True
  ... (all 12 True) ...
column relation derivable from KL for every (i,e): True

PART 2  cofactor certificate (free commuting symbols, expand()-checked)
TARGET - CERT  = 0
TARGET - CERT2 = 0
modulus-free intermediate:  M(N - N^v) + N(conj N - conj N^v) - CERT3 = 0

PART 3  the same, checked inside the real orbit-31 variables
substituted TARGET - CERT2 = 0

PART 4  numerical confirmation on genuine phase data
  trial 0: |F1| = 6.326e+00   |TARGET - (-F1*N)| = 2.220e-16
  trial 1: |F1| = 1.237e+00   |TARGET - (-F1*N)| = 4.441e-16
  trial 2: |F1| = 1.385e+00   |TARGET - (-F1*N)| = 2.220e-15
  trial 3: |F1| = 6.874e+00   |TARGET - (-F1*N)| = 3.972e-15
  trial 4: |F1| = 7.312e+00   |TARGET - (-F1*N)| = 4.441e-16

$ python fam3deg.py
PART A  the general (k,l) identity, cofactor-certified
general identity certified for all 16 (k,l): True

PART B  degenerate configurations (numeric, all hypotheses checked)
  (B1) rho = 1 on every column, a_0 != 0  [t_01 = 0]
     max |family-three residual| = 1.79e-15   (all 12 conditions)
     max |column relation|       = 0.00e+00
     max ||v_e| - |a_e||         = 0.00e+00
     |a_0| = 1.281   |T_01| = 0.000e+00
     |M_01 - conj(v_0) v_1|      = 3.453e+00   <-- conclusion FAILS
  (B2) rho = 1 on every column, a_0 = 0
     max |family-three residual| = 1.78e-15   (all 12 conditions)
     max |column relation|       = 0.00e+00
     max ||v_e| - |a_e||         = 0.00e+00
     |a_0| = 0.000   |T_01| = 0.000e+00
     |M_01 - conj(v_0) v_1|      = 2.207e+00   <-- conclusion FAILS

$ python fam3final.py   (and the same looped over all six pairs)
pair {0,1}, Klein mask 000011
family three F1_01 = sum lambda_z * D(mask,z):
    z = 000000   lambda = 1/4
    z = 000010   lambda = -1/4
    z = 000001   lambda = -1/4
    z = 000011   lambda = 1/4
all column relations expressed in raw off-diagonal KL conditions: OK
TARGET - CERT (orbit-31 symbols) = 0
TARGET - RAWCERT (raw KL conditions only) = 0

  pair {0,1} ... TARGET - RAWCERT (raw KL conditions only) = 0
  pair {0,2} ... TARGET - RAWCERT (raw KL conditions only) = 0
  pair {0,3} ... TARGET - RAWCERT (raw KL conditions only) = 0
  pair {1,2} ... TARGET - RAWCERT (raw KL conditions only) = 0
  pair {1,3} ... TARGET - RAWCERT (raw KL conditions only) = 0
  pair {2,3} ... TARGET - RAWCERT (raw KL conditions only) = 0

$ (moment-polytope feasibility of alpha_e = 0)
row sums (want 1/4): [1/4, 1/4, 1/4]
col sums: [1/8, 5/24, 5/24, 5/24]
alpha: [0, 1/12, 1/12, 1/12]  sum: 1/4  all >=0: True
alpha_0 == 0 : True

## degenerate_cases

The IDENTITY itself never degenerates: it holds with no nonvanishing hypotheses
whatsoever (both sides are 0 = 0 in the degenerate cases).  What degenerates is
the EXTRACTION of M_ef = star(v_e) v_f from it.  Write T_ef := v_e star(v_f) - a_e star(a_f).

1. t_ef = 0 (rho_e = rho_f), with a_e, a_f nonzero.  Then T_ef = 0 and the
   identity says 0 = 0.  The conclusion is genuinely FALSE here, not merely
   unprovable: configuration (B1) — rho ≡ 1 on all four columns, i.e. d = star(c)
   everywhere, with random c — satisfies all twelve family-three conditions
   (residual 1.8e-15), all twelve column relations exactly, and all sixteen
   moment facts exactly, yet |M_01 - star(v_0) v_1| = 3.45.  So SOME nonvanishing
   hypothesis is mandatory; there is no unconditional version.

2. a_e = 0 (equivalently, by the moment fact, v_e = 0).  Then T_ef = 0
   identically, whatever rho does, and the identity again says 0 = 0.  This case
   splits further:
   2a. a_e = 0 and rho_e = rho_f.  Conclusion FALSE — configuration (B2), the
       same rho ≡ 1 construction with a_0 set to 0, satisfies everything and
       still has |M_01 - star(v_0) v_1| = 2.21.
   2b. a_e = 0 and rho_e ≠ rho_f.  The conclusion is TRUE (family three collapses
       to M_ef = M^u_ef = star(rho_e) rho_f M_ef, forcing M_ef = 0 = star(v_e) v_f),
       but the A-row identity cannot see it, because with a_e = v_e = 0 every
       trace of column e's phase has left the (a, v, M) data.
   This is not a defect of my particular identity — NO hypothesis stated in
   a, v, M alone can cover the a_e = 0 branch.  Argument (machine-backed by (B2)):
   let H(a,v,M) be any predicate making "family three + column relations +
   moments + H  ⟹  M_ef = star(v_e) v_f" true.  Every point of the slice
   {a_e = v_e = 0, M any Gram matrix} is realised by the rho ≡ 1 configuration,
   which satisfies all three hypothesis families; so H must already be false at
   every such point with M_ef ≠ 0, i.e. H restricted to that slice implies the
   conclusion itself.  Any genuine hypothesis must therefore mention a B-row.
   THE FIX, still division-free: use the general (k,l) identity with a B row,
     (M_ef - star(v_e) v_f) * (u_ke * star(u_lf) - b_ke * star(b_lf)) = 0,
   whose nonvanishing side condition needs only b_ke ≠ 0 and b_lf ≠ 0 (plus
   rho_e ≠ rho_f).  It brings the top B-amplitudes u into the statement, but no
   division.  Certified for all 16 (k,l).

3. a_f = 0: symmetric to case 2.

4. This case split is REAL, not hypothetical.  The moment facts you quoted
   (alpha_e = sum_i beta_ie - 1/8, sum_e beta_ie = 1/4 per B row, sum alpha = 1/4)
   admit alpha_0 = 0: beta_i0 = 1/24, beta_ie = 5/72 for e = 1,2,3 gives row sums
   1/4, alpha = (0, 1/12, 1/12, 1/12), sum 1/4, all nonnegative.  So a_e ≠ 0 is
   not free from the polytope and you will have to branch on it (or use the B-row
   identity uniformly).

SUMMARY ANSWER to "does a division-free form exist": YES, unconditionally, and
in two strengths (the modulus-free quartic, and the "= 0" form after the moment
facts).  The unavoidable extra hypothesis is only for the corollary, and it is
exactly  v_e * star(v_f) ≠ a_e * star(a_f)  — which is t_ef ≠ 0 AND a_e ≠ 0 AND
a_f ≠ 0.  You cannot weaken it to t_ef ≠ 0 while staying inside a, v, M.

## confidence

machine-verified

## lean

## compiled

True

## file_path

C:\Users\richa\AppData\Local\Temp\claude\D--UTD-Project-purdue\e2435927-3651-49b0-acfb-31f3430ee257\scratchpad\Fam3Bridge.lean

## lemma_source

import Mathlib

/-!
# Orbit 31, family three: a division-free pin for `M_ef = conj (v_e) * v_f`

Everything below is stated over `ℂ` with `star`, and every hypothesis and
conclusion is **polynomial**: no `rho`, no inverses, no nonvanishing side
conditions except in the final extraction corollaries.

Notation.  For the column pair `{e, f}` of the 4x4 orbit-31 table:

* `ae`, `af`            bottom amplitudes at the `A` row of columns `e`, `f`;
* `be1 be2 be3`         bottom amplitudes at the `B` rows of column `e`;
* `bf1 bf2 bf3`         bottom amplitudes at the `B` rows of column `f`;
* `ve`, `vf`            `conj (d at the complement of A_e)`, resp. of `A_f`;
* `ue1 ue2 ue3`         `conj (d at the complement of B_{i,e})`;
* `uf1 uf2 uf3`         likewise for column `f`;
* `M_ef = be1 * star bf1 + be2 * star bf2 + be3 * star bf3`  the `B`-column Gram.

The chain is
`row_key`  (fully general, one row of each column chosen)
  -> `key_of_raw` (the `A` rows)  -> `M_eq_of_raw`,
and separately the already-cleared `(a, v, M)`-only form `key` -> `M_eq`,
linked to the raw form by `hH3_of_raw`.
-/

namespace Fam3Bridge

open scoped ComplexConjugate

/-! ## 1.  The general identity, one bottom row chosen in each column -/

/-- **The family-three identity.**

`p, q` are the bottom and top amplitude at *any* chosen position of column `e`
(so `(p, q) = (ae, ve)` on the `A` row and `(p, q) = (be i, ue i)` on a `B` row),
and `p', q'` likewise for column `f`.

Hypotheses, all division free:

* `hFam` : the raw family-three relation for the pair `{e, f}` — "b-Gram plus
  conjugate a-Gram equals u-Gram plus conjugate v-Gram";
* `hColE i`, `hColF i` : the column relations (`rho` constant along a column) in
  cross-multiplied form, anchored at the chosen position;
* `hPe`, `hPf` : the phase-transfer facts at the chosen positions.  On the `A`
  rows these are literally the moment facts `|v| = |a|`.

The conclusion carries the factor `q * star q' - p * star p'` and is
**unconditionally true**; it degenerates to `0 = 0` exactly when that factor
vanishes, which is where `M_ef` genuinely is not determined. -/
theorem row_key
    (ae af ve vf p q p' q' be1 be2 be3 bf1 bf2 bf3 ue1 ue2 ue3 uf1 uf2 uf3 : ℂ)
    (hFam : (be1 * star bf1 + be2 * star bf2 + be3 * star bf3) + star ae * af
              = (ue1 * star uf1 + ue2 * star uf2 + ue3 * star uf3) + star ve * vf)
    (hColE1 : ue1 * p = q * be1)
    (hColE2 : ue2 * p = q * be2)
    (hColE3 : ue3 * p = q * be3)
    (hColF1 : uf1 * p' = q' * bf1)
    (hColF2 : uf2 * p' = q' * bf2)
    (hColF3 : uf3 * p' = q' * bf3)
    (hPe : star ve * q = star ae * p)
    (hPf : vf * star q' = af * star p') :
    ((be1 * star bf1 + be2 * star bf2 + be3 * star bf3) - star ve * vf)
      * (q * star q' - p * star p') = 0 := by
  have hC1 : star uf1 * star p' = star q' * star bf1 := by
    rw [← star_mul', ← star_mul', hColF1]
  have hC2 : star uf2 * star p' = star q' * star bf2 := by
    rw [← star_mul', ← star_mul', hColF2]
  have hC3 : star uf3 * star p' = star q' * star bf3 := by
    rw [← star_mul', ← star_mul', hColF3]
  linear_combination
    (-(p * star p')) * hFam
      - (star bf1 * star q') * hColE1 - (star bf2 * star q') * hColE2
      - (star bf3 * star q') * hColE3
      - (ue1 * p) * hC1 - (ue2 * p) * hC2 - (ue3 * p) * hC3
      - (star ae * p) * hPf - (vf * star q') * hPe

/-! ## 2.  The `A`-row specialisation -/

/-- The `A`-row case of `row_key`.  Here the phase-transfer hypotheses are
exactly the verified moment facts `p_1 (v-bar) = p_0 (v)` at `A_e` and `A_f`,
stated multiplicatively so that they stay division free. -/
theorem key_of_raw
    (ae af ve vf be1 be2 be3 bf1 bf2 bf3 ue1 ue2 ue3 uf1 uf2 uf3 : ℂ)
    (hFam : (be1 * star bf1 + be2 * star bf2 + be3 * star bf3) + star ae * af
              = (ue1 * star uf1 + ue2 * star uf2 + ue3 * star uf3) + star ve * vf)
    (hColE1 : ue1 * ae = ve * be1)
    (hColE2 : ue2 * ae = ve * be2)
    (hColE3 : ue3 * ae = ve * be3)
    (hColF1 : uf1 * af = vf * bf1)
    (hColF2 : uf2 * af = vf * bf2)
    (hColF3 : uf3 * af = vf * bf3)
    (hKe : ve * star ve = ae * star ae)
    (hKf : vf * star vf = af * star af) :
    ((be1 * star bf1 + be2 * star bf2 + be3 * star bf3) - star ve * vf)
      * (ve * star vf - ae * star af) = 0 :=
  row_key ae af ve vf ae ve af vf be1 be2 be3 bf1 bf2 bf3 ue1 ue2 ue3 uf1 uf2 uf3
    hFam hColE1 hColE2 hColE3 hColF1 hColF2 hColF3
    (by linear_combination hKe) hKf

/-- Extraction of `M_ef` from the `A`-row identity.  The single division-free
side condition `ve * star vf ≠ ae * star af` packages all three nondegeneracy
requirements at once: `ae ≠ 0`, `af ≠ 0` and `rho_e ≠ rho_f`. -/
theorem M_eq_of_raw
    (ae af ve vf be1 be2 be3 bf1 bf2 bf3 ue1 ue2 ue3 uf1 uf2 uf3 : ℂ)
    (hFam : (be1 * star bf1 + be2 * star bf2 + be3 * star bf3) + star ae * af
              = (ue1 * star uf1 + ue2 * star uf2 + ue3 * star uf3) + star ve * vf)
    (hColE1 : ue1 * ae = ve * be1)
    (hColE2 : ue2 * ae = ve * be2)
    (hColE3 : ue3 * ae = ve * be3)
    (hColF1 : uf1 * af = vf * bf1)
    (hColF2 : uf2 * af = vf * bf2)
    (hColF3 : uf3 * af = vf * bf3)
    (hKe : ve * star ve = ae * star ae)
    (hKf : vf * star vf = af * star af)
    (hT : ve * star vf - ae * star af ≠ 0) :
    be1 * star bf1 + be2 * star bf2 + be3 * star bf3 = star ve * vf := by
  rcases mul_eq_zero.mp
      (key_of_raw ae af ve vf be1 be2 be3 bf1 bf2 bf3 ue1 ue2 ue3 uf1 uf2 uf3
        hFam hColE1 hColE2 hColE3 hColF1 hColF2 hColF3 hKe hKf) with h | h
  · exact sub_eq_zero.mp h
  · exact absurd h hT

/-! ## 3.  The `(a, v, M)`-only form, and the bridge to it -/

/-- The bridge: the raw family-three relation together with the column
relations already implies the *cleared* relation `hH3`, which is the original
`M_ef * t_ef = - star (N_ef * t_ef)` multiplied through by `N_ef = ae * star af`.
No moment fact and no nonvanishing hypothesis is needed here. -/
theorem hH3_of_raw
    (ae af ve vf be1 be2 be3 bf1 bf2 bf3 ue1 ue2 ue3 uf1 uf2 uf3 : ℂ)
    (hFam : (be1 * star bf1 + be2 * star bf2 + be3 * star bf3) + star ae * af
              = (ue1 * star uf1 + ue2 * star uf2 + ue3 * star uf3) + star ve * vf)
    (hColE1 : ue1 * ae = ve * be1)
    (hColE2 : ue2 * ae = ve * be2)
    (hColE3 : ue3 * ae = ve * be3)
    (hColF1 : uf1 * af = vf * bf1)
    (hColF2 : uf2 * af = vf * bf2)
    (hColF3 : uf3 * af = vf * bf3) :
    (be1 * star bf1 + be2 * star bf2 + be3 * star bf3)
        * (star vf * ve - star af * ae)
      = -(ae * star af) * (vf * star ve - af * star ae) := by
  have hC1 : star uf1 * star af = star vf * star bf1 := by
    rw [← star_mul', ← star_mul', hColF1]
  have hC2 : star uf2 * star af = star vf * star bf2 := by
    rw [← star_mul', ← star_mul', hColF2]
  have hC3 : star uf3 * star af = star vf * star bf3 := by
    rw [← star_mul', ← star_mul', hColF3]
  linear_combination
    (-(ae * star af)) * hFam
      - (star bf1 * star vf) * hColE1 - (star bf2 * star vf) * hColE2
      - (star bf3 * star vf) * hColE3
      - (ue1 * ae) * hC1 - (ue2 * ae) * hC2 - (ue3 * ae) * hC3

/-- **The `(a, v, M)`-only identity.**  Division free: no `rho`, no inverses,
no side conditions.  `star vf * ve - star af * ae` is the division-free stand-in
for `t_ef * star af * ae`. -/
theorem key (ae af ve vf M : ℂ)
    (hKe : ve * star ve = ae * star ae)
    (hKf : vf * star vf = af * star af)
    (hH3 : M * (star vf * ve - star af * ae)
             = -(ae * star af) * (vf * star ve - af * star ae)) :
    (M - star ve * vf) * (star vf * ve - star af * ae) = 0 := by
  linear_combination hH3 - (star vf * vf) * hKe - (ae * star ae) * hKf

/-- The usable corollary of `key`. -/
theorem M_eq (ae af ve vf M : ℂ)
    (hKe : ve * star ve = ae * star ae)
    (hKf : vf * star vf = af * star af)
    (hH3 : M * (star vf * ve - star af * ae)
             = -(ae * star af) * (vf * star ve - af * star ae))
    (hT : star vf * ve - star af * ae ≠ 0) :
    M = star ve * vf := by
  rcases mul_eq_zero.mp (key ae af ve vf M hKe hKf hH3) with h | h
  · exact sub_eq_zero.mp h
  · exact absurd h hT

/-! ## 4.  Phase transfer, which feeds `row_key` on a `B` row -/

/-- On a `B` row the phase-transfer hypothesis of `row_key` is itself a
consequence of that row's column relation and moment fact, provided the bottom
amplitude there is nonzero.  This is what rescues the `ae = 0` branch, at the
price of assuming `b ≠ 0` instead. -/
theorem phase_transfer (ae ve b u : ℂ)
    (hCol : u * ae = ve * b)
    (hMom : u * star u = b * star b)
    (hb : b ≠ 0) :
    star ve * u = star ae * b := by
  have hCb : star u * star ae = star ve * star b := by
    rw [← star_mul', ← star_mul', hCol]
  have h : (star ve * u - star ae * b) * star b = 0 := by
    linear_combination (-u) * hCb + (star ae) * hMom
  rcases mul_eq_zero.mp h with h' | h'
  · exact sub_eq_zero.mp h'
  · exact absurd (star_eq_zero.mp h') hb

/-! ## 5.  The degenerate branches -/

/-- If `ae = 0` then the moment fact forces the whole `A`-row factor to vanish,
so the `A`-row identity is vacuous and `M_ef` is genuinely undetermined by it. -/
theorem T_eq_zero_of_ae (ae af ve vf : ℂ) (h0 : ae = 0)
    (hKe : ve * star ve = ae * star ae) :
    star vf * ve - star af * ae = 0 := by
  have hv : ve = 0 := by
    rcases mul_eq_zero.mp (by rw [hKe, h0]; ring : ve * star ve = 0) with h | h
    · exact h
    · exact star_eq_zero.mp h
  rw [hv, h0]; simp

/-- Symmetrically for `af = 0`. -/
theorem T_eq_zero_of_af (ae af ve vf : ℂ) (h0 : af = 0)
    (hKf : vf * star vf = af * star af) :
    star vf * ve - star af * ae = 0 := by
  have hv : vf = 0 := by
    rcases mul_eq_zero.mp (by rw [hKf, h0]; ring : vf * star vf = 0) with h | h
    · exact h
    · exact star_eq_zero.mp h
  rw [hv, h0]; simp

end Fam3Bridge

## compile_output

$ cd D:/UTD/Project_purdue/Lean_certification
$ lake env lean C:/Users/richa/.../scratchpad/Fam3Bridge.lean
exit=0
(zero bytes of output: ZERO errors, ZERO warnings; compiled on the first attempt, no iteration needed)

$ lake env lean C:/Users/richa/.../scratchpad/Fam3BridgeAxioms.lean
'Fam3Bridge.row_key' depends on axioms: [propext, Classical.choice, Quot.sound]
'Fam3Bridge.key_of_raw' depends on axioms: [propext, Classical.choice, Quot.sound]
'Fam3Bridge.M_eq_of_raw' depends on axioms: [propext, Classical.choice, Quot.sound]
'Fam3Bridge.hH3_of_raw' depends on axioms: [propext, Classical.choice, Quot.sound]
'Fam3Bridge.key' depends on axioms: [propext, Classical.choice, Quot.sound]
'Fam3Bridge.M_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'Fam3Bridge.phase_transfer' depends on axioms: [propext, Classical.choice, Quot.sound]
'Fam3Bridge.T_eq_zero_of_ae' depends on axioms: [propext, Classical.choice, Quot.sound]
'Fam3Bridge.T_eq_zero_of_af' depends on axioms: [propext, Classical.choice, Quot.sound]
exit=0
(toolchain leanprover/lean4:v4.27.0, pinned Mathlib; no native_decide anywhere)

## axioms

[propext, Classical.choice, Quot.sound] — exactly, for all nine theorems (row_key, key_of_raw, M_eq_of_raw, hH3_of_raw, key, M_eq, phase_transfer, T_eq_zero_of_ae, T_eq_zero_of_af).

## notes

WHICH DERIVATION IS RIGHT: both. They do not disagree — they land on literally the same identity. I re-verified both independently in sympy (conjugates as free symbols, formal bar involution) before writing any Lean:

  * Derivation 1's cofactor certificate P = g3 - (star vf * vf)*g1 - (ae * star ae)*g2 expands to exactly 0; grevlex Groebner reduction of P modulo <g1,g2,g3> gives remainder 0; the negative controls reproduce (M - star ve * vf) alone reduces to itself, and (M - star ve*vf)*star T is NOT in the ideal, so the orientation of T is forced.
  * Derivation 2's cofactor certificate expands to exactly 0, as does its stronger modulus-free form.
  * The two "second factors" are the same object: (star vf * ve - star af * ae) - (ve * star vf - ae * star af) = 0.

So the user's guessed rebalancing t_ef * star(a_f) * a_e = star(v_f) v_e - star(a_f) a_e is CORRECT. It is confirmed twice: directly under the rho-parametrisation, and independently by derivation 2's route which never introduces rho at all.

I built the Lean file on DERIVATION 2, because it is strictly the more upstream statement: it takes the raw family-three relation (b-Gram + conjugate a-Gram = u-Gram + conjugate v-Gram) and the cross-multiplied column relations as hypotheses, so nothing between the KL conditions and the conclusion is left on trust. Derivation 1 then appears as a downstream corollary (`key`, `M_eq`), and `hH3_of_raw` is the bridge proving that derivation 1's hypothesis hH3 follows from derivation 2's raw hypotheses using the column relations alone — no moment fact and no nonvanishing condition. That bridge is the part that was previously assumed rather than checked, and it is now kernel-verified.

ONE CORRECTION TO DERIVATION 2. It claims the general (k,l) row identity is "certified for all 16 (k,l)" with a side condition needing only b_ke != 0 and b_lf != 0. That is not quite the shape of the truth, and the difference matters. The general identity is NOT in the ideal generated by family three + column relations + moments alone. What I found and certified is:

  (M_ef - star v_e * v_f) * (q * star q' - p * star p') = 0

holds given family three, the column relations ANCHORED AT THE CHOSEN ROW, and two PHASE-TRANSFER facts at the chosen positions: star v_e * q = star a_e * p and v_f * star q' = a_f * star p'. On the A rows (p,q) = (a_e, v_e) those phase-transfer facts ARE the moment facts, which is why the A-row case is unconditional. On a B row they are not automatic: `phase_transfer` derives them from that row's column relation plus its moment fact, and that derivation genuinely needs b != 0 (the certificate is (star v_e * u - star a_e * b) * star b = -u*hCb + star a_e * hMom, so the b factor cannot be removed). Net effect is the same as derivation 2 claimed — b_ke != 0, b_lf != 0 — but the honest statement splits into two lemmas, and `row_key` is the general one with the phase-transfer facts exposed as hypotheses. This packaging is better than either derivation proposed: `key_of_raw` is now a one-line application of `row_key`, since the A-row case is just p := a_e, q := v_e, p' := a_f, q' := v_f.

NON-VACUITY AND NECESSITY (numerically confirmed, not just asserted):
  * A generic configuration (rho_e != rho_f, a_e != 0) satisfies all Lean hypotheses to 1e-15 with |T| = 3.66, and the conclusion M = star v_e * v_f holds. So M_eq_of_raw is not vacuous.
  * With rho_e = rho_f and M chosen freely, ALL hypotheses of M_eq_of_raw except hT are still satisfied to 1e-16, yet |M - star v_e * v_f| = 3.21. So hT is genuinely necessary and there is no unconditional version. Same with a_e = 0 additionally imposed (|M - star v_e * v_f| = 3.86).
  This reproduces derivation 2's (B1)/(B2) counterexamples independently.

THE REMAINING GAP, unchanged and worth restating: the t_ef = 0 branch (two columns in phase) is a real hole in the column-pair argument, and derivation 2's polytope check shows alpha_e = 0 is feasible, so a_e != 0 is not free either. `phase_transfer` + `row_key` on a B row is the intended escape when a_e = 0 but rho_e != rho_f; nothing here closes the rho_e = rho_f case.

FILES (all in the scratchpad; nothing under D:\UTD\Project_purdue\Lean_certification\SixQubit was touched, and nothing in the project was modified at all):
  C:\Users\richa\AppData\Local\Temp\claude\D--UTD-Project-purdue\e2435927-3651-49b0-acfb-31f3430ee257\scratchpad\Fam3Bridge.lean         — the deliverable
  C:\Users\richa\AppData\Local\Temp\claude\D--UTD-Project-purdue\e2435927-3651-49b0-acfb-31f3430ee257\scratchpad\Fam3BridgeAxioms.lean   — same content + the nine #print axioms lines
  C:\Users\richa\AppData\Local\Temp\claude\D--UTD-Project-purdue\e2435927-3651-49b0-acfb-31f3430ee257\scratchpad\verify_both.py          — independent re-verification of both derivations
  C:\Users\richa\AppData\Local\Temp\claude\D--UTD-Project-purdue\e2435927-3651-49b0-acfb-31f3430ee257\scratchpad\verify_cert.py          — the cofactor certificates that became the linear_combination calls

A practical note for reuse: the Groebner route dies in the 32-variable setting (2-minute timeout), and sympy's `reduced` against a non-Groebner generator list returns a nonzero remainder even when the polynomial IS in the ideal, so it is useless as a membership test here. The workable method is to derive the cofactors by hand from the mechanism and then confirm with a single `sp.expand(goal - cert) == 0`, which is instant and is exactly what transcribes into `linear_combination`.
