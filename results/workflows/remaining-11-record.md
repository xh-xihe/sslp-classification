# Workflow record: remaining-11

six mechanism groups, each built then adversarially audited

Run `w4ve1y9yl`; 1963868 subagent tokens, 516 tool calls.

---

## groups

#### group

spinor

#### label

spinor orbits (12 and 6)

#### builderReport

Both orbits are complete and kernel-clean.

## Files created (all inside `D:/UTD/Project_purdue/Lean_certification`)

| absolute path | lines | SHA-256 |
|---|---|---|
| `D:/UTD/Project_purdue/Lean_certification/SixQubit/Spinor.lean` | 225 | `3AF33F83CC94907DF27A2B08EB3AD2B12B923EB1BBE5E9133E4DFE82903A5423` |
| `D:/UTD/Project_purdue/Lean_certification/SixQubit/Orbit12.lean` | 1049 | `49886F731A9F1120D6E129DBA6C9BB1A994D8C7F50E2D1AD84BC8BB0313630AE` |
| `D:/UTD/Project_purdue/Lean_certification/SixQubit/Orbit6.lean` | 1656 | `801E68C4385C90C4CE50C451D99EA811B82715FDD1D466F6FC5D7591A819D0CE` |
| `D:/UTD/Project_purdue/Lean_certification/tools/generators/gen12.py` | 567 | `36F27C2455F50687E93E820B51110E41FE87BDF968BE9B058E295498BAAA3586` |
| `D:/UTD/Project_purdue/Lean_certification/tools/generators/gen6.py` | 637 | `959A86521E47ADD3F8AF7AD8B030BA90BB3697F27F56B9FE9E994D215781A815` |
| `D:/UTD/Project_purdue/Lean_certification/tools/verification/audit_spinor.py` | 144 | `57AC1FF5C192435FE91F18B016E46C8EC4039BB7D240E7708E8E2728DB847DD9` |

`SixQubit.lean` and `SixQubit/Audit.lean` were **not** touched; no pre-existing orbit module was modified.

## Compilation (commands run, output read)

```
cd D:/UTD/Project_purdue/Lean_certification
lake build SixQubit.Spinor            -> "Built SixQubit.Spinor"
lake env lean SixQubit/Spinor.lean    -> EMPTY   (no errors, no warnings)
lake env lean SixQubit/Orbit12.lean   -> EMPTY
lake env lean SixQubit/Orbit6.lean    -> EMPTY
lake build SixQubit.Orbit12 / .Orbit6 -> "Build completed successfully"
```
All three were re-run at the end; all three produced empty output.

## `#print axioms`, verbatim

```
'SixQubit.Orbit12.no_go_of_moments' depends on axioms: [propext, Classical.choice, Quot.sound]
'SixQubit.Orbit12.S0_eq_fiber' depends on axioms: [propext, Classical.choice, Quot.sound]
'SixQubit.Orbit12.S1_eq_fiber' depends on axioms: [propext, Classical.choice, Quot.sound]
'SixQubit.Orbit6.no_go_of_moments' depends on axioms: [propext, Classical.choice, Quot.sound]
'SixQubit.Orbit6.S0_eq_fiber' depends on axioms: [propext, Classical.choice, Quot.sound]
'SixQubit.Orbit6.S1_eq_fiber' depends on axioms: [propext, Classical.choice, Quot.sound]
'SixQubit.Spinor.cancel_perp' depends on axioms: [propext, Classical.choice, Quot.sound]
'SixQubit.Spinor.edge_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'SixQubit.Spinor.lagrange' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Hypothesis classification (machine-checked, not asserted)

`tools/verification/audit_spinor.py` re-reads the generated Lean, recomputes the fibers and the moment system from `(q,a,delta)` independently, and pattern-matches every hypothesis. Output: **AUDIT PASSED**, with

| headline | total hyps | (a) `offSum … = 0` | (b) `diagBot … = diagTop …` | (c) `MomentSystem` | outside (a)/(b)/(c) |
|---|---|---|---|---|---|
| `SixQubit.Orbit12.no_go_of_moments` | 25 | 20 | 4 | 1 | **0** |
| `SixQubit.Orbit6.no_go_of_moments` | 43 | 40 | 2 | 1 | **0** |

The audit also confirmed, per module: the `y`/`z` strings are exactly the two residue fibers; the 23 `MomentSystem` equalities are exactly the two normalizations plus the 21 one- and two-coordinate moment rows of those fibers (no extra rows) with one nonnegativity per basis state; every `(mask, dressing)` pair used satisfies `|supp(e) ∪ supp(z)| ≤ 2`; no `sorry` / `native_decide` outside docstrings. `offSum`, `diagBot`, `diagTop` are byte-identical to `Orbit13.lean`'s.

## What the proofs actually do (both deviate from the paper, deliberately)

**Orbit 12.** The paper argues "two cancelling rank-one matrices share both spans", picks unit vectors on the two lines, and eliminates a scalar. I replaced that with a division-free elimination in `Spinor.cancel_perp`: with `s = a†ũ`, `t = a†ṽ`, `Bu = u†w`, `Bv = v†w`, contracting the four cross-block entries with `a` gives `u_q* s + v_q* t = 0`; contracting *that* with `w` and substituting the two pair rows `s + Bv = 0`, `Bu + t = 0` yields `2st = 0`, and `u ≠ 0`, `v ≠ 0` force `s = t = 0`, hence `u†w = v†w = 0`. No spans, no unit vectors, no division. `Spinor.edge_zero` then contracts the `H = 0` diagonal block with `w` and gets `‖w‖⁴ ≤ 0`. The moment layer supplies `‖u‖² = ‖v‖² = 1/4` and the fact that the three complementary pair masses sum to `1/4`, giving a 3-way `rcases`; the same lemma pair is applied in each branch.

**Orbit 6.** I did **not** formalize the paper's `P_U = P_C` projector alignment (which needs "all nonzero `c_i` parallel", a case split on which `t_i > 0`, and a projector calculus). Instead: the W5 rows (5 dressings, coefficients `1/3, 1/6, 1/6, 1/6, 1/6`, solved by sympy) kill every `u†b_k`; the reduced state on the zero-angle qubit contracted with `u` gives `‖u‖⁴ + Σ|a_ij†u|² = Σ|b_k†u|² + Σ|c_i†u|²`; Lagrange's identity (`Spinor.lagrange`) turns each `|u†c_i|²` into `‖u‖²‖c_i‖² − |det(u,c_i)|²`; with `‖u‖² = 1/3` and `Σ‖c_i‖² = 1/3` the two `1/9`s cancel *exactly*, leaving `Σ|a_ij†u|² + Σ|det|² = 0` — a vanishing sum of nonnegative reals. So every `a_ij ⊥ u`; the four `X_k` matrix entries then collapse to `‖u‖² b_k = 0`, so all ten `b`-amplitudes vanish, contradicting `Σ‖b_k‖² = 2/3`. This is shorter than the paper and needs no case analysis.

## Paper claims I recomputed rather than trusted

* Orbit 12 moment data: `‖u‖² = ‖v‖² = ‖ũ‖² = ‖ṽ‖² = 1/4`, `x_e = y_e`, `x_e = x_ē`, `X = 1/2` — all reproduced by exact rational row reduction and re-derived inside Lean by `linarith` from `MomentSystem` alone (`MomentSystem.facts`).
* Orbit 6, the `17×17` minor: recomputed. The aggregate system is `17×21` of **rank 17**, the lexicographic-pivot minor has **det = 144** (paper's value confirmed), and the general solution is exactly the paper's four-simplex `r = 1/3`, `y_k = 1/6 − t_k/2`, `x_ij = (t_i+t_j)/2`, `Σt_i = 1/3`.
* Orbit 6, `det W5 = −48`: I did not compute the determinant symbolically; I instead had sympy solve the 5-row system for the target monom

#### auditVerdict

INDEPENDENT AUDIT — spinor group (orbits 12 and 6). Verdict: **PASS on every check. No overclaim found.**

## 1-2. Files present, SHA-256 (recomputed by me, `sha256sum`)

| absolute path | exists | lines | SHA-256 vs claim |
|---|---|---|---|
| `D:/UTD/Project_purdue/Lean_certification/SixQubit/Spinor.lean` | yes | 225 ✓ | `3af33f83…5423` **MATCH** |
| `D:/UTD/Project_purdue/Lean_certification/SixQubit/Orbit12.lean` | yes | 1049 ✓ | `49886f73…30ae` **MATCH** |
| `D:/UTD/Project_purdue/Lean_certification/SixQubit/Orbit6.lean` | yes | 1656 ✓ | `801e68c4…0cde`… `…819d0ce` **MATCH** |
| `D:/UTD/Project_purdue/Lean_certification/tools/generators/gen12.py` | yes | 567 ✓ | `36f27c24…3586` **MATCH** |
| `D:/UTD/Project_purdue/Lean_certification/tools/generators/gen6.py` | yes | 637 ✓ | `959a8652…815` **MATCH** |
| `D:/UTD/Project_purdue/Lean_certification/tools/verification/audit_spinor.py` | yes | 144 ✓ | `57ac1ff5…8ed` **MATCH** |

All six byte-identical to the claim. No file absent.

## 3. Recompilation (my own runs)

```
lake env lean SixQubit/Spinor.lean    -> (empty)   exit 0
lake env lean SixQubit/Orbit12.lean   -> (empty)   exit 0
lake env lean SixQubit/Orbit6.lean    -> (empty)   exit 0
```
Zero errors, **zero warnings**. PASS.

## 4. `#print axioms` (my own scratch file, since deleted)

```
'SixQubit.Spinor.lagrange'             depends on axioms: [propext, Classical.choice, Quot.sound]
'SixQubit.Spinor.cancel_perp'          depends on axioms: [propext, Classical.choice, Quot.sound]
'SixQubit.Spinor.edge_zero'            depends on axioms: [propext, Classical.choice, Quot.sound]
'SixQubit.Orbit12.S0_eq_fiber'         depends on axioms: [propext, Classical.choice, Quot.sound]
'SixQubit.Orbit12.S1_eq_fiber'         depends on axioms: [propext, Classical.choice, Quot.sound]
'SixQubit.Orbit12.MomentSystem.facts'  depends on axioms: [propext, Classical.choice, Quot.sound]
'SixQubit.Orbit12.no_go_of_moments'    depends on axioms: [propext, Classical.choice, Quot.sound]
'SixQubit.Orbit6.S0_eq_fiber'          depends on axioms: [propext, Classical.choice, Quot.sound]
'SixQubit.Orbit6.S1_eq_fiber'          depends on axioms: [propext, Classical.choice, Quot.sound]
'SixQubit.Orbit6.no_go_of_moments'     depends on axioms: [propext, Classical.choice, Quot.sound]
```
Nothing extra. PASS.

## 5. `sorry` / `native_decide` / kernel bypass

Only 3 hits repo-wide in these files, all inside `/-! ... -/` docstrings, verified by reading context: `Spinor.lean:58`, `Orbit12.lean:30`, `Orbit6.lean:37` — each is the sentence "`native_decide` is not used." Zero `sorry`, zero `sorryAx`, zero `axiom` declarations. I also grepped adversarially for `set_option` (incl. `debug.skipKernelTC`), `unsafe`, `opaque`, `implemented_by`, `macro_rules`, `attribute [` — **no hits at all**. PASS.

## 6. Hypothesis classification — the important one

I parsed the binders mechanically **and** cross-checked against Lean's own re-elaborated `#check` output (no reliance on the builder's `audit_spinor.py`):

| theorem | total | (a) `offSum … = 0` | (b) `diagBot = diagTop` | (c) `MomentSystem` | **outside (a)/(b)/(c)** |
|---|---|---|---|---|---|
| `SixQubit.Orbit12.no_go_of_moments` | 25 | 20 | 4 | 1 | **0** |
| `SixQubit.Orbit6.no_go_of_moments` | 43 | 40 | 2 | 1 | **0** |

**No smuggled algebraic facts.** The only non-binder arguments are `(c d : SS.BitString 6 → ℂ)`. Conclusion is literally `False` in both.

Anti-smuggling checks on the *contents* of `MomentSystem` (this is where a fact could hide):
- I regenerated both fibers from `(q, a, residue)` and recomputed all 2 normalizations + 6 one-coordinate + 15 two-coordinate marginals from scratch. **All 23 rows in each structure matched an independently computed marginal, term for term. Zero rows unaccounted for, zero predicted rows omitted.**
- Nonnegativity fields: 32 = 16+16 (Orbit12), 42 = 22+20 (Orbit6). Exactly one per basis state, no strict positivity smuggled in.
- `offSum` / `diagBot` / `diagTop` are **byte-identical** to `Orbit13.lean`'s (already-certified module) — not redefined.
- Every `(mask, dressing)` pair: **max `|supp(e) ∪ supp(z)| = 2`**, zero violations (24 distinct pairs for O12, 42 for O6). All are legitimate weight-≤2 KL conditions.
- Non-vacuity: I ran an LP. Both moment systems are **feasible** with all 32 / 42 coordinates able to be strictly positive; affine dimension 12 (O12) and 19 (O6) — which independently reproduces the paper's Table columns (`12` for orbit 12, `19` for orbit 6). So the LP alone does not close either orbit; the algebraic layer is genuinely doing the work, and neither theorem is vacuously true.

## 7. Fibers vs. the paper

- **Orbit 12**: `av = ![0,1,1,1,1,2] : Fin 6 → ZMod 4`, residues 0 and 2. Paper §11819 `(q,m,a) = (4,2,(0,1,1,1,1,2))`; bottom active fiber `(∅,0),(V,0),(e,1)` → weight 0 mod 4; top `(∅,1),(V,1),(e,0)` → weight 2 mod 4. **delta = 2 confirmed from the paper's own fiber description, not from fiber sizes.** Sizes 16/16 match the paper's table. My recomputed fiber equals the `y0…y15` / `z0…z15` lists exactly, and *in the same order*. Anchors check out: `y0 = 000000` = (∅,0), `y7 = 011110` = (V,0), `y8`/`y15` their zero-angle partners.
- **Orbit 6**: `av = ![0,1,1,1,1,1] : Fin 6 → ZMod 3`, residues 0 and 1. Paper §7282 `(q,m,a) = (3,3,(0,1,1,1,1,1))`, `T₀ = {|S| ∈ {0,3}}` → 0 mod 3, `T₁ = {|S| ∈ {1,4}}` → 1 mod 3. **delta = 1 confirmed.** Sizes 22/20 match the paper's table (2·(1+10), 2·(5+5)). Fiber lists match mine exactly and in order.
- `MomentSystem.facts` derives `q0+q8 = 1/4` (O12) and `q0+q11 = 1/3`, `Σ‖c‖² = 1/3`, `Σ‖b‖² = 2/3` (O6) — I reproduced `1/4` and `1/3` numerically from the LP. Orbit 6's closing `linarith only [hB, nb1_0, …, nb5_1]` uses exactly `Σ‖b_k‖² = 2/3` against ten `normSq (d z_k) = 0`, and `{z0,z1,z2,z3,z5,z10,z11,z12,z13,z15}` are precisely the ten `|S|=1` b-states. Sound.

## Caveats — all disclosed by the builder, all confirmed accurate, none material

- **Not registered**: `grep -E "SixQub

#### group

phase

#### label

phase propagation (orbits 49 and 51)

#### builderReport

Both orbits are done, division-free, kernel-only.

## Files created / modified (all inside `D:/UTD/Project_purdue/Lean_certification`)

| File | lines | SHA-256 |
|---|---|---|
| `D:/UTD/Project_purdue/Lean_certification/SixQubit/Orbit49.lean` (new) | 609 | `BDE3E4BC425756EFB4AA2DCBA641023A29DFE9A69D2A0D6A0EFC3093D24CC848` |
| `D:/UTD/Project_purdue/Lean_certification/SixQubit/Orbit51.lean` (new) | 455 | `586946FDC29A7291F008B2F46355C0657ABEFF43F6278CE2449E9FC2FCBD6730` |
| `D:/UTD/Project_purdue/Lean_certification/SixQubit/Triangle.lean` (appended only) | 153 | `3706718569CB726C010C353BB608F0B91FE209BEA8FF109821CDE4C04B66728F` |

Tooling (new): `tools/generators/an4951.py` (128), `tools/generators/ver4951.py` (125, sympy proof of every identity), `tools/generators/gen4951.py` (606, emits both modules), `tools/verification/audit4951.py` (162), `tools/verification/nonvac4951.py` (89).
`SixQubit.lean` and `SixQubit/Audit.lean` were NOT touched. No pre-existing orbit module was touched; `Triangle.lean` only gained three new theorems after the existing `prod_eq_zero` / `contradiction` / `contradiction_of_normSq`, which are byte-unchanged.

## Compilation (empty output = success, and warnings would appear here too)

```
lake env lean SixQubit/Triangle.lean   -> empty
lake env lean SixQubit/Orbit49.lean    -> empty
lake env lean SixQubit/Orbit51.lean    -> empty
lake env lean SixQubit/Orbit50.lean    -> empty   (pre-existing Triangle dependent, unbroken)
lake build SixQubit.Triangle SixQubit.Orbit49 SixQubit.Orbit51 -> "Build completed successfully (7893 jobs)."
```
Regenerating from `python tools/run.py generators/gen4951.py` reproduces both files byte-identically (hashes above are post-regeneration).

## `#print axioms`, verbatim

```
'SixQubit.Orbit49.no_go_of_moments' depends on axioms: [propext, Classical.choice, Quot.sound]
'SixQubit.Orbit51.no_go_of_moments' depends on axioms: [propext, Classical.choice, Quot.sound]
'SixQubit.Orbit49.S0_eq_fiber' depends on axioms: [propext, Classical.choice, Quot.sound]
'SixQubit.Orbit49.S1_eq_fiber' depends on axioms: [propext, Classical.choice, Quot.sound]
'SixQubit.Orbit51.S0_eq_fiber' depends on axioms: [propext, Classical.choice, Quot.sound]
'SixQubit.Orbit51.S1_eq_fiber' depends on axioms: [propext, Classical.choice, Quot.sound]
'SixQubit.Triangle.pair_prod_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'SixQubit.Triangle.pair_contradiction_of_normSq' depends on axioms: [propext, Classical.choice, Quot.sound]
'SixQubit.Orbit49.MomentSystem.pinned' depends on axioms: [propext, Classical.choice, Quot.sound]
'SixQubit.Orbit51.MomentSystem.pinned' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Hypothesis classification of the headline theorems

Machine-checked by `tools/verification/audit4951.py`, which re-parses the emitted Lean text:

- `SixQubit.Orbit49.no_go_of_moments`: **21** hypotheses — (a) `offSum c d ef_k w_j = 0`: **20**; (b) `diagBot = diagTop`: **0**; (c) `MomentSystem`: **1**. Nothing outside (a)/(b)/(c).
- `SixQubit.Orbit51.no_go_of_moments`: **12** hypotheses — (a) **11**, (b) **0**, (c) **1**. Nothing outside (a)/(b)/(c).

The audit also re-derives, independently of the generator: both fibers from `av` over all 64 strings; that the top fiber is the bitwise complement; that every used `(mask, dressing)` pair satisfies `|supp(e) ∪ supp(z)| ≤ 2`; every `incidence_ef_k` set; and that all 23 `MomentSystem` equations equal the recomputed moment rows with all 20 nonnegativity fields present, instantiated at `Complex.normSq (c y_i)` / `Complex.normSq (d z_j)` in order. Result: `AUDIT CLEAN`.

Non-vacuity (`tools/verification/nonvac4951.py`): each parsed `MomentSystem` has rank 17 in 20 unknowns and admits an explicit **strictly positive** rational solution, so neither no-go is vacuous; the pinned point `p = (1/12^8, 1/6, 1/6)` is feasible for the linear part in both, so the contradiction genuinely comes from the amplitude relations.

## The division-free route actually used

The paper's phase ratios `rho_i = d_i / conj(c_i)` are never introduced. `tools/generators/ver4951.py` proves every identity below in sympy with residual exactly 0.

**Orbit 49 — the uniform phase is not needed at all.** The eight weight-two masks pairing `i ≤ 7` with anchor 8 give `star(c y8)*d z_i + star(c y_i)*d z8 = 0`. Multiplying a rank-one mask row by `star (c y8)` and substituting four of these gives the identity
```
star(c y8) * (u3 v0 + u2 v1 + u1 v2 + u0 v3) = -2 * (d z8) * (u0 u3 + u1 u2)
```
and `normSq (d z8) = 1/6` from moments alone, so the quadric vanishes outright — no synchronisation step, no `rho`. Four such quadrics, conjugated and passed through `normSq`, become `p0p3 = p1p2`, `p0p5 = p1p4`, `p0p7 = p1p6`, which collapse the 3-parameter polytope to `p0 = … = p7 = 1/12` (`linear_combination 6*e_i` after eliminating `q1,q3,q5,q7`). The new `Triangle.pair_contradiction_of_normSq` closes it.

**Orbit 51 — synchronisation without division.** Eliminating between the four reciprocal relations on the pair `{6,7}` gives, identically,
```
d z6 * (star(c y8)*d z9 - star(c y9)*d z8) = 0 ,   d z7 * (same) = 0 ,
```
and the moment system forces `r6 + r7 = 1/6`, so one factor is nonzero and `W := star(c y8)*d z9 - star(c y9)*d z8 = 0` holds on the whole closed polytope, boundary included. This is the promised replacement for the paper's `rho_8 = rho_9`. Then `star(c y8)*star(c y9)*M = (u0u3+u1u2)*(u8v9+u9v8)` modulo the two weight-one kernels, and with `W = 0` the right factor is `2*star(c y8)*d z9 ≠ 0`. Pinning comes first (from `normSq` of the two kernel relations: `q1 r8 = q0 r9`, `q3 r8 = q2 r9`, reducing to `9q0+3q2 = 1`, `3q0+9q2 = 1` by `linear_combination (-18)*e_i`), which supplies the nonvanishing the synchronisation step needs.

**New in `Triangle.lean`** (`pair_prod_eq_zero`, `pair_contradiction`, `pair_contradiction_of_normSq`): the mixed pair triangle `a*f+b*e = 0`, `c*f+d*e = 0`, `a*d+b*c = 0` ⟹ `e*b*c = 0` v

#### auditVerdict

INDEPENDENT AUDIT — phase propagation group (orbits 49, 51). Verdict: **PASS on all three files.** No smuggled hypotheses, no axiom leakage, no `sorry`, no vacuity. Every builder claim I could test held.

## 1-2. Files present, hashes recomputed (all MATCH)

| File | lines | recomputed SHA-256 | vs claim |
|---|---|---|---|
| `D:/UTD/Project_purdue/Lean_certification/SixQubit/Orbit49.lean` | 609 | `bde3e4bc425756efb4aa2dcba641023a29dfe9a69d2a0d6a0efc3093d24cc848` | MATCH |
| `D:/UTD/Project_purdue/Lean_certification/SixQubit/Orbit51.lean` | 455 | `586946fdc29a7291f008b2f46355c0657abeff43f6278ce2449e9fc2fcbd6730` | MATCH |
| `D:/UTD/Project_purdue/Lean_certification/SixQubit/Triangle.lean` | 153 | `3706718569cb726c010c353bb608f0b91fe209bea8fF109821cdE4C04B66728F` (case-insens. match) | MATCH |

All five claimed tool scripts exist under `tools/generators/` and `tools/verification/`.

## 3. Recompilation (my own runs)

`Triangle` / `Orbit49` / `Orbit51` / `Orbit50` / `Orbit20` / `Audit.lean` — **every one exit=0 with literally zero output** (Audit.lean emits only its own `#print axioms` lines). No warnings, no `unused variable`, nothing. Triangle's other four dependents are unbroken.

## 4. `#print axioms` (my own scratch file, since deleted)

All eleven — both `no_go_of_moments`, all four `S0/S1_eq_fiber`, all three new Triangle lemmas, plus the two pre-existing Triangle lemmas — return exactly `[propext, Classical.choice, Quot.sound]`. No `sorryAx`, no `Lean.ofReduceBool` (which is what `native_decide` would have injected).

## 5. `sorry` / `native_decide`

Zero `sorry` hits. Three `native_decide` hits, all inside the closing lines of module docstrings (`Orbit49.lean:39`, `Orbit51.lean:37`, `Triangle.lean:36`), each in a `/-- … -/` block terminated by `-/` before the `namespace` line — I read the surrounding 12 lines of each. None in tactic position. Also zero `axiom`, `admit`, `unsafe`, `implemented_by`.

## 6. Hypothesis classification — THE IMPORTANT ONE

Machine-extracted from the theorem statements myself, not from the builder's audit script:

- `SixQubit.Orbit49.no_go_of_moments`: **21 hypotheses** = (a) 20 × `offSum c d ef_k w_j = 0` + (b) 0 + (c) 1 × `MomentSystem`. Nothing else.
- `SixQubit.Orbit51.no_go_of_moments`: **12 hypotheses** = (a) 11 + (b) 0 + (c) 1. Nothing else.

Counts confirm the claim. I then attacked the two places a fact could still hide:

- **Inside `MomentSystem`**: both structures contain exactly 23 fields that are purely *linear* equations in `q0..q9, r0..r9` plus exactly 20 nonnegativity fields (`nq0..nq9`, `nr0..nr9`). **No quadratic, no product, no amplitude term anywhere.** A planted `p0*p3 = p1*p2` would have been the obvious cheat; it is not there.
- **Inside `offSum`**: `Orbit49.lean:294` and `Orbit51.lean:231` are byte-identical to the pre-existing house definition used by `Orbit50`/`Orbit48`/all 50-odd orbit modules. Not weakened.

I re-derived all 23 moment equations from the fibers: `m1..m6` are exactly the single-qubit marginals (`Σ_{y:y_k=1} q_y = Σ_{z:z_k=1} r_z`) and `m12..m56` exactly the 15 two-qubit marginals, with `n0/n1` normalization. **Zero mismatches** — the moment system is the genuine one, not fabricated. I also verified every `(mask, dressing)` pair has `|supp(e) ∪ supp(z)| = 2 ≤ 2`, so no illegitimate weight-3 constraint was slipped in; all 20 / 11 pairs are distinct.

## 7. Fibers, `av`, residues, delta

Recomputed both fibers from scratch over all 64 strings:

- **Orbit 49**: `av = ![1,1,1,3,3,5]` — matches the paper's `(q,m,a)=(6,3,(1,1,1,3,3,5))` (tex line 7850) and table row 49. Residue-0 fiber has 10 elements and equals Lean's `S0` **exactly**; residue-2 fiber has 10 and equals `S1` **exactly**. Lean's `y0..y9` are string-for-string the paper's `x_0..x_9` in `eq:o49-S0`.
- **Orbit 51**: `av = ![1,1,2,3,3,4]` — matches tex line 8161 and table row 51. Same result; `y0..y9` match `eq:o51-S0` exactly.
- **Delta = 2 is correct, not guessed.** `Σa = 14 ≡ 2 (mod 6)` for both, so the complement of a residue-0 string necessarily sits at residue 2 — and I confirmed `S1` *is* the bitwise complement of `S0` in both. This is the failure mode I was most alert to; it does not occur. (The table's last column is `ν`, not δ — columns are `(|S_0|,|S_δ|) & r_* & d_LP & ν`.)

## Non-vacuity — verified independently, and it is the strongest evidence

I solved both `MomentSystem`s symbolically. Both give a **23×20 matrix of rank 17 → a 3-dimensional solution set**, matching the paper's "rank seventeen" and `d_LP = 3`. The solution sets reproduce the paper's published normal forms exactly:

- Orbit 49 → pairs `(0,1),(2,3),(4,5),(6,7)` each sum to `1/6`, `q8=q9=1/6`, `q0+q2+q4+q6=1/3` — algebraically identical to `eq:o49-moments`.
- Orbit 51 → `q6=q5, q7=q4, q9=q0+q2, q8=1/3−q9` — algebraically identical to `eq:o51-moments`.

Strictly positive feasible points exist in both (e.g. orbit 49 at `r3=r5=r7=1/12`, orbit 51 at `r3=r7=1/12, r9=1/6`, both giving `q=r=(1/12×8, 1/6, 1/6)`). So the linear part alone is satisfiable with all probabilities positive — **the contradiction genuinely comes from the amplitude relations, not from an infeasible polytope faking a proof.**

The new `Triangle.pair_prod_eq_zero` is honest general algebra; I verified the certificate by hand: `(c/2)(af+be) − (a/2)(cf+de) + (e/2)(ad+bc) = bce`. It carries no orbit-specific content.

## Where the builder overclaimed (minor, and mostly self-disclosed)

1. **Two claims I could not verify, and the builder stated them as fact.** (a) "Regenerating reproduces both files byte-identically" — I did not re-run `gen4951.py`, as it would clobber the audited files. (b) `Triangle.lean`'s pre-existing three theorems are "byte-unchanged" — there is no VCS in this repo, so byte-identity is unprovable after the fact. Both are *plausible*: the three originals are present at lines 47/56/71 with the new ones appended at 118/127/141, and all five Triangle dependents compile and are axiom-clean. Treat as

#### group

projector

#### label

projector orbits (19 and 20)

#### builderReport

Both orbits are certified. Report follows.

## Files created (all inside `D:/UTD/Project_purdue/Lean_certification`)

| absolute path | lines | SHA-256 |
|---|---|---|
| `D:\UTD\Project_purdue\Lean_certification\SixQubit\Orbit19.lean` | 833 | `05A6C9B57F5CDD5BA526BA8579B5DB77EED838EB71BBA80DE654C197DF4C921D` |
| `D:\UTD\Project_purdue\Lean_certification\SixQubit\Orbit20.lean` | 1016 | `EBA14FB031D12A696F56540BFD010AC21E2451731A74FEF8BDFBAC99A8F1000E` |
| `D:\UTD\Project_purdue\Lean_certification\tools\generators\gen19.py` | 326 | `3811080B98B8370A84EFCCE0ED765AED670FD5BC1EDDBDD2FEF2B58ABFAC89BA` |
| `D:\UTD\Project_purdue\Lean_certification\tools\generators\gen20.py` | 413 | `B68778635F20C336AC23F461763870C0C513D66B407A9A7FBC114A73D72FB265` |
| `D:\UTD\Project_purdue\Lean_certification\tools\verification\check1920.py` | 154 | `993812308C3C9261CFF26F4817CC440481CA399E2D340B3FBDD09B2555C900D4` |
| `D:\UTD\Project_purdue\Lean_certification\tools\verification\moments1920.py` | 123 | `E3693939652A6C30FDD9C51CCB1F080DC5CE36115F941834DE6F31CC5E8AAD5E` |

No pre-existing file was created, edited or deleted. `SixQubit.lean` and `SixQubit/Audit.lean` untouched. Every Lean line in both modules is script-emitted (`gen19.py` / `gen20.py`); nothing typed by hand.

## Compilation (commands run, output read)

```
cd D:/UTD/Project_purdue/Lean_certification
lake build SixQubit.Common SixQubit.Triangle   -> "Build completed successfully"
lake env lean SixQubit/Orbit19.lean            -> EMPTY output, exit 0   (35 s)
lake env lean SixQubit/Orbit20.lean            -> EMPTY output, exit 0   (52 s)
lake build SixQubit.Orbit19 SixQubit.Orbit20   -> "Build completed successfully"
```
Empty in both cases: zero errors and zero warnings. (Orbit20 needed two fixes to get there: `lt_or_le` does not exist in this Mathlib — it is `lt_or_ge`; and the headline exceeded the 200 000-heartbeat budget, so it carries `set_option maxHeartbeats 4000000 in`, the same device `Orbit25.lean`/`Orbit26.lean` already use. The endgame `linarith`s are `linarith only [...]` and the 24 expansion hypotheses are `clear`ed before the case split, so the budget is not being used to paper over a slow proof.)

## `#print axioms`, verbatim

```
'SixQubit.Orbit19.no_go_of_moments' depends on axioms: [propext, Classical.choice, Quot.sound]
'SixQubit.Orbit20.no_go_of_moments' depends on axioms: [propext, Classical.choice, Quot.sound]
```
Also checked clean: `Orbit19.S0_eq_fiber`, `S1_eq_fiber`, `MomentSystem.anchors`; `Orbit20.S0_eq_fiber`, `S1_eq_fiber`, `MomentSystem.blockMass`, `MomentSystem.uniform`, `blockMatch`. The strings `sorry`/`native_decide`/`admit` occur only inside docstrings (machine-checked by `check1920.py`).

## Hypothesis classification

**`SixQubit.Orbit19.no_go_of_moments`** — 25 hypotheses (plus the data binder `(c d : SS.BitString 6 -> ℂ)`):
- (a) `offSum ... = 0`: **24** — masks `efA = 000010` (= X₅) and `efB = 000001` (= X₆), each with all **12** admissible dressings `{z : |supp(e) ∪ supp(z)| ≤ 2}`.
- (b) `diagBot = diagTop`: **0** (this orbit needs no nonzero-flip diagonal row).
- (c) `MomentSystem ...`: **1**.

**`SixQubit.Orbit20.no_go_of_moments`** — 25 hypotheses:
- (a) `offSum ... = 0`: **24** — masks `efA/efB/efC = 000100 / 000010 / 000001`, each with the **8** dressings `{0,eₖ} × {0,e₁,e₂,e₃}` that span `Π_r(1±χₖ)/2`. All 8 satisfy `|supp(e) ∪ supp(z)| ≤ 2`.
- (b) `diagBot = diagTop`: **0** (all diagonal input is the `e = 0` pure-Z rows, i.e. `MomentSystem` itself).
- (c) `MomentSystem ...`: **1**.

Nothing falls outside (a)/(b)/(c). Verified mechanically, not by eye: `python tools/run.py verification/check1920.py` parses the two `.lean` files back, recomputes the fibers from `(q,a,δ)`, and asserts that the headline binder list is exactly `(c d : …)`, one `MomentSystem`, and *n* `offSum … = 0`; that every `(e,z)` pair is admissible; that the `MomentSystem` fields are literally the 2 normalizations + 21 moment equalities + 32 nonnegativities of the true fibers; and that all 48 Walsh-expansion bodies equal `Σ_y (−1)^{z·y} conj(c_{y⊕e}) d_y`. Output: `ALL CHECKS PASSED`.

## What each proof actually does

**Orbit 19** (fibers 16 + 16, `av = ![1,1,1,1,2,2] : ZMod 4`). Each of the eight anchor monomials is isolated by an exact rational combination of the 12 dressings of one mask, e.g. `star (c y₀) * d z₀ = 0` from `(1/8)h₁₂ − (1/8)h₁₃ + … − (1/16)h₂₃`. The eight are exactly `{c_000000, c_000011} × {d_000001, d_000010}` and `{c_111100, c_111111} × {d_111101, d_111110}` — matching the paper's Eqs. (o19-X5-anchor0/4) and (o19-X6-anchor0/4). `nsqZero` turns each into `normSq · normSq = 0`; summing gives `P₀Q₀ = 0`, `P₄Q₄ = 0`. `MomentSystem.anchors` derives `P₀ = Q₀`, `P₄ = Q₄`, `P₀ + P₄ = 1/2` by `linarith` alone, so `P₀² = P₄² = 0` and `linarith` closes.

**Orbit 20** (fibers 16 + 16, `av = ![1,1,1,2,2,2] : ZMod 4`). The 24 reciprocal relations are emitted already in Triangle orientation and proved by `linear_combination` over 8 hypotheses each. `minorEq` converts each to a vanishing 2×2 minor. `blockMatch` (a division-free, positivity-free lemma: `(pᵢ − qᵢ)·μ = 0` by `linear_combination`, then one case split on `μ = 0` vs `μ > 0`) turns minors + `blockMass` into the 16 equalities `|c_{r,y}|² = |d̃_{r,y}|²`. `MomentSystem.uniform` then makes all four blocks uniform and gives `4(α₀+α₁+α₂+α₃) = 1`, by `linarith`. A four-way case split finds a positive block and hands three of its pair relations to `SixQubit.Triangle.contradiction_of_normSq` (reused unmodified).

Independent cross-check of the two derived-probability lemmas, over ℚ, with a deliberate negative control: `python tools/run.py verification/moments1920.py` reports `P0−Q0 → 0`, `P4−Q4 → 0`, `P0+P4 → 1/2`, `P0 alone → None`; and for orbit 20 base rank 20, all four block-mass differences → 0, augmented rank 29, every within-block difference → 0, `4(Σα) → 1`. Ranks 20 and 29 agree with the paper's stated values.

## Deviations from the paper and things not done

- Orbi

#### auditVerdict

Audit complete. Findings below.

---

# AUDIT: projector orbits 19 and 20 — both PASS

## 1. File existence + 2. SHA-256

All six claimed files exist. **All six hashes match the claim byte-for-byte.**

| file | lines (`wc -l`) | SHA-256 vs claim |
|---|---|---|
| `D:\UTD\Project_purdue\Lean_certification\SixQubit\Orbit19.lean` | 833 ✓ | `05A6C9B5…C4921D` **MATCH** |
| `D:\UTD\Project_purdue\Lean_certification\SixQubit\Orbit20.lean` | 1016 ✓ | `EBA14FB0…8F1000E` **MATCH** |
| `D:\UTD\Project_purdue\Lean_certification\tools\generators\gen19.py` | 326 ✓ | `3811080B…FAC89BA` **MATCH** |
| `D:\UTD\Project_purdue\Lean_certification\tools\generators\gen20.py` | 413 ✓ | `B6877863…3D72FB265` **MATCH** |
| `D:\UTD\Project_purdue\Lean_certification\tools\verification\check1920.py` | 154 ✓ | `99381230…555C900D4` **MATCH** |
| `D:\UTD\Project_purdue\Lean_certification\tools\verification\moments1920.py` | 123 ✓ | `E3693939…5CE8AAD5E` **MATCH** |

## 3. Recompilation (mine, from the repo)

```
$ lake env lean SixQubit/Orbit19.lean
                          <- literally empty
EXIT19=0
$ lake env lean SixQubit/Orbit20.lean
                          <- literally empty
EXIT20=0
$ lake build SixQubit.Orbit19 SixQubit.Orbit20
Build completed successfully (7893 jobs).
```
Zero errors, **zero warnings**, in both. The only `set_option` in either file is `maxHeartbeats 4000000` at `Orbit20.lean:823` — a resource budget, not a soundness lever, and disclosed.

## 4. `#print axioms` (my own scratch module, verbatim)

```
'SixQubit.Orbit19.no_go_of_moments'      depends on axioms: [propext, Classical.choice, Quot.sound]
'SixQubit.Orbit19.S0_eq_fiber'           depends on axioms: [propext, Classical.choice, Quot.sound]
'SixQubit.Orbit19.S1_eq_fiber'           depends on axioms: [propext, Classical.choice, Quot.sound]
'SixQubit.Orbit19.MomentSystem.anchors'  depends on axioms: [propext, Classical.choice, Quot.sound]
'SixQubit.Orbit20.no_go_of_moments'      depends on axioms: [propext, Classical.choice, Quot.sound]
'SixQubit.Orbit20.S0_eq_fiber'           depends on axioms: [propext, Classical.choice, Quot.sound]
'SixQubit.Orbit20.S1_eq_fiber'           depends on axioms: [propext, Classical.choice, Quot.sound]
'SixQubit.Orbit20.MomentSystem.blockMass' depends on axioms: [propext, Classical.choice, Quot.sound]
'SixQubit.Orbit20.MomentSystem.uniform'  depends on axioms: [propext, Classical.choice, Quot.sound]
'SixQubit.Orbit20.blockMatch'            depends on axioms: [propext, Classical.choice, Quot.sound]
'SixQubit.Triangle.contradiction_of_normSq' depends on axioms: [propext, Classical.choice, Quot.sound]
```
Nothing beyond the three standard axioms anywhere. PASS.

## 5. `sorry` / `native_decide` / `admit`

Exactly two hits total, both the identical sentence *"Everything computational is decided by the Lean kernel; `native_decide` is not used."* — `Orbit19.lean:25` and `Orbit20.lean:31`. I read the surrounding lines: both sit inside the module header `/-! … -/` block (which opens at line 6 and closes at line 26 / 33 respectively). Neither is in tactic position. Also grepped clean for `^axiom`, `^constant`, `unsafe`, `opaque`, `implemented_by`, `^variable`, `^instance`, `^@[` — **none present**, so no hypotheses are smuggled in via a `variable` block.

## 6. Hypothesis classification — THE IMPORTANT ONE

I parsed the full binder list of each headline mechanically, not by eye.

**`SixQubit.Orbit19.no_go_of_moments`** — 25 binders + 1 data binder `(c d : SS.BitString 6 → ℂ)`:
- (a) `offSum … = 0`: **24** — `efA=000010` ×12 dressings, `efB=000001` ×12. All 24 distinct.
- (b) `diagBot = diagTop`: **0**
- (c) `MomentSystem`: **1**
- **outside (a)/(b)/(c): NONE.**

**`SixQubit.Orbit20.no_go_of_moments`** — 25 binders + 1 data binder:
- (a) `offSum … = 0`: **24** — `efA/efB/efC = 000100/000010/000001`, 8 dressings each. All 24 distinct.
- (b) `diagBot = diagTop`: **0**
- (c) `MomentSystem`: **1**
- **outside (a)/(b)/(c): NONE.**

Both match the builder's report exactly, and match the house pattern of already-accepted orbits (Orbit29 has the identical `{offSum, MomentSystem, data}` shape). **No smuggled algebraic fact.**

Additional checks I ran that the task did not require but that are where a fake would hide:
- **Dressing admissibility**: recomputed `|supp(e) ∪ supp(z)|` for all 48 `(e,z)` pairs. Max is 2. **Zero inadmissible** — every hypothesis is a legitimate weight-≤2 KL row.
- **Walsh expansions**: recomputed all 48 `ex{A,B,C}_w*` right-hand sides from scratch as `Σ_{y∈S1, y⊕e∈S0} (−1)^{z·y} conj(c_{y⊕e}) d_y`, including signs. **48 checked, 0 mismatches.**
- **`MomentSystem` contents**: recomputed the true monomial moments `E[n_S]` for all `|S| ≤ 2` from the fibers. Both structures are *exactly* 2 normalizations + **21** moment rows (6 singles + 15 pairs) + **32** nonnegativities, and **every one of the 21 rows matches the true index sets on both sides**. Note the rows are genuinely asymmetric (e.g. `m56 : q1 + q15 = r3+r5+r7+r9+r11+r13`); I initially flagged this as wrong before realizing the convention is monomial moments, not characters — recomputed under the correct convention it is right.
- **Non-vacuity** (the failure mode that would make both theorems worthless): LP'd `MomentSystem` *alone*. Feasible for both orbits, and **strictly** feasible — max-min-coordinate `1/24` (orbit 19) and `1/16` (orbit 20), so interior points with all 32 probabilities positive exist. The off-diagonal hypotheses are doing real work; neither theorem is vacuously true.

## 7. Fibers really pinned

- **Orbit 19**: `av = ![1,1,1,1,2,2]`. Paper Eq. (o19-record): `(q,m,a) = (4,2,(1,1,1,1,2,2)), δ=2`. **Match.** Fiber theorems are `filter (SS.weight av x = 0) = S0` and `= 2 = S1`, both closed by `decide` — kernel-computed, not hand-asserted. I independently recomputed both fibers: sizes 16/16, and `S0`/`S1` are the exact lex-ordered fibers. Structure reproduces the paper's table (`w∈{0,4} → s=t`, `w=2 → s≠t`).
- **Orbit 20**: `av = ![1,1

#### group

trace

#### label

orbit 5 (trace inequality in C^4)

#### builderReport

Both modules compile clean. Final verification is done. Here is the report.

---

## Files created (all inside `D:/UTD/Project_purdue/Lean_certification`)

| absolute path | lines |
|---|---|
| `D:/UTD/Project_purdue/Lean_certification/SixQubit/Trace5.lean` | 657 |
| `D:/UTD/Project_purdue/Lean_certification/SixQubit/Orbit5.lean` | 1892 |
| `D:/UTD/Project_purdue/Lean_certification/tools/generators/gen5algebra.py` | 304 |
| `D:/UTD/Project_purdue/Lean_certification/tools/generators/build5.py` | 22 |
| `D:/UTD/Project_purdue/Lean_certification/tools/generators/gen5orbit.py` | 131 |
| `D:/UTD/Project_purdue/Lean_certification/tools/generators/gen5lean.py` | 371 |
| `D:/UTD/Project_purdue/Lean_certification/tools/generators/gen5lean2.py` | 165 |
| `D:/UTD/Project_purdue/Lean_certification/tools/generators/o5data.py`, `o5scan.py` | 79, 46 |
| `build_zh/trace5_head.lean`, `trace5_tail.lean`, `orbit5_part1.lean`, `orbit5_part2.lean` | build artifacts |

No pre-existing file was modified. `SixQubit.lean` and `SixQubit/Audit.lean` untouched.

## Compilation (commands actually run, output actually read)

```
cd D:/UTD/Project_purdue/Lean_certification && lake env lean SixQubit/Trace5.lean   -> EMPTY output, exit 0
cd D:/UTD/Project_purdue/Lean_certification && lake env lean SixQubit/Orbit5.lean   -> EMPTY output, exit 0
lake build SixQubit.Trace5   -> "Built SixQubit.Trace5 (59s)"
lake build SixQubit.Orbit5   -> "Built SixQubit.Orbit5 (72s)"
```
Zero errors and zero warnings in both files.

## SHA-256

```
SixQubit\Trace5.lean   078E01662A1B865FBCDEEC431F5E2D07D4E9240F7820A4080C58C07E37402BBC
SixQubit\Orbit5.lean   4B103967ECB664515B7B74B123AA9B9AA1F689A78EC7FD84C206BA7D7BAC52AB
```

## `#print axioms` (verbatim)

```
'SixQubit.Trace5.cs_tight' depends on axioms: [propext, Classical.choice, Quot.sound]
'SixQubit.Trace5.bell_contradiction' depends on axioms: [propext, Classical.choice, Quot.sound]
'SixQubit.Trace5.orthogonal_overflow' depends on axioms: [propext, Classical.choice, Quot.sound]
'SixQubit.Trace5.cs' depends on axioms: [propext, Classical.choice, Quot.sound]
'SixQubit.Orbit5.frame_reduction' depends on axioms: [propext, Classical.choice, Quot.sound]
'SixQubit.Orbit5.S0_eq_fiber' depends on axioms: [propext, Classical.choice, Quot.sound]
'SixQubit.Orbit5.S1_eq_fiber' depends on axioms: [propext, Classical.choice, Quot.sound]
'SixQubit.Orbit5.two_flip_12' depends on axioms: [propext, Classical.choice, Quot.sound]
'SixQubit.Orbit5.two_flip_13' depends on axioms: [propext, Classical.choice, Quot.sound]
'SixQubit.Orbit5.two_flip_14' depends on axioms: [propext, Classical.choice, Quot.sound]
'SixQubit.Orbit5.two_flip_23' depends on axioms: [propext, Classical.choice, Quot.sound]
'SixQubit.Orbit5.two_flip_24' depends on axioms: [propext, Classical.choice, Quot.sound]
'SixQubit.Orbit5.two_flip_34' depends on axioms: [propext, Classical.choice, Quot.sound]
'SixQubit.Orbit5.MomentSystem.norms' depends on axioms: [propext, Classical.choice, Quot.sound]
'SixQubit.Orbit5.MomentSystem.marginal' depends on axioms: [propext, Classical.choice, Quot.sound]
```
No `sorry`, no `native_decide` anywhere in tactic position (only in docstrings).

## Hypothesis classification

**`SixQubit.Orbit5.frame_reduction`** — 21 hypotheses (plus the two amplitude functions `c d`):
* (c) `MomentSystem` — 1 (`hm`, on the 40 `Complex.normSq` values)
* (a) `offSum c d e z = 0` — 8: `(f1,w0) (f1,f2) (f2,w0) (f2,f3) (f3,w0) (f3,f4) (f4,w0) (f4,f1)`
* (b) `diagBot c e z = diagTop d e z` — 12: `p1,p2,p3 × w0,w1,w2,w3` where `p1=100000, p2=010000, p3=110000`, `w0..w3 = 000000,100000,010000,110000`

Nothing outside (a)/(b)/(c). Every `(e,z)` used was machine-checked against `tools/core/kl.py`'s admissible list (`|supp(e) ∪ supp(z)| ≤ 2`): 26 rows used, 0 inadmissible.

**`SixQubit.Orbit5.two_flip_12/13/14/23/24/34`** — 1 hypothesis each, all class (a) (`offSum c d g** w0 = 0`, the weight-2 active flips).

**`SixQubit.Trace5.*`** — these are *pure `ℂ⁴` algebra lemmas*, not orbit theorems. Their hypotheses are algebraic (`nsq x = 1/3`, `ip x y = 0`, frame equality), which is why they carry no (a)/(b)/(c) classification; the classification duty sits entirely on the orbit module that feeds them. `bell_contradiction` has 26 hypotheses, `cs_tight` has 7.

## What is proved

`Trace5.lean` (algebra layer, 9 declarations):
* `cs`, `lagrange`, `wedges_zero`, `par` — Cauchy–Schwarz in `ℂ⁴` from the Lagrange identity, plus its tightness case.
* `cs_tight` — **the Cauchy–Schwarz tightness step**: `‖u‖²=‖v‖²=1/3`, `u†bᵢ=0`, and equality of the two free-pair marginals give `u†aᵢ=0` for all `i` and `vv† = uu†`, hence `Σᵢ aᵢaᵢ† = Σᵢ bᵢbᵢ†`.
* `frame_swap`, `frame_idem`, `frame_kernel`, `fr_diag`, `mass_le`, `orthogonal_overflow`, `bell_contradiction` — **the Bell-branch trace contradiction**.

I did **not** use the paper's `Tr(S²) ≥ (Tr S)²/3` route. In coordinates that needs a rank/eigenvalue argument. Instead: `Tr(R²) = Σᵢⱼ|aᵢ†bⱼ|² = Σᵢ|aᵢ†bᵢ|² ≤ 4·(1/6)² = 1/9` while `Tr(R²) = Σᵢⱼ|aᵢ†aⱼ|² ≥ Σᵢ‖aᵢ‖⁴ = 1/9`, so equality forces the four `aᵢ` pairwise orthogonal; then `6R` is an idempotent (`Πₖₖ = Σₗ|Πₖₗ|²`, trace 4 in dimension 4) hence `I`, and `Ru = 0` gives `u = 0` against `‖u‖²=1/3`. This is elementary (`linarith`/`nlinarith` on coordinates) and needs no `ℂ³` Pauli basis and no PSD trace inequality. It is a *stronger* statement than the paper's: five pairwise orthogonal nonzero vectors cannot fit in `ℂ⁴`.

`Orbit5.lean`: fibers by `decide` over all 64 strings; the 29-equation moment system with `MomentSystem.norms` (all ten squared norms, `linarith`) and `MomentSystem.marginal` (the four diagonal marginal equalities, `linarith`); the off-diagonal and diagonal Walsh layers; the six `two_flip_ij : aᵢ†bⱼ + aⱼ†bᵢ = 0`; and `frame_reduction`, which delivers `u†aᵢ = 0`, `aᵢ†v = 0`, `u†bᵢ = 0` and `Σᵢaᵢaᵢ† = Σᵢbᵢbᵢ†` — exactly steps 1–3 of the assigned route.

## What I could NOT finish — stated plainly

**There is no `False` headline for orbit 5.*

#### auditVerdict

(none)

#### group

graph

#### label

orbit 17 (hafnians and the support graph)

#### builderReport

# Orbit 17 — complete, kernel-checked

## Files created (all inside `D:/UTD/Project_purdue/Lean_certification`)

| absolute path | lines | SHA-256 |
|---|---|---|
| `D:/UTD/Project_purdue/Lean_certification/SixQubit/Hafnian.lean` | 430 | `7E5E36E57784ECFCF0DB53376C97CA5992233723ADBECE093E660413B46F2389` |
| `D:/UTD/Project_purdue/Lean_certification/SixQubit/Orbit17.lean` | 1059 | `5E8A2D1C230ABF201058D54CBE2A17CE13DED949A7CC86AC6D49B43F748631EC` |

Generators / audit tools (Python, all new, none pre-existing):
`tools/generators/gen17haf.py` (408), `gen17.py` (320), `o17_analyse.py` (113), `o17_haf.py` (139), `o17_graphs.py` (81), `o17_graphs2.py` (106), `o17_cert.py` (73), `o17_check.py` (139).
No pre-existing file was modified. `SixQubit.lean` and `SixQubit/Audit.lean` untouched; `Triangle.lean` untouched (another agent is editing it, so I copied its one-line elimination identity into my own layer rather than importing it).

## Compilation (commands actually run, output read)

```
cd D:/UTD/Project_purdue/Lean_certification && lake build SixQubit.Hafnian
      -> "Built SixQubit.Hafnian (16s)"
cd D:/UTD/Project_purdue/Lean_certification && lake env lean SixQubit/Hafnian.lean
      -> EMPTY output, exit 0        (zero errors, zero warnings)
cd D:/UTD/Project_purdue/Lean_certification && lake env lean SixQubit/Orbit17.lean
      -> EMPTY output, exit 0  (43 s)  (zero errors, zero warnings)
cd D:/UTD/Project_purdue/Lean_certification && lake build SixQubit.Orbit17
      -> "Built SixQubit.Orbit17 (42s)"
```

## `#print axioms`, verbatim

```
'SixQubit.Orbit17.no_go_of_moments' depends on axioms: [propext, Classical.choice, Quot.sound]
'SixQubit.Orbit17.S0_eq_fiber' depends on axioms: [propext, Classical.choice, Quot.sound]
'SixQubit.Orbit17.S1_eq_fiber' depends on axioms: [propext, Classical.choice, Quot.sound]
'SixQubit.Hafnian.no_go' depends on axioms: [propext, Classical.choice, Quot.sound]
'SixQubit.Hafnian.deg4' depends on axioms: [propext, Classical.choice, Quot.sound]
'SixQubit.Orbit17.MomentSystem.normalForm' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Hypothesis classification of the headline

`SixQubit.Orbit17.no_go_of_moments` — 33 binders: 2 data arguments (`c d : SS.BitString 6 -> ℂ`) and **31 hypotheses**:

* (a) `offSum c d e = 0`: **30** — the 15 edge masks `e01 … e45`, each with dressings `wz` (z = 0) and `wp_i` (i the lower endpoint). Every one satisfies `|supp(e) ∪ supp(z)| = 2 ≤ 2`; checked against `kl.dressings_full` (4 admissible dressings per edge mask; the other two are the sign-duplicates of these).
* (b) `diagBot = diagTop`: **0** — no diagonal row is used.
* (c) `MomentSystem …`: **1**.

Nothing else. `SixQubit.Hafnian.no_go` takes a single hypothesis, `Sys` (15 hafnian equations + 6 degree equations), and every one of those 21 is *derived* inside `Orbit17.lean` from (a) and (c) by `linear_combination`/`linarith`.

## What the proof does, and where it leaves the paper

The moment layer is fully derived: `MomentSystem.normalForm` proves, by `linarith` from the 23 exact moment rows alone, `r15 = 1/4` and the six weighted-degree equations `∑_{e∋v} |c_e|² = 1/4`. (I never need `|a|²=1/4` nor `x_e = y_e`.) For each edge mask the half-difference of the two dressings is the anchor flip `conj(a) d_f + conj(c_f) b = 0`, the half-sum is the pair flip. Multiplying the pair flip by `conj(a)` and substituting the six anchor flips gives `2 b · haf_Q = 0` with no division at all — the paper's `λ = -b/conj(a)` never appears — and `|b|² = 1/4` cancels `b`.

The combinatorial core is **not** the paper's max-degree ladder. Formalising "Δ ≤ 2 ⟹ paths and cycles" and the 10×10 K₅ determinant is expensive, and `decide` over 2¹⁵ support graphs is far beyond the kernel. Instead:

* `deg4` — a single degree-4 monomial identity, `c01·c02·c03·c45 = (c04c05/3)H₀₁₂₃ − (c03c05/6)H₀₁₂₄ − …` (10 terms), obtained by eliminating the ten edges of the opposite K₅. It replaces the paper's Δ=3,4,5 pair-sum/rank arguments in one stroke. (`o17_haf.py` records the honest negative result that the *degree-3* monomials `c01c23c0x` are **not** in the ideal, which is why degree 4 is needed.)
* `tri` — the odd-triangle elimination, used three ways to kill the three edges at a vertex non-adjacent to a degree-3 vertex.
* the degree equations, which forbid an isolated vertex (`iso`) and forbid a star (`star`: leaves force mass 1/4 on each of five edges, so the centre carries 5/4).

The whole hypothesis bundle is closed under vertex relabelling (`swap01 … swap45`), so `key` ("no vertex has three active edges"), `disjA`/`disj` ("no two disjoint active edges") and `main1` are each proved once in a canonical labelling and transported by a word in those five lemmas. Before committing to this route I verified in Python over all 32768 graphs that no-isolated-vertex + the three kill rules leaves 0 graphs (`o17_graphs2.py`: 27449 → 27443 → 196 → 10 → 0); that enumeration is a design check only — the Lean proof does not depend on it.

## Machine audits actually run (`tools/run.py generators/o17_check.py`)

```
1. every used dressing admissible : True      (4 admissible dressings per edge mask)
2. Lean moment fields = the 23 exact moment rows : True   (rank 23 of (23, 32))
3. normalForm facts are linear consequences : True [True x7]
4. incidence / flip / sign tables match the fibers : True
5. Orbit17.lean  sorry:False  native_decide:False  decide calls:585
5. Hafnian.lean  sorry:False  native_decide:False  decide calls:0
```

Non-vacuity: the moment polytope is non-empty — `q_∅ = r_V = 1/4`, all fifteen edge masses `1/20` satisfies all 23 equations and every nonnegativity (`full_moment_ok` returns True). So the contradiction genuinely comes from the 30 KL rows, not from an infeasible moment system.

## Not done / caveats

* The module is **not registered** in `SixQubit.lean` or `SixQubit/Audit.lean` — deliberately, per instructions; the orchestrator must add `import SixQubit.Orbit17` (which pulls in 

#### auditVerdict

AUDIT OF ORBIT 17 — VERDICT: **PASS on both files. No overclaim found.**

## `D:/UTD/Project_purdue/Lean_certification/SixQubit/Hafnian.lean` — PASS
- Exists, 430 lines. SHA-256 `7e5e36e5…46f2389` — **matches the claim exactly**.
- `lake env lean SixQubit/Hafnian.lean` → **literally empty output, exit 0, 20.5s**. Zero errors, zero warnings.
- `sorry`: 0 hits. `native_decide`: 1 hit, line 35, inside the module docstring `/-! … -/` closed at line 36 — not tactic position. Only 1 occurrence of the substring "decide" in the whole file (that same docstring word), so the claim "decide calls: 0" is correct.
- `#print axioms SixQubit.Hafnian.no_go` / `.deg4` / `.key` / `.main1` / `.disj` / `.star` / `.iso` → all `[propext, Classical.choice, Quot.sound]`. No `sorryAx`, no `Lean.ofReduceBool`.
- Headline `no_go` takes exactly one hypothesis, `Sys`, whose 21 fields I read: 15 hafnian equations `c_ij c_kl + c_ik c_jl + c_il c_jk = 0` over the 15 four-subsets of {0..5}, and 6 degree equations `∑_{e∋v} normSq c_e = 1/4`. Nothing else. Imports are `Mathlib`, `SS.FullKL`, `SixQubit.Common` — `SixQubit.Triangle` is genuinely not imported, as disclosed.

## `D:/UTD/Project_purdue/Lean_certification/SixQubit/Orbit17.lean` — PASS
- Exists, 1059 lines. SHA-256 `5e8a2d1c…48631ec` — **matches the claim exactly**.
- `lake env lean SixQubit/Orbit17.lean` → **literally empty output, exit 0, 41.2s**. Zero errors, zero warnings.
- `sorry`: 0 hits. `native_decide`: 1 hit, line 40, inside the module docstring closed at line 42. `by decide` occurrences: **585**, matching the claim.
- `#print axioms` on `no_go_of_moments`, `S0_eq_fiber`, `S1_eq_fiber`, `MomentSystem.normalForm` → all `[propext, Classical.choice, Quot.sound]`.

### Item 6 — hypothesis classification (the important one)
I parsed the top-level binder groups of `no_go_of_moments` mechanically, not by eye:
`{offSum: 30, MomentSystem: 1, diagBot/diagTop: 0, data (c d): 1 group = 2 vars, OTHER: []}`.
**Zero hypotheses outside the three permitted categories. Nothing smuggled.** The 30 rows are the 15 edge masks × {`wz`, `wp_lower-endpoint`}. `d z15 ≠ 0` (line 910) is *derived* from `normalForm`, not assumed; `hg0…hg5` likewise (line 909).

Anti-smuggling checks on the definitions themselves, since both `offSum` and `MomentSystem` are declared locally:
- `offSum` body (lines 132–134) **diffs byte-identical** against `SixQubit/Orbit12.lean:115` — the established framework definition, not a weakened local copy.
- All 30 `(e, z)` pairs are admissible under the repo's own `tools/core/kl.py::dressings_full` (the corrected 154-Pauli version, not the undercounting `scan.dressings`). 4 admissible dressings per weight-2 mask, 2 used per edge — consistent.
- I regenerated the moment system independently from `tools/core/orbit.py`'s canonical recipe (2 normalizations + 6 one-bit + 15 two-bit correlators) over the fibers, and compared row-by-row to the 23 equality fields parsed out of the Lean `structure MomentSystem`: **23/23 matched exactly, 0 unmatched Lean rows, 0 canonical rows missing.** No extra equation was slipped in.
- **Non-vacuity independently confirmed**: `q0 = r15 = 1/4`, all 30 edge masses `1/20` satisfies all 23 Lean equality rows exactly (rational arithmetic) with every coordinate ≥ 0. The `False` comes from the KL rows, not from an infeasible polytope.

### Item 7 — fibers
`av = ![1,1,1,1,1,1]` matches the paper's row 17 (`six_qubit_sslp_v7.tex:9431`: `17 & 4 & 2 & $(1,1,1,1,1,1)$ & $(16,16)$ & 6 & 9 & 4`). Residues are 0 and 2. Fiber sizes for δ=1,2,3 under this angle vector are 12, 16, 20 — so `(16,16)` **uniquely pins δ=2**; the Lean choice is not a free guess. `S0_eq_fiber`/`S1_eq_fiber` are stated as `univ.filter (weight av · = 0/2) = S0/S1` and closed by kernel `decide`, so the 16-element literals are genuinely pinned to the fibers (no duplicate-collapse loophole).

### Chain integrity
`no_go_of_moments` really routes through the hafnian layer: line 1052 constructs `SixQubit.Hafnian.Sys` from 15 derived `hf*` and 6 derived `hs*`, then line 1055 `exact SixQubit.Hafnian.no_go hsys`. Not dead code, not a parallel shortcut.

## Caveats I confirmed rather than found
- Not registered: `grep Orbit17|Hafnian SixQubit.lean SixQubit/Audit.lean` returns nothing. The orchestrator must add `import SixQubit.Orbit17`. Disclosed by the builder, and true.
- The builder's Python design-enumeration (`o17_graphs2.py`) is not load-bearing; I confirmed the Lean proof does not reference it.
- I could not verify the "no pre-existing file was modified" claim — the directory is not a git repo, so there is no baseline to diff against. This is the one claim I am unable to check; it is unverified, not refuted.
- Housekeeping: I created and then deleted `D:/UTD/Project_purdue/Lean_certification/AuditO17.lean` (the `#print axioms` harness). The repo is back to the state I found it in.

No reason to reject this certification.
