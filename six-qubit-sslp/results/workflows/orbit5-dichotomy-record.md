# Workflow record: orbit5-dichotomy

three independent angles on the flip-kernel dichotomy

Run `w8qswj18k`; 907274 subagent tokens, 204 tool calls.

---

## attempts

#### angle

schmidt

#### report

**Done — orbit 5 closes.** `SixQubit.Orbit5.no_go_of_moments` exists and proves `False`.

## Files

| path | lines | SHA-256 |
|---|---|---|
| `D:/UTD/Project_purdue/Lean_certification/SixQubit/Flip5.lean` (NEW) | 641 | `4136c5e16dd8671156afa03c7839be881e246f12db3d52d7aa1d5d5b0af34868` |
| `D:/UTD/Project_purdue/Lean_certification/SixQubit/Orbit5.lean` (regenerated, 1892 → 2851) | 2851 | `749789376939189cb2ef458246e06390c88d0a1a353771d8611eb38365abdcf2` |
| `.../tools/generators/gen5flip.py` (NEW) | 250 | `0ed3b8c9339acccf6929876dda92187bff21b229c30c9aa5fcd163d8247b55e7` |
| `.../tools/generators/gen5flip2.py` (NEW) | 225 | `512226a7fa5a442e9746580d3fd4aeebfc8f049f3d113fa0b1c20a849f395bc7` |
| `.../tools/generators/gen5flip3.py` (NEW) | 275 | `0782d78fb3a85f5b803e7a537d0085c208d4e1f1da87588d1c2a7f00e4eaa1a1` |
| `.../tools/generators/gen5lean3.py` (NEW) | 274 | `21d679daa8e926699e68a3a6c252a1c5b42f9a754146623d039a226b1d8c83e7` |
| `.../tools/generators/gen5lean.py` (patched: adds `import SixQubit.Flip5`, docstring) | 371 | `a7f5cd3fed4f1dc9c1cc8d22cfd9a7aa7f0335c5700191dfe7ade54446bec3ad` |

Untouched (mtimes predate this session): `SixQubit.lean`, `SixQubit/Audit.lean`, `SixQubit/Trace5.lean`, `SixQubit/Triangle.lean`.

## Compile commands run and observed

- `cd D:/UTD/Project_purdue/Lean_certification && lake env lean SixQubit/Flip5.lean` → **output empty**.
- `cd D:/UTD/Project_purdue/Lean_certification && lake env lean SixQubit/Orbit5.lean` → **output empty** (redirected to `build_zh/o5.log`, exit 0, file 0 lines). SHA-256 of both `.lean` files was taken immediately before and after and is identical, so this is a verification of the exact bytes tabled above.
- `lake build SixQubit.Orbit5` → `Build completed successfully (7894 jobs).`
- `lake build` (whole project, incl. `SixQubit/Audit.lean`) → `Build completed successfully (7965 jobs).` All 50 pre-existing orbits still audit to the three axioms.
- No `sorry`, no `native_decide` (the two grep hits are the docstrings saying so).

## `#print axioms`, verbatim

```
'SixQubit.Orbit5.no_go_of_moments' depends on axioms: [propext, Classical.choice, Quot.sound]
```
Also verified: `Flip5.core`, `Flip5.line_key`, `Flip5.bell_G`, `Flip5.anchor_scale`, `Orbit5.S0_eq_fiber`, `Orbit5.S1_eq_fiber`, `Orbit5.frame_reduction` — all the same three.

## Hypothesis list of `no_go_of_moments (c d : SS.BitString 6 -> ℂ)` — 51, all admissible

**MomentSystem (1)** — `hm : MomentSystem (Complex.normSq (c y0)) … (Complex.normSq (d z19))`

**`offSum … = 0` (38)**
- undressed / Z-dressed one-flips (8, pre-existing): `ho1a` `f1 w0`, `ho1b` `f1 f2`, `ho2a` `f2 w0`, `ho2b` `f2 f3`, `ho3a` `f3 w0`, `ho3b` `f3 f4`, `ho4a` `f4 w0`, `ho4b` `f4 f1`
- **new dressed one-flips (24)**, for i = 1..4: `hz{i}1 : f{i} p1` (= Z₀Xᵢ), `hz{i}2 : f{i} p2` (= Z₁Xᵢ), `hk{i}0 : k{i} w0` (= X₀Xᵢ), `hk{i}1 : k{i} p1` (= Y₀Xᵢ), `hl{i}0 : l{i} w0` (= X₁Xᵢ), `hl{i}2 : l{i} p2` (= Y₁Xᵢ), where `k{i} = f{i} ⊕ p1`, `l{i} = f{i} ⊕ p2`. Every one has physical weight two.
- two-flips (6, pre-existing): `ht12 : g12 w0`, `ht13`, `ht14`, `ht23`, `ht24`, `ht34`

**`diagBot … = diagTop …` (12)** — `hd{p}{w} : diagBot c p{p} w{w} = diagTop d p{p} w{w}` for p ∈ {p1,p2,p3}, w ∈ {w0,w1,w2,w3}

No algebraic hypothesis of any other shape appears.

## How the WLOG was discharged (your option (b), plus an honest rephasing)

No Schmidt normal form and no local unitaries. `SixQubit/Flip5.lean` runs the split off a scalar invariant:

- `dsc u = (u†u)² − 4·conj(det U)·det U`. `dsc_real` shows it equals `((1/9 − 4‖det U‖² : ℝ) : ℂ)`, and the case split is `by_cases Complex.normSq (dtu u) = 1/36`.
- The paper's "rephase `|1_L⟩` so `v = u`" is proved, not assumed: `anchor_scale` re-derives Cauchy–Schwarz tightness from the marginal equality and produces `∃ sc, (∀ l, sc * v l = u l) ∧ star sc * sc = 1`.
- `flip_reduce` takes the eight partial-trace entries `B U† + U A† = 0`, `U† B + A† U = 0` (rescaled by `sc`, with their conjugates obtained by `congrAr

#### angle

basisfree

#### report

(none)

#### angle

coords

#### report

RESULT — brute-coordinate flip-kernel dichotomy: **complete and machine-verified**, but the shared `SixQubit/Orbit5.lean` was overwritten by a concurrent session while I was verifying. Full detail below.

## Files

| path | lines | SHA-256 |
|---|---|---|
| `D:/UTD/Project_purdue/Lean_certification/SixQubit/Kernel5.lean` (new, live in repo) | 451 | `2220004e5631401175b4dbe1640168ce81da5e307ce83b5f6c9241eed184e0e1` |
| `D:/UTD/Project_purdue/Lean_certification/SixQubit/Orbit5_brutecoords.lean.txt` (my finished `Orbit5.lean`, parked as `.txt` so lake ignores it) | 2914 | `aa4ecb13ddd152c8fbc4b9e96dba53f3d95b8399110ca469d0bf4334f47b3854` |
| `D:/UTD/Project_purdue/Lean_certification/SixQubit/Orbit5.lean` (NOT mine — a peer session's `Flip5`-based version, written 06:59) | 2851 | `749789376939189cb2ef458246e06390c88d0a1a353771d8611eb38365abdcf2` |

`SixQubit/Trace5.lean`, `SixQubit/Triangle.lean`, `SixQubit.lean`, `SixQubit/Audit.lean` were **not** touched. Pristine pre-change `Orbit5.lean` saved at `C:/Users/richa/AppData/Local/Temp/claude/D--UTD-Project-purdue/e2435927-3651-49b0-acfb-31f3430ee257/scratchpad/Orbit5_original.lean`; generators `mk_kernel5.py`, `mk_orbit5.py`, `mk_orbit5_safe.py` are in the same scratchpad.

Adopting my version is one command: `cp SixQubit/Orbit5_brutecoords.lean.txt SixQubit/Orbit5.lean` (needs `SixQubit/Kernel5.lean`, already present). I did **not** do this myself — a peer's compiling work is on disk and clobbering it is not my call.

## Compile commands and outputs (all from `D:/UTD/Project_purdue/Lean_certification`)

- `lake env lean SixQubit/Kernel5.lean` → **empty**
- `lake build SixQubit.Kernel5` → `Built SixQubit.Kernel5`
- `lake env lean SixQubit/Orbit5.lean` (while my version was on disk) → **empty**
- `lake build SixQubit.Orbit5` → `Built SixQubit.Orbit5 (84s)`
- `lake env lean SixQubit/Audit.lean` → 229 axiom lines, **no warning/error/sorryAx**
- `lake build` → `Build completed successfully (7965 jobs)`, no warnings
- After the overwrite, fresh re-verification of my variant from its parked copy:
  `lake env lean <scratchpad>/Orbit5_brute.lean` → **empty**;
  `lake env lean <scratchpad>/Orbit5_brute_ax.lean` (same file + `#print axioms`) → axiom lines below.

## `SixQubit.Orbit5.no_go_of_moments`

Exists in my variant and closes to `False` (`: False := by …`, no `sorry`, no `native_decide`; the two `native_decide` grep hits in `Kernel5.lean`/`Orbit5*` are docstring prose saying it is not used).

Verbatim, from the fresh post-overwrite run:

```
'SixQubit.Orbit5.no_go_of_moments' depends on axioms: [propext, Classical.choice, Quot.sound]
'SixQubit.Orbit5.marginal_equality' depends on axioms: [propext, Classical.choice, Quot.sound]
'SixQubit.Orbit5.S0_eq_fiber' depends on axioms: [propext, Classical.choice, Quot.sound]
'SixQubit.Orbit5.S1_eq_fiber' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Hypotheses — 51 total, every one of the three permitted forms (mechanically re-parsed from the file text):

- **MomentSystem** (1): `hm` on the 40 `Complex.normSq (c y·)` / `Complex.normSq (d z·)`.
- **offSum … = 0** (38):
  - anchor rows (8, pre-existing): `ho1a ho1b ho2a ho2b ho3a ho3b ho4a ho4b` — `(f_i,w0)`, `(f_i,f_{i+1})`
  - two-flip rows (6, pre-existing): `ht12 ht13 ht14 ht23 ht24 ht34` — `(g_ij,w0)`
  - **new dressed one-flip rows (24)**: for `i = 1..4`, `kA_i (f_i,p1)`, `kB_i (hx_i,w0)`, `kC_i (hx_i,p1)`, `kD_i (f_i,p2)`, `kE_i (hy_i,w0)`, `kF_i (hy_i,p2)`, with `hx_i = f_i ⊕ p1`, `hy_i = f_i ⊕ p2` (i.e. `Z_A X_i`, `X_A X_i`, `Y_A X_i` for each zero-angle qubit `A`).
- **diagBot … = diagTop …** (12): `hd11 … hd34` on `p1,p2,p3 × w0..w3`.

Physical weight of every row checked by script: `offSum` rows max weight **2**, diagonal rows max weight **2**. Nothing else appears in the signature.

## What the new mathematics is

`SixQubit/Kernel5.lean` does the dichotomy in raw coordinates — no matrices, no Schmidt form, no normalisation. With `M = U†U`, `N = UU†`, `τ = Σ star(u k)

## audit

Scratch file removed; repo left exactly as found (hashes verified stable pre/post).

---

# VERDICT: Orbit 5 is genuinely closed. The certification holds.

I verified every claim myself. No smuggled hypotheses, no broken predecessors, no cheats.

## 1. Full build — nothing broken
`lake build` → exit 0, **`Build completed successfully (7965 jobs)`**, **0 errors, 0 warnings** (231-line log, all `info:` axiom lines). All 50 pre-existing orbits still audit to the three axioms. Nothing that used to compile is broken.

## 2. Individual compiles — all clean
`lake env lean` on `SixQubit/Orbit5.lean`, `Flip5.lean`, `Kernel5.lean`, `Trace5.lean`, `Triangle.lean` → **literal output empty, exit 0** in every case. The Orbit5 run was hash-guarded: SHA-256 `74978937…8365abdcf2` identical before and after, so the empty output is for the exact bytes on disk now. This is elaboration from source, not a stale-`.olean` replay.

## 3. The headline exists and concludes `False`
`SixQubit/Orbit5.lean:2421`, `theorem no_go_of_moments (c d : SS.BitString 6 -> ℂ) … : False := by`. Single occurrence, no shadowing declaration. Body ends `exact Flip5.core (uu c) (vv d) (aa1 c) … ` at line 2841.

## 4. Axioms — clean (my own scratch file, since deleted)
```
'SixQubit.Orbit5.no_go_of_moments' depends on axioms: [propext, Classical.choice, Quot.sound]
'SixQubit.Orbit5.S0_eq_fiber'      depends on axioms: [propext, Classical.choice, Quot.sound]
'SixQubit.Orbit5.S1_eq_fiber'      depends on axioms: [propext, Classical.choice, Quot.sound]
'SixQubit.Flip5.line_key'          depends on axioms: [propext, Classical.choice, Quot.sound]
'SixQubit.Triangle.contradiction'  depends on axioms: [propext, Classical.choice, Quot.sound]
'SixQubit.Trace5.bell_contradiction' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## 5. THE CRITICAL CHECK — every hypothesis classified (mechanically, from the signature text)
```
total hypotheses: 51
  (c) MomentSystem      :  1
  (a) offSum ... = 0    : 38   physical weights {1,2}, max 2
  (b) diagBot = diagTop : 12   physical weights {1,2}, max 2
  classified total      : 51
  UNCLASSIFIED          : NONE
  rows of weight > 2    : NONE
```
Nothing outside the three permitted forms. Weight computed as `|supp(e) ∪ supp(z)|` from the actual `bs …` bit patterns, not from names.

## 6. No `sorry`, no `native_decide`
Six grep hits across `Orbit5/Flip5/Kernel5/Trace5/Triangle` — every one inside a `/-! -/` docstring saying the tactic is *not* used (lines 50, 47, 53, 41, 36). One extra hit on `admit` is the English word "admits" in the theorem docstring. Zero tactic-position hits. No `axiom`, no `unsafe`, no `implemented_by`.

## 7. No predecessor weakened
`Triangle.lean` (read in full) is generic and matches its docstring exactly: `prod_eq_zero`, `contradiction`, `contradiction_of_normSq`, plus the mixed-pair family. No orbit-5-specific special case, no added hypothesis. `Trace5.bell_contradiction` still carries its full docstring-promised burden (norms `1/3`/`1/6`, anchor orthogonality, common frame, twelve off-diagonal orthogonalities). Both are imported by **Orbit20, Orbit49, Orbit50, Orbit51** as well, all of which still build — a weakening would have shown up. `SS/` infrastructure untouched (all Aug 18 14:37, predating the session).

## Beyond the brief — I attacked the definitions, not just the proof
The signature is only as good as what `offSum`/`diagBot`/`MomentSystem`/`S0`/`S1` *mean*. So:
- **Fibers are real.** I independently recomputed the weight-0 and weight-1 fibers of `av = (0,0,1,1,1,1)` over `ZMod 3` and confirmed `S0`/`S1` are *exactly* those sets — complete, not a convenient subset. (Lean also `decide`s this.) `av` matches the paper's orbit 5 (q=3, residues 0 and 1).
- **`offSum`/`diagBot`/`diagTop` are byte-identical in form to the certified Orbit49 versions.** No redefinition.
- **`MomentSystem` has exactly 63 fields**: 2 normalisations, 21 marginal equalities, 40 non-negativities. No smuggled field.
- **All 21 marginal rows are genuine weight-≤2 diagonal KL conditions.** I solved, over ℚ, for a degree-≤2 Z-observable reproducing each row's q-side and r-side indicator simultaneously. Every row succeeded: `m1..m6` = `(I − Z_i)/2`, `m12..m56` = `(I − Z_i − Z_j + Z_iZ_j)/4`. Both normalisations sum all 20 amplitudes to 1. Nothing in the polytope is fabricated.

## Two real defects — neither affects soundness, one should be fixed
1. **`SixQubit/Audit.lean` does not cover the orbit-5 headline.** It prints `Orbit5.S0_eq_fiber` and `Orbit5.S1_eq_fiber` (lines 308–309) but **not** `#print axioms SixQubit.Orbit5.no_go_of_moments`. Orbit 5 is the *only* orbit with this gap — I diffed the set of files containing the theorem against the set audited: `HAVE theorem but NOT audited: Orbit5`. The repo's own audit harness therefore does not yet witness the new result. One-line fix. Both agents reported "all orbits audit" without noticing their own was excluded.
2. **`SixQubit/Kernel5.lean` (451 lines) is orphaned.** Nothing imports it; it is the coords attempt's parallel route. It builds cleanly with correct axioms so it is harmless, but it is dead weight, as is the inert 206 KB `SixQubit/Orbit5_brutecoords.lean.txt`. Delete both if the Flip5 route is adopted.

## On the concurrency collision
The schmidt version won on disk: live `SixQubit/Orbit5.lean` = `749789376939189cb2ef458246e06390c88d0a1a353771d8611eb38365abdcf2`, exactly the hash **both** reports independently attribute to the Flip5-based file. That is the version I audited, and its hash never moved during my audit. The coords agent's honesty check-outs out: it did not clobber a peer's compiling work, and its parked `.txt` is genuinely inert under the lakefile glob (which globs `SixQubit` submodules only). The `basisfree` attempt left no report and no identifiable trace on disk. Every falsifiable claim in both surviving reports that I could test was accurate.

**Bottom line: the six-qubit no-go set is complete — 51 orbits, orbit 5 included, all on `[propext, Classical.choice, Quot.sound]`, all from moment-polytope and weight-≤2 Knill–Laflamme rows only.** Add the missing `#print axioms` line to `Audit.lean` so the repo can prove that to the next reader.
