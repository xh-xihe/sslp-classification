# Workflow record: orbit26-finish

orbit 26 transcription and assembly

Run id `w1opn0zf0`; 398707 subagent tokens, 62 tool calls.

---

## asm

## compiled

True

## complete

True

## file_path

C:\Users\richa\AppData\Local\Temp\claude\D--UTD-Project-purdue\e2435927-3651-49b0-acfb-31f3430ee257\scratchpad\Orbit26.lean

## sha256

936826b12e3865c25ec9e885606462fd84eb2d41426b38223c29e43a43278f4c

## source

-- Appended assembly layer, lines 1891-2831 of Orbit26.lean.  5 new theorems:
-- quad, ipw, sandwich, core, no_go_of_moments.  (hm and the repetitive
-- hypothesis blocks are elided with "..." below; nothing else is.)

/-! ================ HEADLINE (file lines 836-941) ================ -/

set_option maxHeartbeats 4000000 in
/-- **Headline.**  The Knill-Laflamme system for orbit 26 has no solution. -/
theorem no_go_of_moments (c d : SS.BitString 6 -> ℂ)
    (hm : MomentSystem (Complex.normSq (c y0)) ... (Complex.normSq (d z15)))
      -- 32 arguments: q0..q15 = normSq (c y_k), then r0..r15 = normSq (d z_j)
    (hO1_0  : offSum c d ef1  w0 = 0) (hO1_6  : offSum c d ef1  w6 = 0)
    (hO2_0  : offSum c d ef2  w0 = 0) (hO2_2  : offSum c d ef2  w2 = 0)
    (hO3_0  : offSum c d ef3  w0 = 0) (hO3_3  : offSum c d ef3  w3 = 0)
    (hO4_0  : offSum c d ef4  w0 = 0) (hO4_6  : offSum c d ef4  w6 = 0)
    (hO5_0  : offSum c d ef5  w0 = 0) (hO5_2  : offSum c d ef5  w2 = 0)
    (hO6_0  : offSum c d ef6  w0 = 0) (hO6_3  : offSum c d ef6  w3 = 0)
    (hO7_0  : offSum c d ef7  w0 = 0) (hO7_6  : offSum c d ef7  w6 = 0)
    (hO8_0  : offSum c d ef8  w0 = 0) (hO8_2  : offSum c d ef8  w2 = 0)
    (hO9_0  : offSum c d ef9  w0 = 0) (hO9_3  : offSum c d ef9  w3 = 0)
    (hO11_0 : offSum c d ef11 w0 = 0) (hO11_6 : offSum c d ef11 w6 = 0)
    (hO12_0 : offSum c d ef12 w0 = 0) (hO12_6 : offSum c d ef12 w6 = 0)
    (hO13_0 : offSum c d ef13 w0 = 0) (hO13_6 : offSum c d ef13 w6 = 0)
    (hD0_0 : diagBot c ef0 w0 = diagTop d ef0 w0) ...        -- ef0  x 8 dressings
    (hD10_0 : diagBot c ef10 w0 = diagTop d ef10 w0) ...     -- ef10 x 8 dressings
      -- the 8 dressings, in order: w0 w5 w4 w1 w6 w9 w8 w7
    : False := by
  exact core
    (c y0) (c y1) (c y2) (c y3) (c y4) (c y5) (c y6) (c y7)          -- a_i = (C_i)_1
    (c y8) (c y9) (c y10) (c y11) (c y12) (c y13) (c y14) (c y15)    -- b_i = (C_i)_2
    (d z7) (d z6) (d z5) (d z4) (d z3) (d z2) (d z1) (d z0)          -- p_i = (D_i)_1
    (d z15) (d z14) (d z13) (d z12) (d z11) (d z10) (d z9) (d z8)    -- q_i = (D_i)_2
    (by linarith only [mPQ0 hm]) ... (by linarith only [mT2b hm])    -- 15 moment facts
    (outer_g0h1_a0b0 c d hO7_0 hO7_6) ...                     -- 12 outer, passed VERBATIM
    (by rw [ip_eq, ip_eq]; linear_combination anch_i0_j6 c d hO3_0 hO3_3) ...  -- 12 anchor
    (mom_g0_a0b0 c d hD0_0 hD0_5 hD0_4 hD0_1 hD0_6 hD0_9 hD0_8 hD0_7) ...      -- 16 matrix

/-! ================ SKELETON OF `core` (file lines 45-835) ================ -/
-- core takes 32 complex block components a0..a7 b0..b7 p0..p7 q0..q7 and 55
-- hypotheses (15 real moment facts, 12 outer, 12 anchor scalars in `ip` form,
-- 16 matrix moment identities) and concludes False.  Everything below is a
-- `have` inside one tactic block.

theorem core (a0 ... q7 : ℂ) (hPQ0 ... M3_22) : False := by
  -- PRELUDE.  Work in the orthogonal frame (m, m^perp) of C^2 with m := D_6,
  -- m^perp := (-star q6, star p6); `ip m^perp v = m1*v2 - m2*v1`.
  have hQ6 : normSq p6 + normSq q6 = 1/8 := ...        -- Q_6 = P_6 = 1/8
  have hQ7 : normSq p7 + normSq q7 = 1/8 := ...
  have parC{i}/parD{i} : normSq (ip m X) + normSq (ip m^perp X) = 1/8 * ‖X‖²
      := by have h := lagrange p6 q6 ..; rw [ipw]; rw [hQ6] at h; linarith   -- 16, PARSEVAL
  have nnCM{i} nnCW{i} nnDM{i} nnDW{i} nnCN{i} nnDN{i} := Complex.normSq_nonneg ..  -- 48
  have SM{g}/SW{g}/SN{g} := sandwich ..                -- 12: the 4 group moment
      -- identities sandwiched with m = D_6, with m^perp, and with D_7
  have E6_{i} : ip a6 b6 p{i} q{i} = - star (ip p6 q6 a{i} b{i}) := ...  -- X6_i = -conj<m,C_i>
  have E7_{i} : ip a7 b7 p{i} q{i} = - star (ip p7 q7 a{i} b{i}) := ...  -- 12, from An{i}_{j}
  have hdm6 : normSq (ip p6 q6 p6 q6) = 1/64          -- <D_6,D_6> = 1/8
  have hdn7 : normSq (ip p7 q7 p7 q7) = 1/64
  have hdw6 : normSq (ip (-star q6) (star p6) p6 q6) = 0
  have nz6 nz7 dmz cmbz dmzero nnA{i} nnB{i} : zero-tests and casts
  -- STEP 1.  No anchor can annihilate two whole groups.  (m-sandwich for the two
  -- groups + sum over all four groups forces every remaining m-weight to vanish,
  -- but D_6 itself carries m-weight 1/64.)
  have no66_01, no66_02, no66_12 : ¬(Y6g ∧ Y6h)       -- Y6g := (X6_{2g}=0 ∧ X6_{2g+1}=0)
  have no77_01, no77_02, no77_12 : ¬(Y7g ∧ Y7h)
  -- STEP A of the brief: per_anchor x6, cross_anchor x3.
  have A6_01 A7_01 := per_anchor a0 b0 a1 b1 a2 b2 a3 b3 p0 q0 .. p{j} q{j} a{j} b{j}
                        O01_11 O01_12 O01_21 O01_22 An0_{j} An1_{j} An2_{j} An3_{j}
  have C_01 := cross_anchor .. p7 q7 a6 b6 (ip a7 b7 p0 q0) .. O01_.. An0_7 ..
  ...  -- likewise for the pairs (0,2) and (1,2)
  by_cases hdet : ip (-star q6) (star p6) p7 q7 = 0    -- det(D_6, D_7) = 0 ?
  -- ============ CASE B: D_6 ∥ D_7 ============
  · have hdw7 : normSq (ip (-star q6) (star p6) p7 q7) = 0 := by rw [hdet]; ..
    -- group 3 sandwiched with m^perp gives  sum_{i<=5} u_i = u_6 + u_7 <= 1/32,
    -- where u_i := normSq (ip m^perp C_i) and u_i = P_i/8 exactly when X6_i = 0.
    by_cases hY60 .. hY61 .. hY62 ..                   -- 8 leaves
    · exact no66_01 ⟨hY60, hY61⟩                       -- 4 leaves killed by STEP 1
    · -- |Z_6| = 0: axis_lemma on the three anchor-6 rows
      have HX := axis_lemma (ip a6 b6 p0 q0) .. hY60 hY61 hY62 A6_01 A6_02 A6_12
      rcases HX with ⟨o1,o3,o5⟩ | ⟨o0,o2,o4⟩           -- 3 blocks reach u_i = P_i,
      · linarith only [SW3, hdw6, hdw7, .., hT2b]      --   summing to 3/64 > 2/64
      · linarith only [.., hT2a]
    · -- |Z_6| = 1, say group g, others h < k:  BRANCH 2.  The bound is tight, so
      -- u_i = 0 for i in groups h,k;  C_h,C_k ∥ m,  D_h,D_k ⟂ m,  D_g ∥ m.
      have tc{2g} tc{2g+1} := nz6 ..                    -- X6 row g vanishes
      have hu{i} : normSq (ip m^perp C_i) = 0 := by linarith only [SW3, ..]   -- i in h,k
      have hUC67 : u_6 + u_7 = 1/32 := by linarith only [..]
      have hdm{i} : normSq (ip m D_i) = 0 := by linarith only [SW{h}, ..]     -- i in h,k
      have hDg : normSq (ip m D_{2g}) + normSq (ip m D_{2g+1}) = 1/32
      have ez{i} := dmz p{i} q{i} hdm{i}
      have Bh Bk : <C_h, m><m, D_{g+1}> + <C_{h+1}, m><m, D_g> = 0 := by
        linear_combination (p6*star p6)*O.._11 + (p6*star q6)*O.._12
          + (q6*star p6)*O.._21 + (q6*star q6)*O.._22 - .. * ez.. - .. * ez..
      have hDelta : X*W - Y*Z = 0                       -- 2x2 determinant, via hDg
      have hSig : X*W + Y*Z = 0                         -- from per_anchor A6_{h}{k}
      have hzz1 : X*W = 0;  have hzz2 : Y*Z = 0
      rcases mul_eq_zero.mp hzz1 .. mul_eq_zero.mp hzz2 ..   -- 4 leaves
      · linarith only [.., hT{h}]                       -- P_{2h} = P_{2h+1} = 0 vs 1/4
      · linarith only [.., hT2a, hT{g}, ..]             -- P_{2g} = 3/8 > 1/4
      · linarith only [.., hT2b, hT{g}, ..]             -- P_{2g+1} = 3/8 > 1/4
      · linarith only [.., hT{k}]                       -- P_{2k} = P_{2k+1} = 0 vs 1/4
  -- ============ CASE A: D_6, D_7 independent ============
  · have hdetc : star p6 * star q7 - star q6 * star p7 ≠ 0 := ...
    have kill : ∀ x y, star (ip p6 q6 x y) = 0 → star (ip p7 q7 x y) = 0 →
        normSq x + normSq y = 0 := ...                  -- Cramer against hdetc
    have no67_0 no67_1 no67_2 : ¬(Y6g ∧ Y7g)            -- else P_{2g}+P_{2g+1} = 0
    have closeA : (X6_1=0 ∧ X6_3=0 ∧ X6_5=0 ∧ X7_1=0 ∧ X7_3=0 ∧ X7_5=0)
                ∨ (X6_0=0 ∧ X6_2=0 ∧ X6_4=0 ∧ X7_0=0 ∧ X7_2=0 ∧ X7_4=0) → False := by
      rintro (⟨u1,u3,u5,v1,v3,v5⟩ | ⟨u0,u2,u4,v0,v2,v4⟩)
      · have z1 := kill a1 b1 .. ; .. ; linarith only [z1, z3, z5, hT2b]
      · have z0 := kill a0 b0 .. ; .. ; linarith only [z0, z2, z4, hT2a]
    by_cases hY60 .. hY61 .. hY62 ..
    · exact no66_.. ⟨.., ..⟩                            -- |Z_6| >= 2 impossible
    · -- |Z_6| = {g}: branch3_aligned, anchor 6 distinguished (3 permuted calls)
      have H := branch3_aligned (X6 slots g,h,k) (X7 slots g,h,k)
        hY6{g}.1 hY6{g}.2 hY6{h} hY6{k} (fun hh => no67_{g} ⟨hY6{g}, hh⟩)
        (by simp only [Jform] at A6_{h}{k} ⊢; linear_combination A6_{h}{k})
        (.. A7_{g}{h} ..) (.. A7_{g}{k} ..) (.. C_{g}{h} ..) (.. C_{g}{k} ..)
      rcases H with ⟨..⟩ | ⟨..⟩ <;> exact closeA (Or.inl/inr ⟨..⟩)
    · -- Z_6 = empty: split on the anchor-7 rows
      by_cases hY70 .. hY71 .. hY72 ..
      · exact no77_.. ⟨.., ..⟩
      · have H := branch3_aligned ..                    -- anchors swapped, 3 calls
      · have H := branch4_aligned (X6_0) .. (X7_5) hY60 hY61 hY62 hY70 hY71 hY72
          A6_01' A6_02' A6_12' A7_01' A7_02' A7_12' C_01' C_02' C_12'
        rcases H with ⟨..⟩ | ⟨..⟩ <;> exact closeA (Or.inl/inr ⟨..⟩)

## compile_output

`cd D:\UTD\Project_purdue\Lean_certification && lake env lean <scratchpad>\Orbit26.lean` -> EXIT 0, ZERO bytes of output (no errors, no warnings).  Whole-file wall time ~90 s.

Also compiled the identical file in place: `lake build` -> "Build completed successfully (7935 jobs)", "Built SixQubit.Orbit26 (91s)", no errors, no warnings.  `lake env lean SixQubit\Orbit26.lean` -> EXIT 0, zero output.

The assembly was built and compiled in four stages, each checked before the next: (1) helpers `quad`/`ipw`/`sandwich`; (2) the `core` prelude, elaborated against a `True` goal so every `have` was type-checked; (3) `core` concluding False; (4) the headline.  Three real defects were found and fixed en route: `parD6` needed `hQ6` as an extra `linarith` hint (its Parseval RHS is `(‖m‖²)²`, both factors rewritten at once); the `closeA` block was emitted at the wrong indent and fell outside its bullet; and the `n70` slot of `branch3_aligned` in case A needed `(fun hh => no67_g ⟨hY6g, hh⟩)` rather than a nonexistent `hY7g`.

`grep -n "sorry|native_decide|axiom "` over the file matches ONLY the prose line "`native_decide` is not used" in the module docstring.  No `sorry`, no `native_decide`, no `axiom` declaration.

INSTALLED.  `SixQubit\Orbit26.lean` now byte-identical to the scratchpad file (same sha256), and `SixQubit\Audit.lean` gained `import SixQubit.Orbit26` plus `#print axioms` for `S0_eq_fiber`, `S1_eq_fiber`, `quad`, `ipw`, `sandwich`, `core`, `no_go_of_moments`.  Backups of both pre-edit files are at /tmp/Orbit26.backup.lean and /tmp/Audit.backup.lean.  `SixQubit.lean` already imported `SixQubit.Orbit26`, so no edit was needed there.

File now 2831 lines, 586 theorems (581 transcription + 5 new).

## axioms

All five newly added theorems report exactly [propext, Classical.choice, Quot.sound]:

'SixQubit.Orbit26.quad'             depends on axioms: [propext, Classical.choice, Quot.sound]
'SixQubit.Orbit26.ipw'              depends on axioms: [propext, Classical.choice, Quot.sound]
'SixQubit.Orbit26.sandwich'         depends on axioms: [propext, Classical.choice, Quot.sound]
'SixQubit.Orbit26.core'             depends on axioms: [propext, Classical.choice, Quot.sound]
'SixQubit.Orbit26.no_go_of_moments' depends on axioms: [propext, Classical.choice, Quot.sound]

Checked twice: once in a standalone copy (scratchpad\Orbit26AsmAudit.lean) and once through the project build via SixQubit\Audit.lean lines 201-207.  No sorryAx, no Lean.ofReduceBool.  The 581 transcription theorems were already audited clean and are unchanged (the appendix only adds).

## unfinished

NOTHING IS UNFINISHED for the stated goal: `no_go_of_moments` concludes `False` from the MomentSystem plus 24 `offSum ... = 0` and 16 `diagBot ... = diagTop ...` hypotheses alone, with clean axioms.  The case tree is exhaustive by construction (nested `by_cases`, no residual goals).  Three caveats worth recording:

1. THE ROUTE DEVIATES FROM THE SUGGESTED BRANCH LIST, and closes gaps #2/#3/#4 of the survey by a different, cheaper mechanism instead of filling them.  Everything is done in the orthogonal frame (m, m^perp) of C^2 with m := D_6 (‖m‖² = Q_6 = P_6 = 1/8) and m^perp := (-star q6, star p6), which needs NO square roots and NO normalized vector.  Two new tools carry it: `sandwich` (a group moment identity contracted with an arbitrary vector, giving a real equation among `normSq (ip v ·)`), and Parseval `normSq (ip m X) + normSq (ip m^perp X) = (1/8)‖X‖²`, which is `Block26.lagrange` verbatim.  Consequences:
   * The `branch 2` six-step chain (survey gap #2) is replaced by: the m^perp-bound is tight, hence C_h,C_k ∥ m and D_h,D_k ⟂ m; contracting the two outer identities with m on BOTH indices leaves a 2x2 system whose determinant must vanish; `per_anchor` supplies the opposite-sign relation; the two together force two products of block components to vanish, and (T)/(T2a)/(T2b) close the four leaves.  Steps 1,3,4,5 of the old chain are never needed.
   * `branch4b`'s `hsand` and `branch1_full`'s S/A matrices (gaps #3, #4) are never assembled: the same content is carried by `linarith` on the real quantities u_i = normSq (ip m^perp C_i), t_i = 8·normSq (ip m C_i).  No perpendicular-unit-vector constructor was needed.

2. BLOCK26 LEMMAS ACTUALLY CALLED: `per_anchor` (x6), `cross_anchor` (x3), `branch3_aligned` (x6 = 3 with anchor 6 distinguished + 3 with the anchors swapped), `branch4_aligned` (x1), `axis_lemma` (x1, directly, for the |Z_6| = 0 leaf of case B), `lagrange` (x16), plus `ip`, `ip_eq`, `Jform`.  NOT called: `contract`, `axis_isotropic`, `mul_conj_self`, `mixed_core`, `branch4a`, `branch3_step`, `unit_pair_orthogonal`, `branch2_step6`, `cauchy_schwarz_unit`, `branch4b_core`, `branch4b`, `branch1`, `branch1_full`, `ip_conj`.  The first five of those are consumed inside the lemmas that ARE called; the rest are genuinely unused by this route and remain available in Block26.

3. THE HYPOTHESIS SURFACE IS UNCHANGED from the transcription brief — 24 offSum + 16 diagonal, all previously machine-checked admissible for the weight-<=2 KL system.  I did not re-verify their KL admissibility this session; that was done by the transcription pass.  Note the headline consumes exactly those 40 and nothing else, so any orbit-26 driver must supply them under the names hO{ef}_{w} / hD{ef}_{w} (ef and w numbered as in the file's ef0..ef13 / w0..w9 tables).

## trans

## compiled

True

## generator_path

C:\Users\richa\AppData\Local\Temp\claude\D--UTD-Project-purdue\e2435927-3651-49b0-acfb-31f3430ee257\scratchpad\gen26f.py

## file_path

C:\Users\richa\AppData\Local\Temp\claude\D--UTD-Project-purdue\e2435927-3651-49b0-acfb-31f3430ee257\scratchpad\Orbit26.lean

## lines

1890

## theorems

581

## compile_output

`cd D:\UTD\Project_purdue\Lean_certification && lake env lean <scratchpad>/Orbit26.lean` -> exit 0, ZERO bytes of output (no errors, no warnings). Wall time ~41s. Compiled after every one of the seven stages, not just at the end; the only two failures encountered en route were fixed in the generator: (a) the `linter.unusedSimpArgs` linter rejected `SixQubit.signMul_true` in expansions whose signs are all `false` -- the generator now emits only the signMul lemmas that actually fire; (b) `/-- ... -/` immediately followed by `set_option ... in` is a parse error ("unexpected token 'set_option'; expected 'lemma'") -- the stage-7 section header is now a `/-! ... -/` module doc.

AXIOM AUDIT (separate file Orbit26Audit.lean = Orbit26.lean + one `#print axioms` per theorem): all 581 theorems report exactly `depends on axioms: [propext, Classical.choice, Quot.sound]`. No sorryAx, no Lean.ofReduceBool. `grep sorry|native_decide` matches only the prose line "`native_decide` is not used" in the module docstring.

INDEPENDENT CHECKS RUN
* Every (flip, dressing) pair appearing in a hypothesis -- 40 distinct pairs, 24 offSum + 16 diagonal, exactly the counts the brief predicts -- was re-checked against `kl.dressings_full`: all admissible, max |supp(e) u supp(z)| = 2.
* All certificates recomputed inside the generator and asserted: `solve_dressing` verifies M*x == rhs exactly; each of the 16 diagonal certificates is re-expanded symbolically and asserted `sum coeff*cond(e,z) - target(a,b,g) == 0`; each of the 17 moment facts is asserted to have `reduce_mod_linear` remainder 0.
* Spot-checked emitted Lean statements against the brief verbatim: outer_g0h1_a0b0, outer_g1h2_a0b0, anch_i0_j6, anch_i5_j6, mom_g0_a0b0 (sign octet -1 +1 +1 +1 -1 +1 +1 +1), mom_g3_a0b1 -- all match, and the MomentSystem's 23 equations match section D line for line.

SEAM VERIFIED (out of band, C:\Users\richa\AppData\Local\Temp\claude\D--UTD-Project-purdue\e2435927-3651-49b0-acfb-31f3430ee257\scratchpad\Orbit26Seam.lean, compiles clean): the transcribed lemmas feed `SixQubit.Block26.per_anchor` directly. The four outer entries pass VERBATIM as E11/E12/E21/E22 -- `conj` vs `star` is transparent to the elaborator, no conversion needed. The four anchor scalars need one line each, because `ip a b p q + ip r s t u` associates as (A+B)+(C+D) while the transcription produces ((A+B)+C)+D:
    (by rw [ip_eq, ip_eq]; linear_combination R20)
`ip_eq` is shipped in the file (`SixQubit.Block26.ip a1 a2 b1 b2 = star a1 * b1 + star a2 * b2 := rfl`), so gap #6 of the survey costs one rewrite, not a `simp` hunt. NOTE: `simp only [Block26.ip]` does NOT work -- it leaves `starRingEnd` and `star` as distinct `ring` atoms; use `ip_eq`.

Nothing under D:\UTD\Project_purdue\Lean_certification\SixQubit was modified.

## covered

All seven requested stages are transcribed and kernel-checked. Breakdown of the 581 theorems (namespace SixQubit.Orbit26, imports Mathlib / SS.FullKL / SixQubit.Common / SixQubit.Block26):

1. POSITIONS AND FIBERS (2 thms, 34 defs). `bs`; y0..y15, z0..z15 exactly the S0/S1 of the brief's index map; `S0`, `S1`; `av : Fin 6 -> ZMod 4 := ![0,1,1,2,2,3]`; `S0_eq_fiber` and `S1_eq_fiber` by `decide` over all 64 strings.

2. MOMENT SYSTEM (1 structure + 17 thms). `MomentSystem` with all 23 equations of section D (n0 n1 m1..m6 c12..c56) plus nq0..nq15, nr0..nr15. Every moment fact from the brief, each stated as `<expr> = 0` and proved by `obtain` + a single `linear_combination` whose coefficients came from `reduce_mod_linear` (remainder 0 asserted at generation time):
   mPQ0..mPQ7  (P_i = Q_i, all eight blocks)
   mP6, mP7    (q6+q14-1/8 = 0, q7+q15-1/8 = 0)
   mSUM6       (sum_{i<6} P_i = 3/4)
   mT0..mT3    ((T): P_{2g}+P_{2g+1} = 1/4 for all FOUR groups incl. the anchor)
   mT2a, mT2b  ((T2): P_0+P_2+P_4 = 3/8 and P_1+P_3+P_5 = 3/8 -- both present, NOT omitted)
   Unused structure fields are `_`-prefixed in each `obtain`, which is what keeps the file warning-free.

3. WALSH SUMS AND THE DECIDABLE LAYER (3 defs + 2 thms + 464 `decide` thms). `offSum`, `diagBot`, `diagTop` in the Orbit25/29 shape; `sq : star z * z = normSq z`; `ip_eq` (the Block26 bridge, by `rfl`). ef0..ef13 and w0..w9 numbered exactly as the brief. Then, all `by decide`: 12 off incidence sets (`incO_*`), 2 diagonal bottom + 2 diagonal top incidence sets (`incB_*`, `incT_*`, both 16 elements), 96 off flip lemmas (`fo_*`), 32+32 diagonal flip lemmas (`fb_*`, `ft_*`), and 128+160 sign lemmas (`sy_*`, `sz_*`, globally de-duplicated over the whole file so the two diagonal flips share one sign table).

4. WALSH EXPANSIONS (56 thms). 24 off-diagonal (`exO_<ef>_<w>`, 8 terms each, the 12 masks x 2 dressings) and 32 diagonal (`exB_<ef>_<w>`, `exT_<ef>_<w>`, 16 terms each, flips 000000/100000 x the 8 dressings 000000,010000,001000,000001,100000,110000,101000,100001). Each proof: `unfold` / `rw [inc..]` / sum_insert chain / `rw [flips]` / `simp only [signs, signMul_*]` / `try ring`.

5. OUTER IDENTITIES (12 thms). `outer_g<g>h<h>_a<a>b<b>` for 0 <= g < h <= 2 and all four matrix entries, each taking the two `offSum ... = 0` hypotheses for its mask and concluding the 4-term sum = 0. Term order is exactly Block26.contract's E11/E12/E21/E22, i.e. (C_{2g},D_{2h+1}), (C_{2g+1},D_{2h}), (C_{2h},D_{2g+1}), (C_{2h+1},D_{2g}); a = c-component, b = d-component. Masks/certs reproduce the brief: (0,1)->010000 & 110000, (0,2)->001000 & 101000, (1,2)->000001 & 100001, always (1/2)w0 +/- (1/2)w6.

6. ANCHOR SCALARS (12 thms). `anch_i<i>_j<j>` for i in 0..5, j in {6,7}. Stated BLOCK-FIRST -- `ip C_i D_j + ip C_j D_i = 0`, i.e. the order Block26's per_anchor/cross_anchor consume for R2k -- resolving survey gap #7 in the direction the algebra wants. Six masks (000101, 000011, 001100, 001010, 010100, 010010), each carrying two of the twelve, separated by the sign of the second dressing exactly as the brief describes.

7. MATRIX MOMENT IDENTITY (16 thms). `mom_g<g>_a<a>b<b>` for all four groups (including the anchor group 3) and all four entries. Each takes the eight `diagBot c ef<e> w<k> = diagTop d ef<e> w<k>` hypotheses (e = 000000 for (0,0)/(1,1), 100000 for (0,1)/(1,0)) and concludes
   sum_{i in GROUPS[g]} (C_i C_i^H + D_i D_i^H)_{ab} = 1/2 * sum_{i=0..7} (C_i C_i^H)_{ab}
   via an 8-term `linear_combination` with coefficients +-1/8, under `set_option maxHeartbeats 2000000 in`. The sign octets match the brief's table exactly.

The hypothesis surface the headline theorem will need is therefore already fixed and validated: 24 offSum hypotheses + 16 diagBot/diagTop hypotheses, all 40 confirmed admissible weight-<=2 Paulis.

## missing

Only the transcription layer was in scope (the task listed stages 1-7); the ASSEMBLY is not written. Concretely, still missing:

1. NO HEADLINE `no_go_of_moments`. The file stops after stage 7. The assembly still has to: define the twelve anchor pairings X60..X65 / X70..X75, run Step A (6 x `per_anchor`, 3 x `cross_anchor`), do the six `by_cases` case tree on (Z_6, Z_7), and close branches 1/2/3/4. Everything it consumes is now present and typed, and the per_anchor seam is proven to work (see compile_output).

2. SURVEY GAP #2 IS UNTOUCHED (the largest). Block26 supplies only steps 2 and 6 of branch 2; steps 1, 3, 4, 5 (the span/rank-one-subtraction/determinant/independence chain) exist in neither Block26 nor this file.

3. SURVEY GAPS #3 AND #4 ARE UNTOUCHED. No perpendicular-unit-vector constructor (u := (-conj v2, conj v1)); no derivation of `branch1_full`'s S11..S22 / A11..A22, and none of `branch4b`'s `hsand`, nor case (i) of branch 4b.

4. NO REGISTRATION. Per instructions I did not touch D:\UTD\Project_purdue\Lean_certification\SixQubit, so the file lives in the scratchpad and is compiled standalone with `lake env lean`. To land it, someone must copy it to SixQubit\Orbit26.lean and add `import SixQubit.Orbit26` to SixQubit.lean and to SixQubit\Audit.lean (plus the `#print axioms` line there). Because it is not importable yet, the axiom audit and the Block26 seam test were run on CONCATENATED copies (Orbit26Audit.lean, Orbit26Seam.lean in the scratchpad), not via `import`.

5. NOT TRANSCRIBED, BY DESIGN. Only the relations the brief listed are present. Nothing generates the Q-side analogues of (T)/(T2), the full 14-mask x all-dressings KL system, or any relation for masks outside the 12 off + 2 diagonal flips used. `Block26.contract`, `axis_lemma`, `axis_isotropic`, `mul_conj_self`, `lagrange`, `branch4b_core`, `branch1`, `branch4a` are (correctly) never referenced -- they are internal to the lemmas the assembly will call.

6. ONE COSMETIC ITEM. The anchor scalars are stated block-first; if the assembly instead wants anchor-first it must flip the term order itself (both are `= 0`, so this is silent -- worth stating).

## survey

## interfaces

FILE: D:\UTD\Project_purdue\Lean_certification\SixQubit\Block26.lean  (415 lines, namespace `SixQubit.Block26`, `open scoped ComplexConjugate`, imports only `Mathlib`).  NOTE: Block26 is written with `conj` (= `starRingEnd ℂ`); the transcription layer (Orbit29/31 idiom) produces `star`. On ℂ these are definitionally equal — Orbit29's `sq` closes `z * star z = normSq z` with `Complex.normSq_eq_conj_mul_self; rfl`. Expect to need `show`/`rfl`/`simp only [RCLike.star_def]` at the seam, nothing deeper.

=== TWO DEFINITIONS (used in every statement below) ===

def ip (a1 a2 b1 b2 : ℂ) : ℂ := conj a1 * b1 + conj a2 * b2
def Jform (r1 r2 s1 s2 : ℂ) : ℂ := r1 * s2 + r2 * s1

@[simp] theorem ip_conj (a1 a2 b1 b2 : ℂ) : conj (ip a1 a2 b1 b2) = ip b1 b2 a1 a2

=== THE 19 THEOREMS, VERBATIM, IN FILE ORDER ===

(1)  theorem mul_conj_self (z : ℂ) : z * conj z = (Complex.normSq z : ℂ)

(2)  theorem axis_lemma (a0 b0 a1 b1 a2 b2 : ℂ)
         (h0 : ¬(a0 = 0 ∧ b0 = 0)) (h1 : ¬(a1 = 0 ∧ b1 = 0)) (h2 : ¬(a2 = 0 ∧ b2 = 0))
         (e01 : Jform a0 b0 a1 b1 = 0) (e02 : Jform a0 b0 a2 b2 = 0)
         (e12 : Jform a1 b1 a2 b2 = 0) :
         (b0 = 0 ∧ b1 = 0 ∧ b2 = 0) ∨ (a0 = 0 ∧ a1 = 0 ∧ a2 = 0)

(3)  theorem axis_isotropic (a0 b0 a1 b1 a2 b2 : ℂ)
         (h0 : ¬(a0 = 0 ∧ b0 = 0)) (h1 : ¬(a1 = 0 ∧ b1 = 0)) (h2 : ¬(a2 = 0 ∧ b2 = 0))
         (e01 : Jform a0 b0 a1 b1 = 0) (e02 : Jform a0 b0 a2 b2 = 0)
         (e12 : Jform a1 b1 a2 b2 = 0) :
         Jform a0 b0 a0 b0 = 0 ∧ Jform a1 b1 a1 b1 = 0 ∧ Jform a2 b2 a2 b2 = 0

(4)  theorem contract
         (c01 c02 c11 c12 c21 c22 c31 c32 : ℂ)
         (d01 d02 d11 d12 d21 d22 d31 d32 : ℂ) (p1 p2 q1 q2 : ℂ)
         (E11 : conj c01 * d31 + conj c11 * d21 + conj c21 * d11 + conj c31 * d01 = 0)
         (E12 : conj c01 * d32 + conj c11 * d22 + conj c21 * d12 + conj c31 * d02 = 0)
         (E21 : conj c02 * d31 + conj c12 * d21 + conj c22 * d11 + conj c32 * d01 = 0)
         (E22 : conj c02 * d32 + conj c12 * d22 + conj c22 * d12 + conj c32 * d02 = 0) :
         ip c01 c02 p1 p2 * ip q1 q2 d31 d32 + ip c11 c12 p1 p2 * ip q1 q2 d21 d22
           + ip c21 c22 p1 p2 * ip q1 q2 d11 d12 + ip c31 c32 p1 p2 * ip q1 q2 d01 d02 = 0

(5)  theorem cross_anchor
         (c01 c02 c11 c12 c21 c22 c31 c32 : ℂ)
         (d01 d02 d11 d12 d21 d22 d31 d32 : ℂ) (p1 p2 q1 q2 : ℂ)
         (X70 X71 X72 X73 : ℂ)
         (E11 : conj c01 * d31 + conj c11 * d21 + conj c21 * d11 + conj c31 * d01 = 0)
         (E12 : conj c01 * d32 + conj c11 * d22 + conj c21 * d12 + conj c31 * d02 = 0)
         (E21 : conj c02 * d31 + conj c12 * d21 + conj c22 * d11 + conj c32 * d01 = 0)
         (E22 : conj c02 * d32 + conj c12 * d22 + conj c22 * d12 + conj c32 * d02 = 0)
         (R20 : ip c01 c02 p1 p2 + X70 = 0) (R21 : ip c11 c12 p1 p2 + X71 = 0)
         (R22 : ip c21 c22 p1 p2 + X72 = 0) (R23 : ip c31 c32 p1 p2 + X73 = 0) :
         Jform X70 X71 (ip q1 q2 d21 d22) (ip q1 q2 d31 d32)
           + Jform X72 X73 (ip q1 q2 d01 d02) (ip q1 q2 d11 d12) = 0

(6)  theorem per_anchor
         (c01 c02 c11 c12 c21 c22 c31 c32 : ℂ)
         (d01 d02 d11 d12 d21 d22 d31 d32 : ℂ) (p1 p2 q1 q2 : ℂ)
         (E11 : conj c01 * d31 + conj c11 * d21 + conj c21 * d11 + conj c31 * d01 = 0)
         (E12 : conj c01 * d32 + conj c11 * d22 + conj c21 * d12 + conj c31 * d02 = 0)
         (E21 : conj c02 * d31 + conj c12 * d21 + conj c22 * d11 + conj c32 * d01 = 0)
         (E22 : conj c02 * d32 + conj c12 * d22 + conj c22 * d12 + conj c32 * d02 = 0)
         (R20 : ip c01 c02 p1 p2 + ip q1 q2 d01 d02 = 0)
         (R21 : ip c11 c12 p1 p2 + ip q1 q2 d11 d12 = 0)
         (R22 : ip c21 c22 p1 p2 + ip q1 q2 d21 d22 = 0)
         (R23 : ip c31 c32 p1 p2 + ip q1 q2 d31 d32 = 0) :
         Jform (ip q1 q2 d01 d02) (ip q1 q2 d11 d12) (ip q1 q2 d21 d22) (ip q1 q2 d31 d32) = 0

(7)  theorem mixed_core (a0 a1 a2 b0 b1 b2 : ℂ)
         (ha0 : a0 ≠ 0) (ha2 : a2 ≠ 0) (hb1 : b1 ≠ 0)
         (h01 : b0 * a1 + b1 * a0 = 0) (h02 : b0 * a2 + b2 * a0 = 0)
         (h12 : b1 * a2 + b2 * a1 = 0) : False

(8)  theorem branch4a (a0 a1 a2 b0 b1 b2 : ℂ)
         (ha0 : a0 ≠ 0) (ha2 : a2 ≠ 0) (hb1 : b1 ≠ 0)
         (h01 : Jform 0 b0 a1 0 + Jform 0 b1 a0 0 = 0)
         (h02 : Jform 0 b0 a2 0 + Jform 0 b2 a0 0 = 0)
         (h12 : Jform 0 b1 a2 0 + Jform 0 b2 a1 0 = 0) : False

(9)  theorem branch3_step (p s1 s2 : ℂ) (hp : p ≠ 0) (h : Jform p 0 s1 s2 = 0) : s2 = 0

(10) theorem unit_pair_orthogonal (n1 n2 m1 m2 : ℂ)
         (M11 : n1 * conj n1 + m1 * conj m1 = 1)
         (M12 : n1 * conj n2 + m1 * conj m2 = 0)
         (M21 : n2 * conj n1 + m2 * conj m1 = 0)
         (M22 : n2 * conj n2 + m2 * conj m2 = 1)
         (hm : ip m1 m2 m1 m2 = 1) (hn : ¬(n1 = 0 ∧ n2 = 0)) :
         ip n1 n2 m1 m2 = 0

(11) theorem branch2_step6 (g0 g1 c10 c11 c20 c21 : ℂ)
         (hg1 : g1 ≠ 0) (hc10 : c10 ≠ 0) (hc20 : c20 ≠ 0)
         (h1 : g0 * c11 + g1 * c10 = 0) (h2 : g0 * c21 + g1 * c20 = 0)
         (h3 : c10 * c21 + c11 * c20 = 0) : False

(12) theorem lagrange (u1 u2 v1 v2 : ℂ) :
         Complex.normSq (ip u1 u2 v1 v2) + Complex.normSq (u1 * v2 - u2 * v1)
           = (Complex.normSq u1 + Complex.normSq u2) * (Complex.normSq v1 + Complex.normSq v2)

(13) theorem cauchy_schwarz_unit (u1 u2 v1 v2 : ℂ)
         (hu : Complex.normSq u1 + Complex.normSq u2 = 1) :
         Complex.normSq (ip u1 u2 v1 v2) ≤ Complex.normSq v1 + Complex.normSq v2

(14) theorem branch4b_core (A e P6 P7 : ℝ) (he : 0 ≤ e)
         (hsand : 2 * A = e + 3 / 8 + A) (hcs : A ≤ P6 + P7)
         (hP6 : P6 = 1 / 8) (hP7 : P7 = 1 / 8) : False

(15) theorem branch4b (w1 w2 c61 c62 c71 c72 : ℂ) (e : ℝ) (he : 0 ≤ e)
         (hw : Complex.normSq w1 + Complex.normSq w2 = 1)
         (hP6 : Complex.normSq c61 + Complex.normSq c62 = 1 / 8)
         (hP7 : Complex.normSq c71 + Complex.normSq c72 = 1 / 8)
         (hsand : 2 * (Complex.normSq (ip w1 w2 c61 c62) + Complex.normSq (ip w1 w2 c71 c72))
           = e + 3 / 8 + (Complex.normSq (ip w1 w2 c61 c62) + Complex.normSq (ip w1 w2 c71 c72))) :
         False

(16) theorem branch1 (u1 u2 v1 v2 k1 k2 j1 j2 : ℂ)
         (hu : ip u1 u2 u1 u2 = 1) (huv : ip u1 u2 v1 v2 = 0)
         (M11 : k1 * conj k1 + j1 * conj j1 = 5 / 8 * (v1 * conj v1) - 1 / 8)
         (M12 : k1 * conj k2 + j1 * conj j2 = 5 / 8 * (v1 * conj v2))
         (M21 : k2 * conj k1 + j2 * conj j1 = 5 / 8 * (v2 * conj v1))
         (M22 : k2 * conj k2 + j2 * conj j2 = 5 / 8 * (v2 * conj v2) - 1 / 8) : False

(17) theorem branch4_aligned
         (X60 X61 X62 X63 X64 X65 X70 X71 X72 X73 X74 X75 : ℂ)
         (n60 : ¬(X60 = 0 ∧ X61 = 0)) (n61 : ¬(X62 = 0 ∧ X63 = 0))
         (n62 : ¬(X64 = 0 ∧ X65 = 0)) (n70 : ¬(X70 = 0 ∧ X71 = 0))
         (n71 : ¬(X72 = 0 ∧ X73 = 0)) (n72 : ¬(X74 = 0 ∧ X75 = 0))
         (A601 : Jform X60 X61 X62 X63 = 0) (A602 : Jform X60 X61 X64 X65 = 0)
         (A612 : Jform X62 X63 X64 X65 = 0)
         (A701 : Jform X70 X71 X72 X73 = 0) (A702 : Jform X70 X71 X74 X75 = 0)
         (A712 : Jform X72 X73 X74 X75 = 0)
         (C01 : Jform X70 X71 X62 X63 + Jform X72 X73 X60 X61 = 0)
         (C02 : Jform X70 X71 X64 X65 + Jform X74 X75 X60 X61 = 0)
         (C12 : Jform X72 X73 X64 X65 + Jform X74 X75 X62 X63 = 0) :
         (X61 = 0 ∧ X63 = 0 ∧ X65 = 0 ∧ X71 = 0 ∧ X73 = 0 ∧ X75 = 0)
           ∨ (X60 = 0 ∧ X62 = 0 ∧ X64 = 0 ∧ X70 = 0 ∧ X72 = 0 ∧ X74 = 0)

(18) theorem branch3_aligned
         (X60 X61 X62 X63 X64 X65 X70 X71 X72 X73 X74 X75 : ℂ)
         (hZ0 : X60 = 0) (hZ1 : X61 = 0)
         (n61 : ¬(X62 = 0 ∧ X63 = 0)) (n62 : ¬(X64 = 0 ∧ X65 = 0))
         (n70 : ¬(X70 = 0 ∧ X71 = 0))
         (A612 : Jform X62 X63 X64 X65 = 0)
         (A701 : Jform X70 X71 X72 X73 = 0) (A702 : Jform X70 X71 X74 X75 = 0)
         (C01 : Jform X70 X71 X62 X63 + Jform X72 X73 X60 X61 = 0)
         (C02 : Jform X70 X71 X64 X65 + Jform X74 X75 X60 X61 = 0) :
         (X61 = 0 ∧ X63 = 0 ∧ X65 = 0 ∧ X71 = 0 ∧ X73 = 0 ∧ X75 = 0)
           ∨ (X60 = 0 ∧ X62 = 0 ∧ X64 = 0 ∧ X70 = 0 ∧ X72 = 0 ∧ X74 = 0)

(19) theorem branch1_full (u1 u2 v1 v2 w1 w2 k1 k2 j1 j2 x1 x2 : ℂ)
         (hu : ip u1 u2 u1 u2 = 1) (huv : ip u1 u2 v1 v2 = 0)
         (S11 : k1 * conj k1 + j1 * conj j1 + 1 / 2 * (w1 * conj w1) + x1 * conj x1
           = 1 / 2 * (w1 * conj w1 + v1 * conj v1))
         (S12 : k1 * conj k2 + j1 * conj j2 + 1 / 2 * (w1 * conj w2) + x1 * conj x2
           = 1 / 2 * (w1 * conj w2 + v1 * conj v2))
         (S21 : k2 * conj k1 + j2 * conj j1 + 1 / 2 * (w2 * conj w1) + x2 * conj x1
           = 1 / 2 * (w2 * conj w1 + v2 * conj v1))
         (S22 : k2 * conj k2 + j2 * conj j2 + 1 / 2 * (w2 * conj w2) + x2 * conj x2
           = 1 / 2 * (w2 * conj w2 + v2 * conj v2))
         (A11 : x1 * conj x1 = 1 / 8 * (1 - v1 * conj v1))
         (A12 : x1 * conj x2 = -(1 / 8) * (v1 * conj v2))
         (A21 : x2 * conj x1 = -(1 / 8) * (v2 * conj v1))
         (A22 : x2 * conj x2 = 1 / 8 * (1 - v2 * conj v2)) : False

=== WHICH ONES THE ASSEMBLY CALLS, AND IN WHAT ORDER ===

Notation fixed once. `C_i` = bottom block i = (c y_{BOT i 0}, c y_{BOT i 1}); `D_i` = top block i = (d z_{TOP i 0}, d z_{TOP i 1}) (see index_map).  Define the twelve anchor pairings
    X6i := ip (c y_{BOT 6 0}) (c y_{BOT 6 1}) (d z_{TOP i 0}) (d z_{TOP i 1})   -- = ip C_6 D_i , i = 0..5
    X7i := ip C_7 D_i , i = 0..5
and the rows R_g^(j) := (X^j_{2g}, X^j_{2g+1}) for g = 0,1,2 (the three NON-anchor groups).
Set Z_j := { g ∈ {0,1,2} : R_g^(j) = 0 }.

STEP A (unconditional, always):
  A1. Per-anchor relations — 6 calls of `per_anchor`, one per (pair g<h, anchor j∈{6,7}):
        per_anchor (C_{2g})_1 (C_{2g})_2 (C_{2g+1})_1 (C_{2g+1})_2 (C_{2h})_1 (C_{2h})_2 (C_{2h+1})_1 (C_{2h+1})_2
                   (D_{2g})_1 (D_{2g})_2 (D_{2g+1})_1 (D_{2g+1})_2 (D_{2h})_1 (D_{2h})_2 (D_{2h+1})_1 (D_{2h+1})_2
                   (D_j)_1 (D_j)_2 (C_j)_1 (C_j)_2
                   E11 E12 E21 E22  R2(2g,j) R2(2g+1,j) R2(2h,j) R2(2h+1,j)
      p := D_j  (a-slot), q := C_j  (b-slot).  R2(i,j) is the anchor scalar
      `ip C_i D_j + ip C_j D_i = 0` — EXACTLY the shape of the anchor-scalar lemma
      (first two terms `ip C_i D_j`? no: the lemma statement is `ip c_k p + ip q d_k = 0`
      i.e. `ip C_k D_j + ip C_j D_k = 0`; the transcribed anchor lemma produces the
      terms in the order `ip C_j D_k` first, so pass it after a `linear_combination`
      or state the transcribed lemma in the order `ip C_k D_j + ip C_j D_k`).
      Yields A601 A602 A612 (j=6) and A701 A702 A712 (j=7).
  A2. Cross-anchor relations — 3 calls of `cross_anchor`, one per pair g<h, with
      p := D_7, q := C_6, and X70..X73 := X7_{2g}, X7_{2g+1}, X7_{2h}, X7_{2h+1};
      R20..R23 are the anchor scalars R2(2g,7), R2(2g+1,7), R2(2h,7), R2(2h+1,7).
      Yields C01, C02, C12.
  (E11..E22 in both A1 and A2 are the four transcribed outer-identity lemmas for the
   pair (g,h); the a-index is the Lean-1/Lean-2 component slot, see certificates.)
  `contract` is NEVER called directly — it is internal to (5) and (6).

STEP B (case tree on (Z_6, Z_7); exhaustive and mutually exclusive, verified by
x26_tree.py Part A over all 8×8 = 64 ordered pairs of subsets of {0,1,2}):
  B1 |Z_6| ≥ 2 or |Z_7| ≥ 2   → `branch1_full`   (uses no R1)
  B2 |Z_6|,|Z_7| ≤ 1 and Z_6 ∩ Z_7 ≠ ∅ (so Z_6 = Z_7 = {g})
                              → `unit_pair_orthogonal` (step 2), then `branch2_step6` (step 6)
  B3 |Z_6|,|Z_7| ≤ 1, disjoint, not both empty
                              → `branch3_aligned` (optionally `branch3_step` inline),
                                 then falls into the branch-4b closure
  B4 Z_6 = Z_7 = ∅            → `branch4_aligned`  (this call also disposes of the MIXED
                                 sub-case internally via `mixed_core`; `branch4a` is a
                                 stand-alone restatement and need not be called)
  B3/B4 both exit with the disjunction (all odd X = 0) ∨ (all even X = 0); each disjunct
  is closed by:
      case (i)  D_6, D_7 linearly independent  → C_1 = C_3 = C_5 = 0 → contradicts (T2b);
                (even branch: C_0 = C_2 = C_4 = 0 → contradicts (T2a))
      case (ii) D_6 ∥ D_7                      → `branch4b`  (which calls
                `cauchy_schwarz_unit` → `lagrange` and `branch4b_core` internally)

  So the DIRECT calls are exactly:
      per_anchor ×6, cross_anchor ×3, branch4_aligned ×1, branch3_aligned ×(B3 sub-cases),
      branch1_full ×1, unit_pair_orthogonal, branch2_step6, branch4b ×2 (odd/even),
      and possibly mixed_core / branch3_step / cauchy_schwarz_unit if the glue is inlined.
  NOT called by the assembly: `contract`, `axis_lemma`, `axis_isotropic`, `mul_conj_self`,
  `lagrange`, `branch4b_core`, `branch1`, `branch4a` — all of these are consumed inside
  the lemmas above.  `ip_conj` is a `@[simp]` lemma.

## certificates

All numbers below were produced and re-verified in Python this session
(scripts left at C:\Users\richa\AppData\Local\Temp\claude\D--UTD-Project-purdue\e2435927-3651-49b0-acfb-31f3430ee257\scratchpad\rep26.py, rep26b.py, rep26c.out, rep26d.out).
Every dressing certificate was checked by exact matrix multiplication (assert in
solve_dressing); every diagonal certificate was checked by expanding
sum coeff*(diagBot - diagTop) symbolically over free amplitude symbols and
subtracting the target — all 16 differences are identically 0.

CONVENTIONS
  offSum c d e z = ∑_{y ∈ S1, y⊕e ∈ S0} signMul (bdot z y) (star (c (y⊕e)) * d y)
     -> the term indexed by the incidence pair (i, j) is  star (c y_i) * d z_j.
  diagBot c e z = ∑_{x ∈ S0, x⊕e ∈ S0} signMul (bdot z x) (star (c (x⊕e)) * c x)
  diagTop d e z = ∑_{y ∈ S1, y⊕e ∈ S1} signMul (bdot z y) (star (d (y⊕e)) * d y)
  Bit strings are LITTLE-ENDIAN as printed: position 0 is the leftmost character
  and is the zero-angle qubit.  '010000' = Z on qubit index 1.

DRESSING NAMES (10 distinct, suggested `w` numbering by sorted order):
  w0 = 000000   w1 = 000001   w2 = 000010   w3 = 000100   w4 = 001000
  w5 = 010000   w6 = 100000   w7 = 100001   w8 = 101000   w9 = 110000
FLIP NAMES (14 distinct, suggested `ef` numbering by sorted order):
  ef0 = 000000  ef1 = 000001  ef2 = 000011  ef3 = 000101  ef4 = 001000
  ef5 = 001010  ef6 = 001100  ef7 = 010000  ef8 = 010010  ef9 = 010100
  ef10 = 100000 ef11 = 100001 ef12 = 101000 ef13 = 110000
Every (e,z) pair below is admissible for the full weight-≤2 KL system
(kl.dressings_full) — machine-checked, all True.

--------------------------------------------------------------------
A.  OUTER IDENTITY.  12 entries = 3 group pairs × 4 matrix entries.
    (a,b) are 0-based; Lean's component subscripts 1/2 correspond to a=0/a=1.
    E11=(0,0), E12=(0,1), E21=(1,0), E22=(1,1) in Block26.contract's naming.
    Each mask has 8 incidences; the 4 wanted ones are picked out by the
    two-dressing certificate; the complementary 4 are the "other" entry.
--------------------------------------------------------------------

PAIR (g,h) = (0,1)   [ blocks C_0,C_1 | C_2,C_3 ]
 E11 (a=0,b=0)  mask 010000  cert  (1/2)*offSum(010000,000000) + (1/2)*offSum(010000,100000)
     incidences: (0,4)(1,5)(2,6)(3,7)(8,12)(9,13)(10,14)(11,15)
     statement:  star (c y0) * d z4 + star (c y1) * d z5 + star (c y2) * d z6 + star (c y3) * d z7 = 0
 E12 (a=0,b=1)  mask 110000  cert  (1/2)*offSum(110000,000000) + (-1/2)*offSum(110000,100000)
     incidences: (8,4)(9,5)(10,6)(11,7)(0,12)(1,13)(2,14)(3,15)
     statement:  star (c y0) * d z12 + star (c y1) * d z13 + star (c y2) * d z14 + star (c y3) * d z15 = 0
 E21 (a=1,b=0)  mask 110000  cert  (1/2)*offSum(110000,000000) + (1/2)*offSum(110000,100000)
     statement:  star (c y8) * d z4 + star (c y9) * d z5 + star (c y10) * d z6 + star (c y11) * d z7 = 0
 E22 (a=1,b=1)  mask 010000  cert  (1/2)*offSum(010000,000000) + (-1/2)*offSum(010000,100000)
     statement:  star (c y8) * d z12 + star (c y9) * d z13 + star (c y10) * d z14 + star (c y11) * d z15 = 0

PAIR (g,h) = (0,2)   [ blocks C_0,C_1 | C_4,C_5 ]
 E11 (0,0)  mask 001000  cert (1/2)*offSum(001000,000000) + (1/2)*offSum(001000,100000)
     incidences: (0,2)(1,3)(4,6)(5,7)(8,10)(9,11)(12,14)(13,15)
     star (c y0) * d z2 + star (c y1) * d z3 + star (c y4) * d z6 + star (c y5) * d z7 = 0
 E12 (0,1)  mask 101000  cert (1/2)*offSum(101000,000000) + (-1/2)*offSum(101000,100000)
     incidences: (8,2)(9,3)(12,6)(13,7)(0,10)(1,11)(4,14)(5,15)
     star (c y0) * d z10 + star (c y1) * d z11 + star (c y4) * d z14 + star (c y5) * d z15 = 0
 E21 (1,0)  mask 101000  cert (1/2)*offSum(101000,000000) + (1/2)*offSum(101000,100000)
     star (c y8) * d z2 + star (c y9) * d z3 + star (c y12) * d z6 + star (c y13) * d z7 = 0
 E22 (1,1)  mask 001000  cert (1/2)*offSum(001000,000000) + (-1/2)*offSum(001000,100000)
     star (c y8) * d z10 + star (c y9) * d z11 + star (c y12) * d z14 + star (c y13) * d z15 = 0

PAIR (g,h) = (1,2)   [ blocks C_2,C_3 | C_4,C_5 ]
 E11 (0,0)  mask 000001  cert (1/2)*offSum(000001,000000) + (1/2)*offSum(000001,100000)
     incidences: (2,2)(3,3)(4,4)(5,5)(10,10)(11,11)(12,12)(13,13)
     star (c y2) * d z2 + star (c y3) * d z3 + star (c y4) * d z4 + star (c y5) * d z5 = 0
 E12 (0,1)  mask 100001  cert (1/2)*offSum(100001,000000) + (-1/2)*offSum(100001,100000)
     incidences: (10,2)(11,3)(12,4)(13,5)(2,10)(3,11)(4,12)(5,13)
     star (c y2) * d z10 + star (c y3) * d z11 + star (c y4) * d z12 + star (c y5) * d z13 = 0
 E21 (1,0)  mask 100001  cert (1/2)*offSum(100001,000000) + (1/2)*offSum(100001,100000)
     star (c y10) * d z2 + star (c y11) * d z3 + star (c y12) * d z4 + star (c y13) * d z5 = 0
 E22 (1,1)  mask 000001  cert (1/2)*offSum(000001,000000) + (-1/2)*offSum(000001,100000)
     star (c y10) * d z10 + star (c y11) * d z11 + star (c y12) * d z12 + star (c y13) * d z13 = 0

--------------------------------------------------------------------
B.  ANCHOR SCALARS.  12 relations  ip C_j D_i + ip C_i D_j = 0  (i ≤ 5, j ∈ {6,7}).
    6 masks, each carrying TWO of the twelve, separated by the SIGN of the
    second dressing.  Term order below = ip C_j D_i first, then ip C_i D_j.
--------------------------------------------------------------------
 (i=0, j=6)  mask 000101  cert (1/2)*offSum(000101,000000) + (-1/2)*offSum(000101,000100)
     incidences: (1,0)(0,1)(7,6)(6,7)(9,8)(8,9)(15,14)(14,15)
     star (c y6)*d z7 + star (c y14)*d z15 + star (c y0)*d z1 + star (c y8)*d z9 = 0
 (i=1, j=7)  mask 000101  cert (1/2)*offSum(000101,000000) + (1/2)*offSum(000101,000100)
     star (c y7)*d z6 + star (c y15)*d z14 + star (c y1)*d z0 + star (c y9)*d z8 = 0
 (i=0, j=7)  mask 000011  cert (1/2)*offSum(000011,000000) + (-1/2)*offSum(000011,000010)
     incidences: (0,0)(1,1)(6,6)(7,7)(8,8)(9,9)(14,14)(15,15)
     star (c y7)*d z7 + star (c y15)*d z15 + star (c y0)*d z0 + star (c y8)*d z8 = 0
 (i=1, j=6)  mask 000011  cert (1/2)*offSum(000011,000000) + (1/2)*offSum(000011,000010)
     star (c y6)*d z6 + star (c y14)*d z14 + star (c y1)*d z1 + star (c y9)*d z9 = 0
 (i=2, j=6)  mask 001100  cert (1/2)*offSum(001100,000000) + (-1/2)*offSum(001100,000100)
     incidences: (3,0)(2,1)(7,4)(6,5)(11,8)(10,9)(15,12)(14,13)
     star (c y6)*d z5 + star (c y14)*d z13 + star (c y2)*d z1 + star (c y10)*d z9 = 0
 (i=3, j=7)  mask 001100  cert (1/2)*offSum(001100,000000) + (1/2)*offSum(001100,000100)
     star (c y7)*d z4 + star (c y15)*d z12 + star (c y3)*d z0 + star (c y11)*d z8 = 0
 (i=2, j=7)  mask 001010  cert (1/2)*offSum(001010,000000) + (-1/2)*offSum(001010,000010)
     incidences: (2,0)(3,1)(6,4)(7,5)(10,8)(11,9)(14,12)(15,13)
     star (c y7)*d z5 + star (c y15)*d z13 + star (c y2)*d z0 + star (c y10)*d z8 = 0
 (i=3, j=6)  mask 001010  cert (1/2)*offSum(001010,000000) + (1/2)*offSum(001010,000010)
     star (c y6)*d z4 + star (c y14)*d z12 + star (c y3)*d z1 + star (c y11)*d z9 = 0
 (i=4, j=6)  mask 010100  cert (1/2)*offSum(010100,000000) + (-1/2)*offSum(010100,000100)
     incidences: (5,0)(4,1)(7,2)(6,3)(13,8)(12,9)(15,10)(14,11)
     star (c y6)*d z3 + star (c y14)*d z11 + star (c y4)*d z1 + star (c y12)*d z9 = 0
 (i=5, j=7)  mask 010100  cert (1/2)*offSum(010100,000000) + (1/2)*offSum(010100,000100)
     star (c y7)*d z2 + star (c y15)*d z10 + star (c y5)*d z0 + star (c y13)*d z8 = 0
 (i=4, j=7)  mask 010010  cert (1/2)*offSum(010010,000000) + (-1/2)*offSum(010010,000010)
     incidences: (4,0)(5,1)(6,2)(7,3)(12,8)(13,9)(14,10)(15,11)
     star (c y7)*d z3 + star (c y15)*d z11 + star (c y4)*d z0 + star (c y12)*d z8 = 0
 (i=5, j=6)  mask 010010  cert (1/2)*offSum(010010,000000) + (1/2)*offSum(010010,000010)
     star (c y6)*d z2 + star (c y14)*d z10 + star (c y5)*d z1 + star (c y13)*d z9 = 0

  Total offSum hypotheses needed by the headline theorem: 24
  (6 outer masks × {000000,100000}  +  3 anchor masks × {000000,000100}
   +  3 anchor masks × {000000,000010}).

--------------------------------------------------------------------
C.  MATRIX MOMENT IDENTITY.  o26.solve(a,b,g), all 16 in span, all verified.
    Target for (g,a,b):
      ∑_{i ∈ GROUPS[g]} ( c y_{BOT i a} * star (c y_{BOT i b})
                        + d z_{TOP i a} * star (d z_{TOP i b}) )
        = 1/2 * ∑_{i=0}^{7} c y_{BOT i a} * star (c y_{BOT i b})
    Certificate: target = ∑ coeff * ( diagBot c e z - diagTop d e z ).
    The flip is  e = 000000 for (a,b) ∈ {(0,0),(1,1)}  and  e = 100000 for {(0,1),(1,0)}.
    The eight dressings are always, in this order,
      z1..z8 = 000000, 010000, 001000, 000001, 100000, 110000, 101000, 100001
    and every coefficient has magnitude 1/8.  The sign octets (units of 1/8):

      g=0 (0,0) e=000000 : -1 +1 +1 +1  -1 +1 +1 +1
      g=0 (0,1) e=100000 : -1 +1 +1 +1  -1 +1 +1 +1
      g=0 (1,0) e=100000 : -1 +1 +1 +1  +1 -1 -1 -1
      g=0 (1,1) e=000000 : -1 +1 +1 +1  +1 -1 -1 -1
      g=1 (0,0) e=000000 : -1 +1 -1 -1  -1 +1 -1 -1
      g=1 (0,1) e=100000 : -1 +1 -1 -1  -1 +1 -1 -1
      g=1 (1,0) e=100000 : -1 +1 -1 -1  +1 -1 +1 +1
      g=1 (1,1) e=000000 : -1 +1 -1 -1  +1 -1 +1 +1
      g=2 (0,0) e=000000 : -1 -1 +1 -1  -1 -1 +1 -1
      g=2 (0,1) e=100000 : -1 -1 +1 -1  -1 -1 +1 -1
      g=2 (1,0) e=100000 : -1 -1 +1 -1  +1 +1 -1 +1
      g=2 (1,1) e=000000 : -1 -1 +1 -1  +1 +1 -1 +1
      g=3 (0,0) e=000000 : -1 -1 -1 +1  -1 -1 -1 +1
      g=3 (0,1) e=100000 : -1 -1 -1 +1  -1 -1 -1 +1
      g=3 (1,0) e=100000 : -1 -1 -1 +1  +1 +1 +1 -1
      g=3 (1,1) e=000000 : -1 -1 -1 +1  +1 +1 +1 -1

    Explicit targets (Lean form), for reference:
      g=0 (0,0): c y0*star(c y0) + d z7*star(d z7) + c y1*star(c y1) + d z6*star(d z6)
                 = 1/2*(c y0*star(c y0)+c y1*star(c y1)+...+c y7*star(c y7))
      g=0 (0,1): c y0*star(c y8) + d z7*star(d z15) + c y1*star(c y9) + d z6*star(d z14)
                 = 1/2*(c y0*star(c y8)+c y1*star(c y9)+...+c y7*star(c y15))
      g=0 (1,0): c y8*star(c y0) + d z15*star(d z7) + c y9*star(c y1) + d z14*star(d z6)
                 = 1/2*(c y8*star(c y0)+...+c y15*star(c y7))
      g=0 (1,1): c y8*star(c y8) + d z15*star(d z15) + c y9*star(c y9) + d z14*star(d z14)
                 = 1/2*(c y8*star(c y8)+...+c y15*star(c y15))
      g=1: blocks 2,3 -> (c y2,d z5) (c y3,d z4)   [ (1,*) row uses y10,y11,z13,z12 ]
      g=2: blocks 4,5 -> (c y4,d z3) (c y5,d z2)   [ (1,*) row uses y12,y13,z11,z10 ]
      g=3: blocks 6,7 -> (c y6,d z1) (c y7,d z0)   [ (1,*) row uses y14,y15,z9,z8  ]
      (the RHS ∑_{i=0}^{7} is the same for all four g at a fixed (a,b))

    Total diagonal hypotheses needed: 16, namely
      diagBot c ef z = diagTop d ef z   for ef ∈ {000000, 100000} and the 8 dressings above.
    Index facts (machine-checked, both True):
      S0[k] ⊕ 100000 = S0[(k+8) mod 16]   and   S1[j] ⊕ 100000 = S1[(j+8) mod 16].
    So for e=000000 the diag term at index k is  star (c y_k) * c y_k  with sign (-1)^{z·S0[k]};
    for e=100000 it is  star (c y_{(k+8) mod 16}) * c y_k  with the same sign; identically for d/S1.

--------------------------------------------------------------------
D.  THE MOMENT SYSTEM for orbit 26 (cert.build on this S0/S1), 23 equations.
    Field names in order: n0 n1 m1..m6 c12 c13 c14 c15 c16 c23 c24 c25 c26
                          c34 c35 c36 c45 c46 c56, then nq0..nq15, nr0..nr15.
--------------------------------------------------------------------
  n0  : q0+q1+q2+q3+q4+q5+q6+q7+q8+q9+q10+q11+q12+q13+q14+q15 = 1
  n1  : r0+r1+r2+r3+r4+r5+r6+r7+r8+r9+r10+r11+r12+r13+r14+r15 = 1
  m1  : q8+q9+q10+q11+q12+q13+q14+q15 = r8+r9+r10+r11+r12+r13+r14+r15
  m2  : q4+q5+q6+q7+q12+q13+q14+q15 = r4+r5+r6+r7+r12+r13+r14+r15
  m3  : q2+q3+q6+q7+q10+q11+q14+q15 = r2+r3+r6+r7+r10+r11+r14+r15
  m4  : q1+q3+q5+q7+q9+q11+q13+q15 = r1+r3+r5+r7+r9+r11+r13+r15
  m5  : q1+q3+q5+q6+q9+q11+q13+q14 = r0+r3+r5+r7+r8+r11+r13+r15
  m6  : q2+q3+q4+q5+q10+q11+q12+q13 = r0+r1+r6+r7+r8+r9+r14+r15
  c12 : q12+q13+q14+q15 = r12+r13+r14+r15
  c13 : q10+q11+q14+q15 = r10+r11+r14+r15
  c14 : q9+q11+q13+q15 = r9+r11+r13+r15
  c15 : q9+q11+q13+q14 = r8+r11+r13+r15
  c16 : q10+q11+q12+q13 = r8+r9+r14+r15
  c23 : q6+q7+q14+q15 = r6+r7+r14+r15
  c24 : q5+q7+q13+q15 = r5+r7+r13+r15
  c25 : q5+q6+q13+q14 = r5+r7+r13+r15
  c26 : q4+q5+q12+q13 = r6+r7+r14+r15
  c34 : q3+q7+q11+q15 = r3+r7+r11+r15
  c35 : q3+q6+q11+q14 = r3+r7+r11+r15
  c36 : q2+q3+q10+q11 = r6+r7+r14+r15
  c45 : q1+q3+q5+q9+q11+q13 = r3+r5+r7+r11+r13+r15
  c46 : q3+q5+q11+q13 = r1+r7+r9+r15
  c56 : q3+q5+q11+q13 = r0+r7+r8+r15
  (q_k := Complex.normSq (c y_k),  r_j := Complex.normSq (d z_j); plus nq*/nr* ≥ 0.)

  Block norms:
    P_0 = q0+q8   P_1 = q1+q9   P_2 = q2+q10  P_3 = q3+q11
    P_4 = q4+q12  P_5 = q5+q13  P_6 = q6+q14  P_7 = q7+q15
    Q_0 = r7+r15  Q_1 = r6+r14  Q_2 = r5+r13  Q_3 = r4+r12
    Q_4 = r3+r11  Q_5 = r2+r10  Q_6 = r1+r9   Q_7 = r0+r8

--------------------------------------------------------------------
E.  MOMENT FACTS.  Every one has reduce_mod_linear REMAINDER = 0.
    In particular, EXPLICITLY: the four (T) facts T0,T1,T2,T3 all have
    remainder 0, and BOTH halves of (T2) — T2a and T2b — have remainder 0.
    ALL REMAINDERS ZERO: True (single run, no exceptions).
    Each is stated as `<expr> = 0` and proved by the shown `linear_combination`
    after `obtain ⟨n0, n1, m1, ..., c56, nq0, ..., nr15⟩ := h`.
--------------------------------------------------------------------
 PQ0 : q0 + q8 - r15 - r7 = 0
   linear_combination (1)*n0 + (-1)*n1 + (-1)*m2 + (-1)*m3 + (-1)*m6 + (1)*c25 + (1)*c26 + (1)*c34 + (1)*c36 + (-1)*c45
 PQ1 : q1 + q9 - r14 - r6 = 0
   linear_combination (1)*c23 + (-1)*c25 + (-1)*c34 + (1)*c45
 PQ2 : q10 + q2 - r13 - r5 = 0
   linear_combination (1/2)*m6 + (-1/2)*c23 + (1)*c25 + (-1/2)*c26 + (1/2)*c34 + (-1/2)*c35 + (1/2)*c36 + (-1/2)*c46 + (-1/2)*c56
 PQ3 : q11 + q3 - r12 - r4 = 0
   linear_combination (1)*m2 + (-1/2)*m6 + (-1/2)*c23 + (-1)*c25 + (-1/2)*c26 + (-1/2)*c34 + (1/2)*c35 + (1/2)*c36 + (1/2)*c46 + (1/2)*c56
 PQ4 : q12 + q4 - r11 - r3 = 0
   linear_combination (1/2)*m6 + (-1/2)*c23 + (1/2)*c26 + (1/2)*c34 + (1/2)*c35 + (-1/2)*c36 + (-1/2)*c46 + (-1/2)*c56
 PQ5 : q13 + q5 - r10 - r2 = 0
   linear_combination (1)*m3 + (-1/2)*m6 + (-1/2)*c23 + (1/2)*c26 + (-1/2)*c34 + (-1/2)*c35 + (-1/2)*c36 + (1/2)*c46 + (1/2)*c56
 PQ6 : q14 + q6 - r1 - r9 = 0
   linear_combination (1/2)*m6 + (1/2)*c23 + (-1/2)*c26 + (-1/2)*c34 + (1/2)*c35 + (-1/2)*c36 + (1/2)*c46 + (-1/2)*c56
 PQ7 : q15 + q7 - r0 - r8 = 0
   linear_combination (1/2)*m6 + (1/2)*c23 + (-1/2)*c26 + (1/2)*c34 + (-1/2)*c35 + (-1/2)*c36 + (-1/2)*c46 + (1/2)*c56
 P6  : q14 + q6 - 1/8 = 0
   linear_combination (1/8)*n1 + (1/8)*m2 + (1/8)*m3 + (1/8)*m6 + (1/4)*c23 + (-1/4)*c26 + (-1/2)*c34 + (1/2)*c35 + (-1/4)*c36
 P7  : q15 + q7 - 1/8 = 0
   linear_combination (1/8)*n1 + (1/8)*m2 + (1/8)*m3 + (1/8)*m6 + (1/4)*c23 + (-1/4)*c26 + (1/2)*c34 + (-1/2)*c35 + (-1/4)*c36
 SUM6 : q0+q1+q2+q3+q4+q5+q8+q9+q10+q11+q12+q13 - 3/4 = 0
   linear_combination (1)*n0 + (-1/4)*n1 + (-1/4)*m2 + (-1/4)*m3 + (-1/4)*m6 + (-1/2)*c23 + (1/2)*c26 + (1/2)*c36
 T0 (P_0+P_1 = 1/4) : q0 + q1 + q8 + q9 - 1/4 = 0        REMAINDER 0
   linear_combination (1)*n0 + (-3/4)*n1 + (-3/4)*m2 + (-3/4)*m3 + (-3/4)*m6 + (1/2)*c23 + (1/2)*c26 + (1/2)*c36
 T1 (P_2+P_3 = 1/4) : q2 + q3 + q10 + q11 - 1/4 = 0      REMAINDER 0
   linear_combination (1/4)*n1 + (1/4)*m2 + (1/4)*m3 + (1/4)*m6 + (-1/2)*c23 + (-1/2)*c26 + (1/2)*c36
 T2 (P_4+P_5 = 1/4) : q4 + q5 + q12 + q13 - 1/4 = 0      REMAINDER 0
   linear_combination (1/4)*n1 + (1/4)*m2 + (1/4)*m3 + (1/4)*m6 + (-1/2)*c23 + (1/2)*c26 + (-1/2)*c36
 T3 (P_6+P_7 = 1/4, ANCHOR) : q6 + q7 + q14 + q15 - 1/4 = 0   REMAINDER 0
   linear_combination (1/4)*n1 + (1/4)*m2 + (1/4)*m3 + (1/4)*m6 + (1/2)*c23 + (-1/2)*c26 + (-1/2)*c36
 T2a (P_0+P_2+P_4 = 3/8, LOAD-BEARING) : q0 + q2 + q4 + q8 + q10 + q12 - 3/8 = 0   REMAINDER 0
   linear_combination (1)*n0 + (-5/8)*n1 + (-5/8)*m2 + (-5/8)*m3 + (-1/8)*m6 + (-3/4)*c23 + (1)*c25 + (3/4)*c26 + (1)*c34 + (3/4)*c36 + (-1)*c45 + (-1/2)*c46 + (-1/2)*c56
 T2b (P_1+P_3+P_5 = 3/8, LOAD-BEARING) : q1 + q3 + q5 + q9 + q11 + q13 - 3/8 = 0   REMAINDER 0
   linear_combination (3/8)*n1 + (3/8)*m2 + (3/8)*m3 + (-1/8)*m6 + (1/4)*c23 + (-1)*c25 + (-1/4)*c26 + (-1)*c34 + (-1/4)*c36 + (1)*c45 + (1/2)*c46 + (1/2)*c56

  Sign convention reminder: a hypothesis `h : X = Y` contributes `coeff * (X - Y)`,
  and the printed coefficients are exactly the ones for the equations as written
  in section D (q-side minus r-side, or minus the constant for n0/n1).

## index_map

ORBIT 26.  a = (0,1,1,2,2,3) mod q=4, delta = 1, fibers 16 + 16.
Lean:  def av : Fin 6 -> ZMod 4 := ![0, 1, 1, 2, 2, 3]
       S0 = filter (SS.weight av x = 0) univ   (theorem S0_eq_fiber, by decide)
       S1 = filter (SS.weight av x = 1) univ   (theorem S1_eq_fiber, by decide)

S0 (bottom, name y_k, `bs` bit order = string order left-to-right):
  y0  000000    y1  000110    y2  001001    y3  001111
  y4  010001    y5  010111    y6  011010    y7  011100
  y8  100000    y9  100110    y10 101001    y11 101111
  y12 110001    y13 110111    y14 111010    y15 111100

S1 (top, name z_j):
  z0  000011    z1  000101    z2  001000    z3  001110
  z4  010000    z5  010110    z6  011001    z7  011111
  z8  100011    z9  100101    z10 101000    z11 101110
  z12 110000    z13 110110    z14 111001    z15 111111

Both fibers are ordered so that index k and index k+8 differ ONLY in the
zero-angle qubit (position 0):  y_k ⊕ 100000 = y_{(k+8) mod 16} and
z_j ⊕ 100000 = z_{(j+8) mod 16}.  (Machine-checked, both True.)

THE EIGHT BLOCKS.  Block i carries the bottom tail T0[i] (the last five bits of
the bottom strings) and the top pair on the COMPLEMENTED tail — NOT the sorted
top tail.  blocks.py's `structure` returns TOP indexed by sorted top tails; that
indexing is WRONG for block matching and makes the matrix moment identity appear
to fail.  The correct table (this is o26.TOP):

  block | bottom tail | comp tail | C_i = (bottom a=0, a=1) | D_i = (top b=0, b=1) | group
  ------+-------------+-----------+-------------------------+----------------------+------
    0   |   00000     |   11111   | (y0  = 000000, y8  = 100000) | (z7  = 011111, z15 = 111111) |  0
    1   |   00110     |   11001   | (y1  = 000110, y9  = 100110) | (z6  = 011001, z14 = 111001) |  0
    2   |   01001     |   10110   | (y2  = 001001, y10 = 101001) | (z5  = 010110, z13 = 110110) |  1
    3   |   01111     |   10000   | (y3  = 001111, y11 = 101111) | (z4  = 010000, z12 = 110000) |  1
    4   |   10001     |   01110   | (y4  = 010001, y12 = 110001) | (z3  = 001110, z11 = 101110) |  2
    5   |   10111     |   01000   | (y5  = 010111, y13 = 110111) | (z2  = 001000, z10 = 101000) |  2
    6   |   11010     |   00101   | (y6  = 011010, y14 = 111010) | (z1  = 000101, z9  = 100101) |  3 ANCHOR
    7   |   11100     |   00011   | (y7  = 011100, y15 = 111100) | (z0  = 000011, z8  = 100011) |  3 ANCHOR

  As index lists:
    BOT = [(0,8),(1,9),(2,10),(3,11),(4,12),(5,13),(6,14),(7,15)]
    TOP = [(7,15),(6,14),(5,13),(4,12),(3,11),(2,10),(1,9),(0,8)]
      i.e.  TOP[i] = (7-i, 15-i).
  Component convention: index 0 of a block is the string with first bit 0
  (Lean subscript 1 in Block26); index 1 is the string with first bit 1
  (Lean subscript 2).

GROUPS (paired by the virtual bit z of the paper's tail parametrisation
t = (x, y, z, z⊕xy, x⊕y); groups are indexed by (x,y) in sorted order):
    GROUPS = [ [0,1], [2,3], [4,5], [6,7] ]
    group 0 = (x,y)=(0,0) = blocks {0,1}
    group 1 = (x,y)=(0,1) = blocks {2,3}
    group 2 = (x,y)=(1,0) = blocks {4,5}
    group 3 = (x,y)=(1,1) = blocks {6,7}   <-- THE ANCHOR GROUP
  The three "cycle" groups referred to as g,h ∈ {0,1,2} in Block26 are groups
  0,1,2, i.e. blocks 0..5;  the anchors are blocks 6 and 7.
  Tail -> (x,y,z) map:
    00000 -> (0,0,0)   00110 -> (0,0,1)   01001 -> (0,1,0)   01111 -> (0,1,1)
    10001 -> (1,0,0)   10111 -> (1,0,1)   11010 -> (1,1,0)   11100 -> (1,1,1)

BLOCK NORMS in the moment variables (q_k = normSq (c y_k), r_j = normSq (d z_j)):
    P_i = q_{BOT i 0} + q_{BOT i 1}      Q_i = r_{TOP i 0} + r_{TOP i 1}
    P_0 = q0+q8   P_1 = q1+q9   P_2 = q2+q10  P_3 = q3+q11
    P_4 = q4+q12  P_5 = q5+q13  P_6 = q6+q14  P_7 = q7+q15
    Q_0 = r7+r15  Q_1 = r6+r14  Q_2 = r5+r13  Q_3 = r4+r12
    Q_4 = r3+r11  Q_5 = r2+r10  Q_6 = r1+r9   Q_7 = r0+r8

ANCHOR PAIRINGS used by Block26 (define these as local `have`s / abbreviations):
    X6i := ip (c y6) (c y14) (d z_{TOP i 0}) (d z_{TOP i 1})     -- ip C_6 D_i , i = 0..5
    X7i := ip (c y7) (c y15) (d z_{TOP i 0}) (d z_{TOP i 1})     -- ip C_7 D_i , i = 0..5
  Concretely:
    X60 = ip (c y6)(c y14)(d z7)(d z15)      X70 = ip (c y7)(c y15)(d z7)(d z15)
    X61 = ip (c y6)(c y14)(d z6)(d z14)      X71 = ip (c y7)(c y15)(d z6)(d z14)
    X62 = ip (c y6)(c y14)(d z5)(d z13)      X72 = ip (c y7)(c y15)(d z5)(d z13)
    X63 = ip (c y6)(c y14)(d z4)(d z12)      X73 = ip (c y7)(c y15)(d z4)(d z12)
    X64 = ip (c y6)(c y14)(d z3)(d z11)      X74 = ip (c y7)(c y15)(d z3)(d z11)
    X65 = ip (c y6)(c y14)(d z2)(d z10)      X75 = ip (c y7)(c y15)(d z2)(d z10)
  Rows: R_g^(6) = (X6_{2g}, X6_{2g+1}),  R_g^(7) = (X7_{2g}, X7_{2g+1}), g = 0,1,2.
  These are exactly Block26's X60..X65 / X70..X75 in branch4_aligned / branch3_aligned.

## gaps

Things NOT available that the assembly still has to build.  Ordered by size.

1. THERE IS NO Orbit26.lean.  D:\UTD\Project_purdue\Lean_certification\SixQubit\ contains
   Block26.lean but no Orbit26.lean.  Two registration edits are required:
     - add `import SixQubit.Orbit26` to D:\UTD\Project_purdue\Lean_certification\SixQubit.lean
     - add `import SixQubit.Orbit26` and a line
       `#print axioms SixQubit.Orbit26.no_go_of_moments`
       to D:\UTD\Project_purdue\Lean_certification\SixQubit\Audit.lean
       (the file already carries `#print axioms SixQubit.Orbit29.no_go_of_moments` at line 120).

2. BLOCK26 HAS NO GLUE FOR BRANCH 2.  x26_all.out documents six steps; Block26 supplies
   only step 2 (`unit_pair_orthogonal`) and step 6 (`branch2_step6`).  Missing, and
   therefore to be proved inline in Orbit26.lean or added to Block26.lean:
     step 1: from `ip C_6 D_i = 0` and `ip C_7 D_i = 0` for both blocks i of group g,
             plus (T) forcing Q_{2g}+Q_{2g+1} ≠ 0, conclude C_6 ∥ C_7 (direction n),
             D_6 ∥ D_7 (direction m), and C_{2g},C_{2g+1} ∈ span(w), D_{2g},D_{2g+1} ∈ span(v).
     step 3: rank-one subtraction ρ − (1/4)n nᴴ − (1/4)n nᴴ = (1/2) m mᴴ, hence every
             C_i in the other two groups lies in span(m), every D_i in span(n).
     step 4: the 2×2 determinant argument giving d_i = −ν conj(c_i) with |ν| = 1.
     step 5: linear independence of conj(n)nᵀ and conj(m)mᵀ, splitting the R1 entry
             into two brackets that vanish separately.
   Only after these does `branch2_step6` apply.  This is the largest single gap.

3. BLOCK26 HAS NO "PERPENDICULAR UNIT VECTOR" CONSTRUCTOR.  `branch1_full` needs
   (u1,u2) with `ip u u = 1` and `ip u v = 0`; `branch4b` needs a unit w with w ⟂ m;
   branch 2 needs v = nᐧ⊥ and w = mᐧ⊥.  The construction is one line —
   u := (-conj v2, conj v1) gives `ip u v = 0` by `ring` and `ip u u = normSq v1 + normSq v2` —
   but it must be written, and it needs v to be a UNIT vector, which itself has to be
   derived from the moment facts (P_6 = 1/8 gives ‖C_6‖² = 1/8, not 1).

4. BLOCK26 HAS NO GLUE FOR BRANCH 1 or BRANCH 4b.
   - branch1_full consumes S11..S22 and A11..A22 already assembled.  Deriving them
     (C_i ∈ span(w) from the orthogonality; (T) ⟹ C_g C_gᴴ = (1/4) w wᴴ; the anchor
     block xxᴴ = (1/8)(I − v vᴴ) from P_j = 1/8 plus x ⟂ v) is not in Block26.
   - branch4b consumes `hsand : 2A = e + 3/8 + A` and `he : 0 ≤ e`.  Producing hsand
     from the aligned conclusion + the group-3 matrix moment identity + (T2) is not in
     Block26, and neither is case (i) of branch 4b (D_6, D_7 independent ⟹
     C_1 = C_3 = C_5 = 0 ⟹ P_1+P_3+P_5 = 0 against T2b = 3/8).

5. THE CASE TREE IS NOT A LEAN LEMMA.  Exhaustiveness of {branch 1, 2, 3, 4} over the
   64 ordered pairs (Z_6, Z_7) ⊆ {0,1,2}² was verified only in Python (x26_tree.py Part A,
   "pairs hit by a number of branches other than exactly one: []").  In Lean it has to
   be six nested `by_cases` on the propositions `X6_{2g} = 0 ∧ X6_{2g+1} = 0` and
   `X7_{2g} = 0 ∧ X7_{2g+1} = 0`, g = 0,1,2.  Note branch4_aligned and branch3_aligned
   both take the NEGATIONS `¬(X = 0 ∧ Y = 0)` directly, so the split is by `by_cases`
   on those conjunctions.

6. `conj` vs `star`.  Block26 is stated with `conj` (= `starRingEnd ℂ`, via
   `open scoped ComplexConjugate`); the Orbit29/31 transcription idiom produces `star`.
   They are definitionally equal on ℂ (Orbit29's `sq` closes the gap with a bare `rfl`),
   but every hand-off from a transcribed offSum lemma into a Block26 hypothesis will
   need a `show`, `rfl`, or `simp only [RCLike.star_def]`.  Similarly `Block26.ip`
   must be `simp only [ip]`-unfolded before `linear_combination`.

7. TERM ORDER MISMATCH ON THE ANCHOR SCALARS.  Block26's `per_anchor`/`cross_anchor`
   want R2k in the order `ip C_k D_j + ip C_j D_k = 0` (c-block first).  The natural
   transcription from the Walsh certificate produces `ip C_j D_k + ip C_k D_j = 0`
   (anchor block first — that is the order I listed in `certificates`).  State the
   transcribed lemma in whichever order you prefer, but be consistent: getting it
   backwards is silent, because both are `= 0`, but `linear_combination` will then need
   a sign flip in the surrounding glue.

8. gen26c.py IN THE SCRATCHPAD IS OBSOLETE — DO NOT REUSE.  It is built on the
   per-edge matrix relations `D_i C_kᴴ + D_k C_iᴴ = 0` that Block26's own header
   says do not exist ("the weight-one masks carry eight incidences with rank only
   four and admit no two-term relation"), and its `sca_combo` uses only the trivial
   dressing, which yields the SUM of two anchor scalars rather than either one.
   The correct certificates are the ones in this report (two dressings per mask,
   separating the two anchor scalars by the sign of the second dressing).

9. NOT A GAP, but worth stating: nothing here needs `native_decide`.  The decidable
   content is 14 flip masks (12 with 8 off-incidences each, plus the two diagonal flips
   000000 / 100000 with 16 self-incidences each), which is the same scale as Orbit29
   (12 masks) and Orbit31 (both off and diagonal families).  Expect
   `set_option maxHeartbeats 2000000 in` on the headline theorem and possibly on the
   16 diagonal-certificate lemmas (each is an 8-term `linear_combination` over
   32-term diag expansions).

10. HEADLINE SIGNATURE.  `no_go_of_moments (c d : SS.BitString 6 -> ℂ)` will take:
    the `MomentSystem` applied to the 32 `Complex.normSq` values (section D of the
    certificates), 24 `offSum c d ef w = 0` hypotheses, and 16
    `diagBot c ef w = diagTop d ef w` hypotheses, concluding `False`.
    That is 41 hypotheses; Orbit25 already uses the mixed offSum + diagBot/diagTop
    shape (see SixQubit/Orbit25.lean lines 1713-1714), so the pattern exists.
