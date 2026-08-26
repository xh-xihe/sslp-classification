# Workflow record: orbit31-assembly

orbit 31 branch assembly and audit

Run id `wzr52ldrg`; 551161 subagent tokens, 118 tool calls.

---

## audit

## compiled

True

## complete

True

## file_path

C:\Users\richa\AppData\Local\Temp\claude\D--UTD-Project-purdue\e2435927-3651-49b0-acfb-31f3430ee257\scratchpad\AUDIT31.lean

## source

I did NOT take the previous agent's merged file on faith.  I re-spliced from the pristine
project source myself, with this exact command (run from D:\UTD\Project_purdue\Lean_certification):

    SP="C:/Users/richa/AppData/Local/Temp/claude/D--UTD-Project-purdue/e2435927-3651-49b0-acfb-31f3430ee257/scratchpad"
    head -n 1774 SixQubit/Orbit31.lean  >  "$SP/AUDIT31.lean"
    cat  "$SP/APPEND.lean"              >> "$SP/AUDIT31.lean"
    tail -n +1775 SixQubit/Orbit31.lean >> "$SP/AUDIT31.lean"

(line 1775 of the pristine file is the `end` that closes the `noncomputable section`;
1777 is `end SixQubit.Orbit31`.  The appended block therefore lands inside both.)

THE EXACT BYTES I VALIDATED, with checksums so the caller can confirm nothing drifted:

  block to append   C:\Users\richa\AppData\Local\Temp\claude\D--UTD-Project-purdue\e2435927-3651-49b0-acfb-31f3430ee257\scratchpad\APPEND.lean
                    120,719 bytes / 1876 lines
                    sha256 ad482a36b074434720164f5d0e7e304a84366c8d6b8d6639a7251e141cb81941

  merged file I compiled
                    C:\Users\richa\AppData\Local\Temp\claude\D--UTD-Project-purdue\e2435927-3651-49b0-acfb-31f3430ee257\scratchpad\AUDIT31.lean
                    255,207 bytes / 3653 lines
                    sha256 617ed804de703ea1b988a278d6ecb0f3588a5bcfeb4d59ee6978cd017a2a71de

  pristine input    D:\UTD\Project_purdue\Lean_certification\SixQubit\Orbit31.lean
                    sha256 20f676f2469cb70add5892f23148e697a4f3142fa834f125518cca0c9f0bd681
  unchanged dep     D:\UTD\Project_purdue\Lean_certification\SixQubit\Table31.lean
                    sha256 72eaa4511e9c4f049265dcd5744cf14f82cf15e98ca79edbe8a9cc5286f581b2

INSTALL:  copy AUDIT31.lean over SixQubit\Orbit31.lean.  It is byte-identical to the previous
agent's Orbit31Work.lean except for one blank line (`diff` output was exactly `3650a3651 >`),
so either file installs the same proof.

I am deliberately not inlining 120 KB of Lean through this field.  A dump that large risks
silent truncation or escape corruption in transit, and a corrupted 120 KB blob is strictly
worse for the caller than a path plus a SHA-256 that can be checked in one command.  The
checksummed files above are exactly what compiled.

VERBATIM HEADLINE STATEMENT (AUDIT31.lean lines 3370-3423, abridged only in the 32-argument
MomentSystem application, which is the literal sequence normSq (c y0) .. normSq (c y15),
normSq (d z0) .. normSq (d z15)):

set_option maxHeartbeats 4000000 in
/-- **Orbit 31 admits no six-qubit `((6,2,3))` code.**  The moment system,
the thirty-three off-diagonal Knill-Laflamme conditions listed here and the
twelve Klein-mask diagonal conditions are jointly inconsistent. -/
theorem no_go_of_moments (c d : SS.BitString 6 -> ℂ)
    (hm : MomentSystem (Complex.normSq (c y0)) … (Complex.normSq (d z15)))
    (E0_w0 : offSum c d ef0 w0 = 0) (E0_w1 : offSum c d ef0 w1 = 0)
    (E0_w3 : offSum c d ef0 w3 = 0) (E0_w4 : offSum c d ef0 w4 = 0)
    (E0_w5 : offSum c d ef0 w5 = 0)
    (E1_w0 …) (E1_w2 …) (E1_w3 …) (E1_w4 …) (E1_w5 …)
    (E2_w0 …) (E2_w2 …) (E2_w3 …) (E2_w4 …) (E2_w5 …)
    (E3_w0 …) (E3_w5 …) (E4_w0 …) (E4_w5 …) (E5_w0 …) (E5_w5 …)
    (E6_w0 …) (E6_w4 …) (E7_w0 …) (E7_w4 …) (E8_w0 …) (E8_w4 …)
    (E9_w0 …) (E9_w3 …) (E10_w0 …) (E10_w3 …) (E11_w0 …) (E11_w3 …)
    (D12_w0 : diagBot c ef12 w0 = diagTop d ef12 w0) (D12_w4 …) (D12_w3 …) (D12_w6 …)
    (D13_w0 …) (D13_w5 …) (D13_w3 …) (D13_w7 …)
    (D14_w0 …) (D14_w5 …) (D14_w4 …) (D14_w8 …)
    : False := by …

## compile_output

MY OWN COMPILE, not the previous agent's.  Command, run from D:\UTD\Project_purdue\Lean_certification:

    lake env lean "C:/Users/richa/AppData/Local/Temp/claude/D--UTD-Project-purdue/e2435927-3651-49b0-acfb-31f3430ee257/scratchpad/AUDIT31.lean"

  EXIT = 0
  stdout+stderr = 0 bytes  (ZERO errors, ZERO warnings)
  wall time 90 s
Re-run a second time at the end of the audit: EXIT = 0, no diagnostics.  Reproduced.

Toolchain: leanprover/lean4:v4.27.0.  lakefile.lean sets NO leanOptions, so no linter is
suppressed — an empty output really means zero warnings.

POINT 4 CHECKS (all clean):
  * grep for `sorry`            -> 0 occurrences of the tactic.  The only two `admit`/`sorry`
                                   substring hits in the whole file are the English words
                                   "admit no solution" and "admits no" inside docstrings.
  * grep for `native_decide`    -> 1 hit, in the header docstring: "`native_decide` is not used".
                                   Zero in tactic position.
  * grep for `axiom`/`opaque`/`unsafe`/`partial`/`macro`/`attribute`/`#eval` in the appended
                                   block -> none.
  * `set_option` in the whole file -> only three, all `maxHeartbeats` (1e6, 2e6, 4e6).  No
                                   `debug.skipKernelTC`, no linter disabling.
  * 126 new theorems, 0 name collisions with the 896 pre-existing ones.
  * The appended block sits inside both `namespace SixQubit.Orbit31` and the
    `noncomputable section`, as required.

I did not run a full `lake build` because that would mean writing into the user's project.
It is not needed: `lake env lean` elaborates and kernel-checks the identical module content
against the project's built dependencies, and the only downstream consumer,
SixQubit.lean, merely re-exports Orbit31.

## axioms

MY OWN RUN.  I appended `#print axioms` lines to a copy (AUDIT31ax.lean) and compiled it;
EXIT = 0, and the output was exactly:

  'SixQubit.Orbit31.no_go_of_moments' depends on axioms: [propext, Classical.choice, Quot.sound]
  'SixQubit.Orbit31.master'           depends on axioms: [propext, Classical.choice, Quot.sound]
  'SixQubit.Orbit31.branch_lone'      depends on axioms: [propext, Classical.choice, Quot.sound]
  'SixQubit.Orbit31.branch_pair'      depends on axioms: [propext, Classical.choice, Quot.sound]
  'SixQubit.Orbit31.branch_triple'    depends on axioms: [propext, Classical.choice, Quot.sound]
  'SixQubit.Orbit31.branch_quad'      depends on axioms: [propext, Classical.choice, Quot.sound]
  'SixQubit.Orbit31.lagrange3_real'   depends on axioms: [propext, Classical.choice, Quot.sound]
  'SixQubit.Orbit31.perm_of_raw'      depends on axioms: [propext, Classical.choice, Quot.sound]
  'SixQubit.Orbit31.S0_eq_fiber'      depends on axioms: [propext, Classical.choice, Quot.sound]
  'SixQubit.Orbit31.S1_eq_fiber'      depends on axioms: [propext, Classical.choice, Quot.sound]

Exactly the permitted set.  `#print axioms` is transitive, so the headline line alone already
certifies that nothing anywhere in the 126-theorem dependency cone (nor in Table31, nor in the
896 pre-existing lemmas it leans on) uses sorryAx, Lean.ofReduceBool (native_decide), or any
new axiom.

## unfinished

VERDICT: ORBIT 31 IS CERTIFIED, at the same standard as the other twenty-plus orbits in this
project.  Nothing in the proof is unfinished.  Below: the hypothesis classification you asked
for, the extra hostile checks I ran, and the four things that are genuinely still open (none of
them a hole in the proof).

=== POINT 2: HYPOTHESIS HONESTY.  ALL 46 HYPOTHESES CLASSIFIED. ===
I mechanically grepped the hypothesis block (lines 3374-3423): 33 lines match
`offSum c d ef_ w_ = 0`, 12 match `diagBot c ef_ w_ = diagTop d ef_ w_`, 1 is the MomentSystem,
and grep for any hypothesis line NOT matching one of those three shapes returns EMPTY.  There
is no smuggled algebraic fact, no `≠ 0` side condition, no pre-chewed Gram identity, no
`v_e = 0`, nothing about phases.  Everything in the survey's Gaps 1-4 was actually derived
inside the proof.

(a) `hm : MomentSystem …` — HONEST, and I verified it is EXACTLY the Knill-Laflamme diagonal
    content, not a hand-tuned system.  The structure is a plain conjunction of 23 linear
    equations plus 32 nonnegativity fields, instantiated at q_k = normSq (c y_k),
    r_j = normSq (d z_j).  I built, independently from the bit-strings, the true conditions
    "sum q = 1, sum r = 1, and <0|Z^z|0> = <1|Z^z|1> for every z with 1 <= |z| <= 2"
    (2 + 6 + 15 = 23 conditions) and compared row spaces of the augmented matrices:
        rank(true) = 23, rank(stated) = 23, rank(union) = 23  ->  IDENTICAL AFFINE SOLUTION SET.
    So the MomentSystem neither adds nor drops anything relative to genuine KL.  I also
    re-derived the fibers (a = (1,1,1,2,2,2) mod 4 gives residue 0 on y0..y15 and residue 1 on
    z0..z15) and the complement pairing (comp(y_k) = z_{15-k}) outside Lean; both match, and
    Lean proves them by `decide` anyway (S0_eq_fiber, S1_eq_fiber, hat0..hat15).

(b) the 33 `offSum … = 0` — HONEST.  `offSum c d e z` is defined in-file as
        sum over y in S1 with y XOR e in S0 of (-1)^(z.y) * conj(c (y XOR e)) * d y,
    which is <0_L| X^e Z^z |1_L> up to the nonzero prefactor i^{#Y}.  Correct off-diagonal KL.

(c) the 12 `diagBot = diagTop` — HONEST.  diagBot/diagTop are the analogous restricted sums
    over S0 and S1; both carry the same i^{#Y} prefactor, so equality of the sums is
    equivalent to <0_L|X^e Z^z|0_L> = <1_L|X^e Z^z|1_L>.  Correct diagonal KL.

(d) WEIGHT LEGALITY — I decoded all 45 (mask, dressing) pairs into Paulis.  All 45 are
    DISTINCT and every one has weight <= 2, so each is a legitimate KL condition for a
    distance-3 code.  Full list: X0, X0Z1, X0Z5, X0Z4, X0Z3, X1, Z0X1, X1Z5, X1Z4, X1Z3,
    X2, Z0X2, X2Z5, X2Z4, X2Z3, X0X3, X0Y3, X1X3, X1Y3, X2X3, X2Y3, X0X4, X0Y4, X1X4, X1Y4,
    X2X4, X2Y4, X0X5, X0Y5, X1X5, X1Y5, X2X5, X2Y5 (off-diagonal), and X4X5, Y4X5, X4Y5, Y4Y5,
    X3X5, Y3X5, X3Y5, Y3Y5, X3X4, Y3X4, X3Y4, Y3Y4 (diagonal).  Zero over-weight.

(e) The internal chain is compiler-enforced end to end and I spot-audited the joints:
    - the twelve `hM..` arguments passed to `master` are genuine
      `fun hT => Table31.M_eq_of_raw … hT`, with hFam proved by
      `simp only [star_star]; linear_combination R_ef` from the fam3 lemmas, which are in turn
      `linear_combination` of the four dbot/dtop expansions of the stated diagBot=diagTop
      hypotheses.  No `absurd`, no vacuous discharge.
    - the eighteen permanents come from `congrArg star (fam2_k c d E.._w.. E.._w..)` plus
      `perm_of_raw`, fed the real column relations.
    - the index map is pinned by the type checker: hCol0 must be
      normSq(c y7)+normSq(c y11)+normSq(c y15) = normSq(c y0)+1/8 and is discharged by
      `linarith [col0 hm]`; a wrong column assignment could not typecheck.

=== EXTRA HOSTILE CHECKS I RAN (beyond what was asked) ===
NON-VACUITY 1.  MomentSystem alone is FEASIBLE (LP, HiGHS, status optimal), so the no-go is not
  a statement about an empty set at the moment layer.  On that polytope the derived facts the
  proof uses are confirmed exactly: sum alpha = 1/4 (min = max = 0.25), each B row = 1/4,
  q0 - q7 - q11 - q15 = -1/8.

NON-VACUITY 2 (the decisive one).  I tried to FALSIFY the theorem: 300 random Levenberg-
  Marquardt restarts over the 64 real unknowns (c on S0, d on S1), minimising the residual of
  all 23 moment relations + all 33 off-diagonal + all 12 Klein-diagonal conditions.
      best sum-of-squares residual = 1.93e-01  (2-norm 4.40e-01, worst single residual 2.03e-01)
  No counterexample anywhere near.  The theorem is corroborated numerically, not just formally.

NON-VACUITY 3 (ablation, and the best evidence the new work matters).  Same search with ONLY
  the 12 Klein-diagonal (family three) conditions removed:
      best sum-of-squares residual = 1.31e-20  — SOLVED to machine precision,
  with |a_e|^2 = 1/16 for all four columns (sum = 1/4, as the theory predicts).
  So 34 of the 45 hypotheses are jointly satisfiable, and the twelve family-three conditions
  this assembly introduces are genuinely load-bearing.  The contradiction is real content, not
  an artefact of an over-constrained transcription.

=== WHAT IS STILL MISSING (none of it a gap in the orbit-31 proof) ===
1. WIRING.  `SixQubit.Orbit31` is imported by SixQubit.lean but NOT by SixQubit\Audit.lean, and
   Audit.lean contains no `#print axioms SixQubit.Orbit31.*` line.  Every other certified orbit
   has one.  One-line fix (add the import plus, say, S0_eq_fiber / S1_eq_fiber /
   no_go_of_moments lines); I did not make it, since my remit was audit only.

2. STALE DOCSTRING, now factually wrong.  SixQubit\Table31.lean lines 32-35 still read:
   "Status: partial.  The `(4)`, `(2,2)` and `(2,1,1)` branches are proved on paper but not yet
   here, and the transcription of orbit 31 … is not built, so orbit 31 is NOT yet certified.
   Nothing here is imported by `SixQubit.Audit`."  The first two clauses are false after this
   change; the last is still true (see item 1).  Should be rewritten at install time.

3. THE PREVIOUS AGENT UNDERSTATED THE DEAD CODE IN Table31.  It reported all_distinct,
   partition31 and kernel_identity as unused.  I enumerated every Table31 reference in the
   appended block; the proof uses only M_eq_of_raw (x12), sq (x6), perm_support (x5),
   kernel_norm (x4), gram_eq (x4), det_perm_zero (x3), conj4 (x3), perm_triple (x2),
   tight_pair, pair_gap, pair_class.  So THIRTEEN of Table31's 24 lemmas are off the proof
   path: kernel_identity, all_distinct, partition31, lone_column, kernel_zero, row_key,
   key_of_raw, hH3_of_raw, key, M_eq, phase_transfer, T_eq_zero_of_ae, T_eq_zero_of_af.  Note
   `lone_column` in particular — the previous agent's own prose says the lone-column branch
   "gives v_f = 0" via it, but `branch_lone` reimplements that inline and never calls it.  All
   thirteen still compile; they are simply unused.  No soundness impact, but the claim in the
   handoff was wrong and the caller should not assume Table31 is minimal.

4. PROJECT-WIDE MODELLING GAP, pre-existing and not introduced here.  SixQubit\Bridge.lean
   proves the converse direction ("a valid code makes offdiagMatElt / diagMatElt vanish") in
   terms of SixQubit.offdiagMatElt / diagMatElt from Common.lean.  No orbit file, orbit 31
   included, is formally connected to it: each orbit re-declares its own local `offSum` /
   `diagBot` / `diagTop` over its own S0/S1 (I checked — Orbit25/27/28/29/30/31/32/33/34/35 all
   do this identically).  The step "a ((6,2,3)) code on this orbit satisfies these 45
   hypotheses" is therefore justified by inspection, not by Lean.  I verified that inspection
   by hand above (definitions match the matrix elements, MomentSystem equals the true weight-<=2
   diagonal Z conditions, all 45 Paulis have weight <= 2), so orbit 31 is no worse off than its
   twenty-odd already-certified siblings — but the caller should not describe the pipeline as
   end-to-end formal without closing this for all orbits at once.

Minor cosmetic note, not worth changing: `hcol_1_0` and its eleven siblings shadow the incoming
hypothesis `h2` with `have h2 := congrArg star hh`.  Legal, no warning, no effect.

## asm

## compiled

True

## complete

True

## file_path

C:\Users\richa\AppData\Local\Temp\claude\D--UTD-Project-purdue\e2435927-3651-49b0-acfb-31f3430ee257\scratchpad\Orbit31Work.lean

## source

THE VERBATIM SOURCE TO APPEND IS ON DISK (120,719 bytes / 1876 lines) AT

    C:\Users\richa\AppData\Local\Temp\claude\D--UTD-Project-purdue\e2435927-3651-49b0-acfb-31f3430ee257\scratchpad\APPEND.lean

and the already-merged, already-compiled whole file (3654 lines) is at

    C:\Users\richa\AppData\Local\Temp\claude\D--UTD-Project-purdue\e2435927-3651-49b0-acfb-31f3430ee257\scratchpad\Orbit31Work.lean

Install by copying Orbit31Work.lean over SixQubit/Orbit31.lean, or by splicing APPEND.lean
into the pristine Orbit31.lean immediately AFTER line 1774 (i.e. before the `end` on line 1775
that closes the `noncomputable section`, and before `end SixQubit.Orbit31`).  That is exactly
how Orbit31Work.lean was built.  I am not inlining the 120 KB here because a truncated dump
would be worse than a path; the file is byte-for-byte what compiles.

=================  WHAT THE 1876 LINES CONTAIN, IN ORDER  =================

(1) lines 1-158  -- 72 `by decide` sign facts + 9 expansion lemmas (mechanically generated,
    identical in shape to the existing sg*/ex* lemmas):
      sg0_w3_8..15, sg0_w4_8..15, sg0_w5_8..15
      sg1_w{3,4,5}_{4,5,6,7,12,13,14,15}
      sg2_w{3,4,5}_{0,1,2,3,12,13,14,15}
      ex0_w3, ex0_w4, ex0_w5, ex1_w3, ex1_w4, ex1_w5, ex2_w3, ex2_w4, ex2_w5
    e.g.
      theorem ex0_w3 (c d : SS.BitString 6 -> ℂ) :
          offSum c d ef0 w3 = star (c y0) * d z8 - star (c y1) * d z9 - star (c y2) * d z10
            + star (c y3) * d z11 - star (c y4) * d z12 + star (c y5) * d z13
            + star (c y6) * d z14 - star (c y7) * d z15 := by
        unfold offSum
        rw [incidence0]
        rw [Finset.sum_insert (by decide), ... , Finset.sum_singleton]
        rw [fl0_8, fl0_9, fl0_10, fl0_11, fl0_12, fl0_13, fl0_14, fl0_15]
        simp only [sg0_w3_8, ..., SixQubit.signMul_true, SixQubit.signMul_false]
        try ring

(2) the twelve conjugated column relations `hcol_i_e`, i = 1,2,3, e = 0..3, e.g.
      theorem hcol_1_0 (c d : SS.BitString 6 -> ℂ)
          (h0 : offSum c d ef0 w1 = 0) (h1 : offSum c d ef0 w5 = 0)
          (h2 : offSum c d ef0 w4 = 0) (h3 : offSum c d ef0 w3 = 0)
          : star (d z8) * c y0 = star (d z15) * c y7 := by
        rw [ex0_w1] at h0; rw [ex0_w5] at h1; rw [ex0_w4] at h2; rw [ex0_w3] at h3
        have hh : star (c y0) * d z8 = star (c y7) * d z15 := by
          linear_combination (1/4 : ℂ) * h0 + (1/4 : ℂ) * h1 + (1/4 : ℂ) * h2 + (1/4 : ℂ) * h3
        have hstar := congrArg star hh
        simp only [star_mul', star_star] at hstar
        linear_combination hstar
    (rows 2,3 use ef1/ef2 with w2 in place of w1; sign vectors (+,+,+,+), (+,+,-,-),
     (+,-,+,-), (+,-,-,+) for columns 0,1,2,3 exactly as in the survey.)

(3) the twelve ordered-pair family-three identities `fam3_e_f`, e.g.
      theorem fam3_1_0 (c d : SS.BitString 6 -> ℂ)
          (h0 : diagBot c ef12 w0 = diagTop d ef12 w0)
          (h1 : diagBot c ef12 w4 = diagTop d ef12 w4)
          (h2 : diagBot c ef12 w3 = diagTop d ef12 w3)
          (h3 : diagBot c ef12 w6 = diagTop d ef12 w6)
          : c y6 * star (c y7) + c y10 * star (c y11) + c y14 * star (c y15)
              + star (c y1) * c y0
            = star (d z9) * d z8 + star (d z5) * d z4 + star (d z1) * d z0
              + d z14 * star (d z15) := by
        rw [dbot12_w0, dtop12_w0] at h0
        rw [dbot12_w4, dtop12_w4] at h1
        rw [dbot12_w3, dtop12_w3] at h2
        rw [dbot12_w6, dtop12_w6] at h3
        linear_combination (1/4 : ℂ) * h0 + (1/4 : ℂ) * h1 + (1/4 : ℂ) * h2 + (1/4 : ℂ) * h3
    pairs/masks/signs: (1,0)(3,2)(2,3)(0,1) from ef12; (2,0)(3,1)(1,3)(0,2) from ef13;
    (3,0)(2,1)(1,2)(0,3) from ef14, with eps = (++++),(++--),(+-+-),(+--+).

(4) lines 539-911 -- THE HAND-WRITTEN BRANCH ALGEBRA, reproduced verbatim below.

(5) lines 912-1595 -- `master`, the 681-line branch assembly (fully generated; signature and
    case-tree shape given below).

(6) lines 1596-1876 -- `no_go_of_moments` (generated; signature and body shape given below).

=================  (4) THE BRANCH ALGEBRA, VERBATIM  =================

/-! ## The branch algebra -/

theorem lagrange3_real (x1 x2 x3 y1 y2 y3 : ℂ) :
    (Complex.normSq x1 + Complex.normSq x2 + Complex.normSq x3)
      * (Complex.normSq y1 + Complex.normSq y2 + Complex.normSq y3)
      = Complex.normSq (x1 * star y1 + x2 * star y2 + x3 * star y3)
        + (Complex.normSq (x1 * y2 - x2 * y1) + Complex.normSq (x1 * y3 - x3 * y1)
            + Complex.normSq (x2 * y3 - x3 * y2)) := by
  have hc : (((Complex.normSq x1 + Complex.normSq x2 + Complex.normSq x3)
      * (Complex.normSq y1 + Complex.normSq y2 + Complex.normSq y3) : ℝ) : ℂ)
      = ((Complex.normSq (x1 * star y1 + x2 * star y2 + x3 * star y3)
        + (Complex.normSq (x1 * y2 - x2 * y1) + Complex.normSq (x1 * y3 - x3 * y1)
            + Complex.normSq (x2 * y3 - x3 * y2)) : ℝ) : ℂ) := by
    push_cast
    simp only [← Table31.sq, star_add, star_sub, star_mul', star_star]
    ring
  exact_mod_cast hc

theorem amp_eq_zero_of_v (a v : ℂ) (hK : v * star v = a * star a) (h : v = 0) : a = 0 := by
  have hz : a * star a = 0 := by rw [← hK, h]; ring
  rcases mul_eq_zero.mp hz with h' | h'
  · exact h'
  · exact star_eq_zero.mp h'

theorem v_ne_zero (a v : ℂ) (hK : v * star v = a * star a) (ha : a ≠ 0) : v ≠ 0 := by
  intro h; exact ha (amp_eq_zero_of_v a v hK h)

/-! ### Branch: a column alone in its phase class -/

/-- A column whose phase class is a singleton has `v_f = 0`, hence `a_f = 0`. -/
theorem branch_lone (vf vg1 vg2 vg3 af Mff Mg1f Mg2f Mg3f : ℂ) (alf alg1 alg2 alg3 : ℝ)
    (hEq : vg1 * Mg1f + vg2 * Mg2f + vg3 * Mg3f + vf * Mff = 0)
    (hMff : Mff = (alf : ℂ) + 1/8)
    (t1 : vg1 * Mg1f = (alg1 : ℂ) * vf)
    (t2 : vg2 * Mg2f = (alg2 : ℂ) * vf)
    (t3 : vg3 * Mg3f = (alg3 : ℂ) * vf)
    (hS : alf + alg1 + alg2 + alg3 = 1/4)
    (hKf : vf * star vf = af * star af) : af = 0 := by
  have hSc := congrArg (fun x : ℝ => (x : ℂ)) hS
  push_cast at hSc
  rw [hMff, t1, t2, t3] at hEq
  have h38 : vf * (3/8 : ℂ) = 0 := by linear_combination hEq - vf * hSc
  rcases mul_eq_zero.mp h38 with h | h
  · exact amp_eq_zero_of_v af vf hKf h
  · norm_num at h

/-! ### Branch: a phase class of exactly two columns -/

set_option maxHeartbeats 1000000 in
/-- A class of exactly two columns: the `2 x 2` system is singular, so
Cauchy-Schwarz is tight; the vanishing permanents then confine both columns to a
single row, whose budget they exceed. -/
theorem branch_pair
    (ae af ve vf vg vh b1e b2e b3e b1f b2f b3f Mee Mff Mef Mfe Mge Mhe Mgf Mhf : ℂ)
    (alg alh : ℝ)
    (hEqE : vg * Mge + vh * Mhe + ve * Mee + vf * Mfe = 0)
    (hEqF : vg * Mgf + vh * Mhf + ve * Mef + vf * Mff = 0)
    (tge : vg * Mge = (alg : ℂ) * ve) (the : vh * Mhe = (alh : ℂ) * ve)
    (tgf : vg * Mgf = (alg : ℂ) * vf) (thf : vh * Mhf = (alh : ℂ) * vf)
    (hMee : Mee = (Complex.normSq ae : ℂ) + 1/8)
    (hMff : Mff = (Complex.normSq af : ℂ) + 1/8)
    (hMef : Mef = b1e * star b1f + b2e * star b2f + b3e * star b3f)
    (hMfe : Mfe = b1f * star b1e + b2f * star b2e + b3f * star b3e)
    (hSum : Complex.normSq ae + Complex.normSq af + alg + alh = 1/4)
    (halg : 0 ≤ alg) (halh : 0 ≤ alh)
    (hColE : Complex.normSq b1e + Complex.normSq b2e + Complex.normSq b3e
               = Complex.normSq ae + 1/8)
    (hColF : Complex.normSq b1f + Complex.normSq b2f + Complex.normSq b3f
               = Complex.normSq af + 1/8)
    (hRow1 : Complex.normSq b1e + Complex.normSq b1f ≤ 1/4)
    (hRow2 : Complex.normSq b2e + Complex.normSq b2f ≤ 1/4)
    (hRow3 : Complex.normSq b3e + Complex.normSq b3f ≤ 1/4)
    (p12 : b1e * b2f + b1f * b2e = 0)
    (p13 : b1e * b3f + b1f * b3e = 0)
    (p23 : b2e * b3f + b2f * b3e = 0)
    (hKe : ve * star ve = ae * star ae) (_hKf : vf * star vf = af * star af)
    (hae : ae ≠ 0) (haf : af ≠ 0) : False := by
  have hSc := congrArg (fun x : ℝ => (x : ℂ)) hSum
  push_cast at hSc
  have hcast : ((Complex.normSq ae + Complex.normSq af : ℝ) : ℂ)
      = (Complex.normSq ae : ℂ) + (Complex.normSq af : ℂ) := by push_cast; ring
  rw [hMee, tge, the] at hEqE
  rw [hMff, tgf, thf] at hEqF
  have h0 : ve * ((Complex.normSq ae : ℂ) + 1/8
        + ((1/4 : ℂ) - ((Complex.normSq ae + Complex.normSq af : ℝ) : ℂ))) + vf * Mfe = 0 := by
    rw [hcast]; linear_combination hEqE - ve * hSc
  have h1 : vf * ((Complex.normSq af : ℂ) + 1/8
        + ((1/4 : ℂ) - ((Complex.normSq ae + Complex.normSq af : ℝ) : ℂ))) + ve * Mef = 0 := by
    rw [hcast]; linear_combination hEqF - vf * hSc
  have hve : ve ≠ 0 := v_ne_zero ae ve hKe hae
  have hv : ¬ (ve = 0 ∧ vf = 0) := fun h => hve h.1
  have hpc := Table31.pair_class ve vf Mef Mfe (Complex.normSq ae) (Complex.normSq af)
    (Complex.normSq ae + Complex.normSq af) hv h0 h1
  have hstar : Mfe = star Mef := by
    rw [hMef, hMfe]; simp only [star_add, star_mul', star_star]; ring
  rw [hstar, Table31.sq] at hpc
  push_cast at hpc
  have hreal : (Complex.normSq ae + 1/8 + (1/4 - (Complex.normSq ae + Complex.normSq af)))
      * (Complex.normSq af + 1/8 + (1/4 - (Complex.normSq ae + Complex.normSq af)))
      = Complex.normSq Mef := by
    refine Complex.ofReal_inj.mp ?_
    push_cast
    linear_combination hpc
  have hlag := lagrange3_real b1e b2e b3e b1f b2f b3f
  rw [← hMef, hColE, hColF] at hlag
  have hgap := Table31.pair_gap (Complex.normSq ae) (Complex.normSq af)
    (Complex.normSq ae + Complex.normSq af) rfl
  have hsle : Complex.normSq ae + Complex.normSq af ≤ 1/4 := by linarith
  have n1 := Complex.normSq_nonneg (b1e * b2f - b2e * b1f)
  have n2 := Complex.normSq_nonneg (b1e * b3f - b3e * b1f)
  have n3 := Complex.normSq_nonneg (b2e * b3f - b3e * b2f)
  have hm1 : Complex.normSq (b1e * b2f - b2e * b1f) = 0 := by linarith
  have hm2 : Complex.normSq (b1e * b3f - b3e * b1f) = 0 := by linarith
  have hm3 : Complex.normSq (b2e * b3f - b3e * b2f) = 0 := by linarith
  have d12 : b1e * b2f - b1f * b2e = 0 := by
    have := Complex.normSq_eq_zero.mp hm1; linear_combination this
  have d13 : b1e * b3f - b1f * b3e = 0 := by
    have := Complex.normSq_eq_zero.mp hm2; linear_combination this
  have d23 : b2e * b3f - b2f * b3e = 0 := by
    have := Complex.normSq_eq_zero.mp hm3; linear_combination this
  obtain ⟨q12a, q12b⟩ := Table31.det_perm_zero b1e b1f b2e b2f d12 p12
  obtain ⟨q13a, q13b⟩ := Table31.det_perm_zero b1e b1f b3e b3f d13 p13
  obtain ⟨q23a, q23b⟩ := Table31.det_perm_zero b2e b2f b3e b3f d23 p23
  have z01 : Complex.normSq b1e * Complex.normSq b2f = 0 := by
    rw [← Complex.normSq_mul, q12a]; simp
  have z10 : Complex.normSq b2e * Complex.normSq b1f = 0 := by
    rw [← Complex.normSq_mul]; rw [show b2e * b1f = b1f * b2e by ring, q12b]; simp
  have z02 : Complex.normSq b1e * Complex.normSq b3f = 0 := by
    rw [← Complex.normSq_mul, q13a]; simp
  have z20 : Complex.normSq b3e * Complex.normSq b1f = 0 := by
    rw [← Complex.normSq_mul]; rw [show b3e * b1f = b1f * b3e by ring, q13b]; simp
  have z12 : Complex.normSq b2e * Complex.normSq b3f = 0 := by
    rw [← Complex.normSq_mul, q23a]; simp
  have z21 : Complex.normSq b3e * Complex.normSq b2f = 0 := by
    rw [← Complex.normSq_mul]; rw [show b3e * b2f = b2f * b3e by ring, q23b]; simp
  have hApos : (0 : ℝ) < Complex.normSq ae + 1/8 := by
    have := Complex.normSq_nonneg ae; linarith
  have hBpos : (0 : ℝ) < Complex.normSq af + 1/8 := by
    have := Complex.normSq_nonneg af; linarith
  have htp := Table31.tight_pair (Complex.normSq b1e) (Complex.normSq b2e) (Complex.normSq b3e)
    (Complex.normSq b1f) (Complex.normSq b2f) (Complex.normSq b3f)
    (Complex.normSq ae + 1/8) (Complex.normSq af + 1/8)
    (Complex.normSq_nonneg _) (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)
    (Complex.normSq_nonneg _) (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)
    z01 z02 z10 z12 z20 z21 hColE hColF hApos hBpos hRow1 hRow2 hRow3
  have hpos : 0 < Complex.normSq ae := Complex.normSq_pos.mpr hae
  have hpos' : 0 < Complex.normSq af := Complex.normSq_pos.mpr haf
  linarith

theorem same_phase_ne (ae af ve vf : ℂ)
    (hT : ve * star vf - ae * star af = 0)
    (hKf : vf * star vf = af * star af)
    (hae : ae ≠ 0) (haf : af ≠ 0) :
    ve * af + vf * ae ≠ 0 := by
  intro h
  have key : (2 : ℂ) * (ae * (af * star af)) = 0 := by
    linear_combination (star vf) * h - af * hT - ae * hKf
  rcases mul_eq_zero.mp key with h' | h'
  · norm_num at h'
  · rcases mul_eq_zero.mp h' with h'' | h''
    · exact hae h''
    · rcases mul_eq_zero.mp h'' with h3 | h3
      · exact haf h3
      · exact haf (star_eq_zero.mp h3)

/-- The `B`-column Gram diagonal is the column total, `alpha_e + 1/8`. -/
theorem diag_M (b1 b2 b3 : ℂ) (al : ℝ)
    (h : Complex.normSq b1 + Complex.normSq b2 + Complex.normSq b3 = al + 1/8) :
    b1 * star b1 + b2 * star b2 + b3 * star b3 = (al : ℂ) + 1/8 := by
  rw [Table31.sq, Table31.sq, Table31.sq]
  have hc := congrArg (fun x : ℝ => (x : ℂ)) h
  push_cast at hc
  linear_combination hc

/-- A column with no `A` amplitude contributes nothing to the pairing. -/
theorem term_of_zero (ae ve vf Mef : ℂ) (h0 : ae = 0) (hKe : ve * star ve = ae * star ae) :
    ve * Mef = (Complex.normSq ae : ℂ) * vf := by
  have hv : ve = 0 := by
    rcases mul_eq_zero.mp (by rw [hKe, h0]; ring : ve * star ve = 0) with h | h
    · exact h
    · exact star_eq_zero.mp h
  rw [hv, h0]; simp

/-- A column of a different phase contributes `alpha_e * v_f`. -/
theorem term_of_diff (ae ve vf Mef : ℂ) (hKe : ve * star ve = ae * star ae)
    (hM : Mef = star ve * vf) : ve * Mef = (Complex.normSq ae : ℂ) * vf := by
  rw [hM, ← Table31.sq ae]
  linear_combination vf * hKe

/-- The phase test is symmetric. -/
theorem T_symm (ae af ve vf : ℂ) (h : ve * star vf - ae * star af = 0) :
    vf * star ve - af * star ae = 0 := by
  have hs := congrArg star h
  simp only [star_sub, star_mul', star_star, star_zero] at hs
  linear_combination hs

/-- Same phase kills the permanent outright. -/
theorem perm_extract (ae af ve vf x : ℂ) (hP : (ve * af + vf * ae) * x = 0)
    (hT : ve * star vf - ae * star af = 0) (hKf : vf * star vf = af * star af)
    (hae : ae ≠ 0) (haf : af ≠ 0) : x = 0 := by
  rcases mul_eq_zero.mp hP with h | h
  · exact absurd h (same_phase_ne ae af ve vf hT hKf hae haf)
  · exact h

/-- The phase test is transitive through a column with a nonzero amplitude. -/
theorem T_trans (ae af ag ve vf vg : ℂ)
    (h1 : ve * star vf - ae * star af = 0)
    (h2 : vf * star vg - af * star ag = 0)
    (hKf : vf * star vf = af * star af)
    (haf : af ≠ 0) :
    ve * star vg - ae * star ag = 0 := by
  have key : (ve * star vg - ae * star ag) * (af * star af) = 0 := by
    linear_combination (vf * star vg) * h1 + (ae * star af) * h2 - (ve * star vg) * hKf
  rcases mul_eq_zero.mp key with h' | h'
  · exact h'
  · rcases mul_eq_zero.mp h' with h'' | h''
    · exact absurd h'' haf
    · exact absurd (star_eq_zero.mp h'') haf

/-- Family two, cleared of denominators by the four column relations: the
permanent of the `2 x 2` block is killed by the phase factor. -/
theorem perm_of_raw (ae af ve vf b1e b1f b2e b2f u1e u1f u2e u2f : ℂ)
    (hFam2 : b1f * u2e + b1e * u2f + b2f * u1e + b2e * u1f = 0)
    (hC1e : u1e * ae = ve * b1e) (hC1f : u1f * af = vf * b1f)
    (hC2e : u2e * ae = ve * b2e) (hC2f : u2f * af = vf * b2f) :
    (ve * af + vf * ae) * (b1e * b2f + b1f * b2e) = 0 := by
  linear_combination (ae * af) * hFam2 - (af * b2f) * hC1e - (ae * b2e) * hC1f
    - (af * b1f) * hC2e - (ae * b1e) * hC2f

/-! ### Support propagation along vanishing permanents -/

/-- If one row is nonzero at a column where another vanishes, the vanishing
permanents wipe out the whole of the second row -- impossible, since every row
carries a quarter. -/
theorem row_wipe (be bf bg bh se sf sg sh : ℂ) (hbe : be ≠ 0) (hse : se = 0)
    (pf : be * sf + bf * se = 0) (pg : be * sg + bg * se = 0) (ph : be * sh + bh * se = 0)
    (hrow : Complex.normSq se + Complex.normSq sf + Complex.normSq sg + Complex.normSq sh = 1/4) :
    False := by
  have h1 := Table31.perm_support be bf se sf hbe hse pf
  have h2 := Table31.perm_support be bg se sg hbe hse pg
  have h3 := Table31.perm_support be bh se sh hbe hse ph
  rw [hse, h1, h2, h3] at hrow
  simp only [Complex.normSq_zero] at hrow
  linarith

/-- The three-column version: the wiped row is then confined to the fourth
column, whose total is only an eighth. -/
theorem row_wipe3 (be bf bg se sf sg sh : ℂ) (hbe : be ≠ 0) (hse : se = 0)
    (pf : be * sf + bf * se = 0) (pg : be * sg + bg * se = 0)
    (hrow : Complex.normSq se + Complex.normSq sf + Complex.normSq sg + Complex.normSq sh = 1/4)
    (hsh : Complex.normSq sh ≤ 1/8) : False := by
  have h1 := Table31.perm_support be bf se sf hbe hse pf
  have h2 := Table31.perm_support be bg se sg hbe hse pg
  rw [hse, h1, h2] at hrow
  simp only [Complex.normSq_zero] at hrow
  linarith

/-- Every entry of the bottom block is nonzero once all permanents vanish. -/
theorem entry_ne (xe xf xg xh ye yf yg yh ze zf zg zh : ℂ) (ale : ℝ) (hale : 0 ≤ ale)
    (hcol : Complex.normSq xe + Complex.normSq ye + Complex.normSq ze = ale + 1/8)
    (hrow : Complex.normSq xe + Complex.normSq xf + Complex.normSq xg + Complex.normSq xh = 1/4)
    (qyf : ye * xf + yf * xe = 0) (qyg : ye * xg + yg * xe = 0) (qyh : ye * xh + yh * xe = 0)
    (qzf : ze * xf + zf * xe = 0) (qzg : ze * xg + zg * xe = 0) (qzh : ze * xh + zh * xe = 0) :
    xe ≠ 0 := by
  intro h0
  by_cases hy : ye = 0
  · by_cases hz : ze = 0
    · rw [h0, hy, hz] at hcol
      simp only [Complex.normSq_zero] at hcol
      linarith
    · exact row_wipe ze zf zg zh xe xf xg xh hz h0 qzf qzg qzh hrow
  · exact row_wipe ye yf yg yh xe xf xg xh hy h0 qyf qyg qyh hrow

/-- The three-column version. -/
theorem entry_ne3 (xe xf xg xh ye yf yg ze zf zg : ℂ) (ale : ℝ) (hale : 0 ≤ ale)
    (hcol : Complex.normSq xe + Complex.normSq ye + Complex.normSq ze = ale + 1/8)
    (hrow : Complex.normSq xe + Complex.normSq xf + Complex.normSq xg + Complex.normSq xh = 1/4)
    (hxh : Complex.normSq xh ≤ 1/8)
    (qyf : ye * xf + yf * xe = 0) (qyg : ye * xg + yg * xe = 0)
    (qzf : ze * xf + zf * xe = 0) (qzg : ze * xg + zg * xe = 0) :
    xe ≠ 0 := by
  intro h0
  by_cases hy : ye = 0
  · by_cases hz : ze = 0
    · rw [h0, hy, hz] at hcol
      simp only [Complex.normSq_zero] at hcol
      linarith
    · exact row_wipe3 ze zf zg xe xf xg xh hz h0 qzf qzg hrow hxh
  · exact row_wipe3 ye yf yg xe xf xg xh hy h0 qyf qyg hrow hxh

/-! ### Branch: all four columns in one phase class -/

/-- With every permanent vanishing, all twelve bottom entries are nonzero, and
`perm_triple` then gives a contradiction. -/
theorem branch_quad (b10 b11 b12 b13 b20 b21 b22 b23 b30 b31 b32 b33 : ℂ)
    (al0 al1 al2 : ℝ) (hal0 : 0 ≤ al0) (hal1 : 0 ≤ al1) (hal2 : 0 ≤ al2)
    (hRow1 : Complex.normSq b10 + Complex.normSq b11 + Complex.normSq b12
               + Complex.normSq b13 = 1/4)
    (hRow2 : Complex.normSq b20 + Complex.normSq b21 + Complex.normSq b22
               + Complex.normSq b23 = 1/4)
    (hCol0 : Complex.normSq b10 + Complex.normSq b20 + Complex.normSq b30 = al0 + 1/8)
    (hCol1 : Complex.normSq b11 + Complex.normSq b21 + Complex.normSq b31 = al1 + 1/8)
    (hCol2 : Complex.normSq b12 + Complex.normSq b22 + Complex.normSq b32 = al2 + 1/8)
    (p12_01 : b10 * b21 + b11 * b20 = 0) (p12_02 : b10 * b22 + b12 * b20 = 0)
    (p12_03 : b10 * b23 + b13 * b20 = 0) (p12_12 : b11 * b22 + b12 * b21 = 0)
    (p12_13 : b11 * b23 + b13 * b21 = 0) (p12_23 : b12 * b23 + b13 * b22 = 0)
    (p13_01 : b10 * b31 + b11 * b30 = 0) (p13_02 : b10 * b32 + b12 * b30 = 0)
    (p13_12 : b11 * b32 + b12 * b31 = 0) (p13_13 : b11 * b33 + b13 * b31 = 0)
    (p13_23 : b12 * b33 + b13 * b32 = 0)
    (p23_01 : b20 * b31 + b21 * b30 = 0) (p23_02 : b20 * b32 + b22 * b30 = 0)
    (p23_03 : b20 * b33 + b23 * b30 = 0) : False := by
  have hb11 : b11 ≠ 0 :=
    entry_ne b11 b10 b12 b13 b21 b20 b22 b23 b31 b30 b32 b33 al1 hal1 hCol1 (by linarith)
      (by linear_combination p12_01) (by linear_combination p12_12)
      (by linear_combination p12_13) (by linear_combination p13_01)
      (by linear_combination p13_12) (by linear_combination p13_13)
  have hb12 : b12 ≠ 0 :=
    entry_ne b12 b10 b11 b13 b22 b20 b21 b23 b32 b30 b31 b33 al2 hal2 hCol2 (by linarith)
      (by linear_combination p12_02) (by linear_combination p12_12)
      (by linear_combination p12_23) (by linear_combination p13_02)
      (by linear_combination p13_12) (by linear_combination p13_23)
  have hb20 : b20 ≠ 0 :=
    entry_ne b20 b21 b22 b23 b10 b11 b12 b13 b30 b31 b32 b33 al0 hal0 (by linarith) hRow2
      (by linear_combination p12_01) (by linear_combination p12_02)
      (by linear_combination p12_03) (by linear_combination p23_01)
      (by linear_combination p23_02) (by linear_combination p23_03)
  have htri := Table31.perm_triple b10 b11 b12 b20 b21 b22 p12_01 p12_02 p12_12
  rcases mul_eq_zero.mp htri with h | h
  · rcases mul_eq_zero.mp h with h' | h'
    · exact hb11 h'
    · exact hb12 h'
  · exact hb20 h

/-! ### Branch: three columns in one class, the fourth with no `A` amplitude -/

/-- The three same-phase columns are entirely nonzero on the bottom block, and
`perm_triple` closes the branch. -/
theorem branch_triple (b1e b1f b1g b1h b2e b2f b2g b2h b3e b3f b3g : ℂ)
    (ale alf alg : ℝ) (hale : 0 ≤ ale) (half : 0 ≤ alf) (halg : 0 ≤ alg)
    (hRow1 : Complex.normSq b1e + Complex.normSq b1f + Complex.normSq b1g
               + Complex.normSq b1h = 1/4)
    (hRow2 : Complex.normSq b2e + Complex.normSq b2f + Complex.normSq b2g
               + Complex.normSq b2h = 1/4)
    (hColE : Complex.normSq b1e + Complex.normSq b2e + Complex.normSq b3e = ale + 1/8)
    (hColF : Complex.normSq b1f + Complex.normSq b2f + Complex.normSq b3f = alf + 1/8)
    (hColG : Complex.normSq b1g + Complex.normSq b2g + Complex.normSq b3g = alg + 1/8)
    (hColH : Complex.normSq b1h + Complex.normSq b2h ≤ 1/8)
    (p12_ef : b1e * b2f + b1f * b2e = 0) (p12_eg : b1e * b2g + b1g * b2e = 0)
    (p12_fg : b1f * b2g + b1g * b2f = 0)
    (p13_ef : b1e * b3f + b1f * b3e = 0) (p13_eg : b1e * b3g + b1g * b3e = 0)
    (p13_fg : b1f * b3g + b1g * b3f = 0)
    (p23_ef : b2e * b3f + b2f * b3e = 0) (p23_eg : b2e * b3g + b2g * b3e = 0) : False := by
  have n1h := Complex.normSq_nonneg b1h
  have n2h := Complex.normSq_nonneg b2h
  have hb1f : b1f ≠ 0 :=
    entry_ne3 b1f b1e b1g b1h b2f b2e b2g b3f b3e b3g alf half hColF (by linarith) (by linarith)
      (by linear_combination p12_ef) (by linear_combination p12_fg)
      (by linear_combination p13_ef) (by linear_combination p13_fg)
  have hb1g : b1g ≠ 0 :=
    entry_ne3 b1g b1e b1f b1h b2g b2e b2f b3g b3e b3f alg halg hColG (by linarith) (by linarith)
      (by linear_combination p12_eg) (by linear_combination p12_fg)
      (by linear_combination p13_eg) (by linear_combination p13_fg)
  have hb2e : b2e ≠ 0 :=
    entry_ne3 b2e b2f b2g b2h b1e b1f b1g b3e b3f b3g ale hale (by linarith) hRow2 (by linarith)
      (by linear_combination p12_ef) (by linear_combination p12_eg)
      (by linear_combination p23_ef) (by linear_combination p23_eg)
  have htri := Table31.perm_triple b1e b1f b1g b2e b2f b2g p12_ef p12_eg p12_fg
  rcases mul_eq_zero.mp htri with h | h
  · rcases mul_eq_zero.mp h with h' | h'
    · exact hb1f h'
    · exact hb1g h'
  · exact hb2e h

=================  (5) `master`: SIGNATURE AND CASE TREE  =================

set_option maxHeartbeats 2000000 in
theorem master
    (a0 a1 a2 a3 v0 v1 v2 v3 : ℂ)
    (b10 b11 b12 b13 b20 b21 b22 b23 b30 b31 b32 b33 : ℂ)
    (hK0 : v0 * star v0 = a0 * star a0)          -- and hK1, hK2, hK3
    (hF1 : b10 * v0 + b11 * v1 + b12 * v2 + b13 * v3 = 0)   -- and hF2, hF3
    (hSum : Complex.normSq a0 + Complex.normSq a1 + Complex.normSq a2 + Complex.normSq a3 = 1/4)
    (hRow1 : Complex.normSq b10 + Complex.normSq b11 + Complex.normSq b12
               + Complex.normSq b13 = 1/4)      -- and hRow2, hRow3
    (hCol0 : Complex.normSq b10 + Complex.normSq b20 + Complex.normSq b30
               = Complex.normSq a0 + 1/8)       -- and hCol1, hCol2, hCol3
    (hM01 : v0 * star v1 - a0 * star a1 ≠ 0 →
        (b10 * star b11 + b20 * star b21 + b30 * star b31) = star v0 * v1)  -- 12 in all
    (hP12_01 : (v0 * a1 + v1 * a0) * (b10 * b21 + b11 * b20) = 0)           -- 18 in all
    : False := by
  -- preamble: normSq_nonneg for the 4 a's and 12 b's; hD0..hD3 := diag_M ...;
  --           G0..G3 := Table31.gram_eq ... (the four column pairings)
  -- then  by_cases ha0 : a0 = 0  /  ha1 / ha2 / ha3   (16 branches), and inside each
  -- branch a by_cases tree on the phase tests  v e * star v f - a e * star a f = 0.
  -- 41 leaves in total: 26 x branch_lone, 9 x branch_pair, 4 x branch_triple,
  -- 1 x branch_quad, 1 x linarith (all four alphas zero against sum alpha = 1/4).
  -- Non-transitive test patterns are closed by T_trans; orientation by T_symm;
  -- outside-column terms by term_of_zero / term_of_diff; permanents by perm_extract.

=================  (6) `no_go_of_moments`: SIGNATURE AND BODY SHAPE  =================

set_option maxHeartbeats 4000000 in
theorem no_go_of_moments (c d : SS.BitString 6 -> ℂ)
    (hm : MomentSystem
            (Complex.normSq (c y0)) ... (Complex.normSq (c y15))
            (Complex.normSq (d z0)) ... (Complex.normSq (d z15)))
    (E0_w0 : offSum c d ef0 w0 = 0) (E0_w1 …) (E0_w3 …) (E0_w4 …) (E0_w5 …)
    (E1_w0 …) (E1_w2 …) (E1_w3 …) (E1_w4 …) (E1_w5 …)
    (E2_w0 …) (E2_w2 …) (E2_w3 …) (E2_w4 …) (E2_w5 …)
    (E3_w0 …) (E3_w5 …) (E4_w0 …) (E4_w5 …) (E5_w0 …) (E5_w5 …)
    (E6_w0 …) (E6_w4 …) (E7_w0 …) (E7_w4 …) (E8_w0 …) (E8_w4 …)
    (E9_w0 …) (E9_w3 …) (E10_w0 …) (E10_w3 …) (E11_w0 …) (E11_w3 …)
    (D12_w0 : diagBot c ef12 w0 = diagTop d ef12 w0) (D12_w4 …) (D12_w3 …) (D12_w6 …)
    (D13_w0 …) (D13_w5 …) (D13_w3 …) (D13_w7 …)
    (D14_w0 …) (D14_w5 …) (D14_w4 …) (D14_w8 …)
    : False := by
  -- hK0..hK3 from eq0..eq3 + Table31.kernel_norm, e.g.
  --   have hK0 : star (d z15) * star (star (d z15)) = c y0 * star (c y0) :=
  --     Table31.kernel_norm (c y0) (star (d z15)) (Complex.normSq (c y0))
  --       (by simpa using (by linarith [eq0 hm] :
  --         Complex.normSq (d z15) = Complex.normSq (c y0))) rfl
  -- C10..C33 := hcol_i_e c d E{i-1}_{w1|w2} E{i-1}_w5 E{i-1}_w4 E{i-1}_w3
  -- F1..F3 from fam1_i + Table31.conj4
  -- R{e}{f} := fam3_e_f c d D{mask}_*
  -- Q0..Q17 := congrArg star (fam2_k c d …) followed by
  --            simp only [star_add, star_mul', star_star, star_zero] at Q…
  exact master
    (c y0) (c y1) (c y2) (c y3) (star (d z15)) (star (d z14)) (star (d z13)) (star (d z12))
    (c y7) (c y6) (c y5) (c y4) (c y11) (c y10) (c y9) (c y8) (c y15) (c y14) (c y13) (c y12)
    hK0 hK1 hK2 hK3 F1 F2 F3
    (by linarith [hm.n0, row1 hm, row2 hm, row3 hm])
    (by linarith [row1 hm]) (by linarith [row2 hm]) (by linarith [row3 hm])
    (by linarith [col0 hm]) (by linarith [col1 hm]) (by linarith [col2 hm]) (by linarith [col3 hm])
    (fun hT => Table31.M_eq_of_raw (c y0) (c y1) (star (d z15)) (star (d z14))
        (c y7) (c y11) (c y15) (c y6) (c y10) (c y14)
        (star (d z8)) (star (d z4)) (star (d z0)) (star (d z9)) (star (d z5)) (star (d z1))
        (by simp only [star_star]; linear_combination R01)
        C10 C20 C30 C11 C21 C31 hK0 hK1 hT)
    …  (twelve such, one per ordered pair)
    (perm_of_raw (c y0) (c y1) (star (d z15)) (star (d z14))
        (c y7) (c y6) (c y11) (c y10)
        (star (d z8)) (star (d z9)) (star (d z4)) (star (d z5))
        (by linear_combination Q4) C10 C11 C20 C21)
    …  (eighteen such, one per (row pair, column pair))


## compile_output

`lake env lean C:\Users\richa\AppData\Local\Temp\claude\D--UTD-Project-purdue\e2435927-3651-49b0-acfb-31f3430ee257\scratchpad\Orbit31Work.lean` run from D:\UTD\Project_purdue\Lean_certification:

  exit = 0
  stdout+stderr = 0 bytes  (ZERO errors, ZERO warnings)
  wall time 1m30s

Intermediate checks all clean as well (each `lake env lean`, exit 0, no diagnostics):
  - expansion + column-relation + family-three block alone      : 23 s
  - branch algebra (lagrange3_real … branch_triple) alone       : 21-29 s
  - algebra + `master` alone                                    : 1m22s
  - algebra + `master` + `no_go_of_moments` alone               : 1m27s
  - full merged Orbit31Work.lean (3654 lines)                   : 1m30s

Note: `grep -c "sorry\|native_decide"` over the appended block returns 0.

## axioms

Every one of the 126 newly added theorems was checked with `#print axioms`, by appending 126
`#print axioms SixQubit.Orbit31.<name>` lines to the merged file and compiling
(scratchpad\Orbit31Axioms.lean, 1m48s, exit 0).

Result: 126 / 126 lines read

    'SixQubit.Orbit31.<name>' depends on axioms: [propext, Classical.choice, Quot.sound]

with ZERO non-conforming lines (verified by `grep -v` on the exact string, which returned
nothing, and `grep -c` on it, which returned 126).

In particular:
  SixQubit.Orbit31.no_go_of_moments depends on axioms: [propext, Classical.choice, Quot.sound]
  SixQubit.Orbit31.master           depends on axioms: [propext, Classical.choice, Quot.sound]
  SixQubit.Orbit31.branch_pair / branch_triple / branch_quad / branch_lone : same
  all 72 sg*, all 9 ex*, all 12 hcol_*, all 12 fam3_* : same

No `sorry`, no `native_decide`, no new axioms anywhere.

## unfinished

Nothing is unfinished: all five branches compile and the headline theorem
`SixQubit.Orbit31.no_go_of_moments` concludes `False` from the MomentSystem plus 33 off-diagonal
and 12 Klein-mask diagonal Knill-Laflamme hypotheses.

Three notes for the installer, none of them gaps in the proof:

1. THE BRANCH SPLIT I PROVED IS A REORGANISED (STRICTLY SMALLER) VERSION OF THE ONE IN THE TASK.
   The task's five branches (1,1,1,1)/(2,1,1)/(2,2)/(3,1)/(4) presuppose that "same phase" is an
   equivalence on all four columns.  It is not: `T_ef = v_e conj(v_f) - a_e conj(a_f)` vanishes
   automatically whenever a_e = 0 or a_f = 0, so a zero column is "same phase" as everything and
   transitivity fails there.  I therefore split first on `a_e = 0` (16 cases) and then on the
   phase tests among the live columns, where `T_trans` makes the relation a genuine equivalence.
   That collapses the five branches to four lemmas plus one arithmetic leaf:
     * branch_lone   -- any column alone among the live ones gets v_f = 0, contradicting a_f ≠ 0.
       This subsumes the whole of (1,1,1,1), of (2,1,1) and of the "lone column" half of (3,1).
     * branch_pair   -- a live class of exactly two.  Subsumes (2,2) AND the |N| = 2 case: I do
       NOT need the pair_gap inequality to be strict, because tight_pair already yields
       A + B ≤ 1/4 with A + B = alpha_e + alpha_f + 1/4, so alpha_e = alpha_f = 0, contradicting
       a_e ≠ 0.  pair_gap is still used, to force the Cauchy-Schwarz minors to vanish.
     * branch_triple -- a live class of three (fourth column has alpha = 0).  This is the (3,1)
       branch, and it is proved by the support argument, not by `partition31`.
     * branch_quad   -- all four live and same phase, by the same support argument.
     * one `linarith` -- all four alphas zero against sum alpha = 1/4.
   41 leaves in total (26 lone / 9 pair / 4 triple / 1 quad / 1 arithmetic).
   CONSEQUENCE: `Table31.all_distinct` and `Table31.partition31` are NOT used by the assembly.
   They are still true and still compile; they are simply not on the proof path.  `kernel_identity`
   is likewise unused (the branch equations come from `gram_eq` alone).  If you want a minimal
   Table31 you can drop those three; if you want them exercised, they would need a different
   (larger) case tree.

2. FOUR SMALL LEMMAS THAT LOGICALLY BELONG IN Table31.lean ARE IN Orbit31 INSTEAD, because I was
   told not to touch anything under SixQubit/.  They are `lagrange3_real` (the Lagrange/Cauchy-
   Schwarz identity in C^3, i.e. the survey's Gap 3), `perm_of_raw` (Gap 2), `perm_extract`,
   `T_trans`, `T_symm`, `same_phase_ne`, `diag_M`, `term_of_zero`, `term_of_diff`,
   `amp_eq_zero_of_v`, `v_ne_zero`, `row_wipe`, `row_wipe3`, `entry_ne`, `entry_ne3`.  Move them
   to Table31.lean if you prefer the layering; they depend only on Mathlib and on
   Table31.{sq, perm_support, perm_triple, det_perm_zero, pair_class, pair_gap, tight_pair}.

3. STALE DOCSTRINGS (I did not edit them, since both files are outside my write scope):
   * Table31.lean lines 32-35 still say "Status: partial.  The (4), (2,2) and (2,1,1) branches
     are proved on paper but not yet here, and the transcription of orbit 31 ... is not built,
     so orbit 31 is NOT yet certified.  Nothing here is imported by SixQubit.Audit."  The first
     two clauses are now false.
   * `SixQubit.Orbit31` is imported by SixQubit.lean but still NOT by SixQubit/Audit.lean;
     wiring `no_go_of_moments` into the audit is a separate (one-line) step I did not take.

Also worth recording: all 45 Knill-Laflamme hypotheses of the headline theorem are legal
weight-<= 2 Paulis.  The nine new dressings give X_0Z_5, X_0Z_4, X_0Z_3, X_1Z_5, X_1Z_4, X_1Z_3,
X_2Z_5, X_2Z_4, X_2Z_3; the twelve Klein conditions give X_4X_5, Y_4X_5, X_4Y_5, Y_4Y_5 and the
two analogous quadruples on qubits {3,5} and {3,4}.

## survey

## index_map

FILES (absolute): D:\UTD\Project_purdue\Lean_certification\SixQubit\Orbit31.lean (1777 lines, ends with `end` / `end SixQubit.Orbit31`; the `noncomputable section` opened at line 26 closes at line 1775 — new material goes before it). D:\UTD\Project_purdue\Lean_certification\SixQubit\Table31.lean (490 lines).

=== BOTTOM POSITIONS (from the verbatim `def y<k>` comments, lines 30-45) ===
y0  = 000000 = A0    -> row A , col 0
y1  = 000011 = A1    -> row A , col 1
y2  = 000101 = A2    -> row A , col 2
y3  = 000110 = A3    -> row A , col 3
y4  = 011001 = B13   -> row B1, col 3
y5  = 011010 = B12   -> row B1, col 2
y6  = 011100 = B11   -> row B1, col 1
y7  = 011111 = B10   -> row B1, col 0
y8  = 101001 = B23   -> row B2, col 3
y9  = 101010 = B22   -> row B2, col 2
y10 = 101100 = B21   -> row B2, col 1
y11 = 101111 = B20   -> row B2, col 0
y12 = 110001 = B33   -> row B3, col 3
y13 = 110010 = B32   -> row B3, col 2
y14 = 110100 = B31   -> row B3, col 1
y15 = 110111 = B30   -> row B3, col 0

THE COLUMN REVERSAL IS REAL: the A row is in natural order y0,y1,y2,y3 = cols 0,1,2,3 but every B row is REVERSED: (y4..y7)=(col3,col2,col1,col0), (y8..y11)=(3,2,1,0), (y12..y15)=(3,2,1,0).  Independently confirmed by `col0` (uses q0,q7,q11,q15), `col1` (q1,q6,q10,q14), `col2` (q2,q5,q9,q13), `col3` (q3,q4,q8,q12).

Table (row, col) -> y:
        col0  col1  col2  col3
  A      y0    y1    y2    y3
  B1     y7    y6    y5    y4
  B2     y11   y10   y9    y8
  B3     y15   y14   y13   y12

Amplitude naming for the assembly:
  a0=c y0, a1=c y1, a2=c y2, a3=c y3
  b_{1,0}=c y7, b_{1,1}=c y6, b_{1,2}=c y5, b_{1,3}=c y4
  b_{2,0}=c y11, b_{2,1}=c y10, b_{2,2}=c y9, b_{2,3}=c y8
  b_{3,0}=c y15, b_{3,1}=c y14, b_{3,2}=c y13, b_{3,3}=c y12

=== COMPLEMENT PAIRING (hat lemmas, lines 81-96) ===
`theorem hat<k> : SS.bxor y<k> (SS.ones 6) = z<15-k> := by decide` for k=0..15.  So z_j = complement of y_{15-j}:
  z0 =comp(y15)=comp(B30)  z1 =comp(y14)=comp(B31)  z2 =comp(y13)=comp(B32)  z3 =comp(y12)=comp(B33)
  z4 =comp(y11)=comp(B20)  z5 =comp(y10)=comp(B21)  z6 =comp(y9) =comp(B22)  z7 =comp(y8) =comp(B23)
  z8 =comp(y7) =comp(B10)  z9 =comp(y6) =comp(B11)  z10=comp(y5) =comp(B12)  z11=comp(y4) =comp(B13)
  z12=comp(y3) =comp(A3)   z13=comp(y2) =comp(A2)   z14=comp(y1) =comp(A1)   z15=comp(y0) =comp(A0)

Note the top table is NOT reversed on the B rows and IS reversed on the A row:
        col0  col1  col2  col3
  A      z15   z14   z13   z12
  B1     z8    z9    z10   z11
  B2     z4    z5    z6    z7
  B3     z0    z1    z2    z3

KEY OBJECTS (define these exactly this way):
  v0 := star (d z15),  v1 := star (d z14),  v2 := star (d z13),  v3 := star (d z12)
  u_{1,e} := star (d z8), star (d z9),  star (d z10), star (d z11)   for e=0,1,2,3
  u_{2,e} := star (d z4), star (d z5),  star (d z6),  star (d z7)
  u_{3,e} := star (d z0), star (d z1),  star (d z2),  star (d z3)
(so `d z15 = star v0`, and `star v_e = star (star (d z..))` needs `star_star`.)

  alpha_e = Complex.normSq (c y_{Ae}),  beta_{i,e} = Complex.normSq (c y_{B i e})
  M_ef    = b_{1,e}*star b_{1,f} + b_{2,e}*star b_{2,f} + b_{3,e}*star b_{3,f}

MOMENT-VARIABLE CONVENTION: the whole file is stated in q0..q15 / r0..r15; the assembly instantiates `MomentSystem (normSq (c y0)) ... (normSq (c y15)) (normSq (d z0)) ... (normSq (d z15))`, exactly as `Orbit29.no_go_of_moments` does (see D:\UTD\Project_purdue\Lean_certification\SixQubit\Orbit29.lean:1210-1213).  So q_k = normSq (c y_k), r_j = normSq (d z_j).

## interfaces

=== A. ORBIT31.LEAN, VERBATIM ===

(1) FAMILY ONE (lines 444-469).  Note the hypotheses are `offSum c d ef_i w_j = 0`.

theorem fam1_1 (c d : SS.BitString 6 -> ℂ)
    (h0 : offSum c d ef0 w0 = 0)
    (h1 : offSum c d ef0 w1 = 0)
    : star (c y4) * d z12 + star (c y5) * d z13 + star (c y6) * d z14 + star (c y7) * d z15 = 0

theorem fam1_2 (c d : SS.BitString 6 -> ℂ)
    (h0 : offSum c d ef1 w0 = 0)
    (h1 : offSum c d ef1 w2 = 0)
    : star (c y8) * d z12 + star (c y9) * d z13 + star (c y10) * d z14 + star (c y11) * d z15 = 0

theorem fam1_3 (c d : SS.BitString 6 -> ℂ)
    (h0 : offSum c d ef2 w0 = 0)
    (h1 : offSum c d ef2 w2 = 0)
    : star (c y12) * d z12 + star (c y13) * d z13 + star (c y14) * d z14 + star (c y15) * d z15 = 0

READING: fam1_1 = star(b_{1,3})*star(v3) + star(b_{1,2})*star(v2) + star(b_{1,1})*star(v1) + star(b_{1,0})*star(v0) = 0.
`Table31.conj4` applied with (b0,b1,b2,b3) := (c y4, c y5, c y6, c y7) and (x0,x1,x2,x3) := (d z12, d z13, d z14, d z15) yields
  c y4 * v3 + c y5 * v2 + c y6 * v1 + c y7 * v0 = 0  (since star (d z12) is literally v3, etc.)
i.e. b_{1,0} v0 + b_{1,1} v1 + b_{1,2} v2 + b_{1,3} v3 = 0 after reordering by `linear_combination`.  Same for rows 2 and 3.

(2) FAMILY TWO (lines 883-1044).  Eighteen lemmas = 3 row-pairs x 6 column-pairs.  Representative:

theorem fam2_0 (c d : SS.BitString 6 -> ℂ)
    (h0 : offSum c d ef3 w0 = 0)
    (h1 : offSum c d ef3 w5 = 0)
    : star (c y10) * d z0 + star (c y11) * d z1 + star (c y14) * d z4 + star (c y15) * d z5 = 0

UNIFORM SHAPE.  For row pair {i,j} (i<j) and column pair {e,f} each fam2 says
   star(b_{i,f})*star(u_{j,e}) + star(b_{i,e})*star(u_{j,f}) + star(b_{j,f})*star(u_{i,e}) + star(b_{j,e})*star(u_{i,f}) = 0.
Complete decode (row pair | column pair | hypotheses):
 fam2_0  {2,3} {0,1} (ef3 w0, ef3 w5)   fam2_1  {2,3} {2,3} (ef3 w0, ef3 w5)
 fam2_2  {1,3} {0,1} (ef4 w0, ef4 w5)   fam2_3  {1,3} {2,3} (ef4 w0, ef4 w5)
 fam2_4  {1,2} {0,1} (ef5 w0, ef5 w5)   fam2_5  {1,2} {2,3} (ef5 w0, ef5 w5)
 fam2_6  {2,3} {0,2} (ef6 w0, ef6 w4)   fam2_7  {2,3} {1,3} (ef6 w0, ef6 w4)
 fam2_8  {1,3} {0,2} (ef7 w0, ef7 w4)   fam2_9  {1,3} {1,3} (ef7 w0, ef7 w4)
 fam2_10 {1,2} {0,2} (ef8 w0, ef8 w4)   fam2_11 {1,2} {1,3} (ef8 w0, ef8 w4)
 fam2_12 {2,3} {0,3} (ef9 w0, ef9 w3)   fam2_13 {2,3} {1,2} (ef9 w0, ef9 w3)
 fam2_14 {1,3} {0,3} (ef10 w0, ef10 w3) fam2_15 {1,3} {1,2} (ef10 w0, ef10 w3)
 fam2_16 {1,2} {0,3} (ef11 w0, ef11 w3) fam2_17 {1,2} {1,2} (ef11 w0, ef11 w3)

(3) MOMENT FACTS.

theorem eq0 {q0 ... r15 : Real} (h : MomentSystem q0 ... r15) : -q0 + r15 = 0
General: `eq<k> : -q<k> + r<15-k> = 0`, k = 0..15.  So normSq (d z_{15-k}) = normSq (c y_k), i.e. |v_e| = |a_e| and |u_{i,e}| = |b_{i,e}|.

theorem row1 ... : q4 + q5 + q6 + q7 - 1/4 = 0
theorem row2 ... : q10 + q11 + q8 + q9 - 1/4 = 0     (NOTE the odd term order)
theorem row3 ... : q12 + q13 + q14 + q15 - 1/4 = 0

theorem col0 ... : q0 - q11 - q15 - q7 + 1/8 = 0
theorem col1 ... : q1 - q10 - q14 - q6 + 1/8 = 0
theorem col2 ... : -q13 + q2 - q5 - q9 + 1/8 = 0
theorem col3 ... : -q12 + q3 - q4 - q8 + 1/8 = 0
All eight take the single hypothesis `(h : MomentSystem q0 ... r15)` with all 32 reals implicit.

(4) MOMENTSYSTEM (line 100) field names, in order:
 n0 n1 m1 m2 m3 m4 m5 m6 c12 c13 c14 c15 c16 c23 c24 c25 c26 c34 c35 c36 c45 c46 c56
 nq0..nq15 nr0..nr15  (the nq/nr are `0 ≤ q_k` / `0 ≤ r_j`).
 n0 : q0 + ... + q15 = 1.   sum alpha = 1/4 is NOT a named lemma: derive by `linarith [n0, row1 h, row2 h, row3 h]`.

(5) MASKS AND DRESSINGS (all `def`s):
 ef0=100000 ef1=010000 ef2=001000
 ef3=100100 ef4=010100 ef5=001100 ef6=100010 ef7=010010 ef8=001010 ef9=100001 ef10=010001 ef11=001001
 ef12=000011 ef13=000101 ef14=000110  (Klein masks)
 w0=000000 w1=010000 w2=100000 w3=000001 w4=000010 w5=000100 w6=000011 w7=000101 w8=000110

(6) EXISTING EXPANSION LEMMAS.
 offSum: ex0_w0, ex0_w1, ex1_w0, ex1_w2, ex2_w0, ex2_w2, ex3_w0, ex3_w5, ex4_w0, ex4_w5, ex5_w0, ex5_w5, ex6_w0, ex6_w4, ex7_w0, ex7_w4, ex8_w0, ex8_w4, ex9_w0, ex9_w3, ex10_w0, ex10_w3, ex11_w0, ex11_w3.  Signature `theorem exN_wM (c d : SS.BitString 6 -> ℂ) : offSum c d efN wM = <8-term signed sum>`.
 diagBot/diagTop: dbot12_w0 dtop12_w0 dbot12_w4 dtop12_w4 dbot12_w3 dtop12_w3 dbot12_w6 dtop12_w6 dbot13_w0 dtop13_w0 dbot13_w5 dtop13_w5 dbot13_w3 dtop13_w3 dbot13_w7 dtop13_w7 dbot14_w0 dtop14_w0 dbot14_w5 dtop14_w5 dbot14_w4 dtop14_w4 dbot14_w8 dtop14_w8.  Signature `theorem dbotK_wM (c : SS.BitString 6 -> ℂ) : diagBot c efK wM = <16-term signed sum>` (dtop likewise with d and z).
 Supporting `decide` facts already present: incidence0..incidence11, diagB12/T12/B13/T13/B14/T14, all fl*_*, dfb*_*, dft*_*, and sg/dsb/dst sign facts ONLY for the dressings listed above.

=== B. TABLE31.LEAN, VERBATIM SIGNATURES THE ASSEMBLY CALLS ===
(namespace SixQubit.Table31, `open scoped ComplexConjugate`)

theorem sq (z : ℂ) : z * star z = (Complex.normSq z : ℂ)

theorem conj4 (b0 b1 b2 b3 x0 x1 x2 x3 : ℂ)
    (h : star b0 * x0 + star b1 * x1 + star b2 * x2 + star b3 * x3 = 0)
    : b0 * star x0 + b1 * star x1 + b2 * star x2 + b3 * star x3 = 0

theorem gram_eq (b0 b1 b2 : ℂ) (c0 c1 c2 : ℂ) (d0 d1 d2 : ℂ) (e0 e1 e2 : ℂ)
    (v0 v1 v2 v3 : ℂ) (f0 f1 f2 : ℂ)
    (h0 : b0 * v0 + c0 * v1 + d0 * v2 + e0 * v3 = 0)
    (h1 : b1 * v0 + c1 * v1 + d1 * v2 + e1 * v3 = 0)
    (h2 : b2 * v0 + c2 * v1 + d2 * v2 + e2 * v3 = 0)
    : v0 * (b0 * star f0 + b1 * star f1 + b2 * star f2)
    + v1 * (c0 * star f0 + c1 * star f1 + c2 * star f2)
    + v2 * (d0 * star f0 + d1 * star f1 + d2 * star f2)
    + v3 * (e0 * star f0 + e1 * star f1 + e2 * star f2) = 0
  [INDEXING: subscript 0/1/2 = ROW (B1,B2,B3); letter b/c/d/e = COLUMN 0/1/2/3.
   So h0 is the row-B1 relation, and (f0,f1,f2) is column f's B-vector.
   Coefficient of v_e in the conclusion is exactly M_ef.]

theorem kernel_identity
    (b10 b11 b12 b13 b20 b21 b22 b23 b30 b31 b32 b33 : ℂ) (v0 v1 v2 v3 : ℂ)
    (h1 : b10 * v0 + b11 * v1 + b12 * v2 + b13 * v3 = 0)
    (h2 : b20 * v0 + b21 * v1 + b22 * v2 + b23 * v3 = 0)
    (h3 : b30 * v0 + b31 * v1 + b32 * v2 + b33 * v3 = 0)
    (M00 M01 M02 M03 M10 M11 M12 M13 M20 M21 M22 M23 M30 M31 M32 M33 : ℂ)
    (e00 : M00 = b10 * star b10 + b20 * star b20 + b30 * star b30)  ... (e01..e33 analogous, e_ef : M_ef = b1e*star b1f + b2e*star b2f + b3e*star b3f)
    : v0 * star v0 * M00 + v0 * star v1 * M01 + ... + v3 * star v3 * M33 = 0
  [here bIJ has I = row index 1..3, J = column 0..3]

theorem all_distinct (v0 v1 v2 v3 : ℂ)
    (hS : v0 * star v0 + v1 * star v1 + v2 * star v2 + v3 * star v3 = (1/4 : ℂ))
    (hid : <the kernel_identity value with M_ee := v_e*star v_e + 1/8 and M_ef := star v_e * v_f> = 0) : False

theorem partition31 (a0 a1 a2 a3 : Real)
    (n0 : 0 ≤ a0) (n1 : 0 ≤ a1) (n2 : 0 ≤ a2) (n3 : 0 ≤ a3)
    (hS : a0 + a1 + a2 + a3 = 1/4)
    (hid : a0*a0 + a1*a1 + a2*a2 + a3*a3 + (1/8)*(a0+a1+a2+a3) + 2*a3*(a0+a1+a2) = 0) : False

theorem lone_column (vf : ℂ) (af S : Real) (hS : S = 1/4)
    (h : vf * ((af : ℂ) + 1/8 + ((S : ℂ) - (af : ℂ))) = 0) : vf = 0

theorem pair_class (v0 v1 M01 M10 : ℂ) (a0 a1 s : Real)
    (hv : ¬ (v0 = 0 ∧ v1 = 0))
    (h0 : v0 * ((a0 : ℂ) + 1/8 + ((1/4 : ℂ) - (s : ℂ))) + v1 * M10 = 0)
    (h1 : v1 * ((a1 : ℂ) + 1/8 + ((1/4 : ℂ) - (s : ℂ))) + v0 * M01 = 0)
    : ((a0 : ℂ) + 1/8 + (1/4 - (s : ℂ))) * ((a1 : ℂ) + 1/8 + (1/4 - (s : ℂ))) = M01 * M10

theorem pair_gap (a0 a1 s : Real) (hs : s = a0 + a1)
    : (a0 + 1/8 + (1/4 - s)) * (a1 + 1/8 + (1/4 - s)) - (a0 + 1/8) * (a1 + 1/8) = 1/8 - s/2

theorem tight_pair (p0 p1 p2 q0 q1 q2 A B : Real)
    (_np0 : 0 ≤ p0) (_np1 : 0 ≤ p1) (_np2 : 0 ≤ p2) (_nq0 : 0 ≤ q0) (_nq1 : 0 ≤ q1) (_nq2 : 0 ≤ q2)
    (z01 : p0*q1 = 0) (z02 : p0*q2 = 0) (z10 : p1*q0 = 0) (z12 : p1*q2 = 0) (z20 : p2*q0 = 0) (z21 : p2*q1 = 0)
    (hA : p0+p1+p2 = A) (hB : q0+q1+q2 = B) (hApos : 0 < A) (hBpos : 0 < B)
    (r0 : p0+q0 ≤ 1/4) (r1 : p1+q1 ≤ 1/4) (r2 : p2+q2 ≤ 1/4) : A + B ≤ 1/4

theorem det_perm_zero (x y z w : ℂ) (hd : x*w - y*z = 0) (hp : x*w + y*z = 0) : x*w = 0 ∧ y*z = 0

theorem perm_triple (be bf bg se sf sg : ℂ)
    (pef : be*sf + bf*se = 0) (peg : be*sg + bg*se = 0) (pfg : bf*sg + bg*sf = 0) : bf*bg*se = 0

theorem perm_support (be bf se sf : ℂ) (hbe : be ≠ 0) (hse : se = 0)
    (pef : be*sf + bf*se = 0) : sf = 0

theorem kernel_norm (a v : ℂ) (al : Real) (hv : Complex.normSq v = al) (ha : Complex.normSq a = al)
    : v * star v = a * star a

theorem kernel_zero (a v : ℂ) (al : Real) (hv : Complex.normSq v = al) (ha : Complex.normSq a = al)
    (h : v = 0) : Complex.normSq a = 0

theorem M_eq_of_raw
    (ae af ve vf be1 be2 be3 bf1 bf2 bf3 ue1 ue2 ue3 uf1 uf2 uf3 : ℂ)
    (hFam : (be1 * star bf1 + be2 * star bf2 + be3 * star bf3) + star ae * af
              = (ue1 * star uf1 + ue2 * star uf2 + ue3 * star uf3) + star ve * vf)
    (hColE1 : ue1 * ae = ve * be1) (hColE2 : ue2 * ae = ve * be2) (hColE3 : ue3 * ae = ve * be3)
    (hColF1 : uf1 * af = vf * bf1) (hColF2 : uf2 * af = vf * bf2) (hColF3 : uf3 * af = vf * bf3)
    (hKe : ve * star ve = ae * star ae) (hKf : vf * star vf = af * star af)
    (hT : ve * star vf - ae * star af ≠ 0)
    : be1 * star bf1 + be2 * star bf2 + be3 * star bf3 = star ve * vf

theorem key_of_raw  -- same hypotheses minus hT
    : ((be1*star bf1 + be2*star bf2 + be3*star bf3) - star ve * vf) * (ve * star vf - ae * star af) = 0

theorem hH3_of_raw (…hFam, hColE1..3, hColF1..3…)
    : (be1*star bf1 + be2*star bf2 + be3*star bf3) * (star vf * ve - star af * ae)
      = -(ae * star af) * (vf * star ve - af * star ae)

theorem key (ae af ve vf M : ℂ) (hKe) (hKf) (hH3) : (M - star ve * vf) * (star vf * ve - star af * ae) = 0
theorem M_eq (ae af ve vf M : ℂ) (hKe) (hKf) (hH3) (hT : star vf * ve - star af * ae ≠ 0) : M = star ve * vf

theorem row_key (ae af ve vf p q p' q' be1 be2 be3 bf1 bf2 bf3 ue1 ue2 ue3 uf1 uf2 uf3 : ℂ)
    (hFam …) (hColE1 : ue1 * p = q * be1) (hColE2) (hColE3)
    (hColF1 : uf1 * p' = q' * bf1) (hColF2) (hColF3)
    (hPe : star ve * q = star ae * p) (hPf : vf * star q' = af * star p')
    : ((be1*star bf1 + be2*star bf2 + be3*star bf3) - star ve * vf) * (q * star q' - p * star p') = 0

theorem phase_transfer (ae ve b u : ℂ) (hCol : u * ae = ve * b) (hMom : u * star u = b * star b) (hb : b ≠ 0)
    : star ve * u = star ae * b

theorem T_eq_zero_of_ae (ae af ve vf : ℂ) (h0 : ae = 0) (hKe : ve * star ve = ae * star ae)
    : star vf * ve - star af * ae = 0
theorem T_eq_zero_of_af (ae af ve vf : ℂ) (h0 : af = 0) (hKf : vf * star vf = af * star af)
    : star vf * ve - star af * ae = 0

def SamePhase (ve af vf ae : ℂ) : Prop := ve * af = vf * ae

NOTE: `M_eq_of_raw.hT` is `ve * star vf - ae * star af ≠ 0` while `key/M_eq.hT` is `star vf * ve - star af * ae ≠ 0`.  These are ring-equal but SYNTACTICALLY different; convert with `mul_comm`/`linear_combination`.

=== C. THE EXACT FAMILY-THREE RECIPE (verified term by term) ===
hFam for the ORDERED pair (e,f) is produced by ONE Walsh combination of four ALREADY-PRESENT dbot/dtop lemmas.  Every needed dbot/dtop lemma exists; the hypotheses to add to `no_go_of_moments` are the four KL equalities `diagBot c efK wM = diagTop d efK wM` per mask.

MASK ef12 (dressings w0, w4, w3, w6) — order (w0,w4,w3,w6):
  (1/4)(+w0+w4+w3+w6): bottom picks {y0,y6,y10,y14}, top picks {z0,z4,z8,z14}  =>  (e,f) = (1,0)
  (1/4)(+w0+w4-w3-w6): bottom {y2,y4,y8,y12}, top {z2,z6,z10,z12}              =>  (e,f) = (3,2)
  (1/4)(+w0-w4+w3-w6): bottom {y3,y5,y9,y13}, top {z3,z7,z11,z13}              =>  (e,f) = (2,3)
  (1/4)(+w0-w4-w3+w6): bottom {y1,y7,y11,y15}, top {z1,z5,z9,z15}              =>  (e,f) = (0,1)
MASK ef13 (dressings w0, w5, w3, w7) — order (w0,w5,w3,w7):
  (++++): bottom {y0,y5,y9,y13}, top {z0,z4,z8,z13}   => (2,0)
  (++--): bottom {y1,y4,y8,y12}, top {z1,z5,z9,z12}   => (3,1)
  (+-+-): bottom {y3,y6,y10,y14}, top {z3,z7,z11,z14} => (1,3)
  (+--+): bottom {y2,y7,y11,y15}, top {z2,z6,z10,z15} => (0,2)
MASK ef14 (dressings w0, w5, w4, w8) — order (w0,w5,w4,w8):
  (++++): bottom {y0,y4,y8,y12}, top {z0,z4,z8,z12}   => (3,0)
  (++--): bottom {y1,y5,y9,y13}, top {z1,z5,z9,z13}   => (2,1)
  (+-+-): bottom {y2,y6,y10,y14}, top {z2,z6,z10,z14} => (1,2)
  (+--+): bottom {y3,y7,y11,y15}, top {z3,z7,z11,z15} => (0,3)

Worked instance, (e,f) = (1,0) from ef12:
  (1/4)(dbot12_w0 + dbot12_w4 + dbot12_w3 + dbot12_w6)
     = star (c y1) * c y0 + star (c y7) * c y6 + star (c y11) * c y10 + star (c y15) * c y14
  (1/4)(dtop12_w0 + dtop12_w4 + dtop12_w3 + dtop12_w6)
     = star (d z1) * d z0 + star (d z5) * d z4 + star (d z9) * d z8 + star (d z15) * d z14
Equating (KL) and matching `M_eq_of_raw`'s hFam with
  ae := c y1, af := c y0, be_i := (c y6, c y10, c y14), bf_i := (c y7, c y11, c y15),
  ve := star (d z14), vf := star (d z15),
  ue_i := (star (d z9), star (d z5), star (d z1)), uf_i := (star (d z8), star (d z4), star (d z0))
gives hFam up to `ring` / `star_star` only.  The mixed convention in hFam (B-part `be*star bf`, A-part `star ae * af`) is EXACTLY what the Klein condition produces, because the A row and the B rows have opposite column order.

=== D. THE EXACT COLUMN-RELATION RECIPE (the 12 two-term relations) ===
The needed hCol facts are `u_{i,e} * a_e = v_e * b_{i,e}`, i.e. in raw terms
  star (d z_{u}) * c y_{A_e} = star (d z_{v_e}) * c y_{B_{i,e}}.
Each is the conjugate of a TWO-TERM off-diagonal relation obtained from mask ef_{i-1} (row i) with FOUR dressings.  Coefficient vectors (over the eight incidence terms in the order listed by the ex-lemmas):

Row B1, mask ef0, dressings (w1, w5, w4, w3), terms z8..z15 <-> y0..y7:
  col0 (1/4)(+w1+w5+w4+w3): star (c y0) * d z8  - star (c y7) * d z15 = 0
  col1 (1/4)(+w1+w5-w4-w3): star (c y1) * d z9  - star (c y6) * d z14 = 0
  col2 (1/4)(+w1-w5+w4-w3): star (c y2) * d z10 - star (c y5) * d z13 = 0
  col3 (1/4)(+w1-w5-w4+w3): star (c y3) * d z11 - star (c y4) * d z12 = 0
Row B2, mask ef1, dressings (w2, w5, w4, w3), terms z4,z5,z6,z7,z12,z13,z14,z15 <-> y0,y1,y2,y3,y8,y9,y10,y11:
  col0 (+w2+w5+w4+w3)/4: star (c y0) * d z4 - star (c y11) * d z15 = 0
  col1 (+w2+w5-w4-w3)/4: star (c y1) * d z5 - star (c y10) * d z14 = 0
  col2 (+w2-w5+w4-w3)/4: star (c y2) * d z6 - star (c y9)  * d z13 = 0
  col3 (+w2-w5-w4+w3)/4: star (c y3) * d z7 - star (c y8)  * d z12 = 0
Row B3, mask ef2, dressings (w2, w5, w4, w3), terms z0,z1,z2,z3,z12..z15 <-> y0,y1,y2,y3,y12..y15:
  col0 (+w2+w5+w4+w3)/4: star (c y0) * d z0 - star (c y15) * d z15 = 0
  col1 (+w2+w5-w4-w3)/4: star (c y1) * d z1 - star (c y14) * d z14 = 0
  col2 (+w2-w5+w4-w3)/4: star (c y2) * d z2 - star (c y13) * d z13 = 0
  col3 (+w2-w5-w4+w3)/4: star (c y3) * d z3 - star (c y12) * d z12 = 0
Conjugating (congrArg star + `simp only [star_sub, star_mul', star_star, star_zero]`) turns e.g. the first into
  star (d z8) * c y0 = star (d z15) * c y7, i.e. u_{1,0} * a0 = v0 * b_{1,0} = hColE1 for column 0.
All twelve Paulis are legal weight-2 errors: X_0Z_1, X_0Z_3, X_0Z_4, X_0Z_5, X_1Z_0, X_1Z_3, X_1Z_4, X_1Z_5, X_2Z_0, X_2Z_3, X_2Z_4, X_2Z_5.

=== E. THE FAMILY-TWO -> PERMANENT REDUCTION (algebra, verified) ===
Conjugating fam2 for rows {i,j}, columns {e,f} gives
  b_{i,f} u_{j,e} + b_{i,e} u_{j,f} + b_{j,f} u_{i,e} + b_{j,e} u_{i,f} = 0.
Multiplying by a_e * a_f and substituting the four hCol relations gives the DIVISION-FREE identity
  (v_e * a_f + v_f * a_e) * (b_{i,e} * b_{j,f} + b_{i,f} * b_{j,e}) = 0,
which is the vanishing permanent that `det_perm_zero`, `perm_triple` and `perm_support` consume.

## gaps

Orbit31.lean compiles and covers families one and two completely, and it has EVERY dbot/dtop expansion the family-three step needs.  Four things are genuinely missing.  Gap 1 is the one the task flagged; Gaps 2-4 are additional and equally blocking.

GAP 1 (BIGGEST, and the answer to question 3): THE `hCol*` HYPOTHESES OF `M_eq_of_raw` DO NOT EXIST, AND THE EXPANSION LEMMAS THAT WOULD PRODUCE THEM DO NOT EXIST EITHER.
 - `hFam` IS obtainable with no new expansion lemmas: the twelve ordered-pair hFam facts follow from `dbot12/13/14_*` and `dtop12/13/14_*` (all 24 present) by the Walsh combinations tabulated in section C, each a one-line `rw [dbotK_wM, dtopK_wM, ...] at h0 h1 h2 h3; linear_combination (1/4)*h0 ± (1/4)*h1 ± (1/4)*h2 ± (1/4)*h3` plus `ring`/`star_star`.  Add four KL hypotheses per Klein mask to the top-level theorem: `diagBot c ef12 w0 = diagTop d ef12 w0`, likewise w4, w3, w6; `ef13` with w0, w5, w3, w7; `ef14` with w0, w5, w4, w8.  All twelve are legal weight-2 Paulis.
 - `hKe`/`hKf` ARE obtainable: `eq0`..`eq3` give normSq (d z_{15-k}) = normSq (c y_k); combine with `Table31.sq` (or `kernel_norm` after `Complex.normSq_conj`) to get `ve * star ve = ae * star ae`.  Note `ve = star (d z..)` so you need `Complex.normSq (star w) = Complex.normSq w`.
 - `hColE1..3`, `hColF1..3` ARE NOT AVAILABLE ANYWHERE.  There is no `rho`-constant-along-columns lemma in either file, and grep confirms nothing else in the project provides one.  To build them you must add to Orbit31.lean, before the closing `end`:
     (a) 72 new `by decide` sign facts: `sg0_w3_8 .. sg0_w3_15`, `sg0_w4_8..15`, `sg0_w5_8..15`; `sg1_w3_j`, `sg1_w4_j`, `sg1_w5_j` for j ∈ {4,5,6,7,12,13,14,15}; `sg2_w3_j`, `sg2_w4_j`, `sg2_w5_j` for j ∈ {0,1,2,3,12,13,14,15}.  Truth values (uniform, only the z index matters): `SS.bdot w5 z = true` exactly for z ∈ {z2,z3,z6,z7,z10,z11,z14,z15}; `SS.bdot w4 z = true` exactly for z ∈ {z1,z3,z5,z7,z9,z11,z13,z15}; `SS.bdot w3 z = true` exactly for z ∈ {z1,z2,z5,z6,z9,z10,z12,z15}.
     (b) 9 new expansion lemmas `ex0_w3, ex0_w4, ex0_w5, ex1_w3, ex1_w4, ex1_w5, ex2_w3, ex2_w4, ex2_w5`, each a copy of the existing `ex0_w1`-style proof (`unfold offSum; rw [incidenceN]; rw [Finset.sum_insert (by decide), ...]; rw [flN_*]; simp only [sgN_wM_*, SixQubit.signMul_true, SixQubit.signMul_false]; try ring`).  `incidence0/1/2` and `fl0_*/fl1_*/fl2_*` already exist and are reused unchanged.  Explicit right-hand sides:
        ex0_w3 = +y0z8 -y1z9 -y2z10 +y3z11 -y4z12 +y5z13 +y6z14 -y7z15
        ex0_w4 = +y0z8 -y1z9 +y2z10 -y3z11 +y4z12 -y5z13 +y6z14 -y7z15
        ex0_w5 = +y0z8 +y1z9 -y2z10 -y3z11 +y4z12 +y5z13 -y6z14 -y7z15
        ex1_w3 = +y0z4 -y1z5 -y2z6 +y3z7 -y8z12 +y9z13 +y10z14 -y11z15
        ex1_w4 = +y0z4 -y1z5 +y2z6 -y3z7 +y8z12 -y9z13 +y10z14 -y11z15
        ex1_w5 = +y0z4 +y1z5 -y2z6 -y3z7 +y8z12 +y9z13 -y10z14 -y11z15
        ex2_w3 = +y0z0 -y1z1 -y2z2 +y3z3 -y12z12 +y13z13 +y14z14 -y15z15
        ex2_w4 = +y0z0 -y1z1 +y2z2 -y3z3 +y12z12 -y13z13 +y14z14 -y15z15
        ex2_w5 = +y0z0 +y1z1 -y2z2 -y3z3 +y12z12 +y13z13 -y14z14 -y15z15
       (writing `yAzB` for `star (c yA) * d zB`).
     (c) 12 new `colrel_i_e` lemmas (the "twelve two-term relations"), each a `linear_combination (1/4)*h0 ± (1/4)*h1 ± (1/4)*h2 ± (1/4)*h3` from the four ex-lemmas, with the sign vectors in section D.  Then 12 conjugated `hCol` forms.
     (d) 9 new hypotheses on the top-level theorem: `offSum c d ef0 w3/w4/w5 = 0`, `offSum c d ef1 w3/w4/w5 = 0`, `offSum c d ef2 w3/w4/w5 = 0` (`offSum c d ef0 w1 = 0`, `offSum c d ef1 w2 = 0`, `offSum c d ef2 w2 = 0` are already hypotheses of fam1_1/2/3).

GAP 2: NO LEMMA TURNS FAMILY TWO INTO A VANISHING PERMANENT.  `det_perm_zero`, `perm_triple`, `perm_support` all take `b_{i,e} b_{j,f} + b_{i,f} b_{j,e} = 0` as an input, but nothing derives it.  Table31 needs a new `row_key`-style lemma, e.g.
  theorem perm_of_raw (ae af ve vf bie bif bje bjf uie uif uje ujf : ℂ)
    (hFam2 : bif * uje + bie * ujf + bjf * uie + bje * uif = 0)
    (hCie : uie * ae = ve * bie) (hCif : uif * af = vf * bif)
    (hCje : uje * ae = ve * bje) (hCjf : ujf * af = vf * bjf)
    : (ve * af + vf * ae) * (bie * bjf + bif * bje) = 0
provable by `linear_combination` (verified on paper: multiply hFam2 by ae*af and substitute).  Plus the extraction corollary under `ve * af + vf * ae ≠ 0` (which in the same-phase case reduces to `ve ≠ 0` and `af ≠ 0`, i.e. alpha_e ≠ 0 and alpha_f ≠ 0 via `kernel_zero`).

GAP 3: NO LAGRANGE / TIGHT-CAUCHY-SCHWARZ STEP.  `pair_class` outputs the scalar equality |X_e|^2|X_f|^2 = M_ef*M_fe, but `tight_pair` and `det_perm_zero` need the 2x2 MINORS `b_{i,e} b_{j,f} - b_{i,f} b_{j,e} = 0`.  The bridge (Lagrange identity for two vectors in C^3: |X|^2|Y|^2 - |<X,Y>|^2 = sum_{i<j} |x_i y_j - x_j y_i|^2, hence each minor vanishes) is not in Table31.  A new lemma is required, e.g.
  theorem minors_zero (x1 x2 x3 y1 y2 y3 : ℂ)
    (h : (normSq x1 + normSq x2 + normSq x3) * (normSq y1 + normSq y2 + normSq y3)
         = normSq (x1*star y1 + x2*star y2 + x3*star y3))
    : x1*y2 - x2*y1 = 0 ∧ x1*y3 - x3*y1 = 0 ∧ x2*y3 - x3*y2 = 0
  plus the step from `pair_class`'s complex product form to that real form.  Also note `tight_pair` wants `p_i q_j = 0` for i ≠ j in SQUARED-MODULUS (Real) form, so `det_perm_zero`'s complex `x*w = 0 ∧ y*z = 0` has to be pushed through `normSq`.

GAP 4: SMALL DERIVED FACTS WITH NO NAMED LEMMA (easy, but not present):
  - `alpha_0 + alpha_1 + alpha_2 + alpha_3 = 1/4`: derive by `linarith` from `MomentSystem.n0` and `row1/row2/row3`.
  - `M_ff = alpha_f + 1/8` as a COMPLEX identity: from `col_f` plus `Table31.sq`/`SixQubit.star_mul_self` and `push_cast`.
  - `sum_e normSq v_e = 1/4` (needed to turn `sum_{e not in class} v_e * star v_e` into `1/4 - s_c`): from eq0..eq3 plus the previous item.
  - The Cauchy-Schwarz-tight budget inputs of `tight_pair` (`p_i + q_i ≤ 1/4`) come from row1/row2/row3 plus nq nonnegativity; and `A + B = 1/4` from col_e + col_f, contradicting the conclusion `A + B ≤ 1/4` only when strict — check the arithmetic of the (2,1,1) branch carefully, since `tight_pair` concludes `A + B ≤ 1/4` and the contradiction must come from `A + B = alpha_e + alpha_f + 1/4 > 1/4`.
  - There is no `no_go_of_moments` skeleton in Orbit31.lean at all; copy the hypothesis style from `SixQubit/Orbit29.lean:1210` (MomentSystem instantiated at `Complex.normSq (c y_k)` / `Complex.normSq (d z_j)`, then one `offSum ... = 0` hypothesis per (mask, dressing)), and expect to need `set_option maxHeartbeats 2000000 in`.
  - `SixQubit.Orbit31` is imported by `SixQubit.lean` but NOT by `SixQubit/Audit.lean`; wiring into the audit is a separate step.

NOT A GAP (checked): all 16 `hat` lemmas, `S0_eq_fiber`/`S1_eq_fiber`, all 24 dbot/dtop lemmas, all 18 fam2 lemmas, all 3 fam1 lemmas, all 16 eq lemmas, row1-3, col0-3, and every Table31 branch lemma are present and kernel-checked.
