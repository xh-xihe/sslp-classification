# Workflow record: orbit26-verify

adversarial review of the first orbit 26 argument

Run id `w78j9ds4o`; 399637 subagent tokens, 46 tool calls.

---

## verdict

VERDICT / CONSOLIDATED AUDIT — ORBIT 26 (for the Lean formaliser)

===============================================================================
1. VERDICT
===============================================================================
CORRECT-BUT-INCOMPLETE, and incomplete in a way that is fatal as written: Steps A, B, C4 and C5 are algebraically sound, but Step C1 silently quantifies over both anchors when Steps A/B only ever ran for one, and that mixed-anchor branch is provably consistent with every fact the derivation uses — so the argument as stated proves nothing on a quarter of the case tree, plus it never opens the six degenerate branches at all. Every hole is repairable with relations already legally available (the full matrix R1 plus R2), so do not throw the proof away — but do not start formalising C1 as written either.

===============================================================================
2. CONFIRMED FATAL PROBLEMS
===============================================================================

F1. STEP C1 — THE TWO-ANCHOR MERGE. **Real, fatal, repairable.**
X_i := C_j^dagger D_i is anchor-indexed. The Step A contraction puts the SAME j in both slots (a-slot D_j, b-slot conj(C_j)), so Step B outputs an axis choice eps_j per anchor: two independent binary choices. C1's opening sentence ("X_i = 0 for i in {1,3,5} and BOTH anchors") assumes eps_6 = eps_7. Nothing in R1 (which never touches blocks 6,7) or R2 (which has no i=6,j=7 instance) links them. The "say ... the FIRST axis" WLOG is spendable exactly once: the only relabelling that flips an axis is the GLOBAL within-group swap i -> i XOR 1 for i <= 5, and that reverses R_g for both anchors simultaneously.
This is not a presentational gap. Two referees built explicit witnesses of the mixed branch satisfying every listed verified fact (P_i = Q_i, both 3/8 sums, P_6 = P_7 = 1/8, the matrix moment identity for all four groups, R2 exactly) and Step A's conclusion for both anchors with all three R_g nonzero — in which C_6 is not parallel to C_7, A has rank two, and C5's ledger closes at 0 or with strictly positive slack. I confirm the structural reason: with only anchor 6 giving D_6 ⟂ u, the count reads <u|A|u> + 2|<u,D_7>|^2 >= 3/8, and 1/4 + 2(1/8) = 1/2 >= 3/8 is satisfiable. **One anchor is provably insufficient for the counting argument. No repair of C3/C4/C5 can close this branch; a new relation is required.**
REPAIR (verified by me symbolically, see section 4): the cross-anchor contraction of R1.

F2. STEP B'S NONZERO HYPOTHESIS IS NEVER DISCHARGED. **Real, fatal, repairable.**
The lemma is true over C and its proof is correct, but it needs r_0, r_1, r_2 all nonzero, and R_g = 0 merely says C_j ⟂ D_{2g}, D_{2g+1} — perfectly possible. With one R_g = 0 the lemma is false: R_0 = 0, R_1 = (1,1), R_2 = (1,-1) satisfies all three Step-A relations with no vanishing transversal. R1 supplies no g = h instance, so no R_g is known to be isotropic on its own either. The derivation gets no axis, hence no input to C1, on six whole branches (three sizes of Z_j, two anchors). These branches do close, but each needs its own argument (section 3).

F3. UNVERIFIED SILENT INPUTS TO STEP A. **Not errors, but pre-flight checks whose failure is undetectable.** Step A's entire output is -(1+omega) * R_g J R_h^T, where omega is R1's relative coefficient weighted by R2's per-block phases. Two failure modes produce 0 = 0 with no symptom whatsoever, which then gets fed to Step B as if it were content:
  (a) If R1's true relative sign is minus (omega = -1), Step A yields nothing at all.
  (b) If R2's coefficient ratio mu_i = Y_i/X_i varies by block, the four terms do not collapse to the J-form. With a = (0,1,1,2,2,3) mod 4 the KL off-diagonals carry i^a phases, so per-block phases are exactly the thing to suspect. Concrete break: mu = (-1,-1,-1,+1,-1,-1) yields -2X_1X_2 = 0, -2(X_0X_5+X_1X_4) = 0, -2X_2X_5 = 0, on which Step B's conclusion is false (X_1 = X_2 = X_5 = 0 with X_0, X_3, X_4 nonzero gives three nonzero R_g on no common axis).
  (c) The J structure must hold for all three pairs under ONE global choice of the virtual bit c, and R_g := (X_{2g}, X_{2g+1}) must use that same column order. Flipping one group's order turns that pair's relation into the I-form X_{2g}X_{2h} + X_{2g+1}X_{2h+1} = 0, under which the three relations force R_2 = 0 instead of a common axis — a different branch structure entirely. A non-uniform flip also breaks C5, which would then need a mixed sum like P_1+P_3+P_4 that is NOT among the verified facts.
  (d) R1's b-index and R2's D-side index must be the same identification of the two S1 bit labels. If R2's available scalar is sum_b conj((C_j)_b)(D_i)_{1-b} (i.e. its Pauli also flips qubit one), the substitution Y = -X in Step A is applied to a different scalar and is invalid.
Spend an hour re-deriving the Walsh masks and pinning (a)-(d) BEFORE writing any Lean. Everything downstream is worthless if any of them is wrong, and none of them announces itself.
Note: R2's OVERALL sign is harmless (Y = +X gives +2 R_g J R_h^T = 0, same conclusion). Do not audit that.

REFEREE COMPLAINTS I DISCARD:
- "Step A's algebra/index bookkeeping is wrong." Discarded — three independent symbolic checks and my own re-derivation agree. The clean statement is D_j^T [R1] conj(C_j) = R'_g J R_h^T + R'_h J R_g^T with R'_g = (Y_{2g}, Y_{2g+1}), which needs no index chasing at all. The factor -2 is fine in char 0.
- "Step B's lemma is false / needs the diagonal relation." Discarded — the lemma is true over C, self-isotropy is a consequence not a hypothesis, and mixed axes really are excluded by the equations ((1,0) J (0,1)^T = 1 != 0). The char-2 caveat is irrelevant over C; just state the lemma for C or for a field with 2 != 0 so a Mathlib port cannot generalise it silently.
- "C4/C5's arithmetic is wrong." Discarded — (1-k^2)/2 - 3/8 - (1-k^2)/4 = (1-k^2)/4 - 3/8 <= -1/8 is exact, the block decomposition is disjoint and exhaustive, and A is not double-counted. C4/C5 are correct; they are simply conditional on a premise C1 does not deliver. (Replace them anyway — see section 5.)
- "The derivation smuggles in a forbidden per-edge matrix relation D_i C_k^dagger + D_k C_i^dagger = 0." Discarded — I traced it too. Only the SCALAR R2 (the trace of that forbidden identity) is ever used; C1/C2 use scalar orthogonality plus "orthogonal to two independent vectors in C^2 => zero"; C3 uses "lies in a line" plus P_6 + P_7 = 1/4; C4 uses only the allowed diagonal group identity. All proposed repairs are also clean: they contract the allowed R1 with vectors and use R2.
- "P vs Q bookkeeping" and "P is both a weight and a projector; C_g is both a group matrix and a block vector." Downgraded to Lean-hygiene, but genuinely worth fixing: C1 needs Q_1+Q_3+Q_5 = 3/8 (not the P-sum) and C2 needs Q_6 = Q_7 = 1/8, both via P_i = Q_i, which neither cites. And "C_3 C_3^dagger + D_3 D_3^dagger = rho/2" for the anchor group means GROUP 3, not block 3; read as blocks it is a false statement. Use disjoint names (Cmat_g vs C_i, w_i for weights, Proj_w for projectors) or you will hit this in Lean within the first hour.

===============================================================================
3. MISSING BRANCHES (exhaustive)
===============================================================================
First add this DERIVED FACT to the verified list — it is load-bearing in two branches and is a consequence of what you already machine-checked, needing no new KL input:
  (T)  P_{2g} + P_{2g+1} = 1/4 for EVERY group including the anchor.
  Proof: trace the group identity; tr(Cmat_g Cmat_g^dagger) = P_{2g}+P_{2g+1} = Q_{2g}+Q_{2g+1} = tr(Dmat_g Dmat_g^dagger) by P_i = Q_i, and tr rho = 1. Strictly stronger than "sum_{i<6} P_i = 3/4".
Also pin explicitly, in the Lean statement, that rho = sum over all EIGHT blocks (all four groups, anchor included) and that the moment identity was machine-checked at the anchor group. C4 is the hinge and rests on that instance. (Trace consistency confirms the intended reading: tr rho = 1.)

Set Z_j := {g : R^{(j)}_g = 0}. The tree, with all leaves:

B1. |Z_j| = 3 for some anchor j (C_j ⟂ all D_i, i <= 5). CLOSES with one anchor.
    All C_0..C_5 lie in span{u} = D_j^perp (mass 3/4), all D_0..D_5 in span{v} = C_j^perp; C_j ⟂ v, D_j ⟂ u. Put a = <u|A|u>, a' = <u|A'|u>. Then <u|rho|u> = 3/4 + a and A + A' = rho/2 give a + 2a' = 3/4; since a <= tr A = 1/4 and a' <= tr A' = 1/4, equality is forced everywhere, so a' = tr A' means D_6, D_7 both parallel to u — contradicting D_j ⟂ u, D_j != 0.

B2. |Z_j| = 2. CLOSES with one anchor; needs (T).
    WLOG (S_3) Z_j = {0,1}. C_0..C_3 in span{u}, D_0..D_3 in span{v}, and group-0's identity gives rho = (1/2)(Proj_u + Proj_v). Blocks 0..3 carry C-mass 1/2 all along u, so sum_{i in {4,5,6,7}} C_i C_i^dagger = rho - (1/2)Proj_u = (1/2)Proj_v, which is rank <= 1 along v, forcing every one of those C_i parallel to v — in particular C_j, which is nonzero and ⟂ v. Contradiction. Works verbatim when u ∥ v.

B3. |Z_j| = 1. CLOSES, hardest branch; needs (T), PSD-ness, and the FULL matrix R1.
    WLOG Z_j = {0}. C_0 = a_0 u, C_1 = a_1 u, D_0 = b_0 v, D_1 = b_1 v; rho = (1/2)(Proj_u+Proj_v), eigenvalues (1 ± sqrt k)/2 with k = |<u,v>|^2. The anchor identity forces the other anchor block to satisfy C_{j'}C_{j'}^dagger + D_{j'}D_{j'}^dagger = (3/8)(Proj_u+Proj_v) - (1/4)I, whose PSD-ness gives k <= 1/9, hence <u|rho|u> = (1+k)/2 <= 5/9. Now use R1 on pairs (0,1) and (0,2) as a MATRIX: each is a sum of two rank-<=1 terms, giving conj(a_0)D_3 + conj(a_1)D_2 ∥ v, conj(a_0)D_5 + conj(a_1)D_4 ∥ v, and the mirrors along u. With d_i the v-perp component of D_i: if a_0, a_1 are both nonzero then d_3 = -lambda d_2, d_5 = -lambda d_4, and Step A's pair-(1,2) relation d_2d_5 + d_3d_4 = -2 lambda d_2 d_4 = 0 forces R_1 = 0 or R_2 = 0, contradicting |Z_j| = 1. If a_1 = 0 then P_1 = 0, P_0 = 1/4 by (T), the R1 relations give C_0, C_3, C_5 all ∥ u, so <u|rho|u> >= 1/4 + 3/8 = 5/8 > 5/9. a_0 = 0 is the mirror. I checked the shape of this argument and it holds up, but it is the one branch where I would budget real Lean time: it is the only place PSD-ness of a residual matrix is used, and the rank-one splitting of R1 needs the "p ∥ r" degenerate sub-case handled explicitly (M = p q^T + r s^T = 0 gives q ∥ s, not q = s = 0).

B4. Z_6 = Z_7 = empty, eps_6 = eps_7 = axis 1. This is the only branch the write-up covers. Close it with the trace ending (section 5), not C3/C4/C5.

B5. Z_6 = Z_7 = empty, eps_6 = eps_7 = axis 2. Genuine WLOG, but cite the symmetry: the GLOBAL within-group swap sigma: i -> i XOR 1 for i <= 5, anchors untouched. It permutes the four terms of every R1 relation among themselves, fixes every R2 relation, preserves every Cmat_g Cmat_g^dagger, and exchanges P_1+P_3+P_5 with P_0+P_2+P_4 (both 3/8). NEVER justify this with a per-group swap — swapping inside a single group sends R1 to the other pairing (J -> I) and is not a symmetry.

B6. Z_6 = Z_7 = empty, eps_6 != eps_7 (MIXED). Closes only via the cross-anchor relation of section 4.

Also legitimate and worth stating once, for B2/B3: the full S_3 permuting the three cycle groups is a symmetry of the extracted hypothesis set (R1 ranges over all pairs, R2 is per block, all group masses are 1/4 by (T), and group permutations preserve index parity), so "the zero group is group 0" is free.

===============================================================================
4. THE TWO-ANCHOR QUESTION — SETTLED
===============================================================================
NO, Step C1 may NOT use both anchors as written. The axis is a per-anchor conclusion and the mixed assignment is a priori open; and it is not merely open, it is metrically consistent — every mass/moment/positivity count you have is satisfied in the mixed branch, so C4/C5 cannot be patched into excluding it.

YES, you may recover the both-anchor conclusion, from a relation you already own. R1 is a full 2x2 matrix identity, so it may be contracted with ANY vectors: a-slot with D_j, b-slot with conj(C_{j'}), for j != j'. Each factor converts by its own R2 (<C_i, D_j> = -X^{(j)}_i, <C_{j'}, D_k> = X^{(j')}_k). I verified this symbolically over generic complex components, for all three pairs and all four anchor combinations (j,j') in {6,7}^2:

    sum_{a,b} (D_j)_a conj((C_{j'})_b) [R1(g,h)]_{ab}
        = Y^{(j)}_{2g} X^{(j')}_{2h+1} + Y^{(j)}_{2g+1} X^{(j')}_{2h}
        + Y^{(j)}_{2h} X^{(j')}_{2g+1} + Y^{(j)}_{2h+1} X^{(j')}_{2g}  = 0,

i.e. after Y = -X,   B(R^{(j)}_g, R^{(j')}_h) + B(R^{(j)}_h, R^{(j')}_g) = 0   for all 0 <= g < h <= 2, where B(r,s) = r J s^T. Setting j = j' recovers Step A (times 2), so nothing is lost in the aligned case, where the relation is identically satisfied.

In the mixed branch R^{(6)}_g = (x_{2g}, 0) and R^{(7)}_g = (0, y_{2g+1}) with all six entries nonzero (Z_j empty), and the relation collapses to
    x_0 y_3 + x_2 y_1 = 0,  x_0 y_5 + x_4 y_1 = 0,  x_2 y_5 + x_4 y_3 = 0.
I ran a Rabinowitsch saturation of this ideal with all six variables inverted: the Groebner basis is [1]. The system is inconsistent over C. Elementary version: multiply the first by the third, cancel x_2 y_3 != 0 to get x_0 y_5 = x_4 y_1, combine with the second to get 2 x_4 y_1 = 0.

So: the mixed branch dies, but only via a contraction the derivation never invokes, and only AFTER Z_6 = Z_7 = empty has been established independently (the division needs nonvanishing). F1 and F2 must be closed separately; neither repair covers the other.

Structural consequence for the write-up: do not extract scalars in Step A and throw R1 away. Before any case split, record the full extract — for each anchor j' the vector identity conj(Cmat_g) J (R^{(j')}_h)^T + conj(Cmat_h) J (R^{(j')}_g)^T = 0, its mirror R^{(j)}_g J Dmat_h^T + R^{(j)}_h J Dmat_g^T = 0, and the scalar cross-anchor relation above. Both fatal gaps and branch B3 live inside that extract; Step A as written keeps 3 scalars out of it and that impoverishment IS the bug.

===============================================================================
5. WHAT IS SAFE TO BUILD NOW
===============================================================================
Safe today, zero rework risk:
- The J-orthogonality lemma (Step B), stated over C or a field with 2 != 0, with the nonzero hypothesis as an EXPLICIT side condition and the conclusion in the strong form "all three lie on one common coordinate axis". Use the coordinate proof (case a_0 = 0; else t_g = b_g/a_g, three equations t_g + t_h = 0, so 2t = 0) — it avoids perps and ports to Mathlib cleanly. Also record the strengthening "each r_g is isotropic", which B3 uses.
- The general contraction lemma: for vectors p, q, contracting the a-index of R1 with p and the b-index with conj(q) yields sum over the four terms of <C_i, p><q, D_k>. State it once, for arbitrary p, q; then Step A, its mirrors, and the cross-anchor relation are all instances. This is the single highest-value piece of Lean infrastructure here.
- The derived per-group mass fact (T): P_{2g} + P_{2g+1} = 1/4 for all four groups, from the trace of the group moment identity plus P_i = Q_i plus tr rho = 1.
- The linear-algebra micro-lemmas: nonzero vector in C^2 has 1-dimensional perp; two independent vectors in C^2 have zero common perp; for PSD A and unit u, <u|A|u> <= tr A; a sum of PSD rank-ones equal to a rank-one along v forces every summand parallel to v; M = p q^T + r s^T = 0 implies q ∥ s (with the p ∥ r sub-case).
- Branches B1 and B2 in full. They are single-anchor, short, and use only (T), the moment identity, and positivity.
- THE REPLACEMENT ENDING for B4/B5 — build this instead of C3/C4/C5. With both anchors on axis 1: D_6, D_7 ⟂ u (u = the common direction of C_1, C_3, C_5, well defined because D_6 != 0 makes D_6^perp a line and P_1+P_3+P_5 = 3/8 > 0 makes some C_i nonzero), so <u|A'|u> = 0; A + A' = rho/2 gives <u|rho|u> = 2<u|A|u>; and <u|rho|u> = sum_i |<u,C_i>|^2 >= 3/8 + <u|A|u>; hence <u|A|u> >= 3/8 > 1/4 = P_6+P_7 = tr A. Contradiction. This needs no v, no kappa, no rank-one form for A, no claim that C_6 ∥ C_7, and no positivity of the {0,2,4} remainder; it transfers unchanged to B5; and zero blocks among C_1, C_3, C_5 are harmless (a zero vector lies on every line). Drop C1's parallelism claim and C3's projector formulas entirely — they were never the load-bearing content.

DO NOT build yet:
- Anything phrased as "X_i" without an anchor superscript. Make the anchor an explicit index in every definition from line one; the entire bug is a suppressed quantifier.
- C1, C2, C3 as written, and the kappa computation in C4/C5.
- Branch B3 — write it on paper first, including the degenerate rank-one splitting, before committing Lean time.
- Any of it, until the four input checks in F3 are re-derived against the Walsh masks: R1's relative PLUS sign per pair, R2's block-independent coefficient ratio across all twelve (i,j) instances given the i^a phases, one global virtual-bit labelling making all three pairs J-form under the same column order as R_g, and the agreement of R1's b-labelling with R2's D-side index. Failures (a) and (b) are silent — they hand you 0 = 0 and no error.

Verification scripts I ran are in C:\Users\richa\AppData\Local\Temp\claude\D--UTD-Project-purdue\e2435927-3651-49b0-acfb-31f3430ee257\scratchpad (referee scripts stepA*.py, stepB*.py, chk.py, cross.py, wlog.py, mixed2.py are also there and reproduce the counterexamples cited above).

## refutations

## step

STEP A — contraction of the outer identity (R1) with the anchor vectors, and its identification with R_g J R_h^T = 0

## verdict

sound

## problems

## claim

Step A's output 'R_g J R_h^T = 0 for the three pairs' is treated downstream (Step C1) as holding simultaneously for both anchors with the SAME axis.

## why_wrong

Every object in Step A is anchor-indexed: X_i = X_i^{(j)} = C_j^dagger D_i and Y_i^{(j)} = C_i^dagger D_j depend on the fixed j in {6,7}. The contraction is D_j^T [R1] conj(C_j), so it yields three quadrics per anchor: R_g^{(6)} J R_h^{(6)T} = 0 and, separately, R_g^{(7)} J R_h^{(7)T} = 0. Nothing in Step A (or B) couples the two systems. Step B applied to j=6 may return 'all on axis 1' (X_1^{(6)}=X_3^{(6)}=X_5^{(6)}=0) while j=7 returns 'all on axis 2' (X_0^{(7)}=X_2^{(7)}=X_4^{(7)}=0). Step C1 explicitly needs 'X_i = 0 for i in {1,3,5} and BOTH anchors j=6,7' to conclude C_6 || C_7 — that cross-anchor axis agreement is assumed, not derived. This is a seam defect at B->C rather than an algebra error inside A, but it originates in A's per-anchor scope and must be closed.

## severity

fixable

## claim

(R1) has a '+' between the two terms: conj(C_g) J D_h^T + conj(C_h) J D_g^T = 0.

## why_wrong

This relative sign is the single most load-bearing input and it fails SILENTLY. Contracting the general form conj(C_g) J D_h^T + omega conj(C_h) J D_g^T = 0 gives (mu_{2g} + omega mu_{2h+1}) X_{2g}X_{2h+1} + (mu_{2g+1} + omega mu_{2h}) X_{2g+1}X_{2h} = 0 where Y_i = mu_i X_i. With mu_i = -1 (i.e. R2 as stated) and omega = -1 this is identically 0 = 0 for all three pairs — verified in sympy. So if the true KL relation carries a minus sign, Step A produces no constraint whatever and yet exhibits no symptom: no contradiction, no degenerate case, just a vacuous identity that then gets fed to Step B as if it were content. Verify the '+' directly against the Walsh-mask row space, per pair, before trusting anything downstream. (Good news: any omega != -1 preserves the conclusion up to the nonzero scalar -(1+omega), so only the exact minus sign is fatal.)

## severity

fixable

## claim

(R2) reads C_j^dagger D_i + C_i^dagger D_j = 0 with coefficient exactly 1 on both terms, uniformly for all i = 0..5 and both j.

## why_wrong

The collapse of the four terms to -2(X_{2g}X_{2h+1} + X_{2g+1}X_{2h}) requires the R2 proportionality Y_i = mu_i X_i to have the SAME mu across the four blocks of each pair. A global phase is harmless (mu_i = mu for all i gives -2mu R_g J R_h^T = 0, same conclusion), but block-dependent phases are not, and with angle vector a = (0,1,1,2,2,3) mod 4 the KL off-diagonal conditions carry i^{a} phases, so per-block phases are exactly the thing to suspect. Concrete break: take mu = (-1,-1,-1,+1,-1,-1) (only block 3 flipped). Sympy gives pair(0,1) -> -2 X_1 X_2 = 0, pair(0,2) -> -2(X_0X_5 + X_1X_4) = 0, pair(1,2) -> -2 X_2 X_5 = 0. That system is NOT the J-form, and Step B's conclusion is false on it: X_1 = X_2 = X_5 = 0 with X_0, X_3, X_4 nonzero satisfies all three, giving R_0 = (X_0,0) on axis 1, R_1 = (0,X_3) on axis 2, R_2 = (X_4,0) on axis 1 — three nonzero vectors, no common axis. So confirm that R2 holds with a block-independent coefficient ratio for all twelve (i,j) instances.

## severity

fixable

## claim

All three pairs of (R1) carry the same swap matrix J on the virtual-bit index.

## why_wrong

This is a statement about a COHERENT choice of the z-labelling across the three cycle groups, not an automatic fact. Relabelling the columns of one group (swapping blocks 2 and 3, say) sends conj(C_1) J D_h^T to conj(C_1) K J D_h^T with K = J, and KJ = I — that pair's relation then reads with the identity, not J. If even one pair is genuinely an I-pair under the labelling that makes the other two J-pairs, Step B's lemma no longer applies: with relations X_0X_3+X_1X_2 = 0, X_0X_5+X_1X_4 = 0 and (I-form) X_2X_4+X_3X_5 = 0, one gets forced R_2 = 0 rather than a common axis, i.e. a different branch structure entirely. The prompt says R1 was machine-checked per group and per entry; make sure that check pinned the J (swap) structure under one fixed z-labelling shared by all three groups, and that R_g := (X_{2g}, X_{2g+1}) uses that same column order — reversing one group's order changes R_g J R_h^T from X_{2g}X_{2h+1}+X_{2g+1}X_{2h} to X_{2g}X_{2h}+X_{2g+1}X_{2h+1}.

## severity

fixable

## claim

Implicitly, the within-block index b appearing in (R1) is the same identification of the two D-side amplitudes as the one used in (R2)'s inner product C_j^dagger D_i.

## why_wrong

The C-side index a and the D-side index b label the qubit-one value of basis states in two DIFFERENT fibers S0 and S1, so 'C_j^dagger D_i' is only meaningful relative to a chosen identification of those two bit labels. R1 is safe on its own (a and b are free, so all four combinations are present), but the step 'sum_b conj((C_j)_b)(D_y)_b = X_y' silently asserts that R1's b-labelling coincides with R2's. If R2 were actually derived from a Pauli that also flips qubit one — i.e. the available scalar is sum_b conj((C_j)_b)(D_i)_{1-b} rather than sum_b conj((C_j)_b)(D_i)_b — then Y_i = -X_i would be a statement about a different scalar than the one produced by the contraction, and the substitution in Step A is invalid. Not shown wrong, but it is an unstated convention hypothesis.

## severity

cosmetic

## claim

'Equivalently R_g J R_h^T = 0 for all three pairs' — presented as though the contraction captures (R1).

## why_wrong

The contraction is a strict weakening, not an equivalence: each (R1) is 4 complex equations (a 2x2 matrix) and Step A extracts exactly 1 scalar from it, discarding 3. The word 'equivalently' is correct only for the relation between the four-term Y-X form and R_g J R_h^T; it is not an equivalence with (R1). Practical consequence: if Step B or C collapses, there is unharvested content — contracting b with conj(C_k) for cycle blocks k <= 5, or a with D_k, produces further bilinear relations in mixed quantities C_k^dagger D_i that Step A never touches, and the full matrix identity is still available.

## severity

cosmetic

## notes

VERDICT ON THE ALGEBRA: I could not break Step A. All four sub-checks pass, verified symbolically over generic complex components (no numeric luck involved), scripts at C:\Users\richa\AppData\Local\Temp\claude\D--UTD-Project-purdue\e2435927-3651-49b0-acfb-31f3430ee257\scratchpad\stepA.py, stepA2.py, stepA3.py.

FIRST, the entry formula is consistent with the matrix form. With the column convention (C_g)_{a,c} = (C_{2g+c})_a, entry (a,b) of conj(C_g) J D_h^T is sum_{c,c'} conj((C_{2g+c})_a) J_{c,c'} (D_{2h+c'})_b, and J_{c,c'} = [c' = 1-c] collapses it to sum_c conj((C_{2g+c})_a)(D_{2h+1-c})_b. Machine-checked equal to the stated entry formula for all three pairs and all four (a,b). So conj() is elementwise, a is a C-side index, b is a D-side index, and no dagger sneaks in.

(i) YES. The b-contraction is right-multiplication by conj(C_j) as a column: (M conj(C_j))_a = sum_b M_{ab} conj((C_j)_b). In R1 the D factors sit un-conjugated at index b, so sum_b conj((C_j)_b)(D_y)_b = C_j^dagger D_y = X_y exactly. The conjugation lands on C_j, which is what the definition X_y = C_j^dagger D_y wants. Result after contracting: sum_c conj((C_{2g+c})_a) X_{2h+1-c} + sum_c conj((C_{2h+c})_a) X_{2g+1-c} = 0.

(ii) YES. The surviving C factors sit conjugated at index a, so the a-contraction must use D_j UN-conjugated: sum_a conj((C_x)_a)(D_j)_a = C_x^dagger D_j = Y_x. Correct as written.

CLEANEST WAY TO SEE THE WHOLE STEP (worth putting in the writeup, it makes the bookkeeping unfalsifiable): the double contraction is just D_j^T [ conj(C_g) J D_h^T + conj(C_h) J D_g^T ] conj(C_j). Now D_j^T conj(C_g) = (Y_{2g}, Y_{2g+1}) =: R'_g as a row, and D_h^T conj(C_j) = (X_{2h}, X_{2h+1})^T = R_h^T as a column. So the contraction IS, with no index chasing at all,
      R'_g J R_h^T + R'_h J R_g^T = 0.
Since J^T = J and a 1x1 is its own transpose, R_h J R_g^T = R_g J R_h^T, so under Y = -X this is -2 R_g J R_h^T = 0.

(iii) YES, the 2 is real and harmless. For (0,1) the four terms are Y_0X_3 + Y_1X_2 + Y_2X_1 + Y_3X_0; under Y = -X the second pair repeats the monomials of the first (scalars commute), giving -2(X_0X_3 + X_1X_2). Char 0, so dividing by -2 is legitimate. Sympy: expand(four + 2*R_g J R_h^T) == 0 for all three pairs.

(iv) YES for all three pairs; the index formula 2h+1-c behaves. Explicit (0,2) case as requested: g=0,h=2. First sum, c in {0,1}: 2g+c in {0,1} and 2h+1-c in {5,4}, giving Y_0X_5 + Y_1X_4. Second sum: 2h+c in {4,5} and 2g+1-c in {1,0}, giving Y_4X_1 + Y_5X_0. Total Y_0X_5 + Y_1X_4 + Y_4X_1 + Y_5X_0 = 0, and Y = -X gives -2(X_0X_5 + X_1X_4) = 0, i.e. X_0X_5 + X_1X_4 = 0 = R_0 J R_2^T. Confirmed. Pair (1,2) likewise gives Y_2X_5+Y_3X_4+Y_4X_3+Y_5X_2 -> X_2X_5 + X_3X_4 = 0 = R_1 J R_2^T. All indices 2h+1-c and 2g+1-c stay inside their own group, as they must.

WHERE THE RISK ACTUALLY LIVES. Step A is a two-line contraction and it is correct; what is NOT airtight is the input it consumes. The derivation's entire output is the scalar -(1 + omega) times R_g J R_h^T where omega is the relative coefficient of R1's second term, weighted by R2's phases mu_i. Two failure modes are silent (they produce 0 = 0, never an inconsistency): omega = -1, and mu_i varying by block. Both are listed above with explicit counterexamples. Also note Step A is robust to R2's overall sign — if R2 were C_j^dagger D_i - C_i^dagger D_j = 0 (Y = +X) you get +2 R_g J R_h^T = 0, the same conclusion — so do not spend audit effort on R2's global sign; spend it on R1's relative sign and on whether R2's coefficient ratio is block-independent given the angle vector (0,1,1,2,2,3) mod 4.

ONE STRUCTURAL OBSERVATION FOR THE PARENT: the derived form is BILINEAR (transpose, not dagger) in the X's — R_g J R_h^T, no conjugation on R_h. So Step B's 'J-orthogonality' is with respect to a nondegenerate SYMMETRIC bilinear form on C^2, whose isotropic vectors are exactly the coordinate axes (r J r^T = 2 r_0 r_1). That is consistent with Step B's lemma and is why the lemma is about coordinate axes rather than an orthogonal complement; Step A hands Step B the right kind of object. Also note Step A yields nothing within a group (R_g J R_g^T = 2 X_{2g}X_{2g+1} is unconstrained) and nothing pairing a cycle group with the anchor group — Step B does not need either, but that is the boundary of what A delivers.

## step

STEP B — J-orthogonality lemma: three nonzero rows in C^{1x2}, pairwise J-orthogonal with J=[[0,1],[1,0]], lie on one common coordinate axis

## verdict

sound

## problems

## claim

Step B's hypothesis 'r_0, r_1, r_2 are NONZERO' is never established for R_g = (X_{2g}, X_{2g+1}), yet the lemma is false the instant one R_g vanishes.

## why_wrong

The lemma itself is fine, but the derivation applies it without discharging the hypothesis, and the degenerate branch is NOT a harmless special case. Explicit counterexample satisfying all three Step-A equations: X_0=X_1=0 (so R_0=0), R_1=(X_2,X_3)=(1,1), R_2=(X_4,X_5)=(1,-1). Check: X_0X_3+X_1X_2 = 0+0 = 0; X_0X_5+X_1X_4 = 0+0 = 0; X_2X_5+X_3X_4 = 1*(-1)+1*(1) = 0. All three (R1)-contracted relations hold, yet neither (X_1,X_3,X_5)=(0,1,-1) nor (X_0,X_2,X_4)=(0,1,1) is zero, so Step C's premise 'X_1=X_3=X_5=0' does not follow. The same failure occurs whenever any single R_g = 0: the remaining two need only be mutually J-orthogonal, and a J-orthogonal pair can be entirely off-axis, e.g. (1,1) and (1,-1). Step C therefore needs a genuine separate branch for 'some R_g = 0' (equivalently: for some g, C_j^dagger D_{2g} = C_j^dagger D_{2g+1} = 0), not a WLOG.

## severity

fixable

## claim

Step C1 uses 'X_i = 0 for i in {1,3,5} and BOTH anchors j = 6,7', treating the axis produced by Step B as anchor-independent.

## why_wrong

X_i := C_j^dagger D_i is a function of the anchor j, so Steps A/B run twice and produce two independent axis choices eps_6, eps_7 in {first, second}. Step B constrains each run separately and says nothing linking them. In the mixed branch eps_6 = first, eps_7 = second, one gets C_6 orth D_1,D_3,D_5 but C_7 orth D_0,D_2,D_4, and the C1 argument ('if C_6, C_7 independent then D_1=D_3=D_5=0') collapses — there is no common triple to kill. Note the intra-anchor WLOG in Step C is legitimate (swapping the two coordinates of every R_g simultaneously is the relabeling block 2g <-> 2g+1, and the supplied facts P_1+P_3+P_5 = P_0+P_2+P_4 = 3/8 are symmetric under it), but that symmetry cannot be invoked twice independently to align two different anchors. This is a B->C interface gap, flagged since it is about whether Step B's conclusion is strong enough to feed C.

## severity

fixable

## claim

Implicit robustness of the lemma to the number of groups.

## why_wrong

Not an error, but the lemma is exactly tight at three vectors and has zero margin: the two-vector version is false over C (r_0=(1,1), r_1=(1,-1) give r_0 J r_1^T = 1*(-1)+1*(1) = 0, both off-axis and linearly independent; a brute-force projective scan found 100 such pairs). The proof consumes all three pairs (0,1),(0,2),(1,2). If a future refactor of orbit 26 ever reduces the cycle to two groups, or if one of the three Step-A relations turns out not to lie in the Walsh row space after all, Step B dies immediately with no weaker fallback than 'the three rows span at most a line'.

## severity

cosmetic

## claim

The lemma as a field-agnostic statement (relevant only if formalized in Lean over a general field or ring).

## why_wrong

The proof divides by 2: the coordinate case-split reduces to t_0+t_1 = t_0+t_2 = t_1+t_2 = 0 => 2t_g = 0, and the invariant proof to B(perp,perp) = -2 a_0 b_0 = 0. In characteristic 2 the lemma is FALSE: r_0=r_1=r_2=(1,1) over F_2 gives r J s^T = 1*1+1*1 = 0 pairwise, all nonzero, none on an axis. Groebner saturation confirms the ideal {J-orth relations, each r_g nonzero, r_0 not isotropic} equals (1) in characteristics 0, 3, 5 but is proper in characteristic 2. Over C this is a non-issue; state the lemma for a field with 2 != 0 (or just for C) so a Mathlib port does not silently generalize it.

## severity

cosmetic

## notes

VERDICT ON STEP B ITSELF: the lemma is TRUE over C, exactly as stated. I tried hard to break it and could not. It does NOT need the diagonal relation r_g J r_g^T = 0 as a hypothesis — self-isotropy is a CONSEQUENCE, which is important because (R1) supplies only g < h and gives nothing for g = h. And the conclusion really is the strong one ("one common coordinate axis"), not merely "all proportional"; both are delivered.

INVARIANT PROOF (three lines). B(r,s) := r J s^T = r_0 s_1 + r_1 s_0 is a SYMMETRIC BILINEAR (not sesquilinear — no conjugates appear in Step A, consistent with the contraction) form on C^2, and det J = -1 != 0, so B is NONDEGENERATE. Hence for r != 0 the space r^perpB := {s : B(r,s)=0} is exactly 1-dimensional; concretely for r=(a,b), B(r,s) = a*s_1 + b*s_0, so r^perpB = span(a,-b). Now given nonzero pairwise-orthogonal r_0,r_1,r_2: both r_1 and r_2 lie in the LINE r_0^perpB = span(a_0,-b_0), so r_1 = lambda(a_0,-b_0), r_2 = mu(a_0,-b_0) with lambda,mu != 0. Then 0 = B(r_1,r_2) = lambda*mu*B((a_0,-b_0),(a_0,-b_0)) = -2*lambda*mu*a_0*b_0, forcing a_0*b_0 = 0, i.e. r_0 is ISOTROPIC. For this form the isotropic vectors are precisely the coordinate axes (B(r,r) = 2 r_0 r_1 = 0 iff r_0 = 0 or r_1 = 0). Finally the axis propagates: if r_0 = (a_0,0), a_0 != 0, then (a_0,-b_0) = (a_0,0) is proportional to r_0, so r_1, r_2 sit on the SAME first axis; if r_0 = (0,b_0) then (a_0,-b_0) = (0,-b_0), same second axis. QED.

COORDINATE PROOF (for a Lean port, avoids talking about perps). Write r_g = (a_g,b_g); the three hypotheses are a_0b_1+b_0a_1 = 0, a_0b_2+b_0a_2 = 0, a_1b_2+b_1a_2 = 0. Case 1: some a_g = 0, say a_0 = 0 (then b_0 != 0 by nonzeroness). Eq(0,1) reduces to b_0 a_1 = 0 => a_1 = 0; Eq(0,2) reduces to b_0 a_2 = 0 => a_2 = 0. All on the second axis. Case 2: all a_g != 0. Put t_g := b_g/a_g; each equation becomes a_g a_h (t_g + t_h) = 0, i.e. t_0+t_1 = t_0+t_2 = t_1+t_2 = 0. Subtracting gives t_1 = t_2 and then 2t_1 = 0 => t_0 = t_1 = t_2 = 0, so all b_g = 0: first axis. The ONLY place any arithmetic beyond a field is used is 2 != 0.

WHY MIXED AXES CANNOT HAPPEN (the thing a referee should check and that does hold): r=(1,0) and s=(0,1) give r J s^T = 1*1 + 0*0 = 1 != 0. So one row on the first axis and another on the second are NEVER J-orthogonal; the lemma's "common" is genuinely enforced by the equations rather than assumed.

IN THE ORBIT-26 VARIABLES the three Step-A equations are X_0X_3+X_1X_2 = 0, X_0X_5+X_1X_4 = 0, X_2X_5+X_3X_4 = 0, and (given all three R_g != 0) the lemma outputs exactly (X_1,X_3,X_5) = (0,0,0) OR (X_0,X_2,X_4) = (0,0,0), plus the free bonus X_0X_1 = X_2X_3 = X_4X_5 = 0. That is precisely the input Step C wants, so the logical shape of B -> C is right; the two "fixable" items above are about the hypothesis (some R_g may vanish) and the anchor-dependence of X, not about the lemma's mathematics.

MACHINE VERIFICATION (scripts kept at C:\Users\richa\AppData\Local\Temp\claude\D--UTD-Project-purdue\e2435927-3651-49b0-acfb-31f3430ee257\scratchpad\stepB.py and C:\Users\richa\AppData\Local\Temp\claude\D--UTD-Project-purdue\e2435927-3651-49b0-acfb-31f3430ee257\scratchpad\stepB3.py):
(1) Exhaustive scan over 102 projective classes of Gaussian-integer rows (real and imaginary parts in -2..2, phase-normalized): 0 counterexamples among all pairwise-J-orthogonal nonzero triples.
(2) Groebner/Rabinowitsch saturation of the ideal generated by the three J-orthogonality relations together with witnesses that each r_g is nonzero and that r_0 is NOT isotropic (w*a_0*b_0 - 1): the basis is [1] in characteristics 0, 3, 5 — the system is inconsistent, so no such configuration exists over C. In characteristic 2 the basis is proper (solutions exist), matching the (1,1)/(1,1)/(1,1) counterexample and confirming that 2 != 0 is the exact hypothesis being used.
(3) The 2-vector weakening and the zero-vector weakening were both confirmed false by explicit witnesses, reported above.

BOTTOM LINE: Step B is airtight over C and I recommend accepting it as written. If you want it bulletproof for formalization, state it as "over a field with 2 != 0" and carry the nonzero hypothesis as an explicit side condition that Step C must discharge — the two fixable items are where a real proof of orbit 26 can still fail, and neither is repaired by anything inside Step B.

## step

Orbit 26 derivation, Steps C1 and C2 (anchor-orthogonality => C_6 ∥ C_7 and D_6 ∥ D_7)

## verdict

flawed

## problems

## claim

C1's premise: 'X_i = C_j^dagger D_i = 0 for i in {1,3,5} and BOTH anchors j = 6,7'

## why_wrong

X_i is anchor-dependent (X_i^{(j)} = C_j^dagger D_i), and Steps A/B run once per anchor: contracting R1 on b with conj(C_j) and on a with D_j uses the SAME j in both slots (verified numerically), so Step B delivers, for each anchor separately, the dichotomy 'axis-1 or axis-2'. Two anchors = two independent binary choices. Nothing in A/B forbids the CROSS case (anchor 6 in axis-1, anchor 7 in axis-2), and the 'say ... the FIRST axis' WLOG cannot be spent twice: the only relabeling that converts axis-2 to axis-1 is the block swap 0<->1, 2<->3, 4<->5, which leaves R1 invariant but reverses R_g for BOTH anchors simultaneously (checked). Explicit cross-case counterexample in C^2 satisfying everything C1 cites: C_6=(1,0)/sqrt8, C_7=(0,1)/sqrt8, D_6=(0,1)/sqrt8, D_7=(1,0)/sqrt8, D_1=D_3=D_5=(0,1)/sqrt8, D_0=D_2=D_4=(1,0)/sqrt8, C_1=C_3=C_5=(1,0)/sqrt8, C_0=C_2=C_4=(0,1)/sqrt8. Here X^{(6)}_{1,3,5}=0, X^{(7)}_{0,2,4}=0, R2 holds on those pairs, P_6=P_7=Q_6=Q_7=1/8, P_1+P_3+P_5=Q_1+Q_3+Q_5=3/8 -- yet rank[C_6 C_7]=rank[D_6 D_7]=2, so C1's and C2's conclusions both fail. REPAIR (not present in the text): contract R1 with mixed anchors (a-slot D_7, b-slot conj(C_6)); this is legal and gives R^{(7)}_g J (R^{(6)}_h)^T + R^{(7)}_h J (R^{(6)}_g)^T = 0, i.e. x_g y_h + x_h y_g = 0 for the three pairs in the cross case, whose only solution with all x_g, y_g nonzero is y = 0 -- contradicting Step B's nondegeneracy. So the cross case dies, but only via a relation the derivation never invokes.

## severity

fixable

## claim

C1: 'D_1 = D_3 = D_5 = 0, contradicting P_1+P_3+P_5 = 3/8'

## why_wrong

The vanishing objects are the D's, so the immediate contradiction is with Q_1+Q_3+Q_5 = 3/8, not with the P-sum. The bridge is the verified fact P_i = Q_i, which C1 never cites. Symmetrically, C2 needs D_6, D_7 nonzero, which requires Q_6 = Q_7 = 1/8; C2 quotes only P_6 = P_7 = 1/8 and again silently uses P_i = Q_i. Both bridges are available, so this is bookkeeping, not a hole -- but each of C1 and C2 uses P_i = Q_i exactly once, in a different place, and neither says so.

## severity

cosmetic

## claim

C1/C2 stand on their own once the axis case is granted

## why_wrong

They silently import Step B's nondegeneracy hypothesis ('r_0, r_1, r_2 NONZERO') for BOTH anchors, i.e. all six R^{(j)}_g nonzero -- a strictly stronger case split than the single-anchor one, and the repair proposed above needs exactly that stronger form. Any branch in which some R^{(j)}_g = 0 yields no axis conclusion at all for that anchor, hence no orthogonality input to C1/C2. The degenerate branches must be discharged per anchor before C1 may be invoked; the write-up does not flag this.

## severity

fixable

## notes

Answers to the four sub-questions -- (i)-(iv) all check out; the damage is elsewhere, in the quantifier over anchors.

(i) CORRECT. With the physics convention C_j^dagger D_i = sum_a conj((C_j)_a)(D_i)_a = <C_j, D_i>, vanishing means D_i ⟂ C_j, and by conjugate symmetry the slot is immaterial for the vanishing statement. The inference used is: D_i ⟂ C_6 and D_i ⟂ C_7 => D_i ∈ (span{C_6,C_7})^perp (valid because the form is conjugate-linear in the first slot, so orthogonality to the two generators gives orthogonality to every combination), and if C_6, C_7 are independent they span C^2, whose perp under a nondegenerate Hermitian form is {0}. No orthonormality is needed, only spanning. Clean.

(ii) CORRECT. P_i = ||C_i||^2 >= 0 and Q_i = ||D_i||^2 >= 0 are real nonnegative, so a sum equal to 3/8 > 0 forces at least one summand nonzero. What C1 actually needs is Q_1+Q_3+Q_5 = 3/8 (see problem 2); with P_i = Q_i that is immediate. Note C3 additionally needs this to define v at all -- if all three D's vanished, "D_1,D_3,D_5 parallel to some v" would be vacuous and A = (1/4)P_{v-perp} ill-posed; the 3/8 fact covers that too.

(iii) CORRECT and necessary. P_6 = P_7 = 1/8 gives ||C_6||^2 = ||C_7||^2 = 1/8 != 0. Two nonzero vectors in C^2 that are linearly dependent satisfy C_7 = lambda C_6 with lambda != 0, so "parallel" is the right word and C3's A = (||C_6||^2+||C_7||^2) P_w = (1/4) P_w follows. Bonus: |lambda|^2 = P_7/P_6 = 1, so lambda is a phase. Without P_6 = P_7 = 1/8 the contrapositive would only give "dependent", which a zero vector satisfies vacuously and which would break C3's rank-one conclusion -- so the check is load-bearing and it passes.

(iv) CORRECT, slot and all. Y_i^{(j)} := C_i^dagger D_j = <C_i, D_j>, so Y_i = 0 says D_j ⟂ C_i, which is exactly "D_6, D_7 each orthogonal to C_1, C_3, C_5". Y_i = -X_i comes from R2 at the same (i,j), so the vanishing transfers pair-by-pair with no index drift. The rest mirrors C1 with P and Q swapped: D_6, D_7 independent would force C_1 = C_3 = C_5 = 0, contradicting P_1+P_3+P_5 = 3/8 (this direction needs no P=Q bridge), and Q_6 = Q_7 = 1/8 makes D_6, D_7 nonzero so "dependent" upgrades to "parallel". C3's u is then the direction of the line D_6^perp, and C_1,C_3,C_5 all lie on it. Sound.

VERDICT RATIONALE. Everything you asked me to check is right. What is not airtight is the sentence C1 opens with: it asserts the axis conclusion for both anchors with the SAME axis, and Steps A/B as written only produce it per anchor. The counterexample above is not a counterexample to the theorem -- it is a counterexample to the inference at the level of detail C1 supplies, and the mixed-anchor contraction repairs it. Add that contraction (or an argument that the two anchors cannot split) as an explicit sub-step C0 before C1, state the P_i = Q_i bridges, and carry Step B's nondegeneracy hypothesis for both anchors explicitly, and C1/C2 become airtight.

Scripts (all checks reproducible):
C:\Users\richa\AppData\Local\Temp\claude\D--UTD-Project-purdue\e2435927-3651-49b0-acfb-31f3430ee257\scratchpad\chk.py -- verifies Step A's contraction index bookkeeping, same-anchor and mixed-anchor, and that the result equals R_g J R_h^T + R_h J R_g^T
C:\Users\richa\AppData\Local\Temp\claude\D--UTD-Project-purdue\e2435927-3651-49b0-acfb-31f3430ee257\scratchpad\cross.py -- the cross-case counterexample and the sympy kill via the mixed contraction
C:\Users\richa\AppData\Local\Temp\claude\D--UTD-Project-purdue\e2435927-3651-49b0-acfb-31f3430ee257\scratchpad\wlog.py -- shows the block swap 0<->1,2<->3,4<->5 leaves R1 invariant but reverses R_g for both anchors at once (so WLOG is spendable only once)

## step

STEP C3 / C4 / C5 of the ORBIT 26 axis-case argument: the claim that A = (1/4)P_{v-perp}, A' = (1/4)P_{u-perp}, rho = 2(A+A'), and hence that the {0,2,4} block share of <u|rho|u> equals (1-kappa^2)/4 - 3/8 <= -1/8 < 0.

## verdict

flawed

## problems

## claim

C3: 'C_6, C_7 orthogonal to v; D_6, D_7 orthogonal to u' — i.e. BOTH anchor blocks are killed by the axis case.

## why_wrong

X_i := C_j^dagger D_i is defined against ONE fixed anchor j, and Steps A/B/C run entirely inside that choice. The axis conclusion X_1=X_3=X_5=0 therefore delivers exactly two facts: C_j perp D_1,D_3,D_5 and (via Y_i=-X_i) D_j perp C_1,C_3,C_5 — for that single j. Nothing offered ties the two anchors together: (R1) ranges only over cycle groups 0<=g<h<=2 and never touches blocks 6,7, and (R2) has no (i=6, j=7) instance. So anchor 7 may land on the OPPOSITE axis (X'_0=X'_2=X'_4=0, giving C_7 perp D_0,D_2,D_4 and nothing about D_1,D_3,D_5), or fall into the 'some R_g = 0' branch that Step B does not cover at all. C1's sub-argument is exactly where this bites: 'if C_6,C_7 were linearly independent then D_1=D_3=D_5=0' silently uses C_7 perp D_i, which is not available. And this is not a harmless gap — the numerics have real slack without it. Keep everything anchor 6 does give (C_6=sqrt(1/8)w with w perp v, D_6=sqrt(1/8)z with z perp u, C_1,C_3,C_5 || u, D_1,D_3,D_5 || v, P_i=Q_i, P_6=P_7=1/8, the per-group matrix identity), leave C_7,D_7 free, and even impose the extra consequence that (R2) at j=7, i odd forces, namely |<v,C_7>|^2 = |<u,D_7>|^2. Explicit witness at kappa^2 = 1/2: v=(1,0), w=(0,1), u=(1,1)/sqrt2, z=(-1,1)/sqrt2, C_6=sqrt(1/8) w, D_6=sqrt(1/8) z, C_7=sqrt(1/8)(sqrt(0.9375) v + sqrt(0.0625) w), D_7=sqrt(1/8)(sqrt(0.9375) u - sqrt(0.0625) z). Then rho=2(A+A') is PSD with trace 1; <u|rho|u> = 0.5448904 while blocks {1,3,5} (=0.375) plus blocks {6,7} (=<u|A|u>=0.1552577) total 0.5302577, leaving +0.0146327 for blocks {0,2,4} — no contradiction. The mirror count along v has identical slack, and the residual matrices M_C = rho - (3/8)uu^dag - A, M_D = rho - (3/8)vv^dag - A' (trace 3/8, eigs 0.0068/0.3682) and the per-cycle-group N = rho/2 - (1/8)(uu^dag+vv^dag) (trace 1/4, eigs 0.0684/0.1816) are all PSD, with M_C+M_D=3N exactly. In this witness C3/C4/C5 are quantitatively false: |<C_6,C_7>|^2/(P_6 P_7) = 0.0625 (C3 needs 1), <u|rho|u> = 0.5449 where C4 predicts (1-kappa^2)/2 = 0.25, and C5's residue formula returns -0.25 where the true residue is +0.0146. Scanning all kappa and all admissible C_7,D_7, the best available slack is (1/8)*s(1-s)/(1+2s) with s=kappa^2, i.e. +0.016747 at kappa^2 = 0.366 — small, but strictly positive for every 0 < kappa < 1. So the whole contradiction rests on the both-anchors alignment, which is precisely the unproven part.

## severity

fatal

## claim

C3: 'A' = (1/4) P_{u-perp}'.

## why_wrong

The 1/4 is Q_6 + Q_7, not P_6 + P_7. It is correct here, but only because P_i = Q_i is one of the verified facts; C3 never invokes it. State it, or the top-side normalisation is asserted without support.

## severity

cosmetic

## claim

Notation: 'P_i = ||C_i||^2' vs 'P_w = orthogonal projector onto span(w)', and 'C_3 C_3^dagger + D_3 D_3^dagger = rho/2' for the anchor group.

## why_wrong

Two live collisions. (a) P is both a block weight and a projector, so 'P_6 + P_7 = 1/4' and 'P_{v-perp}' sit in the same line of C3. (b) C_g/D_g denote 2x2 group matrices while C_i/D_i denote block vectors, so 'C_3 C_3^dagger + D_3 D_3^dagger = rho/2' means group 3 = the anchor pair {6,7}, NOT block 3. Read with block-3 vectors it is a different and false statement: in the axis case C_3 || u and D_3 || v, so it would assert P_3(uu^dag + vv^dag) = rho/2, forcing rho into the u,v plane with P_3 = 1/4, contradicting the per-group weight bound. Any transcription of this step into Lean will hit that ambiguity.

## severity

cosmetic

## notes

Everything you asked me to check inside C3-C5 is correct; the single failure is the premise C3 imports.

(i) VERIFIED as a conditional. In C^2 the orthogonal complement of a unit v is one-dimensional, so C_6 = alpha w, C_7 = beta w for a unit w spanning v-perp, and A = (|alpha|^2+|beta|^2) w w^dagger = (P_6+P_7) P_{v-perp} = (1/4) P_{v-perp} exactly. Checked numerically over random v with random phases: ||A - 0.25*(I - v v^dag)|| ~ 1e-16. Note the identity needs BOTH vectors on the line — one alone would give 1/8, not 1/4 — which is why the antecedent is load-bearing.

(ii) VERIFIED. For a matrix M with columns m_1,m_2, M M^dag = m_1 m_1^dag + m_2 m_2^dag, so the anchor group's C_g C_g^dag is literally C_6 C_6^dag + C_7 C_7^dag = A and D_g D_g^dag = A'. The identity at the anchor group therefore gives rho = 2(A+A') correctly. Trace check pins the reading of rho: tr(A)=tr(A')=1/4 forces tr(rho)=1, which matches sum_{i<6} P_i + P_6 + P_7 = 3/4 + 1/4, confirming that "rho = sum_g C_g C_g^dag" runs over all FOUR groups (including the anchor), not just the three cycle groups.

FREE EXTRA FACT you are not using: taking the trace of the per-group identity gives 2(P_{2g}+P_{2g+1}) = 1/2, i.e. every group carries weight exactly 1/4. That is stronger than "sum_{i<6} P_i = 3/4" and it is what kills the degenerate boundary configurations (see below).

(iii) VERIFIED by direct computation. P_{v-perp} = I - v v^dag for unit v in C^2, so <u|P_{v-perp}|u> = 1 - |<v,u>|^2 = 1 - kappa^2, and <u|P_{u-perp}|u> = 0 identically. Hence <u|rho|u> = 2[(1/4)(1-kappa^2) + 0] = (1-kappa^2)/2 and <u|A|u> = (1-kappa^2)/4. Confirmed to 1e-10 on random unit u,v.

(iv) VERIFIED. (1-k^2)/2 - 3/8 - (1-k^2)/4 = (1-k^2)/4 - 3/8 is exact, and k^2 >= 0 gives <= -1/8. The decomposition {1,3,5} U {0,2,4} U {6,7} = {0,...,7} is exhaustive and disjoint, with no double counting: A enters once as the {6,7} share of the block sum and separately inside the identity rho = 2(A+A') — two expressions for the same operator, not two contributions. The contradiction is not on a knife edge: the deficit is (1-k^2)/4 - 3/8, i.e. between -1/8 (k=0) and -3/8 (k=1).

(v) VERIFIED. rho = sum_i C_i C_i^dag gives <u|rho|u> = sum_i |<u,C_i>|^2 termwise, each term >= 0. For C_i = c_i u with u a unit vector, |<u,C_i>|^2 = |c_i|^2 = ||C_i||^2 = P_i exactly — so blocks 1,3,5 contribute precisely P_1+P_3+P_5 = 3/8, not more and not less. u is well defined: C_1,C_3,C_5 all lie in the one-dimensional D_6-perp (D_6 nonzero since Q_6 = P_6 = 1/8), and at least one is nonzero since P_1+P_3+P_5 = 3/8 > 0. Same for v via C_6-perp.

SHORTER ROUTE (if you keep the argument): subtract A from both expressions for rho to get sum_{i<=5} C_i C_i^dag = A + 2A' directly, then <u| . |u> gives (1-kappa^2)/4 = sum_{i<=5} |<u,C_i>|^2 >= P_1+P_3+P_5 = 3/8, i.e. 1-kappa^2 >= 3/2 > 1. That closes it in one line, never mentions blocks {0,2,4}, and makes the margin (>= 1/8) visible.

ON PATCHING THE REAL GAP. The alignment may well be true; it is just not proved. Two data points. At kappa = 0 and kappa = 1 the unaligned region collapses to a single boundary point (C_7 || v exactly, D_7 || u exactly, with blocks {0,2,4} forced perpendicular to u and D_0,D_2,D_4 perpendicular to v). At that point (R1) for the three group pairs degenerates to the same J-orthogonality system on the pairs s_g = (conj(p_{2g}), d_{2g+1}), which forces either p_0=p_2=p_4=0 (contradicts P_0+P_2+P_4=3/8), or d_1=d_3=d_5=0 (contradicts Q_1+Q_3+Q_5=3/8), or some s_g = 0, which via P_i=Q_i makes that whole group weigh 0 and contradicts the per-group weight 1/4. So the boundary dies. But for 0 < kappa < 1 the positivity counts alone leave strict slack (max +0.0167), so the closure must come from (R1) applied with C_0,C_2,C_4 and D_0,D_2,D_4 NOT parallel — where (R1) reduces to a v^T + conj(u) b^T = 0 and admits the nontrivial solutions a = lambda conj(u), b = -lambda v. That case is not treated anywhere and is what a repair has to handle.

OUT OF SCOPE BUT FLAGGING: Step B's lemma assumes all three R_g nonzero, so even a fully repaired C3-C5 only closes the branch where R_0, R_1, R_2 are all nonzero; the branches with some R_g = 0 are untouched by C3-C5.

## gaps

## summary

VERDICT: the derivation as written covers only 1 of the 10 leaves of the branch tree, and the hole you flagged is REAL — Step C1 silently merges the two anchors, and the two anchors genuinely can (a priori) land on different axes. The mass/moment bookkeeping of C4-C5 is *provably consistent* in the mixed-axis branch, so no repair of C4-C5 can close it; a genuinely new relation is needed (the cross-anchor contraction of R1, which is available and legitimate). All other missing branches do close, but each needs its own argument, and two of them need a fact you did not list: the per-group trace identity P_{2g}+P_{2g+1} = 1/4.

NOTATION for everything below. <a,b> is conjugate-linear in the first slot. For anchor j put X^{(j)}_i = C_j^dagger D_i = <C_j,D_i>; write x_i := X^{(6)}_i, y_i := X^{(7)}_i. R2 gives <C_i,D_j> = -X^{(j)}_i. R^{(j)}_g = (X^{(j)}_{2g}, X^{(j)}_{2g+1}), B(r,s) := r J s^T = r_1 s_2 + r_2 s_1 (bilinear, NOT sesquilinear). Z_j := {g in {0,1,2} : R^{(j)}_g = 0}. Note C_j, D_j are nonzero for j = 6,7 because P_j = Q_j = 1/8.

DERIVED FACT USED THROUGHOUT (not in your list, but it follows from your matrix moment identity): take the trace of C_g C_g^dagger + D_g D_g^dagger = rho/2. tr(C_g C_g^dagger) = P_{2g}+P_{2g+1}, tr(D_g D_g^dagger) = Q_{2g}+Q_{2g+1} = P_{2g}+P_{2g+1}, and tr rho = 1, hence P_{2g}+P_{2g+1} = 1/4 for EVERY group, anchor included. This is strictly stronger than "sum_{i<6} P_i = 3/4" and is load-bearing in the |Z_j| = 1 and |Z_j| = 2 branches.

TWO SYMMETRIES that legitimately collapse branches. (S1) The simultaneous within-group swap sigma: i -> i XOR 1 for all i <= 5 (anchors fixed). It maps the four R1 terms conj(C_{2g})D_{2h+1}^T + conj(C_{2g+1})D_{2h}^T + conj(C_{2h})D_{2g+1}^T + conj(C_{2h+1})D_{2g}^T onto the same set, fixes R2, and swaps P_1+P_3+P_5 with P_0+P_2+P_4 (both 3/8). It exchanges the two axes. WARNING: swapping inside ONE group only is NOT a symmetry (it turns R1 into the other pairing) — only the global swap is. (S2) The full S_3 permuting the three cycle groups: R1 ranges over all pairs, R2 is per-block, all group masses are 1/4, and group permutations preserve the even/odd index classes. This lets you take the zero group to be group 0 WLOG.

BRANCH TREE AND STATUS (details in the gaps below):
  per anchor j: |Z_j| = 3 -> closes (Z3); |Z_j| = 2 -> closes (Z2); |Z_j| = 1 -> closes (Z1, hardest). Hence Z_6 = Z_7 = empty and Step B applies to BOTH anchors separately.
  then: axes differ -> closes only via the new cross-anchor relation (MAIN HOLE); axes equal, first -> your Step C (with a cleaner ending); axes equal, second -> image of the previous under S1.

STEP B ITSELF IS CORRECT and slightly stronger than stated: three nonzero pairwise-J-orthogonal vectors in C^2 must each be ISOTROPIC. Proof: if B(r_0,r_0) != 0 then r_0^perp is a line missing r_0, so r_1 ‖ r_2, and B(r_1,r_2)=0 then forces B(r_1,r_1)=0, so r_1 is isotropic, i.e. on an axis, say r_1 = (t,0); B(r_0,r_1) = t r_{0,2} = 0 puts r_0 on the same axis, contradicting B(r_0,r_0) != 0. So all three are isotropic (= on axes), and two nonzero vectors on DIFFERENT axes have B = ab != 0, so the axis is common. Only pairwise relations are used, which is all R1 supplies.

A CLEANER ENDING for the covered branch (replaces C4-C5, no kappa needed): with both anchors on axis 1 you have C_1,C_3,C_5 ‖ u and D_6,D_7 perp u, so <u|A'|u> = 0 and A + A' = rho/2 gives <u|A|u> = <u|rho|u>/2. Also <u|rho|u> = sum_i |<u,C_i>|^2 >= (P_1+P_3+P_5) + <u|A|u> = 3/8 + <u|rho|u>/2, so <u|rho|u> >= 3/4 and <u|A|u> >= 3/8 > 1/4 = tr A >= <u|A|u>. Contradiction. (v, kappa and "C_6 ‖ C_7" are never needed.)

## gaps

## what

MAIN HOLE — Step C1 uses the vanishing pattern of BOTH anchors at once, but Step A/B run separately for each anchor and only constrain that anchor's own triple. Nothing in R1/R2 as stated ties X^{(6)} to X^{(7)}, so a priori anchor 6 can sit on axis 1 (x_1=x_3=x_5=0) while anchor 7 sits on axis 2 (y_0=y_2=y_4=0).

## why_it_matters

In the mixed-axis branch C1/C2 collapse: from anchor 6 you get only C_6 perp {D_1,D_3,D_5} and D_6 perp {C_1,C_3,C_5}; from anchor 7 only C_7 perp {D_0,D_2,D_4} and D_7 perp {C_0,C_2,C_4}. So A is NOT (1/4)P_{v-perp}, A' is NOT (1/4)P_{u-perp}, and the C5 count breaks: the u-line now carries only 3/8 of the C-mass while a SECOND line u' carries the other 3/8. Worse, the branch is fully consistent with every moment fact you have, so C4-C5 can never be patched into closing it. Explicitly: C_1,C_3,C_5 ‖ u, C_0,C_2,C_4 ‖ u', D_1,D_3,D_5 ‖ v, D_0,D_2,D_4 ‖ v', C_6 ‖ v-perp, C_7 ‖ v'-perp, D_6 ‖ u-perp, D_7 ‖ u'-perp. Group g identity reads P_{2g}(P_{u'}+P_{v'}) + P_{2g+1}(P_u+P_v) = rho/2, which with P_i = 1/8 for all i <= 5 is satisfied identically, and the anchor identity reduces to P_u+P_v+P_{u'}+P_{v'} = 2I, satisfiable (e.g. u perp u', v perp v'). A purely metric/mass argument therefore cannot close this branch.

## how_to_close

Use a CROSS-ANCHOR contraction of R1, which is legitimate and not yet exploited. R1 is a full 2x2 matrix identity M(g,h) = 0, so contracting with any vectors v (index a) and w (index b) is allowed: sum over the four terms of <C_i,v><w,D_k> = 0. Take v = D_7 and w = C_6. Convert each factor by ITS OWN R2 (<C_i,D_7> = -y_i, <C_6,D_k> = x_k) — this is the step your Step A does with a single anchor, and it is exactly why mixing is still valid. Result, for each pair g<h:  y_{2g}x_{2h+1} + y_{2g+1}x_{2h} + y_{2h}x_{2g+1} + y_{2h+1}x_{2g} = 0, i.e. the polarized identity B(R^{(6)}_g, R^{(7)}_h) + B(R^{(7)}_g, R^{(6)}_h) = 0. In the mixed branch x_odd = 0 and y_even = 0, so it collapses to y_{2g+1}x_{2h} + y_{2h+1}x_{2g} = 0, i.e.  (i) x_0 y_3 + x_2 y_1 = 0, (ii) x_0 y_5 + x_4 y_1 = 0, (iii) x_2 y_5 + x_4 y_3 = 0. Since Z_6 = Z_7 = empty (see the other gaps), x_0,x_2,x_4,y_1,y_3,y_5 are ALL nonzero. Multiply (i) by (iii): x_0 y_3 x_2 y_5 = x_2 y_1 x_4 y_3; cancel x_2 y_3 != 0 to get x_0 y_5 = x_4 y_1, which with (ii) gives 2 x_4 y_1 = 0. Contradiction. (Independent second proof, if you want redundancy: in the mixed branch all six cycle C's and D's are aligned, so R1 splits along the linearly independent rank-ones conj(u')v^T and conj(u)v'^T, yielding conj(a_0)b_3 + conj(a_2)b_1 = 0, conj(a_0)b_5 + conj(a_4)b_1 = 0, conj(a_2)b_5 + conj(a_4)b_3 = 0 for C_{2k} = a_{2k}u', D_{2k+1} = b_{2k+1}v, and the same product trick kills it; as pure phases the three equations say B_3-B_1+A_2-A_0 = B_5-B_1+A_4-A_0 = B_5-B_3+A_4-A_2 = pi mod 2pi, whose third is the difference of the first two, forcing pi = 0.)

## what

Exactly one R^{(j)}_g = 0 (|Z_j| = 1), for either anchor. Step B is inapplicable: the two surviving vectors satisfy ONE J-orthogonality relation, which does not force an axis (e.g. r = (1,1), s = (1,-1) have B(r,s) = 0 and neither is isotropic).

## why_it_matters

This is the largest uncovered family — three choices of vanishing group per anchor — and without it you cannot assert Z_j = empty, which is the precondition for Step B and for the cross-anchor argument above.

## how_to_close

WLOG (S_3) Z_j = {0}. R^{(j)}_0 = 0 says C_j perp D_0,D_1 and (via R2) D_j perp C_0,C_1, so with u spanning D_j^perp and v spanning C_j^perp: C_0 = a_0 u, C_1 = a_1 u, D_0 = b_0 v, D_1 = b_1 v, |a_i| = |b_i| = sqrt(P_i), a_0,a_1 not both 0 since P_0+P_1 = 1/4. Group-0 moment identity then gives (1/4)(P_u + P_v) = rho/2, i.e. rho = (1/2)(P_u+P_v); its eigenvalues are (1 +- sqrt(k))/2 with k := |<u,v>|^2. Also C_j ‖ v-perp and D_j ‖ u-perp with norm^2 1/8, so the anchor identity A + A' = rho/2 forces C_{j'}C_{j'}^dagger + D_{j'}D_{j'}^dagger = (3/8)(P_u+P_v) - (1/4)I, whose PSD-ness needs (3/8)(1-sqrt k) >= 1/4, i.e. k <= 1/9, so <u|rho|u> = (1+k)/2 <= 5/9. Now use the FULL matrix R1 on pairs (0,1) and (0,2): e.g. (0,1) reads conj(u)[conj(a_0)D_3 + conj(a_1)D_2]^T + [b_1 conj(C_2) + b_0 conj(C_3)]v^T = 0, a sum of two rank-<=1 matrices, hence conj(a_0)D_3 + conj(a_1)D_2 ‖ v and conj(b_1)C_2 + conj(b_0)C_3 ‖ u (the degenerate case makes both zero, same conclusion). Writing d_i := <v-perp, D_i>, c_i := <u-perp, C_i>: conj(a_0)d_3 + conj(a_1)d_2 = 0, conj(a_0)d_5 + conj(a_1)d_4 = 0, conj(b_1)c_2 + conj(b_0)c_3 = 0, conj(b_1)c_4 + conj(b_0)c_5 = 0. Note x_i = conj(gamma) d_i where C_j = gamma·(v-perp), so Step A's surviving relation X_2X_5 + X_3X_4 = 0 is d_2 d_5 + d_3 d_4 = 0. CASE a_0,a_1 both nonzero: d_3 = -lambda d_2, d_5 = -lambda d_4 with lambda = conj(a_1)/conj(a_0) != 0, so d_2d_5 + d_3d_4 = -2 lambda d_2 d_4 = 0; d_2 = 0 forces d_3 = 0 hence R^{(j)}_1 = 0, and d_4 = 0 forces R^{(j)}_2 = 0 — both contradict |Z_j| = 1. CASE a_1 = 0 (so P_1 = 0, C_1 = D_1 = 0, P_0 = 1/4): the four relations give d_3 = d_5 = 0 and c_3 = c_5 = 0, i.e. C_0,C_3,C_5 all ‖ u, so <u|rho|u> >= P_0 + P_3 + P_5 = 1/4 + 3/8 = 5/8 > 5/9. Contradiction. CASE a_0 = 0: mirror (c_2 = c_4 = 0, C_1,C_2,C_4 ‖ u, mass 1/4 + 3/8 = 5/8 > 5/9). Contradiction.

## what

Exactly two R^{(j)}_g = 0 (|Z_j| = 2). Step B is inapplicable (only one nonzero vector, no constraint at all on it).

## why_it_matters

Three sub-branches per anchor; skipped entirely by the current write-up.

## how_to_close

Short and self-contained, one anchor suffices. WLOG Z_j = {0,1}. Then C_j perp D_0..D_3 and D_j perp C_0..C_3, so C_0..C_3 lie on the line span{u} = D_j^perp and D_0..D_3 on span{v} = C_j^perp. Group-0 identity gives (P_0+P_1)(P_u+P_v) = rho/2 with P_0+P_1 = 1/4, so rho = (1/2)(P_u+P_v). Blocks 0..3 carry C-mass P_0+P_1+P_2+P_3 = 1/2, all in direction u, so sum_{i in {4,5,6,7}} C_i C_i^dagger = rho - (1/2)P_u = (1/2)P_v. The right side is rank <= 1 along v, so EVERY C_i with i in {4,5,6,7} is parallel to v — in particular C_j ‖ v. But C_j perp v and |C_j|^2 = 1/8 != 0. Contradiction. (Works verbatim when u ‖ v.) Note this uses the per-group mass 1/4 twice, hence the trace fact in the summary.

## what

All three R^{(j)}_g = 0 (|Z_j| = 3), i.e. C_j perp D_i for every i <= 5.

## why_it_matters

Step A's conclusions become 0 = 0 and Step B is vacuous; the branch is invisible to the current argument even though it is the most degenerate one.

## how_to_close

One anchor suffices. R2 gives <C_i,D_j> = 0 for all i <= 5 too, so all C_0..C_5 lie on span{u} = D_j^perp (total mass 3/4) and all D_0..D_5 on span{v} = C_j^perp (total 3/4); also C_j perp v, D_j perp u. Put a := <u|A|u>, a' := <u|A'|u>. Then <u|rho|u> = 3/4 + a, and A + A' = rho/2 gives a + a' = (3/4 + a)/2, i.e. a + 2a' = 3/4. Since a <= tr A = 1/4 and a' <= tr A' = 1/4, equality must hold throughout, so a' = tr A' forces A' to be supported on u, i.e. D_6 and D_7 both ‖ u. But D_j perp u and D_j != 0. Contradiction.

## what

The SECOND-axis case with both anchors there (x_0 = x_2 = x_4 = 0 = y_0 = y_2 = y_4).

## why_it_matters

Step C is written only for the first axis; the write-up says "say all R_g on the FIRST axis" without justifying the WLOG, and the WLOG is not free — the two index classes {0,2,4} and {1,3,5} sit differently inside R1's four-term structure.

## how_to_close

It IS a genuine WLOG, but cite the symmetry S1 explicitly: the global within-group swap sigma: i -> i XOR 1 for i <= 5 (anchors untouched) permutes the four terms of every R1 relation among themselves, fixes every R2 relation, and exchanges P_1+P_3+P_5 with P_0+P_2+P_4, both equal to 3/8. It carries axis 2 to axis 1. Alternatively run the argument directly: C_6,C_7 perp D_0,D_2,D_4 and D_6,D_7 perp C_0,C_2,C_4, take u = the common direction of C_0,C_2,C_4 (mass P_0+P_2+P_4 = 3/8) and repeat the trace argument verbatim. Do NOT try to justify the WLOG with a per-group swap — swapping inside a single group maps R1 to the OTHER pairing and is not a symmetry.

## what

Step C1's internal logic is weaker/rougher than it needs to be, independently of the two-anchor issue: it argues "if C_6, C_7 were linearly independent then D_1 = D_3 = D_5 = 0", concluding only C_6 ‖ C_7.

## why_it_matters

As stated it hides which anchor supplies which fact, and "C_6 ‖ C_7" is not actually the quantity C3/C4 need — they need C_6 and C_7 both ORTHOGONAL TO v, which is a strictly stronger statement that does not follow from parallelism alone.

## how_to_close

State the two inferences separately and at full strength. From anchor j alone: C_j != 0 (P_j = 1/8), so D_1,D_3,D_5 all lie on the single line C_j^perp = span{v_j}; and D_j != 0, so C_1,C_3,C_5 all lie on D_j^perp = span{u_j}. That already gives everything (the D's are not all zero since Q_1+Q_3+Q_5 = 3/8, likewise the C's). The upgrade "C_6 AND C_7 perp v, D_6 AND D_7 perp u" then follows only after the two anchors have been shown to share an axis (previous gaps), at which point u_6 = u_7 = u and v_6 = v_7 = v and C_6 ‖ C_7 is a corollary, not a hypothesis.

## what

The fact P_{2g} + P_{2g+1} = 1/4 for every group is used implicitly (and is needed) but is not on your verified-facts list; your list only gives the aggregates 3/4, 3/8, 3/8 and the anchor's 1/4.

## why_it_matters

The |Z_j| = 2 branch needs P_0+P_1+P_2+P_3 = 1/2 exactly, and the |Z_j| = 1 branch needs P_0+P_1 = 1/4 exactly, to pin rho = (1/2)(P_u+P_v). With only the aggregates those branches do not close.

## how_to_close

Derive it from the matrix moment identity you already verified: tr(C_g C_g^dagger + D_g D_g^dagger) = tr(rho)/2 = 1/2, and tr(C_g C_g^dagger) = P_{2g}+P_{2g+1} = Q_{2g}+Q_{2g+1} = tr(D_g D_g^dagger) using P_i = Q_i; hence P_{2g}+P_{2g+1} = 1/4 for each of the four groups. Add it to the verified-facts list (it is a consequence of facts you already machine-checked, so no new KL input is required).

## what

Robustness detail inside the covered branch: C5 needs BOTH D_6 and D_7 perpendicular to u (to make blocks 6,7 contribute exactly <u|A|u> and to get A' = (1/4)P_{u-perp}), and separately C4 needs the exact identity rho = 2(A+A'), which is only the anchor-group instance of the moment identity.

## why_it_matters

If you keep the kappa route, the inequality chain silently assumes A and A' are exactly rank-one projectors scaled by 1/4; if either anchor block fails to be orthogonal to v (resp. u) the projector form is wrong and the final number (1-kappa^2)/4 - 3/8 is not what the moment identity gives. A formalization would stall exactly there.

## how_to_close

Drop C4's kappa computation and use the trace-only ending: <u|A'|u> = 0 (needs D_6,D_7 perp u only), A + A' = rho/2 gives <u|A|u> = <u|rho|u>/2, and <u|rho|u> >= 3/8 + <u|A|u> gives <u|rho|u> >= 3/4, so <u|A|u> >= 3/8 > 1/4 = P_6+P_7 = tr A. This needs no v, no kappa, no rank-one form for A, and no non-negativity of the {0,2,4} remainder; it is also the version that transfers unchanged to the second-axis branch. Zero blocks among C_1,C_3,C_5 or D_1,D_3,D_5 are harmless throughout (a zero vector lies on every line); only the total masses 3/8 and the nonvanishing of C_j, D_j are used.

## summary

Steps A, C4 and C5 are algebraically sound as written (I re-derived every index contraction and checked it numerically in chk.py: the entrywise form of R1 matches conj(C_g) J D_h^T + conj(C_h) J D_g^T, and the double contraction with D_j on a and conj(C_j) on b reproduces exactly Y_0X_3+Y_1X_2+Y_2X_1+Y_3X_0, hence R_g J R_h^T = 0). Step B's lemma is TRUE as stated and its proof is correct (J is nondegenerate, so r_0 nonzero forces r_1, r_2 into the 1-dim beta-complement, forcing r_1 isotropic, forcing all three onto one coordinate axis). No step uses a forbidden per-edge matrix relation D_i C_k^dag + D_k C_i^dag = 0: every anchor consequence stays at the scalar level of (R2), and C3's structure comes from "orthogonal to a nonzero vector => lies in a line", not from a matrix identity. But the chain has two genuine holes, both between Step B and Step C1. (1) Step B requires all three R_g nonzero, and nothing verified forces X_i to be nonzero. (2) Far more seriously, Step A/B run per anchor j, so the axis they select is per anchor, and C1 silently assumes anchors 6 and 7 select the SAME axis. I built an explicit MIXED-AXIS witness (mixed2.py, u=e0, u'=e1: C_1,C_3,C_5,C_7,D_1,D_3,D_5,D_7 // e0 and C_0,C_2,C_4,C_6,D_0,D_2,D_4,D_6 // e1, all norms 1/8) that satisfies EVERY verified fact you listed (P_i=Q_i=1/8 for all eight blocks, both 3/8 sums, rho = I/2 = sum C C^dag = sum D D^dag, and the matrix moment identity to machine precision for all four groups including the anchor), satisfies (R2) exactly, and satisfies Step A's conclusion for BOTH anchors with all three R_g nonzero for both -- yet C_6 is not parallel to C_7, A = I/8 has rank two rather than being (1/4)P_{v-perp}, and C5's ledger closes at exactly 0 instead of -1/8. So the whole of C1-C5 evaporates on that branch. The good news: the branch IS excludable, just not with the tools the derivation uses. Contracting (R1) on a with D_j and on b with conj(C_j') for DIFFERENT anchors j != j' (legal: uses only R1 and R2) gives R^(j)_g J (R^(j'))_h^T + R^(j)_h J (R^(j'))_g^T = 0, which in the mixed case reads x_g y_h + x_h y_g = 0 for the three pairs, i.e. t_g + t_h = 0 for t_g = y_g/x_g, forcing t_0=t_1=t_2=0 and contradicting nonvanishing. mixed2.py confirms this independently: with (R1) forced to vanish on pairs (0,1) and (1,2), pair (0,2) has residual 0.25, and the cross-anchor contraction is exactly the scalar that detects it.

## gaps

## what

FATAL. Step C1 says "X_i = 0 for i in {1,3,5} and BOTH anchors j = 6,7". But Step A and Step B were run for a FIXED anchor j: X_i := C_j^dag D_i depends on j, so the axis produced by Step B is a per-anchor choice. C1 (and C2, and the rank-one form of A and A' in C3) silently assumes anchor 6 and anchor 7 land on the SAME axis. Equivalently, the "say all R_g on the FIRST axis" WLOG of Step C is legitimately available only once; it is being spent twice. Nothing in the verified facts, in (R1), or in (R2) as used links X^(6) to X^(7): the only thing that would is C_6 parallel to C_7, which is precisely what C1 is trying to prove.

## why_it_matters

The mixed-axis branch (anchor 6 on axis 1, anchor 7 on axis 2) is not merely unhandled -- I constructed it explicitly and it passes every ingredient the derivation is entitled to use. In C:\Users\richa\AppData\Local\Temp\claude\D--UTD-Project-purdue\e2435927-3651-49b0-acfb-31f3430ee257\scratchpad\mixed2.py take u=e0, u'=e1 and put C_1,C_3,C_5,C_7,D_1,D_3,D_5,D_7 along e0 and C_0,C_2,C_4,C_6,D_0,D_2,D_4,D_6 along e1, all moduli 1/sqrt(8). Then: P_i = Q_i = 1/8 for all eight blocks; P_1+P_3+P_5 = P_0+P_2+P_4 = 3/8; P_6=P_7=1/8; rho = I/2 and equals both sum_i C_i C_i^dag and sum_i D_i D_i^dag; the matrix moment identity C_g C_g^dag + D_g D_g^dag = rho/2 holds to 3e-17 for all four groups INCLUDING the anchor; (R2) holds exactly (residual 8e-17); and Step A's relations R_g J R_h^T = 0 hold identically for both anchors with all three R_g nonzero for each. X^(6) is supported on even indices (so R^(6)_g = (nonzero,0), axis 1), X^(7) on odd indices (so R^(7)_g = (0,nonzero), axis 2). On this configuration C1's conclusion is FALSE: C_6 is not parallel to C_7. C3's A = (1/4)P_{v-perp} is FALSE: A = I/8, rank two. And C5's ledger reads <u|rho|u> = 1/2, blocks 1,3,5 contribute 3/8, <u|A|u> = 1/8, leaving exactly 0 for blocks 0,2,4 -- no contradiction at all. So the argument as written proves nothing on this branch, and this branch is a full 1/4 of the case tree (mixed either way).

## how_to_close

Two independent routes; the first is cheap and I verified it kills the witness. (a) CROSS-ANCHOR CONTRACTION. Contract (R1) on index a with D_j and on index b with conj(C_j') for j != j' (both in {6,7}). Using (R2) for anchor j to write Y^(j) = -X^(j), this yields, for every 0<=g<h<=2, R^(j)_g J (R^(j'))_h^T + R^(j)_h J (R^(j'))_g^T = 0. This uses only (R1) and the anchor scalar (R2) -- no per-edge matrix relation. Setting j=j' recovers Step A (times 2). In the mixed case R^(6)_g = (x_g,0) and R^(7)_g = (0,y_g), so the relation reads x_g y_h + x_h y_g = 0 for the three pairs; dividing by x_g x_h (legal exactly under Step B's hypothesis) gives t_0+t_1 = t_0+t_2 = t_1+t_2 = 0 with t_g = y_g/x_g, hence t_0=t_1=t_2=0, hence all y_g = 0, contradicting the axis-2 assumption. When the two anchors share an axis the cross relation is identically satisfied, so nothing is lost in the good case. mixed2.py confirms this from the other side: forcing (R1) to vanish on pairs (0,1) and (1,2) leaves pair (0,2) with residual 0.25, and the cross-anchor scalar at (0,2) is exactly the nonzero quantity. (b) Alternatively prove C_6 parallel to C_7 (and D_6 parallel to D_7) up front, directly from the moment system. Then C_7 = mu C_6 gives X^(7) = conj(mu) X^(6), so the two anchors trivially share an axis, C1 becomes unnecessary, and the whole gap disappears.

## what

FATAL. Step B's lemma requires r_0, r_1, r_2 all NONZERO. The derivation supplies no reason that R_g = (X_{2g}, X_{2g+1}) is nonzero for any g. X_i = C_j^dag D_i is an inner product of two nonzero vectors in C^2 and can perfectly well vanish; indeed R_g = 0 just says C_j is orthogonal to both D_{2g} and D_{2g+1}. Note also that (R1) exists only for g < h (no g = h instance), so beta(R_g, R_g) = 2 X_{2g} X_{2g+1} is NOT known to vanish -- no R_g is known to be isotropic on its own. That is exactly why the nonvanishing hypothesis is load-bearing rather than cosmetic.

## why_it_matters

If even one R_g vanishes the lemma's conclusion fails outright: R_0 = 0, R_1 = (1,1), R_2 = (1,-1) satisfies every relation Step A produces (R_1 J R_2^T = 1*(-1) + 1*1 = 0) and no coordinate of R_1 or R_2 vanishes, so there is no transversal index set on which X vanishes and Step C never gets started. The same happens with two of the three zero, e.g. R_0 = R_1 = 0 and R_2 = (a,b) with a,b both nonzero. Only the all-zero branch X^(j) = 0 is harmless (it kills both transversals at once, and C1-C5 then run, in fact more strongly). So the case tree Step C must cover is: for each anchor, (a) all three R_g nonzero -> axis, (b) some but not all X^(j) vanish -> NO conclusion, (c) X^(j) identically zero -> fine. Branch (b) is entirely uncovered.

## how_to_close

Do not contract (R1) all the way down to a scalar. Contracting only on index b with conj(C_j) gives the VECTOR identity conj(Cmat_g) J R_h^T + conj(Cmat_h) J R_g^T = 0 in C^2 (Cmat_g = [C_{2g} | C_{2g+1}]), and contracting only on index a with D_j gives the mirror R_g J Dmat_h^T + R_h J Dmat_g^T = 0. I verified both against the entrywise form numerically (chk.py, residuals ~1e-15); both follow from (R1) alone, so nothing forbidden is introduced, and Step A is just these contracted once more. Now if R_g = 0 then conj(Cmat_g) J R_h^T = 0 and R_h J Dmat_g^T = 0 for both h != g. Since J is invertible, if EITHER Cmat_g or Dmat_g is nonsingular then R_h = 0 for both h, i.e. X^(j) is identically zero -- branch (c), which the existing C1-C5 handle. So branch (b) survives only when the group with the vanishing R_g has BOTH Cmat_g and Dmat_g of rank <= 1, i.e. C_{2g} parallel to C_{2g+1} and D_{2g} parallel to D_{2g+1}. Attack that residue with the group moment identity: rank-one Cmat_g Cmat_g^dag with trace 1/4 forces it to be (1/4)P_w, likewise (1/4)P_w' for D, hence rho = (1/2)(P_w + P_w') is pinned to a very rigid form that must then be reconciled with the other three groups' identities.

## what

The rank-one form of the anchor blocks in C3, A = (1/4)P_{v-perp} and A' = (1/4)P_{u-perp}, is the real load-bearing consequence, and it needs BOTH anchor blocks to lie in the single line v-perp (resp. u-perp). The write-up presents C1 (C_6 parallel to C_7) as the step that does this, but C1 is not what defines v: v is already a well-defined line as soon as C_6 is nonzero (D_1,D_3,D_5 lie in C_6-perp). What C1 actually supplies is the anchor-7 half, and it supplies it only under the same-axis assumption of gap 1.

## why_it_matters

This pinpoints where a mixed-axis or otherwise incomplete branch does its damage: in the witness A = I/8, so <u|A|u> = 1/8 rather than the claimed (1-kappa^2)/4 tied to <u|rho|u> = (1-kappa^2)/2, and the whole C4/C5 ledger rebalances harmlessly. If A is allowed rank two, C5's arithmetic gives no contradiction whatsoever. Also worth noting that A' = (1/4)P_{u-perp} quietly uses Q_6 + Q_7 = 1/4, i.e. the verified P_i = Q_i together with P_6 = P_7 = 1/8 -- that part is fine, but it should be cited explicitly since the argument is written in P's.

## how_to_close

State C3 as the single claim "A is rank one with A = (1/4)P_{Cmat6-line}" and derive it from (i) C_6, C_7 both nonzero and parallel plus (ii) P_6 + P_7 = 1/4, and derive (i) either from gap 1's repair (a) or, better, from an independent proof that C_6 is parallel to C_7 in the moment system. Do the same for A'. Then C4/C5 need nothing else. Separately, C4/C5 can be shortened so kappa never appears: since A' = (1/4)P_{u-perp} annihilates u, rho = 2(A + A') gives <u|rho|u> = 2<u|A|u>; C5's ledger says <u|rho|u> >= 3/8 + <u|A|u>; hence <u|A|u> >= 3/8, contradicting <u|A|u> <= tr A = 1/4. That removes u, v normalization and the (1-kappa^2) bookkeeping from the contradiction entirely, leaving only the >= 0 positivity and tr A = 1/4.

## what

The identification "all R_g on the first coordinate axis" <=> "X_1 = X_3 = X_5 = 0" assumes the within-group bit c used in the machine-checked (R1) masks is labelled the SAME way in all three cycle groups, and that this labelling agrees with the block indexing 2g, 2g+1 used in the verified fact P_1 + P_3 + P_5 = 3/8.

## why_it_matters

If the c-labelling is flipped in one group relative to the mask convention (say group 2 is really (X_5, X_4)), the common-axis conclusion is a MIXED transversal such as {1,3,4}. The verified facts give you only the two parity sums, both 3/8; the sum P_1 + P_3 + P_4 is not among them and is not determined by anything listed. C5 would then be quoting a number it does not have. A uniform flip is harmless -- c -> 1-c applied in all groups to both C and D maps the (R1) summand C_{2g+c} D_{2h+1-c} onto itself and leaves (R2) and the anchor untouched, and both parity classes carry 3/8, so the one-time WLOG in Step C is genuinely justified -- but a non-uniform flip is not.

## how_to_close

Re-derive the (R1) masks and confirm that a single global labelling of the virtual bit c (equivalently, a single choice of which of the two blocks in each group is "even") is what makes (R1) take the form conj(C_g) J D_h^T + conj(C_h) J D_g^T simultaneously for all three pairs. Record that convention alongside the P-sum facts. If it turns out non-uniform, either re-index to make it uniform, or add the missing mixed-transversal P-sums to the verified list before C5 can use them.

## what

C4 applies the matrix moment identity AT THE ANCHOR GROUP, and C5 uses rho = sum over ALL EIGHT blocks. Both are indexing conventions that the fact list leaves slightly open ("rho = sum_g C_g C_g^dag" without stating the range of g, and "verified per group" without stating whether the anchor group was among them).

## why_it_matters

If rho were the sum over the three cycle groups only, tr rho = 3/4, and the anchor instance of the identity would read P_6+P_7+Q_6+Q_7 = 1/2 versus tr(rho)/2 = 3/8 -- inconsistent -- so the intended reading is certainly "all four groups", and my witness confirms all four instances hold with rho = I/2. But if the anchor instance had in fact never been machine-checked, C4's rho = 2(A + A') would be an unverified input and the entire contradiction would rest on it.

## how_to_close

Confirm explicitly that the moment identity was verified for g = anchor as well as the three cycle groups, and that rho is defined as the sum over all four (equivalently, tr rho = 1 and rho = sum_{i=0}^{7} C_i C_i^dag = sum_{i=0}^{7} D_i D_i^dag). Pin this in the write-up/Lean statement rather than leaving it to the reader; it is one line and it is the hinge of C4.

## what

Every nonvanishing and normalization used inside Step C, checked one by one. C_6, C_7, D_6, D_7 nonzero; at least one of C_1, C_3, C_5 nonzero and at least one of D_1, D_3, D_5 nonzero (needed to pin the directions u and v and to make the C1/C2 contradictions bite); u, v taken as unit vectors; kappa = |<u,v>| <= 1; the reduction of Y_i X_k products to -X_i X_k.

## why_it_matters

These are the places a proof of this shape usually dies, so it is worth recording that here they do NOT. If any of them failed the corresponding contradiction would be vacuous rather than wrong -- e.g. if all of C_1, C_3, C_5 were zero there would be no u, and C5 would be comparing nothing.

## how_to_close

All are JUSTIFIED by the verified facts and need no action: C_6, C_7 nonzero from P_6 = P_7 = 1/8 and D_6, D_7 nonzero from Q_i = P_i; the C-direction u exists because P_1+P_3+P_5 = 3/8 > 0 and is a single line because D_6 is nonzero (C_{1,3,5} all lie in D_6-perp, which is 1-dimensional in C^2); symmetrically v from Q_1+Q_3+Q_5 = 3/8 and C_6 nonzero; normalization divides only by nonzero norms; kappa <= 1 is Cauchy-Schwarz on unit vectors, and C5 needs only the crude bound (1-kappa^2)/4 <= 1/4 -- there is no division by (1-kappa^2) or by kappa anywhere, so the degenerate kappa = 0 and kappa = 1 cases are covered. "C_1, C_3, C_5 parallel to u" tolerates zero vectors, and C5's step sum_{1,3,5} |<u,C_i>|^2 = P_1+P_3+P_5 needs exact parallelism (an inequality here would point the wrong way), which the axis case does supply. C1's "two linearly independent vectors in C^2 have zero common orthogonal complement" is correct.

## what

The quadratic form in Steps A and B is the complex SYMMETRIC BILINEAR form beta(r,s) = r J s^T, with no conjugation -- not the Hermitian inner product. The write-up gets this right, but it is worth flagging because the two readings differ qualitatively and the conflation is an easy and fatal one.

## why_it_matters

Under the Hermitian reading, three pairwise-orthogonal nonzero vectors in C^2 are impossible and the axis case would appear to close instantly -- a false proof. Under the correct bilinear reading, isotropic vectors exist (beta(r,r) = 2 r_0 r_1 = 0 exactly on the coordinate axes), so the axis case is a genuine surviving branch that must be killed by the counting argument of C3-C5. Relatedly, the products Y_a X_b become genuinely bilinear in X only because (R2) is invoked to substitute Y = -X; without (R2) Step A gives only the weaker mixed statement R^Y_g J (R^X_h)^T + R^Y_h J (R^X_g)^T = 0, and Step B does not apply to it at all.

## how_to_close

No fix needed -- the derivation is correct here. When formalizing, state Step B over an abstract nondegenerate symmetric bilinear form on a 2-dimensional space and make the isotropy step explicit (r_0 nonzero => r_1, r_2 span the 1-dimensional beta-complement of r_0 => r_1, r_2 parallel => beta(r_1,r_1) = 0 => r_1 isotropic => r_1-perp = C r_1 contains r_0). That formulation makes the all-nonzero hypothesis impossible to drop by accident, and makes clear that no self-orthogonality beta(R_g,R_g) = 0 is available because (R1) has no g = h instance.

## what

Audit of the forbidden per-edge matrix relations D_i C_k^dag + D_k C_i^dag = 0. I traced every step looking for one.

## why_it_matters

You have been burned by this before, and several steps are exactly where such a relation would be tempting: C1/C2 turn scalar vanishing into orthogonality statements, and C3 turns those into the rank-one structure of A and A' -- a place where a matrix identity would feel natural.

## how_to_close

No action needed: the derivation is clean. Step A uses only (R1) plus the definitions of X and Y; the conversion Y_i = -X_i is exactly the anchor SCALAR (R2), i.e. the trace of the forbidden matrix relation, and only the trace is ever used. C1 uses <C_j, D_i> = 0 (a scalar) and the dimension-2 fact about independent vectors; C2 is the same with the roles swapped; C3 derives A = (1/4)P_{v-perp} from "C_6 and C_7 lie in a line" plus P_6 + P_7 = 1/4, not from any relation between blocks; C4 uses only the allowed DIAGONAL group moment identity; C5 is positivity plus the P-sums. Nowhere does an off-diagonal matrix identity between individual blocks appear. Both repairs I propose above are also clean: the vector identities conj(Cmat_g) J R_h^T + conj(Cmat_h) J R_g^T = 0 and R_g J Dmat_h^T + R_h J Dmat_g^T = 0, and the cross-anchor scalar relation, are all obtained by contracting the allowed group-pair identity (R1) with vectors, plus (R2). One caution for the repair itself: the division by x_g x_h in the cross-anchor argument is valid only under Step B's all-nonzero hypothesis, so gaps 1 and 2 must be closed independently -- repair (a) for gap 1 does not also cover gap 2, and vice versa.

## what

Information deliberately discarded in Step A (not an error, but it is where the missing strength lives). Per group pair, (R1) is a 2x2 matrix identity, i.e. four complex equations; Step A keeps a single scalar from it, and only the same-anchor contraction. Across the three pairs, two anchors, and the four contraction choices (a-only with D_6 or D_7, b-only with conj(C_6) or conj(C_7), and the four doubles), Step A retains 3 scalars out of the 12 available vector identities.

## why_it_matters

Both fatal gaps above are gaps only relative to this impoverished extract. The mixed-axis witness satisfies all three same-anchor scalars for both anchors and is nonetheless killed by (R1) -- I confirmed numerically that with (R1) forced to vanish on pairs (0,1) and (1,2) the residual on pair (0,2) is 0.25. So the branch is genuinely infeasible; the argument just cannot see it.

## how_to_close

Before case-splitting, write down the full extract: for each anchor j' the vector identity conj(Cmat_g) J R^(j')_h{}^T + conj(Cmat_h) J R^(j')_g{}^T = 0, for each anchor j the mirror R^(j)_g J Dmat_h^T + R^(j)_h J Dmat_g^T = 0, and for each ordered anchor pair (j,j') the scalar R^(j)_g J (R^(j'))_h^T + R^(j)_h J (R^(j'))_g^T = 0. Then run the case split. Both fatal gaps close inside this extract (the second one completely, the first one down to the rank <= 1 group residue).
