# Workflow record: orbit26-rebuild

pre-checks and the cross-anchor repair for orbit 26

Run id `wrooham5f`; 490225 subagent tokens, 165 tool calls.

---

## precheck

## checks

## what

(a) R1's relative sign omega, read off the actual Walsh row spaces (all 3 group pairs x all 4 matrix entries = 12 instances)

## verdict

holds

## evidence

omega = +1 in all 12 instances; Step A's prefactor is (1+omega) = 2, NOT zero. Method: the KL off-diagonal system splits by X-mask, so the implied relations among the products conj(c_x)d_y with x^y=m are exactly the row space of [(-1)^{z.y}] over z in dressings_full(m). For each (g,h,a,b) the four monomials of E_ab share exactly one mask and the space of relations supported on precisely those four monomials is 1-DIMENSIONAL, with all four coefficients EQUAL. Example, pair (0,1) entry (0,0), mask 010000: the unique relation is -2*[cc(C0_0)D3_0 + cc(C1_0)D2_0 + cc(C2_0)D1_0 + cc(C3_0)D0_0] = 0 -> C_g-first coeffs [-2,-2], C_h-first coeffs [-2,-2], omega = 1, internal sign within each group = +1. Direct membership tests confirm: omega=+1 variant IMPLIED for all 12; omega=-1 variant NOT implied for any; symplectic variant (internal sign -1, i.e. J replaced by [[0,1],[-1,0]]) NOT implied for any. So the form really is the SYMMETRIC J = [[0,1],[1,0]], for which 'three nonzero pairwise J-orthogonal rows lie on one axis' is a valid inference (it would be false for the symplectic form). Masks confirmed: pair (0,1) 010000/110000, (0,2) 001000/101000, (1,2) 000001/100001, matching the fact list. Script: C:\Users\richa\AppData\Local\Temp\claude\D--UTD-Project-purdue\e2435927-3651-49b0-acfb-31f3430ee257\scratchpad\stepA_a.py and stepA_end2.py

## what

(b) R2's per-block phase mu_i = Y_i/X_i, computed for all twelve instances (i = 0..5, anchor j in {6,7})

## verdict

holds

## evidence

mu_i = -1 for ALL TWELVE, no variation. For each (i,j) the X-monomials cc((C_j)_b)(D_i)_b and Y-monomials cc((C_i)_a)(D_j)_a share exactly one admissible mask (j=6: i=0->000101, 1->000011, 2->001100, 3->001010, 4->010100, 5->010010; j=7: i=0->000011, 1->000101, 2->001010, 3->001100, 4->010010, 5->010100 -- identical to o26data.SCA). Each such mask has 8 incidences and a 2-dim relation space (= exactly the two R2's living on it); the relations supported on the 4 X/Y monomials form a 1-dim space whose X-coeffs are (alpha,alpha) and Y-coeffs (alpha,alpha) with alpha = +-2, e.g. j=6,i=0: -2*[cc(C0_0)D6_0 + cc(C6_0)D0_0 + cc(C0_1)D6_1 + cc(C6_1)D0_1] = 0. Hence exactly X_i + Y_i = 0, mu_i = -1 uniformly. Independent global check (72x256 system): X_i+Y_i IMPLIED for all 12, X_i-Y_i NOT implied for any. The a=0 and a=1 coefficients are equal in every case, so the relation genuinely is the inner-product scalar and not a sign-twisted variant. Script: ...\scratchpad\stepA_bd.py

## what

(c) Virtual-bit orientation: one global choice giving J-form (not I-form) simultaneously for all three group pairs

## verdict

holds

## evidence

The single labelling 'block index = position in sorted T0, group g = blocks {2g,2g+1} (c = virtual bit z), D_i = the top block on tail comp(T0[i])' yields J-form for all three pairs, and the I-form is not merely unused but UNAVAILABLE. Evidence: the mask incidence sets themselves force the anti-diagonal pairing. Mask 010000 contains exactly the monomials (bottom,top) = (0,3),(1,2),(2,1),(3,0); mask 001000 exactly (0,5),(1,4),(4,1),(5,0); mask 000001 exactly (2,5),(3,4),(4,3),(5,2). In each case bottom 2g+c pairs with top 2h+1-c -- the J pattern -- for the SAME labelling in all three pairs. The I-form monomials (bottom 2g+c, top 2h+c) do share a mask, but those masks have weight 3 or 4 (010110, 110110, 001110, 101110, 000111, 100111), above the distance-3 KL weight budget, so they carry NO condition at all and no I-form relation exists. GROUPS from o26 is [[0,1],[2,3],[4,5],[6,7]], confirming 2g/2g+1 indexing, with the anchor group {6,7} = (x,y)=(1,1).

## what

(d) Index identification: R2's available scalar is the UNflipped sum_b conj((C_j)_b)(D_i)_b, matching R1's b index

## verdict

holds

## evidence

Decisive and unambiguous: the flipped variant does not exist. The flipped anchor monomials cc((C_j)_b)(D_i)_{1-b} sit on masks 100101, 100011, 101100, 101010, 110100, 110010 -- all of WEIGHT 3, hence carrying no weight-<=2 KL condition. In the global 72x256 system the column for e.g. cc(C6_0)D0_1 is IDENTICALLY ZERO (verified), so the flipped scalar is completely unconstrained; 'flipped X+Y' and 'flipped X-Y' are not implied for any of the 12 (i,j). The only available anchor scalar is the unflipped one, which is exactly the object produced by contracting R1's b index with conj(C_j). R1's b index and R2's D-side index are both, by construction in my labelling, the literal first bit of the S1 string, so they coincide. Script: ...\scratchpad\stepA_global.py

## what

End-to-end: Step A's contraction reproduced symbolically from the computed relation vectors

## verdict

holds

## evidence

sum_{a,b} (D_j)_a conj((C_j)_b) E_ab was expanded as a polynomial in free symbols cb[i,a], d[i,a] and verified EQUAL to sum_c Y_{2g+c}X_{2h+1-c} + sum_c Y_{2h+c}X_{2g+1-c} for both anchors j=6,7 and all three pairs (exact sympy equality, 6/6). Substituting the verified R2 (Y_i = -X_i) gives exactly -2(X_{2g}X_{2h+1} + X_{2g+1}X_{2h}), and that target polynomial is NOT identically zero (checked). So Step A really does deliver X_0X_3+X_1X_2 = 0, X_0X_5+X_1X_4 = 0, X_2X_5+X_3X_4 = 0 for each anchor separately. Sanity controls all behave: single monomial =0, s(0,3)=0, e(0,3)=0, X_0=0, and two-term matrix relations are all NOT implied (negative controls); s(0,3)-s(3,0)=0, s(1,2)+s(3,0)=0, R2 are implied (positive controls). Two independent routes (per-mask row spaces; one global 72-row/256-column system of rank 30) agree on every verdict.

## what

BONUS (not asked, but bears on the repair): extra anchor-free relations on the weight-one masks that the fact list does not credit

## verdict

holds

## evidence

Each weight-one mask has an 8-monomial, rank-4 relation space whose EXACT content is 3 pure scalar relations plus 1 'difference' relation, strictly stronger than R1's two entries E_00, E_11 (whose sum is one of the three). Writing s(b,t) := C_b^dag D_t and e(b,t) := cc((C_b)_0)(D_t)_0 - cc((C_b)_1)(D_t)_1: mask 010000 gives s(0,3) = s(3,0) = -s(1,2) = -s(2,1) and e(0,3)+e(1,2)+e(2,1)+e(3,0) = 0; mask 001000 gives s(0,5) = s(5,0) = -s(1,4) = -s(4,1) plus the matching e-relation; mask 000001 gives s(2,5) = s(5,2) = -s(3,4) = -s(4,3) plus its e-relation. These are per-BLOCK-PAIR inner-product identities with NO anchor involved -- they link individual blocks across different groups, which is precisely the resource the per-anchor axis gap lacks. They do not contradict the recorded fact that no two-term MATRIX (outer-product) relation exists; that fact is about the 8 monomials, these are about traced scalars. Each has a two-term Walsh certificate, e.g. C_0^dag D_3 - C_3^dag D_0 = (1/2)[e=010000,z=001000] + (1/2)[e=010000,z=000100] and C_1^dag D_2 + C_3^dag D_0 = (1/2)[e=010000,z=000000] - (1/2)[e=010000,z=000100] -- Lean-friendly.

## what

Convention caveat: whether per-block Pauli phases could exist at all

## verdict

holds

## evidence

Inherited-but-structural. The audit uses the codebase convention (scan.py, kl.py, o26.py): the off-diagonal KL condition for X^e Z^z is sum_{y in S1, y^e in S0} (-1)^{z.y} conj(c_{y^e}) d_y = 0. All coefficients are real +-1 because X^e Z^z |y> = (-1)^{z.y} |y^e>; a Y factor contributes a single global i multiplying the whole condition, which cannot vary term by term. The residues 2 and 3 in a = (0,1,1,2,2,3) enter only through WHICH strings lie in S0 and S1, not through any coefficient. So the worry behind (b) -- 'Pauli phases could vary by block' -- is structurally impossible in this parametrization, which is why all twelve mu_i came out equal rather than by luck. This is the one place the audit adopts a convention rather than deriving it, but it is the same convention under which the already machine-verified matrix moment identity, R1 and R2 were established.

## fatal

none. All four silent assumptions HOLD: (a) omega = +1 (prefactor 2, not vacuous) and the form is the symmetric J, not symplectic; (b) mu_i = -1 uniformly across all twelve R2 instances; (c) one global virtual-bit orientation gives J-form for all three pairs, and the I-form is unavailable because its monomials live on weight-3/4 masks; (d) the flipped anchor scalar is not merely unused but has identically-zero columns in the whole KL system, so R1's b index and R2's D index necessarily agree. Step A is confirmed non-vacuous end to end: it genuinely yields X_0X_3+X_1X_2 = X_0X_5+X_1X_4 = X_2X_5+X_3X_4 = 0 per anchor. IMPORTANT: this does NOT repair the known fatal gap -- the axis choice is still per-anchor, and nothing verified here links j=6's axis to j=7's. The audit only certifies that the machinery producing those three equations is sound. Worth flagging for the repair: the weight-one masks carry anchor-free per-block scalar identities (C_0^dag D_3 = C_3^dag D_0 = -C_1^dag D_2 = -C_2^dag D_1, and the two analogues) with two-term Walsh certificates; these were not in the fact list and are exactly the kind of cross-group link the per-anchor argument is missing.

## checks

## what

TASK 1. Fact (T): P_{2g}+P_{2g+1} = 1/4 for EVERY group including the anchor {6,7}.

## verdict

holds

## evidence

PROVED, not just checked. cert.reduce_mod_linear against the full 23-equation moment system (rank 20) gives remainder 0 for all four groups, in both the P and the Q version. Script: C:\Users\richa\AppData\Local\Temp\claude\D--UTD-Project-purdue\e2435927-3651-49b0-acfb-31f3430ee257\scratchpad\t26_factT.py. Certificates use only 8 of the 23 equations (n0,n1,m2,m3,m6,c23,c26,c36 -- the tail bits carrying x,y,x^y at 0-indexed positions 1,2,5): group0 = n0 -3/4(n1+m2+m3+m6) +1/2(c23+c26+c36); group1 = 1/4(n1+m2+m3+m6) -1/2 c23 -1/2 c26 +1/2 c36; group2 = 1/4(...) -1/2 c23 +1/2 c26 -1/2 c36; ANCHOR group3 = 1/4(...) +1/2 c23 -1/2 c26 -1/2 c36. Also re-verified with remainder 0: P_i = Q_i (all 8), P_6 = Q_6 = P_7 = Q_7 = 1/8 individually (strictly stronger than (T) on the anchor), sum_{i<6} P_i = 3/4, P_1+P_3+P_5 = P_0+P_2+P_4 = 3/8.

## what

The moment system pins the block masses to a 2-parameter family, and (T) is NOT its strongest linear consequence.

## verdict

holds

## evidence

Exact reduction mod the moment system: P_0=u, P_1=1/4-u, P_2=v, P_3=1/4-v, P_4=3/8-u-v, P_5=u+v-1/8, P_6=P_7=1/8, where u=P_0=r7+r15 and v=P_2=r5+r13. So beyond (T) there is one further independent linear fact, call it (T2): P_0+P_2+P_4 = 3/8 = P_1+P_3+P_5 (equivalently P_5 = P_0+P_2-1/8). (T2) is NOT implied by (T) and it turns out to be the load-bearing one (see the ablation check). Do not stop at (T) when writing the Lean layer -- carry (T2) too.

## what

TASK 2. Exactly which blocks can vanish simultaneously over the moment polytope.

## verdict

holds

## evidence

LP over {q,r >= 0, A[q;r]=b} with P_i=0 forced, all 256 subsets scanned. Feasible zero-sets: the empty set, the six singletons {0},{1},{2},{3},{4},{5}, and exactly six pairs -- {0,3},{0,5},{1,2},{1,4},{2,5},{3,4}. 13 in total. NO triple is feasible; blocks 6 and 7 never vanish (P_6=P_7=1/8 exactly). Block-mass ranges: P_i in [0,1/4] for i<6, P_6=P_7=1/8. The block-mass polytope is a HEXAGON in (u,v): 0<=u<=1/4, 0<=v<=1/4, 1/8<=u+v<=3/8, and the six maximal zero-sets are precisely its six vertices, e.g. (u,v)=(0,1/8) -> P=(0,1/4,1/8,1/8,1/4,0,1/8,1/8) with zero blocks {0,5}. Exact rational witnesses at all six vertices verified against the exact system. Scripts: t26_lp.py and t26_cert.py in the scratchpad.

## what

Every infeasible zero-set has an exact rational Farkas certificate suitable for Lean.

## verdict

holds

## evidence

t26_cert.py emits one for every infeasible set of size 1,2,3. The pattern: within a group, (T) kills it directly (P_{2g}+P_{2g+1}=1/4). Cross-group SAME-parity pairs each reduce to -1/8 via one auxiliary block: P_5-P_0-P_2 = -1/8 kills {0,2}; P_4-P_1-P_3 = -1/8 kills {1,3}; P_3-P_0-P_4 = -1/8 kills {0,4}; P_1-P_2-P_4 = -1/8 kills {2,4}; P_2-P_1-P_5 = -1/8 kills {1,5}; P_0-P_3-P_5 = -1/8 kills {3,5}. Anything containing 6 or 7 dies on P_6 = 1/8. The two triples the argument actually needs: P_1-2P_0-3P_2-3P_4 = -7/8 kills {0,2,4}, and P_0-2P_1-3P_3-3P_5 = -7/8 kills {1,3,5}.

## what

R1 and R2 as stated in the task brief are genuine consequences of the raw weight-<=2 KL system, in the sorted o26.py block indexing.

## verdict

holds

## evidence

Independently re-derived from kl.conditions in t26_rel.py, not taken on trust. The 72 off-diagonal KL forms have rank 30. All 12 R1 entries and all 12 R2 scalars lie in that row space. Masks confirmed exactly as the brief says: R1 pair (0,1) entry (a,a) comes from 010000, entry (a,b) from 110000; R2 (i,j=6) from 000101, (i,j=7) from 000011. The brief's warning is also confirmed: no two-term MATRIX (outer-product) relation D_i C_k^dag + D_k C_i^dag is in the span (0 of them). The group matrix moment identity was re-confirmed by running o26.py itself (True for all four groups and all four entries).

## what

TASK 3. Is R_g = 0 compatible with the verified facts, for some anchor j and group g?

## verdict

fails

## evidence

NO -- all six branches are excluded. Model (real quadratic forms in the 64 real block coordinates, exact Jacobian): (M) group matrix identity, (N) tr rho = 1, (E) P_i=Q_i, (A) P_6=P_7=1/8, (T2) P_0+P_2+P_4=3/8=Q_0+Q_2+Q_4, (R1), (R2). Least squares, 250 multi-scale random starts per branch: every one of R_g^{(j)}=0 for j in {6,7}, g in {0,1,2} bottoms out at residual 2.062e-01, never near zero. Files t26_facts_fast.py and t26_branch2.py (output t26_branch2.out). Structure of such a branch, for the write-up: R_g^{(j)}=0 forces D_{2g},D_{2g+1} onto the line C_j^perp and, via R2, C_{2g},C_{2g+1} onto D_j^perp -- so BOTH C_g and D_g drop to rank one; the group identity plus (T) then pins rho = (1/2)(w w^dag + v v^dag) with w=D_j^perp, v=C_j^perp, and the anchor identity forces C_{j'}C_{j'}^dag + D_{j'}D_{j'}^dag = (3/8)(w w^dag + v v^dag) - I/4, which is PSD only when |<w,v>| <= 1/3. The remaining R1 relations then close it.

## what

The complete branch list the argument must cover, and their status.

## verdict

holds

## evidence

Ten branches, all closed by the verified facts (numerics in t26_branch2.out): (i) six degenerate branches R_g^{(j)}=0, j in {6,7}, g in {0,1,2} -- resid 2.062e-01 each; (ii) two ALIGNED axis branches, odd(6)&odd(7) resid 2.229e-01 and even(6)&even(7) resid 2.652e-01; (iii) two MIXED axis branches, odd(6)&even(7) and even(6)&odd(7), both resid 2.660e-01. The base facts model with no branch constraint is itself infeasible (best 2.0620e-01 over 1200 multi-scale starts, t26_base.out), which logically subsumes all ten.

## what

The MIXED branch -- the brief's fatal gap -- closes on the verified facts, by a symbolically verified argument.

## verdict

holds

## evidence

Proof, machine-checked in t26_mixed_proof.py. In the mixed branch (anchor 6 kills the odd X, anchor 7 the even), R2 forces C_1,C_3,C_5 perp D_6 hence all parallel to one w6; C_0,C_2,C_4 perp D_7 hence parallel to one w7; D_1,D_3,D_5 parallel to v6 = C_6^perp; D_0,D_2,D_4 parallel to v7 = C_7^perp (all four anchor vectors are nonzero because P_6=P_7=Q_6=Q_7=1/8). Writing C_i = c_i w, D_i = d_i v, each R1 matrix identity collapses to [conj(c)d + conj(c')d'] * conj(w7)v6^T + [conj(c'')d'' + ...] * conj(w6)v7^T = 0, verified entry-by-entry symbolically. Whenever conj(w7)v6^T and conj(w6)v7^T are independent this yields SIX scalars, and they are exactly the J-orthogonality relations of the triples r_k = (conj(c_{2k}), d_{2k+1}) and s_k = (conj(c_{2k+1}), d_{2k}), k=0,1,2 (all six equalities checked with sympy). The SAME lemma one level down then gives: either some r_k = 0, i.e. P_{2k}=P_{2k+1}=0, killed by (T); or all r_k share an axis, i.e. P_0+P_2+P_4=0 or P_1+P_3+P_5=0, killed by (T2)=3/8. Degenerate sub-case w6||w7 and v6||v7: then rho = (1/2)(w w^dag + v v^dag) and simultaneously rho = (3/4) w w^dag + (1/4) u u^dag, forcing 3 v v^dag - w w^dag = I, hence v||w and 2 w w^dag = I, impossible in dimension two.

## what

The SUGGESTED repair (cross-anchor contraction of R1) can add nothing.

## verdict

fails

## evidence

The cross-anchor contraction -- contract R1 on b with conj(C_6) and on a with D_7 -- is a linear contraction of the same R1 rows using R2, so it is a logical CONSEQUENCE of facts already in the model. Since the model containing R1 and R2 is what I tested, no consequence of them can be new information; the cross contraction gives R_g^{(7)} J R_h^{(6)T} + R_h^{(7)} J R_g^{(6)T} = 0, a symmetrised relation that does not by itself pin an axis. It is not needed: the mixed branch closes by the r_k / s_k route above, which uses only R1 in MATRIX form plus R2 plus (T) plus (T2). Recommend dropping the cross-anchor idea and mechanising the r_k/s_k route instead.

## what

Ablation: which facts are load-bearing (sanity check that the model is not over-constrained by an encoding bug).

## verdict

holds

## evidence

t26_ablate.out, 250 starts each. FACTS minus nothing: infeasible, 2.062e-01. FACTS minus R1: FEASIBLE, 6.9e-17, P=(0.1968,0.0532,0.1629,0.0871,0.0153,0.2347,1/8,1/8). FACTS minus R2: FEASIBLE, 6.9e-17. FACTS minus (T2): FEASIBLE, 7.3e-17 at P=(0,1/4,0,1/4,0,1/4,1/8,1/8) -- exactly the aligned branch, which is why (T2) is what kills it. FACTS minus (M): FEASIBLE. FACTS minus (A) and minus (E): still infeasible. So R1, R2, (T2) and (M) are each individually necessary and together sufficient; the encoding has solutions whenever it should, so the infeasibility verdict is not an artefact.

## what

There is unused KL information: 6 units of off-diagonal rank, giving new two-term SCALAR relations between cycle blocks.

## verdict

holds

## evidence

t26_gap.py / t26_gap2.py. Off-diagonal KL rank is 30; R1 union R2 spans only 24. The missing 6 sit entirely on the three weight-one masks (010000, 001000, 000001), 2 each. Extracted explicitly, they are SCALAR two-term relations -- the brief's 'no per-edge relations' caveat is correct only at the MATRIX level: mask 010000 (groups 0,1) gives C_0^dag D_3 = C_3^dag D_0 = -C_1^dag D_2 = -C_2^dag D_1; mask 001000 (groups 0,2) gives C_0^dag D_5 = C_5^dag D_0 = -C_1^dag D_4 = -C_4^dag D_1; mask 000001 (groups 1,2) gives C_2^dag D_5 = C_5^dag D_2 = -C_3^dag D_4 = -C_4^dag D_3. On the diagonal side, KL rank is 41 while group identity plus the pure-Z moment equations spans only 27, so 14 units are unused there too. These are not needed for the closure above but are available if a shorter certificate is wanted.

## what

TASK 4. Orbit 26 really is excluded by the FULL weight-<=2 Knill-Laflamme system.

## verdict

holds

## evidence

NO ALARM -- the effort is not misdirected. Setup from kl.conditions: 154 admissible Paulis, 72 non-trivial off-diagonal and 50 non-trivial diagonal equations, 244 homogeneous real residuals in 64 real unknowns (c on S0, d on S1). Every residual is a real quadratic form, so the Jacobian is exact. Minimising on the normalised sphere ||x||^2=2 (which removes the trivial solution and any scale trade-off; the e=z=0 pure-Z condition already forces ||c||=||d||): BEST residual 2-norm = 5.7735026919e-01 = 1/sqrt(3) over 550 starts -- 250 random, 150 seeded from exact solutions of the diagonal-only subsystem, 150 seeded from exact solutions of the off-diagonal-only subsystem. min equalled the 1%-ile in every batch. Largest single Pauli violation at the minimiser: 1.3964e-01, with ||c||^2=||d||^2=1.00000000 exactly. Controls prove the machinery is not the obstruction: the diagonal-only relaxation solves to 3.10e-16, and the off-diagonal-only relaxation solves exactly in 40/40 starts. Scripts t26_kl_fast.py and t26_sphere.py; output t26_sphere.out.

## fatal

none — the approach is sound and orbit 26 is genuinely excluded (best full-KL residual 1/sqrt(3), nowhere near zero). Two course corrections the parent must absorb, neither fatal. (1) The SUGGESTED repair is dead: the cross-anchor contraction is a contraction of R1 using R2, i.e. a consequence of facts the argument already assumes, so it cannot supply new information. (2) It is not needed. The working repair is different and is symbolically verified in ...\scratchpad\t26_mixed_proof.py: in the mixed branch R2 collapses each side into two parallel classes, each R1 matrix identity degenerates to two scalars, and those six scalars are exactly the J-orthogonality relations of the triples r_k = (conj(c_{2k}), d_{2k+1}) and s_k = (conj(c_{2k+1}), d_{2k}). Applying the SAME axis lemma one level down leaves only "some group pair vanishes" (killed by (T)) or "P_0+P_2+P_4 = 0 or P_1+P_3+P_5 = 0" (killed by the 3/8 relation). The one thing that must be added to the fact list is (T2): P_0+P_2+P_4 = 3/8 = P_1+P_3+P_5. It is a proven consequence of the moment system, it is independent of (T), and the ablation shows it is precisely what makes the fact set inconsistent — with R1, R2, (M), (E), (A) and (T2) all present the model is infeasible (2.06e-01 over 1200 starts), while dropping any one of R1, R2, (T2) or (M) restores exact feasibility.

## repair

## closes

True

## cross_anchor

THE RELATION.  Contract R1's matrix entry

    E_ab(g,h) = sum_c conj((C_{2g+c})_a)(D_{2h+1-c})_b + sum_c conj((C_{2h+c})_a)(D_{2g+1-c})_b = 0

on the a index with D_7 and on the b index with conj(C_6), i.e. form
sum_{a,b} (D_7)_a conj((C_6)_b) E_ab(g,h).  Because sum_a conj((C_i)_a)(D_7)_a = Y^7_i and
sum_b conj((C_6)_b)(D_k)_b = X^6_k, the contraction is EXACTLY

    sum_c Y^7_{2g+c} X^6_{2h+1-c}  +  sum_c Y^7_{2h+c} X^6_{2g+1-c}  =  0.

Substituting R2 (Y^j_i = -X^j_i) and writing R_g^{(j)} = (X^j_{2g}, X^j_{2g+1}), J = [[0,1],[1,0]]:

    ***  R_g^{(7)} J R_h^{(6)T}  +  R_h^{(7)} J R_g^{(6)T}  =  0,   for the three pairs g<h.  ***

MACHINE VERIFICATION (x26_cross.py, bilinearity only -- conj((C_i)_a) and (D_i)_b are
independent free symbols, the contraction is a literal double sum over a,b, and equality is
exact polynomial equality; no index was guessed).  All 12 instances (4 anchor placements x 3
group pairs) exact: True.  Cross-checks that came out of the same run:
  * the other order (a-slot D_6, b-slot conj(C_7)) gives R_g^{(6)}JR_h^{(7)T}+R_h^{(6)}JR_g^{(7)T},
    which is the SAME polynomial (J is symmetric, the scalar equals its own transpose) --
    verified identical for all three pairs.  So there is one cross relation per pair, not two.
  * putting the same anchor in both slots reproduces 2 R_g^{(j)} J R_h^{(j)T} = 0, i.e. the
    already-known per-anchor relation -- verified for j=6,7 and all three pairs.  The
    cross-anchor relation is the genuine off-diagonal member of that family.

DOES IT LINK THE AXES?  YES -- and it is the exact repair for the fatal gap.
  * ALIGNED (both anchors on the same axis): R_g^{(6)}=(a_g,0), R_g^{(7)}=(b_g,0).  The cross
    residuals are [0,0,0] -- VACUOUS.  Both coordinate axes are J-isotropic, so nothing is said.
    The aligned branch must be closed by other means (see branch table, Branch 4b).
  * MIXED (anchor 6 on e1, anchor 7 on e2): R_g^{(6)}=(a_g,0), R_g^{(7)}=(0,b_g).  The cross
    residuals become  a_0b_1+a_1b_0,  a_0b_2+a_2b_0,  a_1b_2+a_2b_1.  Dividing the (g,h) one by
    a_g a_h (nonzero in this branch) gives t_g + t_h = 0 with t_g = b_g/a_g, for all three pairs;
    the only solution is t_0=t_1=t_2=0, so every b_g = 0, contradicting R_g^{(7)} != 0.
    Machine-verified two ways: sympy solve gives {b0:0,b1:0,b2:0}, and the Rabinowitsch
    saturation of the three residuals by a0 a1 a2 b0 b1 b2 is the UNIT IDEAL (True), for BOTH
    mixed orientations.  THE MIXED BRANCH IS EMPTY.
  * DEGENERATE (R_g^{(6)} = 0): the cross relation collapses to R_g^{(7)} J R_h^{(6)T} = 0, i.e.
    d_g := R_g^{(7)} is J-orthogonal to both surviving R_h^{(6)}.  Together with the per-anchor
    relation R_{h1}^{(6)}JR_{h2}^{(6)T}=0 that is THREE pairwise J-orthogonal vectors, so the
    axis lemma applies one level deeper.  This is what closes Branch 3.

NOTE ON THE PRE-CHECK.  The second pre-check called the cross-anchor idea "dead" because it is a
logical consequence of R1+R2 and therefore cannot change a numerical feasibility verdict.  That
is true and irrelevant to proof construction: every step of a proof is a consequence of its
premises.  As a proof device the cross contraction is the shortest known kill of the mixed
branch -- three lines of linear algebra, versus the t26_mixed_proof.py route which needs the
r_k/s_k reparametrisation, a rank collapse and a separate degenerate sub-case.  Recommend
keeping it and mechanising it.

## branch_table

Let Z_j = { g in {0,1,2} : R_g^{(j)} = 0 }, j = 6,7.  The tree splits on (Z_6, Z_7).  All 64
ordered pairs of subsets were enumerated and each is caught by EXACTLY ONE branch (machine
check: "pairs NOT hit by exactly one branch: []"; occupancy {1:48, 2:3, 3:12, 4:1}).

AXIS LEMMA (used three times).  Three pairwise J-orthogonal vectors in C^2, none zero, lie on a
common coordinate axis.  Machine-verified: on the variety of the three J-relations the product
(r0_1 r1_1 r2_1)(r0_0 r1_0 r2_0) reduces to 0 mod the ideal (True), and saturating by "the other
two are nonzero" puts each r_k0*r_k1 in the ideal (True x3).  Valid because J is the SYMMETRIC
form [[0,1],[1,0]] -- the first pre-check confirmed omega = +1 in all 12 instances, so the form
really is symmetric and not symplectic (the lemma is false for the symplectic form).

-----------------------------------------------------------------------------------------
BRANCH 1.  |Z_j| >= 2 for some anchor j  (48 of the 64 configurations).
  R2 turns the four vanishing X into C_i perp D_j and D_i perp C_j for the four blocks of the
  two groups; C_j, D_j are nonzero by (A), so those blocks sit on the fixed lines w = D_j^perp
  and v = C_j^perp.  (T) gives C_gC_g^dag = C_hC_h^dag summing to (1/2)ww^dag and, from group g,
  rho = (1/2)(ww^dag + vv^dag).  Since C_j perp v with |C_j|^2 = 1/8, C_jC_j^dag = (1/8)(I-vv^dag).
  Subtracting:   C_kC_k^dag + C_{j'}C_{j'}^dag = (5/8) vv^dag - (1/8) I   (machine-verified equal).
  Its Rayleigh quotient at v^perp is exactly -1/8 (machine-computed), but the left side is a sum
  of two PSD matrices.  CONTRADICTION.
  CLOSED BY: (M), (T), (A), (R2).  R1 not needed.

BRANCH 2.  Z_6 and Z_7 share a group g (3 configurations; with Branch 1 gone, Z_6=Z_7={g}).
  step 1  D_{2g},D_{2g+1} perp C_6 and C_7; if C_6,C_7 were independent both D vanish, so
          Q_{2g}+Q_{2g+1}=0 against (T).  Hence C_6 || C_7 =: n.  Dually D_6 || D_7 =: m.
  step 2  (M) on the anchor group and on group g both equal rho/2, giving nn^dag+mm^dag = I.
          Machine-verified: ||nn^dag+mm^dag-I||_F^2 = 2|<n,m>|^2 identically (True), so n perp m.
          Hence rho = I/2, group g has C in span(n), D in span(m).
  step 3  rho = I/2 minus group g minus the anchors leaves sum_{h!=g} C_hC_h^dag = (1/2)mm^dag
          (machine-verified subtraction), rank one, so EVERY C_i of the other two groups lies in
          span(m); dually every D_i lies in span(n).
  step 4  R2 for both anchors on those blocks is a 2x2 system in (d_i, conj(c_i)).  A nonsingular
          system forces c_i = d_i = 0 for four blocks, i.e. two groups of mass 0, against (T).
          So the determinant vanishes and d_i = -nu conj(c_i), nu != 0.
  step 5  R1(g,h) splits exactly into a conj(n)n^T part and a conj(m)m^T part (verified symbolically
          entry by entry, "exact: True" for both h); those are independent since n perp m, so both
          brackets vanish.  R1(h1,h2) is conj(m)n^T times a single bracket (verified), which
          therefore vanishes too.
  step 6  Substituting d_i = -nu conj(c_i) and conjugating leaves
              gam0 c11 + gam1 c10 = 0,  gam0 c21 + gam1 c20 = 0,  c10 c21 + c11 c20 = 0.
          Groebner basis of the Rabinowitsch ideal saturating by gam0 gam1 c10 c11 c20 c21 is [1]
          -- the UNIT IDEAL.  By hand: the first two force both c-vectors proportional to
          (gam0,-gam1), and then the third reads -2 sig1 sig2 gam0 gam1 = 0.
          The leftover cases gam0 = 0 and gam1 = 0 force P_0+P_2+P_4 = 0 resp. P_1+P_3+P_5 = 0.
          CONTRADICTION with (T2) = 3/8.
  CLOSED BY: (M), (T), (A), (T2), (R1), (R2).

BRANCH 3.  Z_j = {g}, g not in Z_{j'}  (12 configurations).  d_g := R_g^{(j')} != 0.
  Cross-anchor with R_g^{(j)} = 0 gives d_g J R_h^{(j)T} = 0 for both h != g; the per-anchor
  relation gives R_{h1}^{(j)} J R_{h2}^{(j)T} = 0.  Three pairwise J-orthogonal vectors, all
  nonzero (Z_j = {g} exactly), so by the axis lemma they share one axis, say e1.  Then
  X^j_{2h+1} = 0 for h1,h2, X^j_{2g}=X^j_{2g+1}=0 from R_g^{(j)}=0, and X^{j'}_{2g+1}=0 from
  d_g = (p,0).  The per-anchor relation for j' on the pair (g,h) reads d_g J R_h^{(j')T} = p*X^{j'}_{2h+1}
  (symbolically e1*p0), and p != 0, so X^{j'}_{2h+1} = 0 too.  BOTH anchors now annihilate every
  odd X: this is the ALIGNED configuration, closed in Branch 4b.  (Axis e2: same with even indices.)
  REDUCES TO 4b BY: cross-anchor R1, per-anchor R1, axis lemma.

BRANCH 4.  Z_6 = Z_7 = empty (1 configuration).  Each anchor's three R are nonzero and pairwise
  J-orthogonal, so each anchor has a well-defined axis.  Two sub-branches, exhaustive:

  4a MIXED (the historical fatal gap).  Cross-anchor residuals a_g b_h + a_h b_g = 0 for the three
     pairs; Rabinowitsch saturation by a0 a1 a2 b0 b1 b2 = unit ideal (True, both orientations).
     CONTRADICTION.  CLOSED BY: (R1), (R2) alone -- no moment facts needed.

  4b ALIGNED.  Both anchors annihilate the odd X (say).  R2 gives C_1,C_3,C_5 perp D_6 and perp D_7.
     case (i)  D_6, D_7 independent  ->  C_1=C_3=C_5=0  ->  P_1+P_3+P_5 = 0, against (T2)=3/8.
     case (ii) D_6 || D_7 =: m (both nonzero by (A)).  Put w = m^perp; then C_1,C_3,C_5 lie in
               span(w), so sum_odd |<w,C_i>|^2 = P_1+P_3+P_5 = 3/8.  Sandwich (M) on the anchor
               group with w: the D terms die (w perp m), leaving
                   A := |<w,C_6>|^2 + |<w,C_7>|^2 = (w^dag rho w)/2,
               while w^dag rho w = sum_i |<w,C_i>|^2 = ev + 3/8 + A with ev >= 0.  Exact solve of
               2A = ev + 3/8 + A gives A = ev + 3/8 >= 3/8.  But A <= P_6+P_7 = 1/4 by (A), and
               3/8 > 1/4.  CONTRADICTION.
     (Even-axis alignment is identical with P_0+P_2+P_4 = 3/8.)
     CLOSED BY: (M), (A), (T2), (R2).

-----------------------------------------------------------------------------------------
FACT USAGE SUMMARY.  (M) group matrix identity + rho = sum C_iC_i^dag = sum D_iD_i^dag; (T) group
mass 1/4 for P AND for Q, all four groups including the anchor; (A) P_6=Q_6=P_7=Q_7=1/8;
(T2) P_0+P_2+P_4 = P_1+P_3+P_5 = 3/8; (R1) matrix form, three cycle-group pairs; (R2) all twelve.
NOTABLE: (E) P_i = Q_i is never used -- every place it might have been, (T) for Q does the work
directly.  (T2) is load-bearing in Branches 2, 4b (hence also 3), confirming the pre-check's
ablation finding that dropping (T2) makes the fact set feasible exactly at the aligned point
P = (0,1/4,0,1/4,0,1/4,1/8,1/8).

## remaining_gaps

1. THE ARGUMENT IS A DERIVATION FROM THE PRE-VERIFIED FACT LIST, not a re-derivation of it.  I
   did not re-check that (M), (T), (A), (T2), (R1), (R2) follow from the raw weight-<=2 KL system;
   I took the two pre-checks' machine verifications of those (t26_factT.py, t26_rel.py,
   stepA_*.py, o26.py).  If any of those is wrong in the codebase convention, this closure
   inherits the error.

2. CONJUGATES AS INDEPENDENT SYMBOLS.  All the polynomial identities (the contraction, the R1
   splittings in Branch 2) treat conj((C_i)_a) as a free symbol independent of (C_i)_a.  This is
   sound because every identity involved is bilinear/sesquilinear -- it is the same device
   t26_mixed_proof.py used -- but it is a modelling choice, not a theorem, and a Lean formalisation
   will have to carry real inner products or explicit conjugation instead.

3. THE CROSS-ANCHOR RELATION IS VACUOUS IN THE ALIGNED BRANCH (verified: residuals [0,0,0]).  So
   the suggested repair alone does NOT close everything -- it closes 4a (mixed) and enables 3.
   Branch 4b needs the independent D_6/D_7-span + trace argument, and Branches 1 and 2 need the
   PSD/moment arguments.  Anyone reading "the cross-anchor contraction repairs the gap" should
   read it as "repairs the mixed branch", which was the specific fatal gap.

4. BRANCH 2 IS THE LONGEST AND LEAST ROBUST LEAF.  Six chained steps, several of which are
   case splits on linear independence (C_6 vs C_7, D_6 vs D_7, the 2x2 R2 determinant).  Each step
   is machine-checked in isolation (x26_b2.py, x26_branches.py) but the chaining is by hand.  It is
   the leaf I would re-audit first.  It occupies only 3 of the 64 (Z_6,Z_7) configurations, so a
   shorter kill probably exists; I did not find one.

5. NOT MECHANISED.  Nothing here is in Lean.  `SixQubit/Block26.lean` is still built on the
   retracted per-edge matrix assumption and must not be reused.  Suggested Lean order: axis lemma
   (pure C^2 algebra) -> cross-anchor contraction (bilinear expansion) -> Branch 4a -> Branch 4b ->
   Branch 1 -> Branch 3 -> Branch 2.

6. UNUSED AMMUNITION.  The six anchor-free weight-one scalar relations found by the pre-checks
   (C_0^dag D_3 = C_3^dag D_0 = -C_1^dag D_2 = -C_2^dag D_1 and the two analogues, each with a
   two-term Walsh certificate) are NOT used anywhere above.  They would very likely shorten
   Branch 2 and possibly merge Branches 1-3, and they are the cheapest thing to try if the Lean
   layer for Branch 2 turns out to be painful.

7. NUMERICAL CROSS-CHECK CAVEAT.  The independent least-squares runs report every branch
   hypothesis infeasible at residual 2.0620e-01 -- but that is the SAME value as the unconstrained
   base model, i.e. the branch constraints are not even active; the numerics confirm the fact set
   is globally inconsistent, it does not independently confirm each branch's derivation.  Positive
   controls do pass ((M)+(N)+(E) feasible at 1.06e-16, (M)+(N)+(E)+(A)+(T2) at 1.89e-16), so the
   machinery is not trivially infeasible.  The real evidence for the branch closures is the
   symbolic work, not the numerics.

## verification_output

Scripts (all in ...\e2435927-3651-49b0-acfb-31f3430ee257\scratchpad\):
  x26_cross.py    cross-anchor contraction, bilinearity only
  x26_axis.py     axis lemma, aligned/mixed/degenerate analysis
  x26_branches.py the four branches, each step machine-checked
  x26_b2.py       Branch 2 steps 5-6 fully symbolic
  x26_tree.py     exhaustiveness + independent numerics
  x26_all.out     consolidated output, 219 lines, 51 "True", ZERO "False"

=== x26_cross.py ============================================================
STEP 1.  literal contraction  ==  sum_c Y^jA_{2g+c} X^jB_{2h+1-c}
                                + sum_c Y^jA_{2h+c} X^jB_{2g+1-c}
  a-slot D_7 , b-slot conj(C_6) , pair (0,1):  identity holds = True
  a-slot D_7 , b-slot conj(C_6) , pair (0,2):  identity holds = True
  a-slot D_7 , b-slot conj(C_6) , pair (1,2):  identity holds = True
  a-slot D_6 , b-slot conj(C_7) , pair (0,1):  identity holds = True
  a-slot D_6 , b-slot conj(C_7) , pair (0,2):  identity holds = True
  a-slot D_6 , b-slot conj(C_7) , pair (1,2):  identity holds = True
  a-slot D_6 , b-slot conj(C_6) , pair (0,1):  identity holds = True
  a-slot D_6 , b-slot conj(C_6) , pair (0,2):  identity holds = True
  a-slot D_6 , b-slot conj(C_6) , pair (1,2):  identity holds = True
  a-slot D_7 , b-slot conj(C_7) , pair (0,1):  identity holds = True
  a-slot D_7 , b-slot conj(C_7) , pair (0,2):  identity holds = True
  a-slot D_7 , b-slot conj(C_7) , pair (1,2):  identity holds = True
  ALL 12 exact: True

STEP 2.  apply R2  (Y^j_i = -X^j_i)  in abstract scalars
  (a-slot 7, b-slot 6) pair (0,1):  contraction = -[ R_0^(7) J R_1^(6)T + R_1^(7) J R_0^(6)T ]   True
  (a-slot 7, b-slot 6) pair (0,2):  contraction = -[ R_0^(7) J R_2^(6)T + R_2^(7) J R_0^(6)T ]   True
  (a-slot 7, b-slot 6) pair (1,2):  contraction = -[ R_1^(7) J R_2^(6)T + R_2^(7) J R_1^(6)T ]   True
  (a-slot 6, b-slot 7) pair (0,1):  contraction = -[ R_0^(6) J R_1^(7)T + R_1^(6) J R_0^(7)T ]   True
  (a-slot 6, b-slot 7) pair (0,2):  contraction = -[ R_0^(6) J R_2^(7)T + R_2^(6) J R_0^(7)T ]   True
  (a-slot 6, b-slot 7) pair (1,2):  contraction = -[ R_1^(6) J R_2^(7)T + R_2^(6) J R_1^(7)T ]   True
  (a-slot 6, b-slot 6) pair (0,1):  contraction = -[ R_0^(6) J R_1^(6)T + R_1^(6) J R_0^(6)T ]   True
  (a-slot 7, b-slot 7) pair (1,2):  contraction = -[ R_1^(7) J R_2^(7)T + R_2^(7) J R_1^(7)T ]   True

  ==> CROSS-ANCHOR RELATION (a-slot D_7, b-slot conj(C_6)), one per pair g<h:
        R_0^(7) J R_1^(6)T  +  R_1^(7) J R_0^(6)T  =  0
        R_0^(7) J R_2^(6)T  +  R_2^(7) J R_0^(6)T  =  0
        R_1^(7) J R_2^(6)T  +  R_2^(7) J R_1^(6)T  =  0
  ==> the other order (a-slot D_6, b-slot conj(C_7)) gives the transpose,
        pair (0,1): identical as a polynomial: True
        pair (0,2): identical as a polynomial: True
        pair (1,2): identical as a polynomial: True
  ==> same anchor in both slots reproduces the KNOWN per-anchor relation:
        j=6 pair (0,1):  = 2 R_0^(6) J R_1^(6)T   True
        ... (all six True)

=== x26_axis.py =============================================================
LEMMA (axis lemma).  Three pairwise J-orthogonal vectors in C^2, all nonzero,
lie on ONE common coordinate axis.
  is  (r0_1 r1_1 r2_1)(r0_0 r1_0 r2_0)  in the ideal of the J-relations?  True
  is  r0_0 * r0_1  in the ideal after saturating by the other two nonzero?  True
  is  r1_0 * r1_1  in the ideal after saturating by the other two nonzero?  True
  is  r2_0 * r2_1  in the ideal after saturating by the other two nonzero?  True

CASE  ALIGNED:  anchor 6 and anchor 7 pick the SAME axis.
  cross-anchor residuals: [0, 0, 0]
  ==> the cross-anchor relation is VACUOUS in the aligned branch.

CASE  MIXED:  anchor 6 on axis e1 (odd X vanish), anchor 7 on axis e2.
  cross-anchor residuals: [a0*b1 + a1*b0, a0*b2 + a2*b0, a1*b2 + a2*b1]
  is 1 in the saturation by  a0 a1 a2 b0 b1 b2 (all six R nonzero)?  True
  ==> MIXED BRANCH IS EMPTY.  The cross-anchor relation DOES link the axes.
  solving for b over the field:  [{b0: 0, b1: 0, b2: 0}]
  linear system t_g + t_h = 0 : [t0 + t1, t0 + t2, t1 + t2]  ->  [{t0: 0, t1: 0, t2: 0}]
  (re-run for the opposite orientation, 6 on e2 / 7 on e1: unit ideal True as well)

CASE  one anchor degenerate:  R_g^(6) = 0.
     R_g^(7) J R_h^(6)T  +  R_h^(7) J R_g^(6)T  =  R_g^(7) J R_h^(6)T  = 0
     residual with R_g^(6)=(0,0): p0*q1 + p1*q0  == p J q
  ==> d_g := R_g^(7) is J-orthogonal to BOTH R_h^(6), h != g.

=== x26_branches.py =========================================================
BRANCH 1.   |Z_j| >= 2
     sanity: v and w are unit: True True
     C_k C_k^dag + C_j2 C_j2^dag = rho - (1/2) w w^dag - (1/8)(I - v v^dag)
     equals (5/8) v v^dag - (1/8) I : True
     Rayleigh quotient of that matrix at v^perp = -1/8  < 0
     but the left side is a sum of two PSD matrices.   CONTRADICTION.
     [facts used: (M) (T) (A) (R2); no R1 needed]

BRANCH 2.   Z_6 = Z_7 = {g}
  step 2   for a general orthonormal pair (n, m) that identity holds: True
           for ANY two unit n, m: ||n n^dag + m m^dag - I||_F^2 = 2 |<n,m>|^2,
           machine check (difference simplifies to 0): True
  step 3   machine check of that subtraction: True
  step 5   conj(n)n^T and conj(m)m^T are linearly independent (n perp m): True
  step 6   generators: [c10*gam1 + c11*gam0, c20*gam1 + c21*gam0, c10*c21 + c11*c20]
           is 1 in the saturation by gam0*gam1*c10*c11*c20*c21 ?  True
           gam_{2g}=0 -> P_0+P_2+P_4 = 0;  gam_{2g+1}=0 -> P_1+P_3+P_5 = 0;
           both against (T2)=3/8.   CONTRADICTION.
     [facts used: (M) (T) (A) (T2) (R1) (R2)]

BRANCH 3.   Z_j = {g}, g not in Z_j2
  Same-anchor relation for j2 on the pair (g,h):  d_g J R_h^{(j2)T} = e1*p0 = 0,
  and p != 0, so X^j2_{2h+1} = 0.  Both anchors annihilate every odd X -> ALIGNED.

BRANCH 4a.  MIXED
  cross-anchor residuals: [a0*b1 + a1*b0, a0*b2 + a2*b0, a1*b2 + a2*b1]
  is 1 in the saturation by a0 a1 a2 b0 b1 b2 (all six R nonzero)? True
  CONTRADICTION.   [facts used: (R1) (R2) only]

BRANCH 4b.  ALIGNED
            exact solve of 2A = ev + 3/8 + A : [{A: ev + 3/8}]  so A = 3/8 + ev >= 3/8
            but A <= P_6 + P_7 = 1/4 by (A), and 3/8 > 1/4.   CONTRADICTION.
     [facts used: (M) (A) (T2) (R2)]

=== x26_b2.py (Branch 2, steps 5-6, fully symbolic) =========================
STEP 5.  R1(g,h) separates into a conj(n)n^T part and a conj(m)m^T part
  pair (g,h1):  E_ab = conj(n_a) n_b [cgam0*d11 + cgam1*d10]
                     + conj(m_a) m_b [cc10*del1 + cc11*del0]   exact: True
  pair (g,h2):  E_ab = conj(n_a) n_b [cgam0*d21 + cgam1*d20]
                     + conj(m_a) m_b [cc20*del1 + cc21*del0]   exact: True
STEP 5b. R1(h1,h2) is a single bracket times conj(m) n^T
  E_ab = conj(m_a) n_b [cc10*d21 + cc11*d20 + cc20*d11 + cc21*d10]   exact: True
STEP 6.  substitute  d_i = -nu conj(c_i)
  (I)  h1 becomes  -cc10*cgam1*nu - cc11*cgam0*nu   -> gam0*c11 + gam1*c10 = 0
  (I)  h2 becomes  -cc20*cgam1*nu - cc21*cgam0*nu   -> gam0*c21 + gam1*c20 = 0
  (III)     becomes  -2*cc10*cc21*nu - 2*cc11*cc20*nu  -> c10*c21 + c11*c20 = 0
  final system: [G0*u11 + G1*u10, G0*u21 + G1*u20, u10*u21 + u11*u20]
  Groebner basis of the Rabinowitsch ideal (saturate by all six nonzero): [1]
  unit ideal: True
  by hand, machine-confirmed: (I) forces (c_{2h},c_{2h+1}) = sigma_h (gam0,-gam1),
   and then (III) reads  sigma_1 sigma_2 * (-2*G0*G1) = -2*G0*G1*sig1*sig2
   so gam0*gam1 = 0, contradicting "both nonzero".

=== exhaustiveness ==========================================================
ordered pairs (Z_6,Z_7): 64
pairs NOT hit by exactly one branch: []
branch occupancy: {1: 48, 2: 3, 3: 12, 4: 1}

=== independent numerics (t26_facts_fast model, 150 multi-scale starts) ======
  BRANCH 1  Z_6 contains {0,1}     infeasible  resid 2.0620e-01  (69s)
  BRANCH 2  Z_6 = Z_7 = {0}        infeasible  resid 2.0620e-01  (75s)
  BRANCH 3  Z_6 = {0}              infeasible  resid 2.0620e-01  (76s)
  positive control, facts (M)+(N)+(E)          no branch: resid 1.060e-16  -> FEASIBLE
  positive control, facts (M)+(N)+(E)+(A)+(T2) no branch: resid 1.891e-16  -> FEASIBLE
(Branches 4a/4b were already run by the second pre-check: mixed 2.660e-01,
 aligned 2.229e-01 / 2.652e-01.)

=== global tally ============================================================
x26_all.out: 219 lines, 51 occurrences of "True", 0 occurrences of "False".
