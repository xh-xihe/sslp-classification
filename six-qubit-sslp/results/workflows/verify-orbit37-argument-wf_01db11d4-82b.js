export const meta = {
  name: 'verify-orbit37-argument',
  description: 'Adversarially check the four-branch no-go argument for six-qubit moment orbit 37',
  phases: [{ title: 'Refute', detail: 'three skeptics, distinct lenses' }],
}

const ARGUMENT = `
SETTING. A putative ((6,2,d>=3)) qubit code. Bottom amplitudes c on fiber S_0,
top amplitudes d on S_1 = bitwise complement of S_0. Orbit 37: a = (1,1,1,2,3,3),
q = 5, delta = 1. Bottom fiber (13 strings):
  S    = 111100
  A_1  = 000000,  A_2 = 000101,  A_3 = 000110
  B    = 3x3 grid, rows indexed 1..3, columns 1..3:
         row1: 011001 011010 011111
         row2: 101001 101010 101111
         row3: 110001 110010 110111
Write u_x = conj(c_x), v_xhat = d_xhat, P(x,yhat) = u_x v_yhat. A Pauli X^e Z^z
of weight <= 2 gives sum over y in S_1 with y xor e in S_0 of (-1)^{z.y} u_{y xor e} v_y = 0.

FACTS I VERIFIED BY EXACT COMPUTATION (treat as given):
 (F1) q_S = r_Shat = 1/10, forced exactly by the linear moment system.
 (F2) sum_{j=1..3} |c_{A_j}|^2 = 3/10, on both fibers.
 (F3) Each B-row sums to 1/5, on both fibers.
 (F4) Each B-column total lies in [1/10, 2/5]; the lower bound 1/10 is an LP
      consequence of the moment system plus nonnegativity.
 (F5) THREE masks have exactly two incidences: they are the reciprocal pairs
      {A_j <-> Shat, S <-> A_j-hat}, giving  P(A_j,Shat) + P(S,A_j-hat) = 0.
 (F6) THREE masks (X_1, X_2, X_3, weight one) have exactly six incidences each;
      mask X_i has incidences (A_1,B_i3-hat), (A_2,B_i2-hat), (A_3,B_i1-hat),
      (B_i1,A_3-hat), (B_i2,A_2-hat), (B_i3,A_1-hat). Its dressing system has
      RANK 4 and yields, for each row i:
        STAR:  P(A_1,B_i3-hat) + P(A_2,B_i2-hat) + P(A_3,B_i1-hat) = 0
        SYNC:  P(A_k, B_{i,4-k}-hat) = P(B_{i,4-k}, A_k-hat)   for k = 1,2,3
 (F7) NINE masks have exactly four incidences: for rows i<k and columns j<l the
      permanent {(B_ij,B_kl-hat),(B_kl,B_ij-hat),(B_il,B_kj-hat),(B_kj,B_il-hat)}.
      Each such mask's dressing system has RANK ONE -- it gives only its single
      four-term equation and NO direct pairing of its terms.
 (F8) With the extra constraint |c_{A_j}|^2 = 0 imposed, the LP pins the total
      weight of grid column (4-j) to EXACTLY 1/10. With |c_{A_k}|^2 = 0 for both
      k != j0, the LP pins the total weight of column (4-j0) to EXACTLY 2/5.

THE ARGUMENT I WANT REFUTED. Let J = {j : c_{A_j} != 0}.

Preliminary (the bridge at S). From (F5) and (F1): u_S and v_Shat are nonzero,
and P(A_j,Shat) = -P(S,A_j-hat) means u_{A_j} v_Shat = -u_S v_{A_j-hat}. Hence
c_{A_j} = 0 iff d_{A_j-hat} = 0, for each j. (Division-free: multiply out.)

Branch |J| = 0. Then all |c_{A_j}|^2 = 0, contradicting (F2).

Branch |J| = 1, say J = {j0}. For k != j0, u_{A_k} = 0. STAR for row i then
reduces to u_{A_j0} v_{B_{i,4-j0}-hat} = 0, and u_{A_j0} != 0, so
v_{B_{i,4-j0}-hat} = 0 for every row i. SYNC with k = j0 reads
u_{A_j0} v_{B_{i,4-j0}-hat} = u_{B_{i,4-j0}} v_{A_j0-hat}; the left side is now 0
and v_{A_j0-hat} != 0 by the bridge, so u_{B_{i,4-j0}} = 0 for every i. So grid
column (4-j0) is entirely zero, total weight 0 -- contradicting (F8), which pins
that column to 2/5.

Branch |J| = 2, say J = {j1,j2} and a_{j3} = 0. For j in J, the sync relation
plus the bridge identify the phase ratio of grid column (4-j) with that of S, so
for the two active columns c1 = 4-j1, c2 = 4-j2 the four terms of each permanent
(F7) pair up and it collapses to
    (R_ik)   P(B_i,c1, B_k,c2-hat) + P(B_i,c2, B_k,c1-hat) = 0     for i != k,
and its mirror. Writing x_i = c_{B_i,c1}, y_i = c_{B_i,c2}, this is
x_i y_k + x_k y_i = 0 for all i != k. Now:
  * if some x_i = 0 and y_i != 0, then x_k = 0 for all k, so column c1 is
    entirely zero, contradicting the lower bound 1/10 of (F4);
  * if some x_i = 0 and y_i = 0, row i carries its whole weight 1/5 in the
    inactive column (4-j3), whose total is exactly 1/10 by (F8) -- impossible
    since 1/5 > 1/10.
So all x_i != 0, and symmetrically all y_i != 0. Then the three relations
x_1y_2 + x_2y_1 = 0, x_1y_3 + x_3y_1 = 0, x_2y_3 + x_3y_2 = 0 multiply to give
2 x_1x_2x_3 y_1y_2y_3 = 0, a contradiction.

Branch |J| = 3. All three columns are phase-identified with S, so every permanent
collapses as above, giving signed vanishing of all 2x2 minors of the grid. If some
c_{B_ij} = 0, then for all k != i, l != j either c_{B_il} = 0 or c_{B_kj} = 0;
hence either row i vanishes entirely (contradicting the row sum 1/5) or column j
vanishes entirely (contradicting the column bound 1/10). So all nine grid
amplitudes are nonzero, and the length-three odd cycle
P(B_22,B_11-hat) = -P(B_21,B_12-hat), P(B_23,B_11-hat) = -P(B_21,B_13-hat),
P(B_23,B_12-hat) = -P(B_22,B_13-hat) forces a product of six nonzero amplitudes
to vanish.

YOUR TASK. Try hard to REFUTE this. Default to "refuted" if uncertain. Check:
 Q1. The phase-ratio identification in branches |J| = 2, 3: it needs a
     transitivity whose multiplier must be nonzero. Which multiplier exactly, and
     is its nonvanishing actually established, or is it circular? This is where an
     earlier version of my argument was wrong, so scrutinize it hardest.
 Q2. Branch |J| = 2: does "symmetrically all y_i != 0" really follow, or does it
     need the mirror relation? Does the x_i = y_i = 0 sub-branch really force the
     whole row weight into the single inactive column -- what about the OTHER
     active column?
 Q3. Branch |J| = 3: does the 2x2-minor step really give "row or column vanishes"?
     Write out the quantifiers.
 Q4. The odd cycles: verify the monomials coincide and the sign count is odd.
 Q5. Anything assumed without justification, in particular any place I use a
     nonvanishing that was only established for the OTHER fiber.
Answer with algebra, not impressions.`

const SCHEMA = {
  type: 'object',
  additionalProperties: false,
  required: ['refuted', 'verdict', 'gaps', 'algebraCheck'],
  properties: {
    refuted: { type: 'boolean' },
    verdict: { type: 'string', description: 'One paragraph: sound, or exactly where it fails.' },
    gaps: { type: 'string', description: 'Every gap, numbered, each with the missing hypothesis or wrong step. Address Q1-Q3 explicitly.' },
    algebraCheck: { type: 'string', description: 'Explicit working for the transitivity multiplier, the 2x2-minor step, and both odd cycles.' },
  },
}

const LENSES = [
  'the CIRCULARITY lens: trace every nonvanishing claim back to its source and check nothing is used before it is proved, especially across the two fibers',
  'the ALGEBRA lens: recompute every displayed identity symbolically, the collapses, the minors and both odd cycles',
  'the CASE-COVERAGE lens: are the four branches exhaustive, are the sub-branches inside |J|=2 and |J|=3 exhaustive, and does each really terminate in a contradiction',
]

const votes = await parallel(LENSES.map((lens, i) => () =>
  agent(`${ARGUMENT}\n\nApproach this through ${lens}. Be a skeptic: your job is to find the flaw.`,
    { label: `skeptic-${i}`, phase: 'Refute', schema: SCHEMA })))

return { votes: votes.filter(Boolean) }
