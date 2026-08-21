export const meta = {
  name: 'verify-orbit26',
  description: 'Adversarially verify the orbit 26 no-go derivation before building it in Lean',
  phases: [
    { title: 'Refute', detail: 'independent skeptics attack each derivation step' },
    { title: 'Gaps', detail: 'find missing branches and unstated assumptions' },
    { title: 'Synthesize', detail: 'consolidate into a verdict' },
  ],
}

const SETUP = `
CONTEXT. Six-qubit quantum error-correcting codes, ((6,2,3)). A "moment orbit"
fixes two disjoint supports S0, S1 in F_2^6 (the fibers). A putative code has
|0_L> = sum_{x in S0} c_x |x>, |1_L> = sum_{y in S1} d_y |y>, both unit vectors.
Distance 3 means the Knill-Laflamme conditions hold for every Pauli P of weight
at most 2:  <0_L|P|1_L> = 0  and  <0_L|P|0_L> = <1_L|P|1_L>.

ORBIT 26: angle vector a = (0,1,1,2,2,3) mod 4, fibers of size 16 each. Qubit
one carries angle zero, so each fiber is closed under flipping it and splits
into EIGHT blocks of two amplitudes. Read block i as a vector C_i in C^2
(bottom) and D_i in C^2 (top). Write P_i = ||C_i||^2 and Q_i = ||D_i||^2.

Blocks pair into FOUR GROUPS of two by a virtual bit z; group g is a 2x2 matrix
C_g whose columns are its two blocks. With my indexing the groups are
{0,1}, {2,3}, {4,5} and the ANCHOR group {6,7}.

FACTS ALREADY VERIFIED EXACTLY AGAINST THE MOMENT SYSTEM (trust these):
  * P_i = Q_i for all eight blocks
  * P_6 = P_7 = 1/8, so P_6 + P_7 = 1/4
  * sum_{i<6} P_i = 3/4
  * P_1+P_3+P_5 = P_0+P_2+P_4 = 3/8, and the same for the Q's
  * matrix moment identity, verified per group and per matrix entry:
        C_g C_g^dagger + D_g D_g^dagger = rho/2,   rho = sum_g C_g C_g^dagger,
    and rho is also the top reduced state sum_g D_g D_g^dagger.

RELATIONS AVAILABLE FROM KNILL-LAFLAMME (machine-checked to lie in the row
space of the relevant Walsh masks; nothing else off-diagonal is available):
  (R1) OUTER, one per group pair 0 <= g < h <= 2, four matrix entries each:
        conj(C_g) J D_h^T + conj(C_h) J D_g^T = 0,   J = [[0,1],[1,0]].
       Entry (a,b) reads
        sum_c conj((C_{2g+c})_a) (D_{2h+1-c})_b + sum_c conj((C_{2h+c})_a) (D_{2g+1-c})_b = 0.
  (R2) ANCHOR SCALAR, one per (cycle block i <= 5, anchor block j in {6,7}):
        C_j^dagger D_i + C_i^dagger D_j = 0.
IMPORTANT: per-edge matrix relations of the form D_i C_k^dagger + D_k C_i^dagger = 0
are NOT available. I wrongly assumed them once already. Do not use them.

THE DERIVATION UNDER TEST. Fix an anchor block j in {6,7}. Define
    X_i := C_j^dagger D_i,   Y_i := C_i^dagger D_j    (i = 0..5),
so (R2) says Y_i = -X_i. Set R_g := (X_{2g}, X_{2g+1}) for g = 0,1,2.

  STEP A. Contract the outer identity (R1) on index b with conj(C_j), then on
  index a with D_j. Claim: this yields Y_0 X_3 + Y_1 X_2 + Y_2 X_1 + Y_3 X_0 = 0
  for the pair (0,1), and using Y = -X this becomes X_0 X_3 + X_1 X_2 = 0.
  Similarly X_0 X_5 + X_1 X_4 = 0 and X_2 X_5 + X_3 X_4 = 0. Equivalently
  R_g J R_h^T = 0 for all three pairs.

  STEP B. J-orthogonality lemma: if r_0, r_1, r_2 in C^{1x2} are NONZERO and
  pairwise J-orthogonal then all three lie on one common coordinate axis.

  STEP C (the axis case, say all R_g on the FIRST axis, i.e. X_1 = X_3 = X_5 = 0):
    C1. X_i = C_j^dagger D_i = 0 for i in {1,3,5} and BOTH anchors j = 6,7 means
        C_6 and C_7 are each orthogonal to D_1, D_3, D_5. If C_6, C_7 were
        linearly independent then D_1 = D_3 = D_5 = 0, contradicting
        P_1+P_3+P_5 = 3/8. Hence C_6 is parallel to C_7.
    C2. Mirror: Y_i = -X_i = 0 gives C_i^dagger D_j = 0, so D_6, D_7 are each
        orthogonal to C_1, C_3, C_5, hence D_6 parallel to D_7.
    C3. So C_1, C_3, C_5 are all parallel to some u; D_1, D_3, D_5 parallel to
        some v; C_6, C_7 orthogonal to v; D_6, D_7 orthogonal to u. Writing
        A := C_6 C_6^dagger + C_7 C_7^dagger and A' := D_6 D_6^dagger + D_7 D_7^dagger,
        this gives A = (1/4) P_{v-perp} and A' = (1/4) P_{u-perp}, where P_w is
        the orthogonal projector onto the line spanned by w.
    C4. The matrix moment identity at the anchor group is A + A' = rho/2, so
        rho = 2(A + A'). With u, v unit vectors and kappa := |<u,v>|:
             <u|rho|u> = (1 - kappa^2)/2,    <u|A|u> = (1 - kappa^2)/4.
    C5. Blocks 1, 3, 5 are parallel to u and contribute exactly P_1+P_3+P_5 = 3/8
        to <u|rho|u>. Since rho = sum_{i=0}^{7} C_i C_i^dagger and blocks 6,7
        contribute <u|A|u>,
             <u| sum_{i in {0,2,4}} C_i C_i^dagger |u> = (1-kappa^2)/2 - 3/8 - (1-kappa^2)/4
                                                       = (1-kappa^2)/4 - 3/8,
        which is at most 1/4 - 3/8 = -1/8 < 0. But the left side is
        sum_{i in {0,2,4}} |<u, C_i>|^2 >= 0. CONTRADICTION.
`

phase('Refute')

const ATTACKS = [
  { key: 'stepA', prompt: `Attack STEP A only. Is the contraction really valid? Check very carefully:
(i) does contracting the outer identity on b with conj(C_j) really produce sum over the four (x,y) terms of conj((C_x)_a) X_y? Watch the placement of complex conjugation: the outer identity has conj(C_g), NOT C_g^dagger, and X_y = C_j^dagger D_y involves conj of C_j. Verify index by index.
(ii) does the second contraction with D_j on index a really produce Y_x = C_x^dagger D_j? Again check conjugation placement.
(iii) does the factor of 2 work out (the pair (0,1) has terms X_0X_3, X_1X_2, X_2X_1, X_3X_0)?
(iv) is the identification with R_g J R_h^T = 0 correct for ALL THREE pairs (0,1), (0,2), (1,2), given the index formula 2h+1-c?
Write out the (0,2) case explicitly and confirm it gives X_0X_5 + X_1X_4 = 0.` },
  { key: 'stepB', prompt: `Attack STEP B only, the J-orthogonality lemma: three NONZERO rows in C^{1x2}, pairwise J-orthogonal with J = [[0,1],[1,0]], all lie on one coordinate axis.
Note r J s^T = r_0 s_1 + r_1 s_0. Is the lemma TRUE as stated over C? Prove it or find a counterexample. Pay attention to: does "pairwise J-orthogonal" include r_g J r_g^T = 0 (which is NOT assumed here, only g != h)? Does the conclusion "one common coordinate axis" follow, or only "all proportional"? Construct explicit counterexamples if the lemma is false.` },
  { key: 'stepC12', prompt: `Attack STEP C1 and C2 only. The claim is: C_6 and C_7 are each orthogonal to D_1, D_3, D_5; if C_6 and C_7 were linearly independent then D_1 = D_3 = D_5 = 0.
(i) Is that inference right in C^2 with the Hermitian inner product? If C_6, C_7 are independent they span C^2, so any vector orthogonal to both is zero -- check this is what is being used and that the orthogonality is in the right slot (C_j^dagger D_i = 0 means D_i is orthogonal to C_j).
(ii) The step needs P_1+P_3+P_5 = 3/8 to be nonzero, which is given. But does it need at least one of D_1,D_3,D_5 individually nonzero? Yes -- confirm the sum being 3/8 gives that.
(iii) Is "C_6 parallel to C_7" the right conclusion, or could C_6 or C_7 be ZERO? Note P_6 = P_7 = 1/8 so both are nonzero. Confirm.
(iv) Does the mirror argument in C2 really work? Y_i = C_i^dagger D_j = 0 means D_j orthogonal to C_i. Check the slot carefully.` },
  { key: 'stepC345', prompt: `Attack STEP C3, C4 and C5 only -- the final numerical contradiction.
(i) C3 claims A = C_6 C_6^dagger + C_7 C_7^dagger equals (1/4) P_{v-perp}. This needs C_6, C_7 both orthogonal to v AND ||C_6||^2 + ||C_7||^2 = 1/4. In C^2 the orthogonal complement of v is one-dimensional, so both lie on it. Verify the resulting matrix is exactly (P_6+P_7) times the projector.
(ii) C4 uses rho = 2(A+A') from the anchor group identity C_3 C_3^dagger + D_3 D_3^dagger = rho/2. Confirm A and A' really are the anchor group's C_g C_g^dagger and D_g D_g^dagger.
(iii) Verify <u|rho|u> = (1-kappa^2)/2 and <u|A|u> = (1-kappa^2)/4 by direct computation with u, v unit vectors in C^2. Is <u|P_{u-perp}|u> = 0 and <u|P_{v-perp}|u> = 1 - kappa^2 correct?
(iv) Verify the arithmetic of C5: (1-kappa^2)/2 - 3/8 - (1-kappa^2)/4 = (1-kappa^2)/4 - 3/8, and that this is <= -1/8. Is the decomposition of rho into blocks {1,3,5}, {0,2,4}, {6,7} exhaustive and non-overlapping over i = 0..7?
(v) MOST IMPORTANT: is <u|rho|u> really equal to sum_i |<u,C_i>|^2? rho = sum_i C_i C_i^dagger, so yes -- but confirm, and confirm blocks 1,3,5 parallel to u contribute exactly P_1+P_3+P_5 and not something else.` },
]

const REFUTE_SCHEMA = {
  type: 'object',
  properties: {
    step: { type: 'string' },
    verdict: { type: 'string', enum: ['sound', 'flawed', 'unclear'] },
    problems: {
      type: 'array',
      items: {
        type: 'object',
        properties: {
          claim: { type: 'string' },
          why_wrong: { type: 'string' },
          severity: { type: 'string', enum: ['fatal', 'fixable', 'cosmetic'] },
        },
        required: ['claim', 'why_wrong', 'severity'],
      },
    },
    notes: { type: 'string' },
  },
  required: ['step', 'verdict', 'problems', 'notes'],
}

const refutations = await parallel(ATTACKS.map(a => () =>
  agent(`${SETUP}

YOUR TASK. You are a hostile referee. Your job is to BREAK the argument, not to
agree with it. Default to "flawed" if anything is not airtight. Work the algebra
out explicitly in coordinates where you can. Be concrete: if you claim a step is
wrong, give the specific index, sign, or counterexample.

${a.prompt}`, { label: `refute:${a.key}`, phase: 'Refute', schema: REFUTE_SCHEMA })
))

phase('Gaps')

const GAP_SCHEMA = {
  type: 'object',
  properties: {
    gaps: {
      type: 'array',
      items: {
        type: 'object',
        properties: {
          what: { type: 'string' },
          why_it_matters: { type: 'string' },
          how_to_close: { type: 'string' },
        },
        required: ['what', 'why_it_matters', 'how_to_close'],
      },
    },
    summary: { type: 'string' },
  },
  required: ['gaps', 'summary'],
}

const gaps = await parallel([
  () => agent(`${SETUP}

YOUR TASK. The derivation above only handles the branch where all three R_g are
NONZERO (so step B applies) and they land on the FIRST coordinate axis. Enumerate
EVERY branch that is not covered, and say for each whether the argument still
closes and how. In particular:
  * what if exactly one R_g = 0? two? all three?
  * what if the common axis is the SECOND one (X_0 = X_2 = X_4 = 0)?
  * the X_i depend on WHICH anchor block j = 6 or 7 was used. Do the two anchors
    have to land on the same axis? Step C1 quietly uses BOTH anchors at once
    ("X_i = 0 for i in {1,3,5} and BOTH anchors"). Is that justified, or does
    each anchor only give its own vanishing pattern? THIS IS THE MOST LIKELY
    HOLE -- examine it very carefully.
Be exhaustive and concrete.`, { label: 'gaps:branches', phase: 'Gaps', schema: GAP_SCHEMA }),
  () => agent(`${SETUP}

YOUR TASK. Hunt for UNSTATED ASSUMPTIONS and hidden divisions in the derivation.
List every place where the argument implicitly assumes some quantity is nonzero,
some vectors are independent, some object is invertible, or divides by something.
For each, say whether the assumption is justified by the verified facts listed
above, and if not, what breaks. Also check whether any step secretly uses the
per-edge matrix relations that are NOT available (these would be relations of the
form D_i C_k^dagger + D_k C_i^dagger = 0 for individual blocks i, k).`,
    { label: 'gaps:assumptions', phase: 'Gaps', schema: GAP_SCHEMA }),
])

phase('Synthesize')

const verdict = await agent(`${SETUP}

Four hostile referees attacked the four steps, and two more hunted for gaps and
hidden assumptions. Here is everything they reported.

REFUTATIONS:
${JSON.stringify(refutations.filter(Boolean), null, 2)}

GAPS:
${JSON.stringify(gaps.filter(Boolean), null, 2)}

YOUR TASK. Produce a consolidated verdict for the person who will now spend many
hours formalising this in Lean 4. Be blunt. Structure it as:

1. VERDICT: is the derivation as stated correct, correct-but-incomplete, or
   broken? One sentence.
2. CONFIRMED FATAL PROBLEMS: only the ones you judge real after weighing the
   referees against each other. For each: which step, what exactly is wrong, and
   whether it is repairable. Discard referee complaints that are mistaken -- say
   which ones you discarded and why.
3. MISSING BRANCHES: the exhaustive list of cases the argument does not yet
   cover, with a concrete suggestion for each.
4. THE TWO-ANCHOR QUESTION: settle definitively whether step C1 may use both
   anchor blocks simultaneously.
5. WHAT IS SAFE TO BUILD NOW: the sub-parts a formaliser can start on today
   without risk of rework.

Do not be diplomatic. If the argument is broken, say so plainly.`,
  { label: 'synthesize', phase: 'Synthesize', effort: 'high' })

return { verdict, refutations: refutations.filter(Boolean), gaps: gaps.filter(Boolean) }
