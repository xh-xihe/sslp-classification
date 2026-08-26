export const meta = {
  name: 'orbit26-rebuild',
  description: 'Pre-check the silent failure modes, repair the two-anchor gap, and rebuild the orbit 26 algebra in Lean',
  phases: [
    { title: 'Precheck', detail: 'machine-verify the four silent assumptions behind Step A' },
    { title: 'Repair', detail: 'derive the cross-anchor contraction and close the branches' },
    { title: 'Formalise', detail: 'write and compile the repaired algebra layer' },
    { title: 'Report', detail: 'consolidate' },
  ],
}

const REPO = String.raw`D:\UTD\Project_purdue\Lean_certification`
const SCRATCH = String.raw`C:\Users\richa\AppData\Local\Temp\claude\D--UTD-Project-purdue\e2435927-3651-49b0-acfb-31f3430ee257\scratchpad`

const SETUP = `
PROJECT. Lean 4 at ${REPO}, no-go theorems for six-qubit ((6,2,3)) codes.
Build: \`lake build\`.  Single file: \`lake env lean <abs path>\` run from ${REPO}.
\`native_decide\` FORBIDDEN -- every proof must pass the kernel with axioms
exactly [propext, Classical.choice, Quot.sound].  The project must stay at ZERO
errors and ZERO warnings.

Python helpers in ${SCRATCH} (sympy, numpy, scipy).  Use
\`sys.path.insert(0, r'${SCRATCH}')\`, then \`import o26\` and \`import o26data\`
for orbit-26 data, \`from scan import bits, xor, dot\`,
\`from kl import dressings_full, conditions\`, \`from cert import build,
reduce_mod_linear\` (the last reduces an expression modulo the moment system;
remainder 0 means the moment system implies it).
On Windows use the Bash tool with forward slashes and the Write tool for files
(heredocs corrupt backslashes).

ORBIT 26.  a = (0,1,1,2,2,3) mod 4, fibers 16+16.  Qubit one has angle zero, so
each fiber splits into EIGHT blocks of two amplitudes; block i is a vector
C_i (bottom) or D_i (top) in C^2, with P_i = ||C_i||^2, Q_i = ||D_i||^2.
Blocks pair by a virtual bit into FOUR GROUPS, each a 2x2 matrix whose columns
are its two blocks.  In the sorted indexing used by \`o26.py\` the groups are
{0,1}, {2,3}, {4,5} and the ANCHOR group {6,7}.

MACHINE-VERIFIED FACTS (trust, but re-check cheaply if convenient):
  * P_i = Q_i for all eight blocks; P_6 = P_7 = 1/8; sum_{i<6} P_i = 3/4;
    P_1+P_3+P_5 = P_0+P_2+P_4 = 3/8 (and the same for Q).
  * MATRIX MOMENT IDENTITY, verified per group and per matrix entry:
        C_g C_g^dagger + D_g D_g^dagger = rho/2,   rho = sum_g C_g C_g^dagger,
    and rho is also sum_g D_g D_g^dagger.
  * OUTER identity R1, one per group pair 0 <= g < h <= 2, all FOUR matrix
    entries verified to lie in the Walsh row spaces:
        conj(C_g) J D_h^T + conj(C_h) J D_g^T = 0,  J = [[0,1],[1,0]].
    Entry (a,b) is
        sum_c conj((C_{2g+c})_a)(D_{2h+1-c})_b + sum_c conj((C_{2h+c})_a)(D_{2g+1-c})_b = 0.
    Masks: pair (0,1) uses 010000/110000, (0,2) uses 001000/101000,
    (1,2) uses 000001/100001; the (a,a) entries come from the weight-one mask and
    the (a,b) entries from its weight-two partner.
  * ANCHOR SCALAR R2, one per (cycle block i <= 5, anchor block j in {6,7}):
        C_j^dagger D_i + C_i^dagger D_j = 0.   Twelve of these, all available.

NOT AVAILABLE (I wrongly assumed these once): per-edge matrix relations
D_i C_k^dagger + D_k C_i^dagger = 0 for individual blocks.  The weight-one masks
carry EIGHT incidences with rank only FOUR and admit NO two-term relation; only
the group-level sums above exist.  \`SixQubit/Block26.lean\` in the repo is built
on the wrong assumption and carries a warning; do not reuse its
\`overlaps_vanish\` or \`finish26\`.

THE ARGUMENT AND ITS GAP.  Fix an anchor block j in {6,7}, set
X_i := C_j^dagger D_i and Y_i := C_i^dagger D_j (i = 0..5), so R2 says Y_i = -X_i.
Set R_g := (X_{2g}, X_{2g+1}) for g = 0,1,2.  Contracting R1 on the b index with
conj(C_j) and on the a index with D_j gives
    R_g J R_h^T = 0   for all three pairs g < h,
i.e. X_0X_3 + X_1X_2 = 0, X_0X_5 + X_1X_4 = 0, X_2X_5 + X_3X_4 = 0.
Three NONZERO pairwise J-orthogonal rows in C^{1x2} lie on one coordinate axis,
so (say) X_1 = X_3 = X_5 = 0.

FATAL GAP, confirmed by an earlier adversarial review with explicit witnesses:
the axis choice is PER ANCHOR.  Nothing links the axis for j = 6 to the axis for
j = 7, yet the rest of the argument silently uses both at once.  In the mixed
branch C_6 is NOT parallel to C_7 and the counting closes with slack.

SUGGESTED REPAIR (unverified): a CROSS-ANCHOR contraction of R1 -- contract on
the b index with conj(C_6) and on the a index with D_7 (or vice versa) instead
of using the same anchor in both slots.  Also add the derived fact
    (T)  P_{2g} + P_{2g+1} = 1/4 for EVERY group INCLUDING the anchor,
which follows from tr of the group identity plus P_i = Q_i and tr rho = 1, and is
strictly stronger than sum_{i<6} P_i = 3/4.
`

phase('Precheck')

const PRE_SCHEMA = {
  type: 'object',
  properties: {
    checks: {
      type: 'array',
      items: {
        type: 'object',
        properties: {
          what: { type: 'string' },
          verdict: { type: 'string', enum: ['holds', 'fails', 'inconclusive'] },
          evidence: { type: 'string' },
        },
        required: ['what', 'verdict', 'evidence'],
      },
    },
    fatal: { type: 'string', description: 'anything that invalidates the whole approach, or "none"' },
  },
  required: ['checks', 'fatal'],
}

const precheck = await parallel([
  () => agent(`${SETUP}

YOUR TASK. Machine-verify the four SILENT assumptions behind the Step A
contraction.  Each of them, if false, makes Step A produce \`0 = 0\` with no
symptom, so every one must be checked in Python against the actual Walsh data.

  (a) R1's relative sign.  Step A's output is proportional to (1 + omega) times
      R_g J R_h^T.  If the true relative coefficient is omega = -1 the whole
      contraction is vacuous.  Determine omega from the actual row spaces.
  (b) R2's per-block phase.  Step A needs Y_i = mu * X_i with the SAME mu for
      every block i.  The angle vector has a 2 and a 3 in it, so the Pauli phases
      could vary by block.  Compute mu_i for all twelve instances of R2 and check
      they agree.
  (c) The virtual-bit orientation.  The J-form requires ONE global choice of
      which block of a group is "first", used consistently in R1's index formula
      2h+1-c AND in R_g := (X_{2g}, X_{2g+1}).  Check that a single global choice
      makes all three pairs come out in J-form (and not the I-form
      X_{2g}X_{2h} + X_{2g+1}X_{2h+1} = 0 for some pair).
  (d) Index identification.  R1's b index and R2's D-side index must refer to the
      same labelling of the two S1 bits.  Check that R2's available scalar really
      is sum_b conj((C_j)_b)(D_i)_b and not the flipped
      sum_b conj((C_j)_b)(D_i)_{1-b}.

Do this by recomputing the Walsh row spaces from the orbit-26 data and reading
the relations off, NOT by trusting the description above.  Report a verdict per
check with the actual computed evidence.`,
    { label: 'precheck:stepA', phase: 'Precheck', schema: PRE_SCHEMA }),
  () => agent(`${SETUP}

YOUR TASK. Verify the two probability facts the repair leans on, and map out the
degenerate branches.

  1. Prove or refute fact (T): P_{2g} + P_{2g+1} = 1/4 for EVERY group including
     the anchor.  Use \`reduce_mod_linear\` against the moment system; remainder 0
     means the moment system implies it.
  2. Enumerate, by linear programming over the moment polytope, exactly which
     blocks can vanish simultaneously.  Report the feasible zero-sets.
  3. The J-orthogonality lemma needs all three R_g NONZERO.  R_g = 0 means
     C_j is orthogonal to both blocks of group g.  For each anchor j and each
     group g, is R_g = 0 compatible with the verified facts?  List the branches
     the argument must still cover.
  4. Independently confirm that orbit 26 really is excluded by the FULL weight-<=2
     Knill-Laflamme system: set up the raw conditions numerically (kl.conditions)
     and run a least-squares search from many random starts.  Report the best
     residual.  A residual near zero would mean the orbit is NOT excluded and the
     whole effort is misdirected -- say so loudly if that happens.`,
    { label: 'precheck:facts', phase: 'Precheck', schema: PRE_SCHEMA }),
])

phase('Repair')

const REPAIR_SCHEMA = {
  type: 'object',
  properties: {
    closes: { type: 'boolean', description: 'does the repaired argument close every branch' },
    cross_anchor: { type: 'string', description: 'the cross-anchor relation, machine-verified, or why it fails' },
    branch_table: { type: 'string', description: 'every branch and how it closes' },
    remaining_gaps: { type: 'string' },
    verification_output: { type: 'string' },
  },
  required: ['closes', 'cross_anchor', 'branch_table', 'remaining_gaps', 'verification_output'],
}

const repair = await agent(`${SETUP}

Pre-check results:
${JSON.stringify(precheck.filter(Boolean), null, 2)}

YOUR TASK. Repair the two-anchor gap and close every branch.

1. Derive the CROSS-ANCHOR contraction: contract R1 on the b index with
   conj(C_6) and on the a index with D_7, and separately the other way round.
   Write out exactly what relation results, in terms of
   X^j_i = C_j^dagger D_i and Y^j_i = C_i^dagger D_j for j = 6,7.  MACHINE-VERIFY
   it symbolically (bilinearity only -- no index guessing).
2. Determine whether that relation links the axis choice for anchor 6 to the one
   for anchor 7.  If it does, state the linkage precisely.  If it does NOT, say
   so and find another relation that does, or report that the gap is unclosable
   with the available conditions.
3. Cover the branches where some R_g = 0, for each anchor.
4. Assemble the full case tree and say, for each leaf, which verified fact
   produces the contradiction.  Use fact (T) and the 3/8 splits freely if the
   pre-check confirmed them.

Be honest: if a branch does not close, say which one and why, rather than
papering over it.  Paste the actual symbolic verification output.`,
  { label: 'repair', phase: 'Repair', schema: REPAIR_SCHEMA, effort: 'high' })

phase('Formalise')

const LEAN_SCHEMA = {
  type: 'object',
  properties: {
    compiled: { type: 'boolean' },
    file_path: { type: 'string' },
    lemma_source: { type: 'string' },
    compile_output: { type: 'string' },
    axioms: { type: 'string' },
    coverage: { type: 'string', description: 'which parts of the argument are now formalised and which are not' },
  },
  required: ['compiled', 'file_path', 'lemma_source', 'compile_output', 'axioms', 'coverage'],
}

const lean = await agent(`${SETUP}

The repaired argument:
${JSON.stringify(repair, null, 2)}

YOUR TASK. Formalise as much of the repaired argument as will compile.

Write a standalone file at ${SCRATCH}/Block26New.lean starting with
\`import Mathlib\`, namespace \`Block26New\`, \`open scoped ComplexConjugate\`.
Do NOT touch anything under ${REPO}/SixQubit.

Formalise, in this order of priority:
  1. the J-orthogonality lemma over C: three NONZERO rows in C^{1x2}, pairwise
     J-orthogonal with J antidiagonal, lie on one coordinate axis.  (r J s^T =
     r_0 s_1 + r_1 s_0.  Self-isotropy is a CONSEQUENCE, not a hypothesis.)
  2. the cross-anchor relation from the repair, as a conditional statement;
  3. whatever branch closures the repair established.

Useful idioms in this project: \`linear_combination\` for polynomial identities
(a hypothesis \`h : X = Y\` contributes \`coeff * (X - Y)\` -- getting that sign
backwards is the most common failure); \`congrArg star h\` then
\`simp only [star_add, star_mul', star_star, star_zero] at h\` to conjugate;
\`rcases mul_eq_zero.mp h with h | h\` to split a product; \`nlinarith\` with
\`Complex.normSq_nonneg\` hints for real positivity.

Compile with \`lake env lean\` from ${REPO} and ITERATE to ZERO errors and ZERO
warnings (prefix genuinely unused hypotheses with \`_\`).  Then \`#print axioms\`
each headline lemma and confirm [propext, Classical.choice, Quot.sound].

Report the exact compiling source and be explicit about what you did NOT manage
to formalise.`,
  { label: 'formalise', phase: 'Formalise', schema: LEAN_SCHEMA, effort: 'high' })

phase('Report')

const summary = await agent(`${SETUP}

Pre-check: ${JSON.stringify(precheck.filter(Boolean), null, 2)}
Repair:    ${JSON.stringify(repair, null, 2)}
Lean:      ${JSON.stringify(lean, null, 2)}

YOUR TASK. A blunt report for the person who will paste this into the project.

1. Did any pre-check FAIL?  If Step A is vacuous or the orbit is not actually
   excluded, lead with that -- it changes everything.
2. Is the two-anchor gap closed?  Yes or no, and by what relation.
3. The compiling Lean source, verbatim, ready to paste.  If it does not compile,
   say so rather than pasting something untested.
4. The branch table: every leaf and the fact that kills it.  Flag any leaf that
   is still open.
5. The concrete next step.

Label anything unverified as unverified.  Do not pad.`,
  { label: 'summary', phase: 'Report', effort: 'high' })

return { summary, precheck: precheck.filter(Boolean), repair, lean }
