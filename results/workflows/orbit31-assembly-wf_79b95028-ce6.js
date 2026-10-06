export const meta = {
  name: 'orbit31-assembly',
  description: 'Derive, machine-verify and formalise the family-three rebalancing that blocks the orbit 31 assembly',
  phases: [
    { title: 'Derive', detail: 'find a division-free form and verify it symbolically' },
    { title: 'Formalise', detail: 'write and compile the Lean lemma' },
    { title: 'Report', detail: 'consolidate into a usable result' },
  ],
}

const REPO = String.raw`D:\UTD\Project_purdue\Lean_certification`
const SCRATCH = String.raw`C:\Users\richa\AppData\Local\Temp\claude\D--UTD-Project-purdue\e2435927-3651-49b0-acfb-31f3430ee257\scratchpad`

const SETUP = `
PROJECT. A Lean 4 project at
    ${REPO}
proving no-go theorems for six-qubit ((6,2,3)) quantum codes.  Build with
\`lake build\`; check a single file with
    lake env lean <absolute path>
run from ${REPO}.  Mathlib is pinned; \`native_decide\` is FORBIDDEN (every proof
must pass the kernel, axioms exactly [propext, Classical.choice, Quot.sound]).
The project must stay at ZERO errors and ZERO warnings.

Python helpers live in ${SCRATCH} (sympy available).  Add
\`sys.path.insert(0, r'${SCRATCH}')\` then \`import o31\` for orbit-31 data
(S0, S1, POS, NAME), \`from scan import bits, xor, dot\`,
\`from kl import dressings_full\`.  Windows: use the Bash tool with forward
slashes, and write files with the Write tool (heredocs corrupt backslashes).

ORBIT 31.  Angle vector a = (1,1,1,2,2,2) mod 4, both fibers of size 16 and
complementary.  The last three angles are 2, so the Klein four-group
V = {000000, 000110, 000101, 000011} stabilises both fibers.  The sixteen
positions form a 4x4 table: rows A, B_1, B_2, B_3 and columns e_0..e_3.  Bottom
amplitudes are a_e at A_e and b_{i,e} at B_{i,e}; d is the top state.

VERIFIED MOMENT FACTS (trust these): p_1(v-bar) = p_0(v) at all sixteen
positions; sum_e beta_{i,e} = 1/4 for each B row; alpha_e = sum_i beta_{i,e} - 1/8
for each column; sum alpha = 1/4.

Because p_1(v-bar) = p_0(v), every active position admits
d_{v-bar} = rho_v conj(c_v) with |rho_v| = 1, and twelve two-term relations make
rho constant along COLUMNS.  Set

    v_e := conj(d at the complement of A_e),          so v_e = conj(rho_e) a_e,
    M_{ef} := sum_{i=1..3} b_{i,e} conj(b_{i,f}),     (Gram of the B columns)
    N_{ef} := a_e conj(a_f),
    t_{ef} := rho_f conj(rho_e) - 1.

FAMILY THREE is the set of diagonal Knill-Laflamme conditions on the three Klein
masks.  Each mask has four dressings; the two EVEN-weight ones give conditions on
G_{ef} := N_{ef} + M_{ef} and the two ODD-weight ones on H_{ef} := M_{ef} - N_{ef}.
Taking sums and differences, each unordered column pair {e,f} yields exactly

    G_{ef} t_{ef} + G_{fe} t_{fe} = 0,      H_{ef} t_{ef} - H_{fe} t_{fe} = 0,

equivalently (using G_{fe} = conj(G_{ef}) etc.)   M_{ef} t_{ef} = - conj(N_{ef} t_{ef}).
Since this is LINEAR in M_{ef} it determines it uniquely when t_{ef} != 0, and I
verified symbolically that the solution is

    M_{ef} = conj(v_e) v_f.

THE BLOCKER.  The relation above is stated through rho, which does not exist as a
Lean object (defining it needs division by conj(a_e)).  I need a DIVISION-FREE
restatement.  My unverified guess is to rebalance by conj(a_f) a_e, using

    t_{ef} * conj(a_f) * a_e = conj(v_f) v_e - conj(a_f) a_e  =:  T_{ef},

so that the whole relation becomes polynomial in a, v, M.  I have NOT checked
this rebalancing, and rebalancings like it are exactly where I made mistakes
today, so it must be machine-verified before anything is built on it.
`

phase('Derive')

const DERIVE_SCHEMA = {
  type: 'object',
  properties: {
    statement: { type: 'string', description: 'the division-free identity, written as a Lean-style equation in a_e, a_f, v_e, v_f, M_ef' },
    hypotheses: { type: 'array', items: { type: 'string' }, description: 'exactly what must be assumed, each division-free' },
    verified_how: { type: 'string' },
    verification_output: { type: 'string' },
    degenerate_cases: { type: 'string', description: 'what happens when a_e or a_f or t_ef vanishes' },
    confidence: { type: 'string', enum: ['machine-verified', 'derived-only', 'failed'] },
  },
  required: ['statement', 'hypotheses', 'verified_how', 'verification_output', 'degenerate_cases', 'confidence'],
}

const derivations = await parallel([
  () => agent(`${SETUP}

YOUR TASK. Find and MACHINE-VERIFY a division-free polynomial identity that
replaces \`M_{ef} = conj(v_e) v_f\`.

Work symbolically in sympy.  Treat a_e, a_f, v_e, v_f, M_ef and their conjugates
as INDEPENDENT symbols, and impose only what is actually known:
  * |v_e| = |a_e| and |v_f| = |a_f|, i.e. v_e*conj(v_e) = a_e*conj(a_e) and same for f;
  * the family-three relation in the form M_{ef} t_{ef} = - conj(N_{ef} t_{ef});
  * t_{ef} = rho_f conj(rho_e) - 1 where rho_e = conj(v_e)/conj(a_e).
Clear all denominators and report the resulting polynomial identity.  Then VERIFY
it: substitute the parametrisation v_e = conj(rho_e) a_e with |rho| = 1 and check
the identity reduces to zero symbolically.

Report the identity in a form directly usable as a Lean \`theorem\` statement over
ℂ with \`star\` for conjugation.  Be explicit about which hypotheses are needed and
what happens in the degenerate cases a_e = 0, a_f = 0, or t_ef = 0.  Paste the
actual sympy output in verification_output.`,
    { label: 'derive:rebalance', phase: 'Derive', schema: DERIVE_SCHEMA }),
  () => agent(`${SETUP}

YOUR TASK. Same goal as the other deriver, but take a DIFFERENT route: do not
try to rebalance my guess.  Instead go back to the RAW family-three conditions
and eliminate rho from scratch.

Concretely: recompute the twelve Klein-mask diagonal conditions directly from the
Knill-Laflamme definition using the orbit-31 data in Python (${SCRATCH}), with
the substitution d_{v-bar} = rho_v conj(c_v) and rho constant on columns, then
find what combination of them is polynomial in a, v, M alone (no rho).  Note
rho_e conj(rho_e) = 1 is available for simplification, and v_e = conj(rho_e) a_e
lets you trade rho for v.

Report a division-free identity and MACHINE-VERIFY it the same way.  Say clearly
if the honest answer is that NO division-free form exists without extra
hypotheses, and if so exactly which nonvanishing assumption is unavoidable.`,
    { label: 'derive:fromraw', phase: 'Derive', schema: DERIVE_SCHEMA }),
])

phase('Formalise')

const LEAN_SCHEMA = {
  type: 'object',
  properties: {
    compiled: { type: 'boolean' },
    file_path: { type: 'string' },
    lemma_source: { type: 'string', description: 'the full Lean source of the lemma(s), ready to paste' },
    compile_output: { type: 'string' },
    axioms: { type: 'string' },
    notes: { type: 'string' },
  },
  required: ['compiled', 'file_path', 'lemma_source', 'compile_output', 'axioms', 'notes'],
}

const lean = await agent(`${SETUP}

Two independent derivations of the division-free replacement for
\`M_{ef} = conj(v_e) v_f\` were produced:

${JSON.stringify(derivations.filter(Boolean), null, 2)}

YOUR TASK. Turn the SOUNDEST of these into compiling Lean 4.

1. Pick whichever derivation is actually machine-verified; if they disagree,
   re-verify in sympy yourself and say which one is right.
2. Write a standalone test file at
   ${SCRATCH}/Fam3Bridge.lean
   beginning with \`import Mathlib\`, namespace \`Fam3Bridge\`, and
   \`open scoped ComplexConjugate\`.  State the lemma over ℂ with \`star\`.
3. Compile it with \`lake env lean <path>\` run from ${REPO} and ITERATE until it
   compiles with ZERO errors and ZERO warnings.  Useful idioms in this project:
   \`linear_combination\` for polynomial identities (give it the hypotheses with
   explicit coefficients), \`congrArg star h\` followed by
   \`simp only [star_add, star_mul', star_star, star_zero] at h\` to conjugate a
   hypothesis, and \`rcases mul_eq_zero.mp h with h | h\` to split a product.
   A hypothesis \`h : X = Y\` contributes \`coeff * (X - Y)\` to \`linear_combination\`
   -- getting that sign backwards is the most common failure.
4. Check the axioms with a small file that does
   \`#print axioms Fam3Bridge.<name>\` and confirm they are exactly
   [propext, Classical.choice, Quot.sound].
5. Do NOT modify anything under ${REPO}/SixQubit -- work only in the scratchpad.

Report the exact compiling source.  If you cannot make it compile, say so
plainly and report the closest failing state with the error text.`,
  { label: 'formalise', phase: 'Formalise', schema: LEAN_SCHEMA, effort: 'high' })

phase('Report')

const summary = await agent(`${SETUP}

Derivations:
${JSON.stringify(derivations.filter(Boolean), null, 2)}

Lean result:
${JSON.stringify(lean, null, 2)}

YOUR TASK. Write a short, blunt report for the person who will paste this into
the project. Cover, in order:

1. Is the blocker resolved -- yes or no, one sentence.
2. The exact division-free statement that is now machine-verified, and the exact
   hypotheses it needs.
3. The compiling Lean source, verbatim, ready to paste into
   ${REPO}/SixQubit/Table31.lean (which already has \`sq\`, \`gram_eq\`,
   \`lone_column\`, \`pair_class\`, \`pair_gap\`, \`tight_pair\`, \`det_perm_zero\`,
   \`perm_triple\`, \`perm_support\`, \`conj4\`, \`kernel_norm\`, \`kernel_zero\`).
   If it does not compile, say so instead of pasting something untested.
4. The degenerate cases and how the caller must handle them.
5. What the NEXT step of the assembly is, concretely.

Do not pad. If something is unverified, label it unverified.`,
  { label: 'summary', phase: 'Report', effort: 'high' })

return { summary, derivations: derivations.filter(Boolean), lean }
