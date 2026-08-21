export const meta = {
  name: 'orbit26-finish',
  description: 'Build the orbit 26 transcription layer and assembly to complete its certification',
  phases: [
    { title: 'Survey', detail: 'pin the exact interfaces and the certificate coefficients' },
    { title: 'Transcribe', detail: 'generate and compile the transcription layer' },
    { title: 'Assemble', detail: 'wire it to the algebra and conclude False' },
    { title: 'Audit', detail: 'independent recompile and honesty check' },
  ],
}

const REPO = String.raw`D:\UTD\Project_purdue\Lean_certification`
const SCRATCH = String.raw`C:\Users\richa\AppData\Local\Temp\claude\D--UTD-Project-purdue\e2435927-3651-49b0-acfb-31f3430ee257\scratchpad`

const SETUP = `
PROJECT. Lean 4 at ${REPO}.  Build: \`lake build\`.  Single file:
\`lake env lean <abs path>\` run from ${REPO}.  \`native_decide\` FORBIDDEN --
every proof must pass the kernel with axioms exactly
[propext, Classical.choice, Quot.sound].  ZERO errors, ZERO warnings (prefix
genuinely unused hypotheses with \`_\`).  Never write \`sorry\`.
Scratch: ${SCRATCH}.  On Windows use the Bash tool with forward slashes and the
Write tool for files (heredocs corrupt backslashes).

Python helpers in ${SCRATCH}: \`sys.path.insert(0, r'${SCRATCH}')\`, then
\`import o26\` and \`import o26data\` (orbit-26 tables), \`from scan import bits,
xor, dot\`, \`from kl import dressings_full\`, \`from cert import build,
reduce_mod_linear\` (reduces an expression modulo the moment system; remainder 0
means the moment system implies it).

GOAL.  Finish moment orbit 26.  Its ALGEBRA layer is done and installed at
${REPO}/SixQubit/Block26.lean (415 lines, 19 theorems, all axioms clean):
  mul_conj_self, axis_lemma, axis_isotropic, contract, cross_anchor, per_anchor,
  mixed_core, branch4a, branch3_step, unit_pair_orthogonal, branch2_step6,
  lagrange, cauchy_schwarz_unit, branch4b_core, branch4b, branch1,
  branch4_aligned, branch3_aligned, branch1_full.
What is MISSING is the transcription layer and the assembly.

ORBIT 26.  a = (0,1,1,2,2,3) mod 4, fibers 16+16.  Qubit one has angle zero, so
each fiber splits into EIGHT blocks of two amplitudes; block i is a vector in
C^2, P_i = ||C_i||^2 (bottom), Q_i = ||D_i||^2 (top).  Blocks pair into FOUR
GROUPS by a virtual bit; in \`o26.py\`'s sorted indexing the groups are {0,1},
{2,3}, {4,5} and the ANCHOR group {6,7}.  IMPORTANT: \`blocks.py\`'s \`structure\`
returns TOP blocks indexed by SORTED top tails; for block matching you must index
the top block by the COMPLEMENT of the bottom tail, as \`o26.py\` does.  Getting
this wrong makes the matrix moment identity appear to fail.

WHAT MUST BE TRANSCRIBED (all machine-verified to be available):

 * MOMENT FACTS, each provable from the \`MomentSystem\` by \`linear_combination\`
   with coefficients from \`reduce_mod_linear\`:
     P_i = Q_i for all eight blocks;  P_6 = P_7 = 1/8;  sum_{i<6} P_i = 3/4;
     (T)  P_{2g} + P_{2g+1} = 1/4 for EVERY group including the anchor;
     (T2) P_0+P_2+P_4 = P_1+P_3+P_5 = 3/8  -- LOAD-BEARING, an ablation shows
          dropping it makes the fact set feasible again at the aligned point
          P = (0,1/4,0,1/4,0,1/4,1/8,1/8).  Do not omit it.
 * OUTER IDENTITY, one per group pair 0 <= g < h <= 2, all FOUR matrix entries
   verified to lie in the Walsh row spaces:
     sum_c conj((C_{2g+c})_a)(D_{2h+1-c})_b + sum_c conj((C_{2h+c})_a)(D_{2g+1-c})_b = 0.
   Masks: pair (0,1) uses 010000 for the (a,a) entries and 110000 for (a,b);
   pair (0,2) uses 001000/101000; pair (1,2) uses 000001/100001.
 * ANCHOR SCALARS, one per (block i <= 5, anchor j in {6,7}), twelve in all:
     C_j^dagger D_i + C_i^dagger D_j = 0.
   Masks from \`o26data.SCA\`; each mask carries TWO of the twelve.
 * GROUPED DIAGONAL CONDITIONS giving the matrix moment identity
     C_g C_g^dagger + D_g D_g^dagger = rho/2,  rho = sum_g C_g C_g^dagger,
   verified per group and per matrix entry; the certificate coefficients come
   from \`o26.solve(a, b, g)\` which returns a list of (mask, dressing, rational).

PATTERN TO COPY.  ${REPO}/SixQubit/Orbit29.lean (1385 lines) and
${REPO}/SixQubit/Orbit31.lean (1777 lines) are finished transcription layers for
sibling orbits.  Read one of them first; it shows the exact idiom for: \`bs\`,
the \`y*\`/\`z*\` position defs, \`S0_eq_fiber\`/\`S1_eq_fiber\` by \`decide\`, the
\`MomentSystem\` structure, moment lemmas stated as \`<expr> = 0\`, \`offSum\`,
\`diagBot\`, \`diagTop\`, incidence/flip/sign lemmas by \`decide\`, Walsh expansion
lemmas, and the headline \`no_go_of_moments\` taking the MomentSystem plus
\`offSum ... = 0\` / \`diagBot ... = diagTop ...\` hypotheses and concluding \`False\`.
Generate the file with a PYTHON GENERATOR, as those were; do not hand-write 1500
lines.

Idioms that work here: \`linear_combination\` -- a hypothesis \`h : X = Y\`
contributes \`coeff * (X - Y)\`, and getting that sign backwards is the most
common failure; \`congrArg star h\` then
\`simp only [star_add, star_mul', star_star, star_zero] at h\` to conjugate;
\`rcases mul_eq_zero.mp h with h | h\` to split a product; to move a real moment
fact into ℂ use \`have hc := congrArg (fun x : Real => (x : ℂ)) hreal;
push_cast at hc; simp only [sq]; push_cast; linear_combination hc\`;
\`set_option maxHeartbeats 2000000 in\` before a heavy theorem.
`

phase('Survey')

const SURVEY_SCHEMA = {
  type: 'object',
  properties: {
    interfaces: { type: 'string', description: 'verbatim statements of every Block26 lemma the assembly will call, with its exact argument order' },
    certificates: { type: 'string', description: 'the mask/dressing/coefficient certificate for every relation to be transcribed' },
    index_map: { type: 'string', description: 'block index -> the two six-bit strings, bottom and top, and their positions in S0/S1' },
    gaps: { type: 'string' },
  },
  required: ['interfaces', 'certificates', 'index_map', 'gaps'],
}

const survey = await agent(`${SETUP}

YOUR TASK. Pin down everything the generator will need, by READING files and
RUNNING Python -- not by guessing.

1. Read ${REPO}/SixQubit/Block26.lean and copy out the verbatim statement of
   every one of its 19 theorems, with exact argument order.  Say which ones the
   final assembly calls and in what order.
2. Read ${REPO}/SixQubit/Orbit29.lean and extract the exact skeleton of a
   finished transcription layer: the order of sections, the shape of each kind
   of lemma, and how \`no_go_of_moments\` is stated and proved.
3. In Python, compute and report:
   * S0 and S1 for orbit 26, the eight bottom blocks and their matching top
     blocks (matched by COMPLEMENT of the tail, not by sorted order);
   * for each of the twelve outer-identity entries: the mask, the incidence list,
     and the dressing coefficients that realise it;
   * for each of the twelve anchor scalars: the mask and dressing coefficients;
   * for the matrix moment identity: \`o26.solve(a,b,g)\` for every group g and
     entry (a,b), i.e. the certificate over the diagonal conditions;
   * for every moment fact listed in the brief, the \`reduce_mod_linear\`
     coefficients proving it (confirm remainder 0 for each, and SAY SO
     explicitly for (T) and (T2)).
4. Report anything needed that is not available.

Be exact; the next agent writes code against this.`,
  { label: 'survey', phase: 'Survey', schema: SURVEY_SCHEMA, effort: 'high' })

phase('Transcribe')

const GEN_SCHEMA = {
  type: 'object',
  properties: {
    compiled: { type: 'boolean' },
    generator_path: { type: 'string' },
    file_path: { type: 'string' },
    lines: { type: 'number' },
    theorems: { type: 'number' },
    compile_output: { type: 'string' },
    covered: { type: 'string', description: 'which of the required relations are transcribed' },
    missing: { type: 'string' },
  },
  required: ['compiled', 'generator_path', 'file_path', 'lines', 'theorems', 'compile_output', 'covered', 'missing'],
}

const trans = await agent(`${SETUP}

Survey:
${JSON.stringify(survey, null, 2)}

YOUR TASK. Write a Python generator producing the orbit 26 transcription layer,
and make the output compile.

Write the generator to ${SCRATCH}/gen26f.py and its output to
${SCRATCH}/Orbit26.lean, namespace \`SixQubit.Orbit26\`, importing
\`Mathlib\`, \`SS.FullKL\`, \`SixQubit.Common\`, \`SixQubit.Block26\`.
Do NOT modify anything under ${REPO}/SixQubit.

Cover, in this order, compiling after each block:
  1. positions, \`S0\`/\`S1\`, \`S0_eq_fiber\`/\`S1_eq_fiber\` by \`decide\`;
  2. the \`MomentSystem\` structure and EVERY moment fact from the brief,
     including (T) and (T2);
  3. \`offSum\`, \`diagBot\`, \`diagTop\`, and the incidence / flip / sign lemmas by
     \`decide\` for every mask used;
  4. the Walsh expansion lemmas;
  5. the twelve outer-identity entries;
  6. the twelve anchor scalars;
  7. the matrix moment identity, per group and per entry.

Compile with \`lake env lean\` after each stage and fix as you go -- a 1500-line
file that fails at the end is worthless.  Report honestly what is covered and
what is missing.`,
  { label: 'transcribe', phase: 'Transcribe', schema: GEN_SCHEMA, effort: 'max' })

phase('Assemble')

const ASM_SCHEMA = {
  type: 'object',
  properties: {
    compiled: { type: 'boolean' },
    complete: { type: 'boolean', description: 'true only if a headline theorem concluding False from KL hypotheses alone compiles' },
    file_path: { type: 'string' },
    source: { type: 'string', description: 'ONLY the headline theorem statement and the proof skeleton, at most 150 lines. NEVER the whole file.' },
    sha256: { type: 'string' },
    compile_output: { type: 'string' },
    axioms: { type: 'string' },
    unfinished: { type: 'string' },
  },
  required: ['compiled', 'complete', 'file_path', 'source', 'sha256', 'compile_output', 'axioms', 'unfinished'],
}

const asm = await agent(`${SETUP}

OUTPUT BUDGET -- READ THIS FIRST.  A previous attempt at this exact task FAILED by
exceeding the 64000-token output cap: it tried to echo the whole file back.  Do
NOT do that.  Write your work to files on disk and report PATHS plus a SHA-256.
In the source field put ONLY the headline theorem statement and the proof
skeleton, at most 150 lines.  Never paste the transcription layer, never paste
the \`by decide\` lemmas, never paste a generator.  Keep every field short.

Survey: ${JSON.stringify(survey, null, 2)}
Transcription: ${JSON.stringify(trans, null, 2)}

YOUR TASK. Wire the transcription to \`SixQubit.Block26\` and conclude \`False\`.

Append to the transcription file (in the scratchpad copy).  Build the headline

    theorem no_go_of_moments (c d : SS.BitString 6 -> ℂ)
        (hm : MomentSystem <the 32 normSq's>)
        (<the offSum = 0 and diagBot = diagTop hypotheses>) : False

The branch structure, all already proved in Block26:
  * per anchor, the outer identity contracted with that anchor gives three
    J-orthogonality relations; \`axis_lemma\` puts the three rows on one axis --
    but the axis is PER ANCHOR, so there are four combinations;
  * MIXED axes: killed by \`cross_anchor\`/\`mixed_core\` (contract with D_7 on the
    a index and conj(C_6) on the b index);
  * ALIGNED axes: killed by \`branch4b\` / \`branch4_aligned\`, which need the
    moment and positivity facts, ESPECIALLY (T2);
  * the branches where some row is zero: \`branch1\`, \`branch1_full\`,
    \`branch2_step6\`, \`branch3_step\`, \`branch3_aligned\`.

PARTIAL CREDIT IS FINE.  If a branch resists, keep what compiles and say exactly
what is missing.  Never \`sorry\`, never \`native_decide\`, never claim something
compiles that you have not run.  Finish with \`#print axioms\` on every lemma you
added.`,
  { label: 'assemble', phase: 'Assemble', schema: ASM_SCHEMA, effort: 'max' })

phase('Audit')

const audit = await agent(`${SETUP}

Survey: ${JSON.stringify(survey, null, 2)}
Transcription: ${JSON.stringify(trans, null, 2)}
Assembly: ${JSON.stringify(asm, null, 2)}

YOUR TASK. Audit before installation.  You are the last check; be hostile.

1. RECOMPILE the produced file yourself from scratch and report the exact
   output.  Do not trust the previous agents.
2. If a headline \`False\` theorem exists, list EVERY hypothesis and classify each
   as (i) a genuine Knill-Laflamme condition, (ii) the MomentSystem, or
   (iii) something else.  Any (iii) is a smuggled assumption and must be called
   out -- that is how a proof becomes a shell.
3. Confirm the moment lemmas really are derived from \`MomentSystem\` and not
   assumed, and that (T2) is present and used.
4. \`#print axioms\` on the headline; check for \`sorry\`, \`native_decide\`, warnings.
5. State plainly: is orbit 26 certified, or what exactly remains?

OUTPUT BUDGET.  Report PATHS and a SHA-256, not file contents.  In the source
field put ONLY the headline theorem statement and the hypothesis classification,
at most 150 lines.  Never echo the transcription layer or the decide-lemmas --
an earlier agent on this task blew the 64000-token cap doing exactly that.

Report the verbatim source you validated, and the exact commands you ran.`,
  { label: 'audit', phase: 'Audit', schema: ASM_SCHEMA, effort: 'high' })

return { audit, asm, trans, survey }
