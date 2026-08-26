export const meta = {
  name: 'orbit31-finish',
  description: 'Write the five-branch assembly that completes the orbit 31 certification',
  phases: [
    { title: 'Survey', detail: 'read the installed files and pin the exact interfaces' },
    { title: 'Assemble', detail: 'write and compile the branch assembly' },
    { title: 'Verify', detail: 'independent audit of the finished proof' },
  ],
}

const REPO = String.raw`D:\UTD\Project_purdue\Lean_certification`
const SCRATCH = String.raw`C:\Users\richa\AppData\Local\Temp\claude\D--UTD-Project-purdue\e2435927-3651-49b0-acfb-31f3430ee257\scratchpad`

const SETUP = `
PROJECT. Lean 4 at ${REPO}.  Build: \`lake build\`.  Single file:
\`lake env lean <abs path>\` run from ${REPO}.  \`native_decide\` is FORBIDDEN:
every proof must pass the kernel with axioms exactly
[propext, Classical.choice, Quot.sound].  The project must stay at ZERO errors
and ZERO warnings (prefix genuinely unused hypotheses with \`_\`).
Scratch dir for experiments: ${SCRATCH}.  On Windows use the Bash tool with
forward slashes and the Write tool for files (heredocs corrupt backslashes).

GOAL.  Certify moment orbit 31 by writing the final branch assembly.  Everything
else is already installed and kernel-checked; ONLY the assembly is missing.

WHAT IS ALREADY THERE (read these files first, do not guess their contents):

  ${REPO}/SixQubit/Orbit31.lean   1777 lines, 896 theorems.
    Fibers S0, S1 of size 16 with \`S0_eq_fiber\`/\`S1_eq_fiber\` by \`decide\`;
    positions y0..y15 (bottom) and z0..z15 (top); sixteen complement pairings
    \`hat0\`..\`hat15\`; a \`MomentSystem\` structure over the 32 probabilities;
    23 derived moment facts \`eq0\`..\`eq15\` (p_1 at the complement equals p_0),
    \`row1\`..\`row3\` (each B row totals 1/4) and \`col0\`..\`col3\`
    (alpha_e = B-column total minus 1/8), each stated as \`<expr> = 0\`;
    \`offSum\`, \`diagBot\`, \`diagTop\`; incidence/flip/sign lemmas by \`decide\`;
    Walsh expansion lemmas \`ex*_w*\`, \`dbot*_w*\`, \`dtop*_w*\`;
    family one \`fam1_1\`, \`fam1_2\`, \`fam1_3\`; family two \`fam2_0\`..\`fam2_17\`.

  ${REPO}/SixQubit/Table31.lean   490 lines, 24 lemmas, bit-string free:
    sq, kernel_identity, all_distinct, partition31, gram_eq, lone_column,
    pair_class, pair_gap, tight_pair, det_perm_zero, perm_triple, perm_support,
    conj4, kernel_norm, kernel_zero, row_key, key_of_raw, M_eq_of_raw,
    hH3_of_raw, key, M_eq, phase_transfer, T_eq_zero_of_ae, T_eq_zero_of_af.

THE TABLE.  Orbit 31 has a = (1,1,1,2,2,2) mod 4; both fibers are stabilised by
the Klein group on the last three qubits and split into four cosets of four.  The
sixteen positions form a 4x4 table with rows A, B_1, B_2, B_3 and columns
e_0..e_3.  Write a_e for the bottom amplitude at A_e and b_{i,e} at B_{i,e}.
CAREFUL: the paper's B_{i,e} = (u_i, e-bar) reverses the column order relative to
naive sorted indexing.  Recover the exact index map from Orbit31.lean's comments
(each \`def y<k>\` carries the position name) rather than assuming.

KEY OBJECTS.
  v_e := star (d at the complement of A_e)        -- the kernel vector entry
  u_{i,e} := star (d at the complement of B_{i,e})
  M_{ef} := sum_{i=1..3} b_{i,e} * star (b_{i,f})  -- Gram of the B columns
  alpha_e := normSq (a_e),  beta_{i,e} := normSq (b_{i,e})

THE ARGUMENT (all five branches verified on paper and numerically; the algebra
lemmas for each are already in Table31.lean).

  Family one, after \`conj4\`, says sum_e v_e * b_{i,e} = 0 for i = 1,2,3, i.e.
  the four B columns are linearly dependent with coefficients v.  Pairing against
  each column (\`gram_eq\`) gives FOUR scalar equations

      sum_e v_e * M_{ef} = 0,   f = 0,1,2,3.

  Family three (via \`M_eq_of_raw\`) gives M_{ef} = star (v_e) * v_f whenever
  columns e,f have DIFFERENT phases, the division-free test for which is
      v_e * star (v_f) - a_e * star (a_f) != 0.
  Substituting, equation f reads

      v_f * (alpha_f + 1/8 + 1/4 - s_{c(f)}) + sum_{e in c(f), e != f} v_e M_{ef} = 0,

  where s_c is the total alpha of f's phase class.  A column ALONE in its class
  has s_c = alpha_f, the bracket is 3/8, and \`lone_column\` gives v_f = 0.

  Branches by the partition of the four columns into phase classes:
    (1,1,1,1)  every v_f = 0, so sum alpha = 0 against 1/4.
    (2,1,1)    v of the two lone columns vanish, so the pair's class total is
               1/4; its 2x2 system is singular (\`pair_class\`), so Cauchy-Schwarz
               is tight; \`det_perm_zero\` plus family two then put both columns on
               one row (\`tight_pair\`), whose budget 1/4 they exceed.
    (2,2)      same 2x2 singularity plus \`pair_gap\`:
               (3/8-a0)(3/8-a1) - (a0+1/8)(a1+1/8) = 1/8 - s/2 >= 0; strict
               inequality contradicts singularity, equality reduces to the tight
               case above.
    (3,1)      v of the lone column vanishes so its alpha is 0; then either two
               rows are trapped in that column (its total exceeds alpha+1/8), or
               the three same-phase columns are disjointly supported and each
               equation reads v_f (alpha_f + 1/8) = 0, giving sum alpha = 0.
    (4)        no family-three constraint; use family two in full via
               \`perm_triple\` and \`perm_support\`: either some row has three or more
               nonzero entries, and then the columns it carries alone force
               sum alpha = -1/8, or every row has at most two and all three rows
               share one support of size <= 2, leaving an empty column against
               sum_i beta_{i,e} = alpha_e + 1/8 >= 1/8.

Useful facts: sum alpha = 1/4; each B row totals 1/4; every column satisfies
sum_i beta_{i,e} = alpha_e + 1/8 >= 1/8, so NO B column is empty.
`

phase('Survey')

const SURVEY_SCHEMA = {
  type: 'object',
  properties: {
    index_map: { type: 'string', description: 'exact map from table position (row, column) to the y<k>/z<k> names' },
    interfaces: { type: 'string', description: 'exact statements of fam1_*, fam2_*, the moment facts, and the Table31 lemmas that the assembly will call' },
    gaps: { type: 'string', description: 'anything the assembly needs that is NOT already present' },
  },
  required: ['index_map', 'interfaces', 'gaps'],
}

const survey = await agent(`${SETUP}

YOUR TASK. Read the two installed files and report their EXACT interfaces so the
assembly can be written without guessing.

1. Recover the index map: for each of the sixteen bottom positions y0..y15, which
   table cell (row in {A,B1,B2,B3}, column in 0..3) is it?  Use the comments on
   the \`def y<k>\` lines.  Do the same for the top positions z0..z15 and record
   which z is the complement of which y (the \`hat<k>\` lemmas).
2. Write out the exact statements of \`fam1_1\`, \`fam1_2\`, \`fam1_3\`, of a
   representative \`fam2_*\`, of \`eq0\`, \`row1\`, \`col0\`, and of every Table31
   lemma the assembly will call.  Copy them verbatim from the files.
3. Say precisely which family-three inputs the assembly needs (the raw
   \`hFam\`, \`hCol*\` and \`hK*\` hypotheses of \`M_eq_of_raw\`) and whether
   Orbit31.lean already provides them or whether new expansion lemmas must be
   written.  This is the most likely gap -- check carefully.

Be exact.  The next agent will write code against this report.`,
  { label: 'survey', phase: 'Survey', schema: SURVEY_SCHEMA, effort: 'high' })

phase('Assemble')

const ASM_SCHEMA = {
  type: 'object',
  properties: {
    compiled: { type: 'boolean' },
    complete: { type: 'boolean', description: 'true only if a headline theorem concluding False from the KL hypotheses compiles' },
    file_path: { type: 'string' },
    source: { type: 'string', description: 'the full Lean source to append, verbatim' },
    compile_output: { type: 'string' },
    axioms: { type: 'string' },
    unfinished: { type: 'string', description: 'exactly which branches or steps did not compile, if any' },
  },
  required: ['compiled', 'complete', 'file_path', 'source', 'compile_output', 'axioms', 'unfinished'],
}

const asm = await agent(`${SETUP}

Interface survey:
${JSON.stringify(survey, null, 2)}

YOUR TASK. Write the branch assembly and make it compile.

Work in a COPY: copy ${REPO}/SixQubit/Orbit31.lean to
${SCRATCH}/Orbit31Work.lean and append there.  Do NOT modify anything under
${REPO}/SixQubit -- the caller will install your output.

Build up in small compiling steps, checking after each:
  1. any missing family-three expansion lemmas the survey identified;
  2. the bridge \`have\`s: v_e, u_ie, the column relations, the kernel norms;
  3. one branch at a time, each as its own lemma taking the phase hypotheses
     explicitly;
  4. the headline \`theorem no_go_of_moments\` that takes the MomentSystem and the
     offSum/diagBot/diagTop hypotheses and concludes \`False\`, doing the
     \`by_cases\` over the six phase tests
     \`v_e * star (v_f) - a_e * star (a_f) = 0\` and dispatching to the branches.

Idioms that work in this project: \`linear_combination\` for polynomial
identities -- a hypothesis \`h : X = Y\` contributes \`coeff * (X - Y)\`, and
getting that sign backwards is the most common failure; \`congrArg star h\`
followed by \`simp only [star_add, star_mul', star_star, star_zero] at h\` to
conjugate; \`rcases mul_eq_zero.mp h with h | h\` to split; \`simp only [sq]\` then
\`push_cast\` then \`linear_combination hc\` to move a real moment fact into ℂ,
where \`hc := congrArg (fun x : Real => (x : ℂ)) hreal\`; \`nlinarith\` with
\`Complex.normSq_nonneg\` hints for real positivity; \`set_option maxHeartbeats
2000000 in\` before a heavy theorem.

PARTIAL CREDIT IS FINE AND EXPECTED.  If a branch resists, leave it out, keep
everything that compiles, and say exactly what is missing.  NEVER use \`sorry\`,
never use \`native_decide\`, and never report something as compiling that you have
not actually run.  Finish by checking \`#print axioms\` on every lemma you added.`,
  { label: 'assemble', phase: 'Assemble', schema: ASM_SCHEMA, effort: 'max' })

phase('Verify')

const audit = await agent(`${SETUP}

Survey: ${JSON.stringify(survey, null, 2)}
Assembly: ${JSON.stringify(asm, null, 2)}

YOUR TASK. Independently audit the assembly before it is installed.  You are the
last check; be hostile.

1. Take the reported source, splice it into a fresh copy of
   ${REPO}/SixQubit/Orbit31.lean in ${SCRATCH}, and COMPILE IT YOURSELF.  Report
   the exact output.  Do not take the previous agent's word for it.
2. If a headline \`False\` theorem exists, check its hypotheses are HONEST: they
   must be Knill-Laflamme conditions (offSum = 0, diagBot = diagTop) and the
   MomentSystem, NOT smuggled-in algebraic facts that should have been derived.
   List every hypothesis and classify it.
3. Check \`#print axioms\` on the headline theorem.
4. Check there is no \`sorry\`, no \`native_decide\`, and no warnings.
5. State plainly whether orbit 31 is now certified, or exactly what is still
   missing.

Report the verbatim compiling source you validated, so the caller can install
exactly what you checked.`,
  { label: 'audit', phase: 'Verify', schema: ASM_SCHEMA, effort: 'high' })

return { audit, asm, survey }
