export const meta = {
  name: 'sixqubit-nogo-mechanisms',
  description: 'Extract, per orbit, the exact obstruction mechanism and the data a Lean certification needs',
  phases: [{ title: 'Read', detail: 'one agent per no-go section' }],
}

const F = 'D:/UTD/Project_purdue/Lean_certification/six_qubit_sslp_v7.tex'

const COMMON = `
You are reading a mathematics manuscript:
  ${F}
It classifies diagonal transversal gates on six-qubit distance-three quantum codes.
Sections 11 to 17 close 29 "moment orbits" by exact no-go proofs. Your job is to
extract, for EACH orbit in your assigned section, exactly what a formal
(Lean 4) certification would have to check.

Context you need:
 - A moment orbit is given by (q, m, a) with a in Z_q^6. The bottom fiber S0 is
   { x : sum_j a_j x_j = 0 mod q }, the top fiber S_delta uses residue delta.
 - The "moment system" consists of two normalizations plus equalities of the
   first moments E[x_i] and second moments E[x_i x_j] between the two fibers
   (0/1 indicators, per the feature map phi of Section 6).
 - d_LP is the dimension of the exact moment polytope. When d_LP = 0 the
   probabilities are unique; when d_LP > 0 they form a family and positivity of
   particular amplitudes must be argued over the whole family.
 - The already-formalized template (Section 11, orbit 66) is: certify the
   support is the right fiber, solve the 14-equation moment system, show all
   probabilities positive, exhibit an X-mask whose incidence set has exactly two
   edges whose sources differ in some coordinate outside the mask, and close with
   the rank-two Walsh system (A+B=0 and A-B=0 force A=B=0).

For EVERY orbit in your section report, precisely:
 (1) the orbit ID and representative angle vector a;
 (2) the obstruction MECHANISM. Name it exactly: two-edge Walsh / three-edge /
     four-edge / odd cancellation cycle / rank argument / something else. Quote
     the sentence that states it.
 (3) the exact Pauli masks used (which X-mask, which Z coordinates), and the
     incidence sets the document displays;
 (4) which amplitudes must be shown nonzero, and HOW the document argues that
     (unique moment solution? positivity over a parametrized family? give the
     parameter and its interval);
 (5) any determinant or rank certificate the document states, with its value;
 (6) whether the argument is self-contained or defers to an earlier lemma.

RULES
 - Quote line numbers and exact text. Do not paraphrase numbers.
 - If several orbits share one mechanism, say so explicitly and give the shared part once.
 - Do NOT attempt the mathematics yourself; report what the document does.
`

const SCHEMA = {
  type: 'object',
  properties: {
    section: { type: 'string' },
    shared_mechanism: { type: 'string', description: 'mechanism common to several orbits, if any' },
    orbits: {
      type: 'array',
      items: {
        type: 'object',
        properties: {
          id: { type: 'string' },
          angle_vector: { type: 'string' },
          mechanism: { type: 'string' },
          masks: { type: 'string', description: 'X-mask and Z coordinates, plus incidence sets' },
          nonvanishing: { type: 'string', description: 'which amplitudes, and how argued' },
          certificate: { type: 'string', description: 'determinant / rank value stated' },
          line: { type: 'integer' },
        },
        required: ['id', 'mechanism', 'nonvanishing'],
      },
    },
    formalization_notes: { type: 'string', description: '150-300 words: what a Lean certification of this section would need beyond the Section 11 template' },
  },
  required: ['section', 'orbits', 'formalization_notes'],
}

const PARTS = [
  { key: 's12', range: '1129-1535', what: 'Section 12, projective order eight, orbits 64 and 65. Orbit A (64) is a two-edge case; orbit B (65) is called an odd cancellation cycle and has a one-parameter moment family. Report orbit B in full detail: every mask, every ratio, and how the final contradiction is reached.' },
  { key: 's13', range: '1536-2255', what: 'Section 13, projective order seven, orbits 57 to 61 (five orbits).' },
  { key: 's14', range: '2256-3179', what: 'Section 14, projective order six, orbits 53 to 56 (four orbits). This section mentions a four-edge mechanism; describe it exactly.' },
  { key: 's15', range: '3180-5552', what: 'Section 15, projective order four, ten orbits: 25 to 32 and 62 to 63. This is the longest section; identify how it is organised and whether the ten orbits share machinery.' },
  { key: 's17', range: '6348-6913', what: 'Section 17, the seven order-five orbits 33 to 35 and 37 to 40. Note that orbit 36 is NOT a no-go and is handled in Section 16; ignore it.' },
]

phase('Read')

const out = await parallel(PARTS.map(p => () =>
  agent(`${COMMON}

YOUR SECTION: lines ${p.range}.
${p.what}

Read the whole range with the Read tool before answering.`,
    { label: `read:${p.key}`, phase: 'Read', schema: SCHEMA })))

return { sections: out.filter(Boolean) }
