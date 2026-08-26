export const meta = {
  name: 'extract-remaining-nogo-arguments',
  description: 'Extract the exact no-go argument for each of the 13 uncertified six-qubit moment orbits',
  phases: [
    { title: 'Extract', detail: 'one agent per orbit, reading its subsection of six_qubit_sslp_v7.tex' },
  ],
}

const FILE = 'D:/UTD/Project_purdue/Lean_certification/six_qubit_sslp_v7.tex'
const ORBITS = [25, 26, 27, 29, 31, 32, 33, 35, 37, 38, 54, 56, 58]

const SCHEMA = {
  type: 'object',
  additionalProperties: false,
  required: ['orbit', 'anchorNonzero', 'flipData', 'contradiction', 'needsCaseSplit', 'quotes'],
  properties: {
    orbit: { type: 'integer' },
    anchorNonzero: {
      type: 'string',
      description: 'Exactly which amplitudes the proof asserts are nonzero, and the stated reason. If the proof instead uses "not all of these vanish" or a positive SUM of probabilities, say so and give the set and the sum value.',
    },
    flipData: {
      type: 'string',
      description: 'Every flip mask (X-part) and dressing (Z-part) used, as bit strings if displayed; the incidence set of each flip as explicit source->target bit strings; and the matrix/determinant if one is displayed.',
    },
    contradiction: {
      type: 'string',
      description: 'The final contradiction: what is forced to vanish and which positivity statement it violates.',
    },
    needsCaseSplit: {
      type: 'string',
      description: 'Does the argument enumerate cases (faces of the moment polytope, support patterns, sign choices)? If yes, how many cases and what indexes them. If no, say NO.',
    },
    quotes: {
      type: 'string',
      description: 'Up to 8 short verbatim LaTeX excerpts (with line numbers) carrying the numeric data: supports, probabilities, incidence lists, determinants.',
    },
  },
}

const results = await pipeline(
  ORBITS,
  (oid) => agent(
    `Read the file ${FILE}. Find the subsection that proves moment orbit ${oid} is impossible ` +
    `(search for a label like \\label{subsec:q4o${oid}} / q5o${oid} / q6o${oid} / q7o${oid} / q8o${oid}, ` +
    `or a subsection heading naming "Orbit ${oid}"). Read that ENTIRE subsection carefully, ` +
    `including every displayed equation.\n\n` +
    `Context: the setup is a putative ((6,2,d>=3)) code whose two logical states are ` +
    `supported on two residue fibers S_0 and S_delta of the map x -> sum_j a_j x_j mod q. ` +
    `Write u_x = conj(c_x) for a bottom amplitude and v_y = d_y for a top amplitude. ` +
    `A Pauli X^e Z^z of weight at most two contributes the equation ` +
    `sum over y with y xor e in S_0 of (-1)^{z.y} u_{y xor e} v_y = 0.\n\n` +
    `I have already mechanized every orbit whose obstruction is (a) a Walsh system on one flip ` +
    `mask with a target edge whose two endpoint probabilities are forced strictly positive by the ` +
    `moment polytope, or (b) an odd cancellation cycle of three two-term relations with the same ` +
    `property. Orbit ${oid} resists BOTH, and I have verified computationally that its moment ` +
    `polytope forces almost no coordinate to be strictly positive.\n\n` +
    `So the question I need answered precisely is: HOW does this proof establish that something ` +
    `is nonzero? Does it (i) use a positivity that is NOT coordinatewise -- e.g. a sum of ` +
    `probabilities over a set being positive, so that at least one member is nonzero; ` +
    `(ii) enumerate cases over which amplitudes vanish; or (iii) use something else entirely ` +
    `(a rank/determinant argument, a permanent, a modulus or phase-ratio argument)?\n\n` +
    `Report literally what the text says. Do NOT reconstruct, guess, or repair the argument. ` +
    `If the text is terse or leaves a step implicit, say exactly that and quote the terse sentence. ` +
    `Give bit strings verbatim as displayed.`,
    { label: `orbit-${oid}`, phase: 'Extract', schema: SCHEMA }
  )
)

return { orbits: ORBITS, results: results.filter(Boolean) }
