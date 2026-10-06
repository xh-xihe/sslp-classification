export const meta = {
  name: 'verify-orbit38-argument',
  description: 'Adversarially check a restructured no-go argument for six-qubit moment orbit 38',
  phases: [{ title: 'Refute', detail: 'three independent skeptics, distinct lenses' }],
}

const ARGUMENT = `
SETTING. A putative ((6,2,d>=3)) qubit code. Two logical states have amplitudes
c (bottom, supported on fiber S_0) and d (top, on fiber S_1 = complement of S_0).
Orbit 38: a = (1,1,2,2,2,3), q = 5, delta = 1. Bottom fiber (13 strings):
  A_j    = 001001, 000101, 000011, 000000      (j = 1..4)
  B_1j   = 010110, 011010, 011100, 011111
  B_2j   = 100110, 101010, 101100, 101111
  S      = 110001
Top fiber is the bitwise complement of the bottom fiber. Write x-hat for the
complement of x, u_x = conj(c_x), v_yhat = d_yhat, and P(x, yhat) = u_x v_yhat.

A Pauli X^e Z^z of weight at most two (i.e. supp(e) union supp(z) has size <= 2)
contributes the Knill-Laflamme condition
    sum over y in S_1 with y xor e in S_0 of (-1)^{z.y} u_{y xor e} v_y = 0.

ESTABLISHED FACTS (I verified each by exact computation against the moment
system; treat them as given):
 (F1) q_S = |c_S|^2 = 1/5 and the corresponding top probability r_Shat > 0, both
      forced by the linear moment system.
 (F2) Row sums: sum_{j=1}^4 |c_{B_1j}|^2 = sum_{j=1}^4 |c_{B_2j}|^2 = 3/10,
      forced by the moment system.
 (F3) Column sums: |c_{B_1j}|^2 + |c_{B_2j}|^2 >= 1/10 for each j.
 (F4) For each of the eight grid points B_ij there is exactly one weight-two
      flip whose incidence set is exactly the reciprocal pair
      {B_ij <-> S-hat, S <-> B_ij-hat}. (I enumerated all weight<=2 masks and
      confirmed uniqueness.) With the trivial dressing its equation is
          P(B_ij, S-hat) + P(S, B_ij-hat) = 0.
 (F5) For each pair of distinct columns j != k there is a weight-two flip whose
      incidence set is exactly
          {B_1j <-> B_2k-hat, B_2k <-> B_1j-hat, B_1k <-> B_2j-hat, B_2j <-> B_1k-hat},
      giving with the trivial dressing
          P(B_1j,B_2k-hat) + P(B_2k,B_1j-hat) + P(B_1k,B_2j-hat) + P(B_2j,B_1k-hat) = 0.

THE ARGUMENT I WANT REFUTED.

Step 1 (phase-ratio hub). From (F4) applied to B_1j and to B_2k, and using
u_S v_Shat != 0 from (F1):
    (u_{B_2k} v_{B_1j-hat} - u_{B_1j} v_{B_2k-hat}) * (u_S v_Shat)
      = u_{B_2k} v_Shat * (u_S v_{B_1j-hat}) - u_{B_1j} v_Shat * (u_S v_{B_2k-hat})
      = u_{B_2k} v_Shat * (-u_{B_1j} v_Shat) - u_{B_1j} v_Shat * (-u_{B_2k} v_Shat)
      = 0,
hence P(B_2k, B_1j-hat) = P(B_1j, B_2k-hat), and likewise
P(B_2j, B_1k-hat) = P(B_1k, B_2j-hat).

Step 2 (collapse). Substituting into (F5): 2 P(B_1j,B_2k-hat) + 2 P(B_1k,B_2j-hat) = 0,
so for all j != k
    (R_jk)   P(B_1j, B_2k-hat) + P(B_1k, B_2j-hat) = 0.

Step 3 (no b vanishes). Suppose c_{B_1j} = 0 for some j. Then |c_{B_1j}|^2 = 0,
so by (F3) |c_{B_2j}|^2 >= 1/10 > 0, so c_{B_2j} != 0. Also v_{B_2j-hat} != 0
[SEE QUESTION Q1 BELOW]. For every k != j, (R_jk) reads
    P(B_1j, B_2k-hat) + P(B_1k, B_2j-hat) = 0,
and the first term is u_{B_1j} v_{B_2k-hat} = 0 since u_{B_1j} = conj(c_{B_1j}) = 0.
Hence u_{B_1k} v_{B_2j-hat} = 0, and since v_{B_2j-hat} != 0 we get c_{B_1k} = 0
for every k != j. Together with c_{B_1j} = 0 this makes all four c_{B_1k} vanish,
contradicting the row sum 3/10 in (F2). Therefore c_{B_1j} != 0 for every j, and
symmetrically c_{B_2j} != 0 for every j.

Step 4 (odd cycle). Take three distinct columns j, k, l. From (R_jk), (R_kl),
(R_jl) each of the form X + Y = 0:
    (P(B_1j,B_2k-hat) * P(B_1k,B_2l-hat) * P(B_1l,B_2j-hat))
  + (P(B_1k,B_2j-hat) * P(B_1l,B_2k-hat) * P(B_1j,B_2l-hat)) = 0
by the standard three-relation combination, and the two products are the SAME
monomial u_{B_1j} u_{B_1k} u_{B_1l} v_{B_2j-hat} v_{B_2k-hat} v_{B_2l-hat}.
Hence twice that monomial vanishes, so the monomial vanishes, contradicting
Step 3 -- PROVIDED the v factors are also nonzero [SEE QUESTION Q2].

YOUR TASK. Try hard to REFUTE this. Default to "refuted" if you are uncertain.
Check in particular:
 Q1. Step 3 needs v_{B_2j-hat} != 0, i.e. the TOP amplitude at the complement of
     B_2j. I only argued that the BOTTOM amplitude c_{B_2j} is nonzero. Is that
     a real gap? Does anything in (F1)-(F5) give it? If not, the argument is
     broken as written -- say so plainly and say what would be needed.
 Q2. Step 4 needs the top amplitudes v_{B_2j-hat} nonzero for three columns.
     Same question.
 Q3. Verify the exponent bookkeeping in Step 4: are the two triple products
     really the same monomial, and is the number of sign flips really odd?
     Do the algebra explicitly.
 Q4. Step 1: is the displayed chain of equalities actually valid, and does it
     really need only u_S v_Shat != 0?
 Q5. Anything else wrong, circular, or assumed without justification.

Answer concretely with algebra, not impressions.`

const SCHEMA = {
  type: 'object',
  additionalProperties: false,
  required: ['refuted', 'verdict', 'gaps', 'algebraCheck'],
  properties: {
    refuted: { type: 'boolean', description: 'true if the argument as written is broken' },
    verdict: { type: 'string', description: 'One paragraph: is it sound, and if not exactly where it fails.' },
    gaps: { type: 'string', description: 'Every gap found, numbered, each with the specific missing hypothesis or wrong step. Address Q1 and Q2 explicitly.' },
    algebraCheck: { type: 'string', description: 'The explicit Step-4 monomial and sign bookkeeping, worked out, plus the Step-1 chain.' },
  },
}

const LENSES = [
  'the NONVANISHING lens: every place the argument uses "X != 0", ask whether that was actually established or merely assumed, distinguishing carefully between bottom amplitudes c and top amplitudes d',
  'the ALGEBRA lens: recompute every displayed identity symbolically, especially the Step-1 cancellation and the Step-4 triple product and its sign count',
  'the STRUCTURE lens: question whether (F1)-(F5) as stated actually support the steps, whether any step smuggles in a fact about a different fiber, and whether Step 3 is circular',
]

const votes = await parallel(LENSES.map((lens, i) => () =>
  agent(`${ARGUMENT}\n\nApproach this through ${lens}. Be a skeptic: your job is to find the flaw, not to endorse.`,
    { label: `skeptic-${i}`, phase: 'Refute', schema: SCHEMA })))

return { votes: votes.filter(Boolean) }
