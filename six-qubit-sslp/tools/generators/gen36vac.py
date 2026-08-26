#!/usr/bin/env python3
"""Generate `SixQubit/Orbit36Vacuity.lean`.

The orbit-36 chapter's headline `SixQubit.Orbit36Final.orbit36_rigidity` is a
conditional statement: it assumes two support conditions, one `MomentSystem` on
the twenty-four probabilities, and twenty-two Knill--Laflamme rows
`offSum ... = 0`.  A theorem whose hypotheses cannot all hold is true and says
nothing, so the chapter is only worth reading once those twenty-three
hypotheses are known to be SATISFIABLE.

This generator emits the module that discharges every one of them for the
canonical pair `(c36, d36)` of `SixQubit.Orbit36Code`, and then APPLIES
`orbit36_rigidity` to that pair.  The proof is pure composition; every
ingredient already exists:

  Orbit36Code.canonical_is_code       SS.HasDistance ![c36, d36] 3
  Orbit36Code.c36_vanishes_off_S0     support (and d36_vanishes_off_S1)
  Orbit36Code.c36_prob_vertex/_edge   the per-state probabilities 1/10, 1/15
  CodeBridge.offSumOn_eq_zero_of_hasDistance  HasDistance -> each offSum row

Nothing is written by hand into the Lean file; run

    python tools/generators/gen36vac.py

from the repository root and then

    lake env lean SixQubit/Orbit36Vacuity.lean

Empty output means clean.  No `sorry`, no `native_decide`.
"""

import os

# ---------------------------------------------------------------------------
# The twenty-two Knill--Laflamme rows of `orbit36_rigidity`, read off
# `SixQubit/Orbit36Final.lean` in order.  Each entry is (mask, dressing) as
# they appear in the hypothesis block ho0 .. ho21.
# ---------------------------------------------------------------------------

ROWS = [
    ("Orbit36.ex1", "Orbit36.w0"),
    ("Orbit36.ex1", "Orbit36.w2"),
    ("Orbit36.ex1", "Orbit36.w3"),
    ("Orbit36.ex1", "Orbit36.w4"),
    ("Orbit36.ex2", "Orbit36.w0"),
    ("Orbit36.ex2", "Orbit36.w1"),
    ("Orbit36.ex2", "Orbit36.w3"),
    ("Orbit36.ex2", "Orbit36.w4"),
    ("Orbit36.ex3", "Orbit36.w0"),
    ("Orbit36.ex3", "Orbit36.w1"),
    ("Orbit36.ex3", "Orbit36.w2"),
    ("Orbit36.ex3", "Orbit36.w4"),
    ("Orbit36.ex4", "Orbit36.w0"),
    ("Orbit36.ex4", "Orbit36.w1"),
    ("Orbit36.ex4", "Orbit36.w2"),
    ("Orbit36.ex4", "Orbit36.w3"),
    ("Orbit36.ex15", "Orbit36.w0"),
    ("Orbit36.ex25", "Orbit36.w0"),
    ("Orbit36.ex35", "Orbit36.w0"),
    ("Orbit36.ex45", "Orbit36.w0"),
    ("Orbit36.ex56", "Orbit36.w0"),
    ("SixQubit.Orbit36Enum.ex16", "Orbit36.w0"),
]

# The twelve bottom points and the twelve top points, with the theorem that
# supplies each probability and the list membership that theorem needs.
BOT = [("Orbit36.y%d" % k,
        "c36_prob_vertex" if k < 6 else "c36_prob_edge",
        "1/10" if k < 6 else "1/15") for k in range(12)]
TOP = [("Orbit36.z%d" % k,
        "d36_prob_vertex" if k < 6 else "d36_prob_edge",
        "1/10" if k < 6 else "1/15") for k in range(12)]

HEADER = r'''import Mathlib

import SS.FullKL
import SS.HilbertKL
import SixQubit.CodeBridge
import SixQubit.Orbit36
import SixQubit.Orbit36Code
import SixQubit.Orbit36Enum
import SixQubit.Orbit36Final

/-!
# Orbit 36: the rigidity theorem is not vacuously true

`SixQubit.Orbit36Final.orbit36_rigidity` concludes, for an arbitrary orbit-36
solution, the twelve forced magnitudes in each logical word, full twelve-term
support, equivalence with the canonical pair, distance three, and the unique
weight enumerator.  Its hypotheses are

  * the two support conditions `hc`, `hd`,
  * one `MomentSystem` on the twenty-four probabilities,
  * the twenty-two Knill--Laflamme rows `offSum ... = 0`.

Read literally, such a theorem says only that a finite system of equations has
no solution outside one class.  A theorem whose hypotheses cannot all hold is
true and says nothing, so before reading it as a rigidity statement one must
know that the twenty-three hypotheses are jointly SATISFIABLE.

The analogue for the fifty-one no-go orbits is `SixQubit.Vacuity`, where the
witness is a point mass and the missing hypothesis is exactly the one being
refuted.  Here the argument is different, and stronger: the witness is the
canonical pair `(c36, d36)` of `SixQubit.Orbit36Code`, a genuine exact
distance-three code, and it satisfies EVERY hypothesis, so
`orbit36_rigidity` may be applied to it outright.

## What is proved

    canonical_moments      the `MomentSystem` on the twenty-four probabilities
                           of `(c36, d36)`
    canonical_rows         all twenty-two rows `offSum c36 d36 ... = 0`
    hypotheses_satisfiable the twenty-three hypotheses, as one conjunction
    rigidity_nonvacuous    `orbit36_rigidity` APPLIED to `(c36, d36)`, hence
                           its full conclusion for the canonical pair

`rigidity_nonvacuous` is a non-vacuity certificate and a fixed-point statement
at once: the canonical pair lies in its own equivalence class, and the
enumerator `(1, 0, 21/25, 0, 291/25, 384/25, 79/25)` is realized.

## How each hypothesis is discharged

Every ingredient is imported; this module is composition, not new mathematics.

  * support: `Orbit36Code.c36_vanishes_off_S0` and `d36_vanishes_off_S1`, after
    `S0_eq` / `S1_eq` identify the two modules' fibers (one `decide` each);
  * `MomentSystem`: the twenty-four probabilities are the kernel-checked
    constants `1/10` (vertices) and `1/15` (edges) of
    `Orbit36Code.c36_prob_vertex`, `c36_prob_edge`, `d36_prob_vertex`,
    `d36_prob_edge`, and on those constants each of the twenty-three moment
    rows is an arithmetic identity (`moment_uniform`);
  * the twenty-two rows: `SixQubit.offSumOn_eq_zero_of_hasDistance` turns
    `Orbit36Code.canonical_is_code : SS.HasDistance ![c36, d36] 3` into the
    vanishing of every off-diagonal support sum whose Pauli has weight at most
    two, and `Orbit36.offSum` is `SixQubit.offSumOn` at the two fibers by
    definition.  Each weight obligation is one `decide`.

This file is generated by `tools/generators/gen36vac.py`.  No `sorry`, no
`native_decide`.
-/

namespace SixQubit.Orbit36Vacuity

open scoped BigOperators
open SixQubit.Orbit36Code (c36 d36)
open SixQubit.Orbit36Phase (AEnum)

noncomputable section

/-! ## The two modules describe the same pair of fibers

`SixQubit.Orbit36` lists its fibers as `{y0, ..., y11}` and `{z0, ..., z11}`;
`SixQubit.Orbit36Code` builds them as `L0.toFinset` and `L1.toFinset` from the
vertex/edge lists.  The two finsets are equal, decided over all sixty-four
strings. -/

/-- The bottom fibers of the two modules coincide. -/
theorem S0_eq : Orbit36Code.S0 = Orbit36.S0 := by decide

/-- The top fibers of the two modules coincide. -/
theorem S1_eq : Orbit36Code.S1 = Orbit36.S1 := by decide

/-! ## Hypothesis (hc), (hd): the support conditions -/

/-- The canonical bottom word vanishes off the orbit-36 bottom fiber.  This is
hypothesis `hc` of `orbit36_rigidity`. -/
theorem c36_supp : ∀ s, s ∉ Orbit36.S0 → c36 s = 0 := by
  intro s hs
  exact Orbit36Code.c36_vanishes_off_S0 s (by rw [S0_eq]; exact hs)

/-- The canonical top word vanishes off the orbit-36 top fiber.  This is
hypothesis `hd` of `orbit36_rigidity`. -/
theorem d36_supp : ∀ s, s ∉ Orbit36.S1 → d36 s = 0 := by
  intro s hs
  exact Orbit36Code.d36_vanishes_off_S1 s (by rw [S1_eq]; exact hs)

/-! ## Hypothesis (hm): the twenty-four probabilities

`Orbit36Code` records each probability as `star (c36 s) * c36 s`, a complex
equation; the `MomentSystem` wants `Complex.normSq (c36 s)`, a real one.
`SixQubit.star_mul_self` is the bridge. -/

/-- Read a real probability off the complex self-product. -/
theorem normSq_of_star_mul {z : ℂ} {r : ℝ} (h : star z * z = (r : ℂ)) :
    Complex.normSq z = r := by
  rw [SixQubit.star_mul_self] at h
  exact_mod_cast h
'''

FOOTER_MOMENT = r'''
/-- **The moment system on the canonical probabilities.**  On the twelve
vertex values `1/10` and the twelve edge values `1/15` every row of
`Orbit36.MomentSystem` -- the two normalizations, the six one-bit and fifteen
two-bit occupation equalities, and the twenty-four nonnegativities -- is an
arithmetic identity. -/
theorem moment_uniform :
    Orbit36.MomentSystem
      (1/10) (1/10) (1/10) (1/10) (1/10) (1/10)
      (1/15) (1/15) (1/15) (1/15) (1/15) (1/15)
      (1/10) (1/10) (1/10) (1/10) (1/10) (1/10)
      (1/15) (1/15) (1/15) (1/15) (1/15) (1/15) := by
  constructor <;> norm_num
'''


def gen_probs():
    out = []
    for k, (pt, thm, val) in enumerate(BOT):
        out.append("""
/-- The probability of the canonical bottom word at `%s`. -/
theorem pq%d : Complex.normSq (c36 %s) = %s :=
  normSq_of_star_mul (by
    rw [Orbit36Code.%s %s (by decide)]
    norm_num)
""" % (pt, k, pt, val, thm, pt))
    for k, (pt, thm, val) in enumerate(TOP):
        out.append("""
/-- The probability of the canonical top word at `%s`. -/
theorem pr%d : Complex.normSq (d36 %s) = %s :=
  normSq_of_star_mul (by
    rw [Orbit36Code.%s %s (by decide)]
    norm_num)
""" % (pt, k, pt, val, thm, pt))
    return "".join(out)


def moment_args(fn, pts):
    """The twenty-four `Complex.normSq ...` arguments, six to a line."""
    terms = ["Complex.normSq (%s %s)" % (fn, p) for p in pts]
    return terms


def gen_canonical_moments():
    bot = moment_args("c36", [p for p, _, _ in BOT])
    top = moment_args("d36", [p for p, _, _ in TOP])
    terms = bot + top
    lines = []
    for i in range(0, 24, 6):
        lines.append("      " + " ".join("(%s)" % t for t in terms[i:i + 6]))
    body = "\n".join(lines)
    rws = ", ".join(["pq%d" % k for k in range(12)] + ["pr%d" % k for k in range(12)])
    return """
/-- **Hypothesis (hm) for the canonical pair.**  The `MomentSystem` of
`orbit36_rigidity`, instantiated at `(c36, d36)`. -/
theorem canonical_moments :
    Orbit36.MomentSystem
%s := by
  rw [%s]
  exact moment_uniform
""" % (body, rws)


def gen_rows():
    out = ["""
/-! ## The twenty-two Knill--Laflamme rows

`Orbit36.offSum` is `SixQubit.offSumOn` at the two orbit-36 fibers, by
definition, so the generic bridge lemma applies verbatim. -/

/-- The orbit-36 off-diagonal sum is the generic one at `(S0, S1)`. -/
theorem offSum_eq_offSumOn (c d : SS.BitString 6 → ℂ) (e z : SS.BitString 6) :
    Orbit36.offSum c d e z = SixQubit.offSumOn Orbit36.S0 Orbit36.S1 c d e z := rfl

/-- **Every weight-at-most-two off-diagonal row of the canonical pair
vanishes.**  This is `SixQubit.offSumOn_eq_zero_of_hasDistance` applied to
`Orbit36Code.canonical_is_code`; the twenty-two rows below are instances. -/
theorem canonical_offSum (e z : SS.BitString 6)
    (hw : (⟨e, z⟩ : SS.PauliString 6).wt ≤ 2) :
    Orbit36.offSum c36 d36 e z = 0 := by
  rw [offSum_eq_offSumOn]
  exact SixQubit.offSumOn_eq_zero_of_hasDistance Orbit36.S0 Orbit36.S1 c36 d36
    c36_supp d36_supp Orbit36Code.canonical_is_code e z hw
"""]
    for k, (e, z) in enumerate(ROWS):
        out.append("""
/-- Row `ho%d` of `orbit36_rigidity`, for the canonical pair. -/
theorem row%d : Orbit36.offSum c36 d36 %s %s = 0 :=
  canonical_offSum %s %s (by decide)
""" % (k, k, e, z, e, z))
    return "".join(out)


def gen_satisfiable():
    rows = "\n".join(
        "      ∧ Orbit36.offSum c36 d36 %s %s = 0" % (e, z) for (e, z) in ROWS)
    bot = moment_args("c36", [p for p, _, _ in BOT])
    top = moment_args("d36", [p for p, _, _ in TOP])
    terms = bot + top
    mlines = []
    for i in range(0, 24, 6):
        mlines.append("            " + " ".join("(%s)" % t for t in terms[i:i + 6]))
    mbody = "\n".join(mlines)
    proof = ", ".join(["c36_supp", "d36_supp", "canonical_moments"]
                      + ["row%d" % k for k in range(22)])
    return """
/-! ## The hypothesis block is satisfiable -/

/-- **The twenty-three hypotheses of `orbit36_rigidity` are jointly
satisfiable.**  The canonical pair `(c36, d36)` satisfies all of them, so the
theorem is not vacuously true.  Stated as one conjunction so that it can be
read against the hypothesis block of `SixQubit.Orbit36Final.orbit36_rigidity`
line by line. -/
theorem hypotheses_satisfiable :
    (∀ s, s ∉ Orbit36.S0 → c36 s = 0)
      ∧ (∀ s, s ∉ Orbit36.S1 → d36 s = 0)
      ∧ Orbit36.MomentSystem
%s
%s :=
  ⟨%s⟩
""" % (mbody, rows, proof)


def gen_final():
    mags = []
    for k in range(12):
        mags.append("Complex.normSq (c36 Orbit36.y%d) = %s"
                    % (k, "1/10" if k < 6 else "1/15"))
    for k in range(12):
        mags.append("Complex.normSq (d36 Orbit36.z%d) = %s"
                    % (k, "1/10" if k < 6 else "1/15"))
    magblock = "\n".join(
        ("    (" if i == 0 else "        ∧ ") + m for i, m in enumerate(mags))
    supp = []
    for k in range(12):
        supp.append("c36 Orbit36.y%d ≠ 0" % k)
    for k in range(12):
        supp.append("d36 Orbit36.z%d ≠ 0" % k)
    suppblock = "\n".join(
        ("      ∧ (" if i == 0 else "        ∧ ") + s for i, s in enumerate(supp))
    enum = [("AEnum c36 d36 0 = 1"), ("AEnum c36 d36 1 = 0"),
            ("AEnum c36 d36 2 = 21/25"), ("AEnum c36 d36 3 = 0"),
            ("AEnum c36 d36 4 = 291/25"), ("AEnum c36 d36 5 = 384/25"),
            ("AEnum c36 d36 6 = 79/25")]
    enumblock = "\n".join(
        ("      ∧ (" if i == 0 else "          ∧ ") + e for i, e in enumerate(enum))
    args = " ".join(["c36", "d36", "c36_supp", "d36_supp", "canonical_moments"]
                    + ["row%d" % k for k in range(22)])
    return """
/-! ## The rigidity theorem, applied -/

/-- **`orbit36_rigidity` is not vacuously true.**  Its twenty-three hypotheses
all hold for the canonical pair `(c36, d36)` of `SixQubit.Orbit36Code`, so the
theorem may be APPLIED to that pair; what follows is its full conclusion, with
`c := c36` and `d := d36`.

Two things follow at once.  First, the orbit-36 chapter is about a nonempty
set of solutions: there really is an exact orbit-36 solution of the
weight-at-most-two Knill--Laflamme system, so `orbit36_rigidity` is a rigidity
statement and not an empty one.  Second, the canonical pair lies in its own
equivalence class and realizes the boxed enumerator
`(1, 0, 21/25, 0, 291/25, 384/25, 79/25)`; in particular the forced magnitudes
`1/10` and `1/15` are attained, and the `CodeEquiv.Equivalent` conclusion is
consistent, being witnessed here by a pair equivalent to itself. -/
theorem rigidity_nonvacuous :
%s)
%s)
      ∧ CodeEquiv.Equivalent ![c36, d36] ![Orbit36Code.c36, Orbit36Code.d36]
      ∧ SS.HasDistance ![c36, d36] 3
%s) :=
  SixQubit.Orbit36Final.orbit36_rigidity %s
""" % (magblock, suppblock, enumblock, args)


def main():
    here = os.path.dirname(os.path.abspath(__file__))
    root = os.path.dirname(os.path.dirname(here))
    target = os.path.join(root, "SixQubit", "Orbit36Vacuity.lean")
    text = (HEADER
            + gen_probs()
            + FOOTER_MOMENT
            + gen_canonical_moments()
            + gen_rows()
            + gen_satisfiable()
            + gen_final()
            + "\nend\n\nend SixQubit.Orbit36Vacuity\n")
    with open(target, "w", encoding="utf-8", newline="\n") as f:
        f.write(text)
    print("wrote %s (%d lines)" % (target, text.count("\n")))


if __name__ == "__main__":
    main()
