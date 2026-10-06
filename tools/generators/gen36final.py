"""Generate `SixQubit/Orbit36Final.lean`.

The chapter "Rigidity of the order-five orbit 36" of
`documents/20260821/supplementary.tex` (lines 320-1114) ends with two statements:

  * Theorem "Orbit-36 rigidity" (line 981) -- full twelve-term support, the six
    probabilities 1/10 and six probabilities 1/15, and equivalence to the
    canonical pair;
  * the boxed unique enumerator, Eq. (eq:o36uniqueA) at line 1091,

        (A_0, ..., A_6) = (1, 0, 21/25, 0, 291/25, 384/25, 79/25).

`SixQubit.Orbit36Class.orbit36_theorem` already carries the first.  The second
was, until now, conditional: `SixQubit.Orbit36Enum.unique_enumerator` proves
A_0..A_3 outright but takes the quantum MacWilliams normal form for A_4, A_5,
A_6 as three extra hypotheses `hmw4`, `hmw5`, `hmw6`.

Two independent modules have since removed that assumption:

  * `SixQubit.Orbit36Enum4.enumerator_value` -- computes A_4, A_5, A_6 directly
    from the forced magnitudes, the edge three-colouring and the antiunitary
    normal form, per Pauli mask;
  * `SixQubit.Orbit36MacWilliams.orbit36_enumerator` -- proves the subset form
    of the quantum MacWilliams identity for a general ((n, K)) code, specializes
    it to ((6, 2, 3)), and discharges `hmw4`, `hmw5`, `hmw6`.

Both carry exactly the admissible hypothesis block and nothing else.  This
module assembles them:

  * `orbit36_enumerator` and `orbit36_enumerator_macwilliams` -- the same
    unconditional enumerator, proved along each of the two routes;
  * `macwilliams_normal_form` -- the normal form as a CONSEQUENCE, which is the
    direct route confirming the MacWilliams route;
  * `enumerator_sum` -- the invariant sum_j A_j = 32;
  * `orbit36_rigidity` -- the chapter's theorem in one statement: magnitudes,
    full support, equivalence to the canonical pair, distance three, and the
    unique enumerator.

The hypothesis block and the magnitude/support half of the conclusion are read
out of `SixQubit/Orbit36Class.lean` BY CONTENT, so this file cannot drift from
the theorem it extends.

Run:    python tools/generators/gen36final.py
Check:  python tools/generators/gen36final.py --check
"""

import io
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.abspath(os.path.join(HERE, "..", ".."))
SRC = os.path.join(REPO, "SixQubit", "Orbit36Class.lean")
OUT = os.path.join(REPO, "SixQubit", "Orbit36Final.lean")

ARROW = "→"      # ->
WEDGE = "∧"      # /\
NOTIN = "∉"      # not-in
FORALL = "∀"


# ---------------------------------------------------------------------------
# 1.  Read the hypothesis block and the conclusion of `orbit36_theorem`.
# ---------------------------------------------------------------------------

def extract():
    src = io.open(SRC, encoding="utf-8").read()
    anchor = "theorem orbit36_theorem (c d : SS.BitString 6 %s %s)\n" % (
        ARROW, "ℂ")
    i = src.index(anchor) + len(anchor)
    j = src.index("\n    : (", i) + 1
    hyps = src[i:j]
    tail = ("%s CodeEquiv.Equivalent ![c, d] "
            "![Orbit36Code.c36, Orbit36Code.d36] :=\n" % WEDGE)
    k = src.index(tail, j) + len(tail)
    concl = src[j:k]
    body = concl.rstrip()
    assert body.endswith(":="), body[-40:]
    body = body[:-2].rstrip()

    # sanity: the block is exactly the admissible shapes and nothing else
    assert ("(hc : %s s, s %s Orbit36.S0 %s c s = 0)" % (FORALL, NOTIN, ARROW)
            ) in hyps
    assert ("(hd : %s s, s %s Orbit36.S1 %s c s = 0)" % (FORALL, NOTIN, ARROW)
            ).replace("c s", "d s") in hyps
    assert "(hm : MomentSystem" in hyps
    rows = re.findall(r"\(ho(\d+) : ", hyps)
    assert [int(r) for r in rows] == list(range(22)), rows
    offs = len(re.findall(r"offSum ", hyps))
    assert offs == 22, offs
    return hyps, body


HYPS, MAGSUPP = extract()
ROWS = " ".join("ho%d" % i for i in range(22))
ALL = "c d hc hd hm " + ROWS

ENUM = ("AEnum c d 0 = 1\n"
        "      %s AEnum c d 1 = 0\n"
        "      %s AEnum c d 2 = 21/25\n"
        "      %s AEnum c d 3 = 0\n"
        "      %s AEnum c d 4 = 291/25\n"
        "      %s AEnum c d 5 = 384/25\n"
        "      %s AEnum c d 6 = 79/25" % ((WEDGE,) * 6))

ENUM_IN = ENUM.replace("\n      ", "\n          ")


# ---------------------------------------------------------------------------
# 2.  Emit.
# ---------------------------------------------------------------------------

out = io.StringIO()
w = out.write

w("""import Mathlib

import SS.FullKL
import SS.HilbertKL
import SixQubit.Orbit36
import SixQubit.Orbit36Code
import SixQubit.Orbit36Phase
import SixQubit.Orbit36Enum
import SixQubit.Orbit36Enum4
import SixQubit.MacWilliams
import SixQubit.CodeEquiv
import SixQubit.Orbit36Class

/-!
# Orbit 36: the rigidity theorem and the unique weight enumerator

This module is the join of the orbit-36 chapter.  Nothing new is proved about
solutions here; every ingredient is imported.  What it does is state the
chapter's two headline results with the hypothesis block reduced to the four
admissible shapes and NOTHING else:

  * the support conditions `hc`, `hd`,
  * one `MomentSystem` on the twenty-four probabilities,
  * the twenty-two Knill--Laflamme rows `offSum ... = 0`.

## The gap that is now closed

`SixQubit.Orbit36Enum.unique_enumerator` proves `A_0, ..., A_3` outright but
takes the quantum MacWilliams normal form for the top three coefficients as
three extra hypotheses,

    hmw4 : A4 = 15 - 4 * AEnum c d 2 - 3 * AEnum c d 3
    hmw5 : A5 = 12 + 3 * AEnum c d 1 + 4 * AEnum c d 2 + 3 * AEnum c d 3
    hmw6 : A6 = 4  - 4 * AEnum c d 1 -     AEnum c d 2 -     AEnum c d 3

so its enumerator was conditional.  Two independent modules remove the
assumption, and both are used below:

  * `SixQubit.Orbit36Enum4.enumerator_value` computes `A_4, A_5, A_6` directly.
    For a Pauli `(f, zz)` the projector trace splits over the pairs of the
    bottom fiber differing by `f`; the antiunitary normal form makes the top
    contribution a constant multiple of the conjugate bottom one, so only the
    thirty-seven incident masks matter and each is a closed-form inner sum in
    the forced magnitudes, the edge three-colouring, and the triangle identity.
  * `SixQubit.Orbit36MacWilliams.orbit36_enumerator` proves the subset form of
    the quantum MacWilliams identity for an arbitrary family of states, reads
    off the `((6,2,3))` normal form, and discharges `hmw4`, `hmw5`, `hmw6`.

`orbit36_enumerator` below takes the first route and
`orbit36_enumerator_macwilliams` the second; they have identical statements, so
the chapter's boxed enumerator now has two proofs that share no computation.
`macwilliams_normal_form` turns the relation around: it DERIVES the normal form
from the directly computed coefficients, which is the direct route's independent
confirmation of the MacWilliams route.

## The results

    orbit36_enumerator               (A_0, ..., A_6) = (1, 0, 21/25, 0,
                                       291/25, 384/25, 79/25)
    orbit36_enumerator_macwilliams   the same, along the other route
    macwilliams_normal_form          A_4, A_5, A_6 in terms of A_1, A_2, A_3
    enumerator_sum                   sum_j A_j = 32
    orbit36_rigidity                 the chapter's theorem, in one statement

Everything computational is decided by the Lean kernel.  No `sorry`, no
`native_decide`.

This file is generated by `tools/generators/gen36final.py`.
-/

namespace SixQubit.Orbit36Final

open scoped BigOperators
open SixQubit.Orbit36
open SixQubit.Orbit36Phase (AEnum)

section

""")

# --- 1.  the enumerator, direct route ------------------------------------
w("""/-- **The unique orbit-36 weight enumerator, unconditionally.**  Eq.
`(eq:o36uniqueA)` of the chapter.  Every exact orbit-36 solution of the
weight-at-most-two Knill--Laflamme system has Shor--Laflamme `A`-enumerator

    (A_0, ..., A_6) = (1, 0, 21/25, 0, 291/25, 384/25, 79/25),

equivalently `A(z) = 1 + (21/25) z^2 + (291/25) z^4 + (384/25) z^5 +
(79/25) z^6`.  The hypotheses are the support conditions, one `MomentSystem`,
and the twenty-two Knill--Laflamme rows -- nothing else.  This is
`SixQubit.Orbit36Enum4.enumerator_value`, which computes `A_4, A_5, A_6` mask by
mask; see `orbit36_enumerator_macwilliams` for the independent proof through the
quantum MacWilliams identity. -/
theorem orbit36_enumerator (c d : SS.BitString 6 %s %s)
""" % (ARROW, "ℂ"))
w(HYPS)
w("    : %s :=\n" % ENUM)
w("  SixQubit.Orbit36Enum4.enumerator_value %s\n\n" % ALL)

# --- 2.  the enumerator, MacWilliams route -------------------------------
w("""/-- **The same enumerator, along the other route.**  Identical statement to
`orbit36_enumerator`, proved instead by
`SixQubit.Orbit36MacWilliams.orbit36_enumerator`: the subset form of the quantum
MacWilliams identity supplies `hmw4`, `hmw5`, `hmw6`, and
`SixQubit.Orbit36Enum.unique_enumerator` then closes.  The two proofs share the
coefficients `A_0, ..., A_3` and nothing above them. -/
theorem orbit36_enumerator_macwilliams (c d : SS.BitString 6 %s %s)
""" % (ARROW, "ℂ"))
w(HYPS)
w("    : %s :=\n" % ENUM)
w("  SixQubit.Orbit36MacWilliams.orbit36_enumerator %s\n\n" % ALL)

# --- 3.  the normal form, as a consequence -------------------------------
w("""/-- **The MacWilliams normal form, derived rather than assumed.**  The three
relations that `SixQubit.Orbit36Enum.unique_enumerator` takes as hypotheses
`hmw4`, `hmw5`, `hmw6` are here a consequence of the directly computed
enumerator.  Proved from `orbit36_enumerator`, i.e. WITHOUT the MacWilliams
identity, so it is the direct route's confirmation of the other one. -/
theorem macwilliams_normal_form (c d : SS.BitString 6 %s %s)
""" % (ARROW, "ℂ"))
w(HYPS)
w("""    : AEnum c d 4 = 15 - 4 * AEnum c d 2 - 3 * AEnum c d 3
      %s AEnum c d 5 = 12 + 3 * AEnum c d 1 + 4 * AEnum c d 2 + 3 * AEnum c d 3
      %s AEnum c d 6 = 4 - 4 * AEnum c d 1 - AEnum c d 2 - AEnum c d 3 := by
""" % (WEDGE, WEDGE))
w("  obtain %s :=\n" % "⟨h0, h1, h2, h3, h4, h5, h6⟩")
w("    orbit36_enumerator %s\n" % ALL)
w("""  clear h0
  refine %s
  %s rw [h4, h2, h3]; norm_num
  %s rw [h5, h1, h2, h3]; norm_num
  %s rw [h6, h1, h2, h3]; norm_num

""" % ("⟨?_, ?_, ?_⟩", "·", "·", "·"))

# --- 4.  the sum invariant ------------------------------------------------
w("""/-- **The enumerator invariant.**  For a rank-two projector on six qubits
`sum_P |Tr (E Pi)|^2 = 2^6 * Tr (Pi^2) = 128`, so `sum_j A_j = 32`.  Here it is
a corollary of the exact coefficients, and so an arithmetic check on them:
`1 + 0 + 21/25 + 0 + 291/25 + 384/25 + 79/25 = 32`. -/
theorem enumerator_sum (c d : SS.BitString 6 %s %s)
""" % (ARROW, "ℂ"))
w(HYPS)
w("""    : AEnum c d 0 + AEnum c d 1 + AEnum c d 2 + AEnum c d 3 + AEnum c d 4
        + AEnum c d 5 + AEnum c d 6 = 32 := by
""")
w("  obtain %s :=\n" % "⟨h0, h1, h2, h3, h4, h5, h6⟩")
w("    orbit36_enumerator %s\n" % ALL)
w("  rw [h0, h1, h2, h3, h4, h5, h6]\n  norm_num\n\n")

# --- 5.  the rigidity theorem, in one statement ---------------------------
w("""/-- **Theorem (Orbit-36 rigidity), complete.**  The chapter's theorem
`thm:o36rigidity` together with its boxed enumerator `eq:o36uniqueA`, as a
single statement about an arbitrary exact solution.  Every solution of the
weight-at-most-two Knill--Laflamme system supported on the two orbit-36 fibers

  * has six probabilities `1/10` and six probabilities `1/15` in each logical
    word,
  * has the full twelve-term support in each logical word,
  * is equivalent to the canonical pair `(c36, d36)` under physical-qubit
    permutations, local monomial unitaries, logical basis phases, and a possible
    interchange of the two logical basis vectors,
  * is therefore an exact distance-three code, and
  * has Shor--Laflamme enumerator `(1, 0, 21/25, 0, 291/25, 384/25, 79/25)`.

Hence orbit 36 contains exactly one essential exact code class, and that class
has one weight enumerator.  The hypotheses are only the support conditions, one
`MomentSystem`, and the twenty-two Knill--Laflamme rows.

The five components are `SixQubit.Orbit36.magnitudes_forced`,
`SixQubit.Orbit36.full_support`, `SixQubit.Orbit36Class.orbit36_rigidity`,
`SixQubit.Orbit36Class.solution_hasDistance` and `orbit36_enumerator`. -/
theorem orbit36_rigidity (c d : SS.BitString 6 %s %s)
""" % (ARROW, "ℂ"))
w(HYPS)
w(MAGSUPP)
w("\n      %s SS.HasDistance ![c, d] 3\n" % WEDGE)
w("      %s (%s) := by\n" % (WEDGE, ENUM_IN))
w("  obtain %s :=\n" % "⟨hmag, hsupp, heq⟩")
w("    SixQubit.Orbit36Class.orbit36_theorem %s\n" % ALL)
w("  exact %s\n" % "⟨hmag, hsupp, heq,")
w("    SixQubit.Orbit36Class.solution_hasDistance %s,\n" % ALL)
w("    orbit36_enumerator %s%s\n" % (ALL, "⟩"))

w("""
end

end SixQubit.Orbit36Final
""")

text = out.getvalue()

if "--check" in sys.argv:
    have = io.open(OUT, encoding="utf-8", newline="").read() if os.path.exists(OUT) else None
    print("matches" if have == text else "DIFFERS")
    raise SystemExit(0 if have == text else 1)

with io.open(OUT, "w", encoding="utf-8", newline="\n") as f:
    f.write(text)

print("wrote", OUT, "(%d lines)" % text.count("\n"))
