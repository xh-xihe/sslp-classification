import Mathlib
import SS.HilbertKL
import SixQubit.MacWilliams

/-!
# Relabelling a Pauli's `Z`-part without changing its matrix element

Orbit 21's Farkas certificate rests on two coefficient symmetries: multiplying a
Pauli by the forced stabilizer `G`, and conjugating it by the orbit's diagonal
gate `D`.  Stated on labels these are

    z |-> z + g            (multiplication by G)
    z |-> z + (x and g)    (conjugation by D)

with `g` the `Z`-mask of `G`, and the manuscript derives them from `G P = P` and
`D P D^dagger = P`.  Taken that way they need the conjugation action of a
diagonal Clifford on Paulis, which this development does not have -- there is no
Pauli multiplication anywhere in it.

They do not need it.  Both are instances of one elementary fact about `melTr`:
shifting the `Z`-mask by anything on which `chi` is `1` across the terms that
actually contribute leaves the sum alone.  A term contributes only when `s` and
`s + x` both lie in the support, so that is all the hypothesis has to cover, and
for a concrete orbit it is a finite check.

For the two cases at hand:

* `m = g`.  `chi g s = 1` for every support word, which is exactly the even
  overlap that makes `G` a stabilizer in the first place.

* `m = x and g`.  Here `chi (x and g) s = (-1)^{A_a(s and x)}`, and for a
  contributing `s` both `s` and `s + x` lie in the same fiber, so
  `A_a(x) = 2 A_a(s and x) mod q`.  With `A_a(x) = 0 mod 4` -- the vanishing that
  makes the coefficient nonzero at all -- `A_a(s and x)` is even and the sign is
  `1`.

The `i^{#Y}` prefactors of the two labels differ, but every use is through
`normSq`, which discards them.
-/

namespace SixQubit.Orbit21Sym

open SS.MacWilliams

variable {n K : ℕ}

/-- Shifting the `Z`-mask by `m` does not move the matrix element, provided
`chi m s = 1` on every pair of support words the sum actually pairs.

This is the whole content of both orbit-21 coefficient symmetries.  The
hypothesis is stated over the contributing pairs rather than over the support,
because the `D`-conjugation case is `1` only there. -/
theorem melTr_shift (psi : Fin K → SS.State n ℂ) (L : Fin K → List (SS.BitString n))
    (hv : ∀ a s, s ∉ L a → psi a s = 0)
    (x z m : SS.BitString n)
    (hm : ∀ a, ∀ s ∈ L a, SS.bxor s x ∈ L a → chi m s = 1) :
    melTr psi ⟨x, SS.bxor z m⟩ = melTr psi ⟨x, z⟩ := by
  classical
  unfold melTr mel
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun s _ => ?_))
  by_cases hs : s ∈ L a
  · by_cases ht : SS.bxor s x ∈ L a
    · have : chi (SS.bxor z m) s = chi z s := by
        rw [chi_bxor_left, hm a s hs ht, mul_one]
      simp only [this]
    · have h0 : psi a (SS.bxor s x) = 0 := hv a _ ht
      simp only [h0, star_zero, zero_mul, mul_zero]
  · have h0 : psi a s = 0 := hv a s hs
    simp only [h0, mul_zero]

/-- The same conclusion for the squared modulus, which is the form the
enumerator coefficients use.  The `i^{#Y}` prefactors of the two labels differ,
so the equality of `trProj` itself would be false; `normSq` is what survives. -/
theorem normSq_trProj_shift (psi : Fin K → SS.State n ℂ)
    (L : Fin K → List (SS.BitString n))
    (hv : ∀ a s, s ∉ L a → psi a s = 0)
    (x z m : SS.BitString n)
    (hm : ∀ a, ∀ s ∈ L a, SS.bxor s x ∈ L a → chi m s = 1) :
    Complex.normSq (trProj psi ⟨x, SS.bxor z m⟩)
      = Complex.normSq (trProj psi ⟨x, z⟩) := by
  rw [normSq_trProj, normSq_trProj, melTr_shift psi L hv x z m hm]

end SixQubit.Orbit21Sym
