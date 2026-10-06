import Mathlib
import SS.HilbertKL
import SixQubit.MacWilliams
import SixQubit.Orbit21Sym

/-!
# Orbit 21: the two coefficient symmetries, decided

`SixQubit/Orbit21Sym.lean` reduces both symmetries of orbit 21's Farkas
certificate to one hypothesis: `chi m s = 1` across the pairs the matrix element
actually sums over.  For orbit 21 that is a finite condition on its two fibers,
and this module decides it.

The record is `q = 4`, `a = (1,1,1,2,2,3)`, fibers at residues `0` and `2`, of
sixteen words each.  The forced stabilizer is `G = Z_1Z_2Z_3Z_6`, whose `Z`-mask
sits on the coordinates where `a` is odd.

Two facts, both by `decide` over the 64 strings:

* `gmask` has even overlap with every word of either fiber.  That is what makes
  `G` a stabilizer, and it gives the first symmetry directly.

* for every fiber-preserving `x` and every word `s` with `s + x` in the same
  fiber, `x and gmask` has even overlap with `s`.  That is the second symmetry,
  and it is where the vanishing the manuscript does not list -- `a_E = 0` unless
  `A_a(E.x) = 0 mod q` -- earns its place: the statement is false without the
  restriction to fiber-preserving `x`.

Note the second is quantified over *contributing pairs*, not over the fibers.
Stated over the fibers it would be false, which is why looking for a
support-wide version led to the wrong conclusion that the conjugation action of
a diagonal Clifford had to be built.
-/

namespace SixQubit.Orbit21Cert

open SS.MacWilliams

/-! ## The orbit record -/

/-- Orbit 21's angle vector, `q = 4`. -/
def av : Fin 6 → ZMod 4 := ![1, 1, 1, 2, 2, 3]

/-- The `Z`-mask of `G = Z_1 Z_2 Z_3 Z_6`: the coordinates where `av` is odd. -/
def gmask : SS.BitString 6 := ![true, true, true, false, false, true]

/-- Coordinatewise conjunction of two masks. -/
def band (u v : SS.BitString 6) : SS.BitString 6 := fun i => u i && v i

/-- Membership of either fiber. -/
def inFiber (s : SS.BitString 6) : Prop :=
  SS.weight av s = 0 ∨ SS.weight av s = 2

instance : DecidablePred inFiber := fun _ => by unfold inFiber; infer_instance

/-! ## The two decidable facts -/

/-- `G` has even overlap with every word of either fiber.  This is the same
condition that makes it a stabilizer. -/
theorem bdot_gmask : ∀ s : SS.BitString 6, inFiber s → SS.bdot gmask s = false := by
  decide

set_option maxRecDepth 40000 in
/-- For a fiber-preserving `x`, the mask `x and gmask` has even overlap with
every word the matrix element pairs with `s + x`.

Two restrictions are load-bearing and the kernel rejects the statement without
either.  `SS.weight av x = 0` is the vanishing the manuscript's list of
symmetries omits.  And `s + x` must lie in the *same* fiber as `s`, not merely
in one of the two: a matrix element pairs `s` with `s + x` inside a single
logical word's support, and the two words are supported in different fibers.
Allowing either fiber makes the statement false in 192 of 512 cases. -/
theorem bdot_band_gmask :
    ∀ x s : SS.BitString 6, SS.weight av x = 0 → inFiber s →
      SS.weight av (SS.bxor s x) = SS.weight av s →
      SS.bdot (band x gmask) s = false := by
  decide

/-! ## From even overlap to a trivial character -/

lemma chi_eq_one_of_bdot (u v : SS.BitString 6) (h : SS.bdot u v = false) :
    chi u v = 1 := by
  have := signC_bdot u v 1
  rw [h, SS.signC_false, mul_one] at this
  exact_mod_cast this.symm

/-- The first symmetry's hypothesis, in the form `melTr_shift` wants. -/
theorem chi_gmask_one (s : SS.BitString 6) (hs : inFiber s) : chi gmask s = 1 :=
  chi_eq_one_of_bdot _ _ (bdot_gmask s hs)

/-- The second symmetry's hypothesis. -/
theorem chi_band_one (x s : SS.BitString 6) (hx : SS.weight av x = 0)
    (hs : inFiber s) (ht : SS.weight av (SS.bxor s x) = SS.weight av s) :
    chi (band x gmask) s = 1 :=
  chi_eq_one_of_bdot _ _ (bdot_band_gmask x s hx hs ht)

end SixQubit.Orbit21Cert
