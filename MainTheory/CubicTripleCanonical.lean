import SixQubit.Realize
import Mathlib

/-! # Ordinary cubic monomials in a canonical unordered triple basis

Sorting the three indices changes neither the cubic nor its normalization.
In particular no square-root multiplicity factor is introduced.
-/

namespace MainTheory.CubicTripleCanonical

def sort3 {A : Type*} [LinearOrder A] (t : A × A × A) : A × A × A :=
  if t.1 ≤ t.2.1 then
    if t.2.1 ≤ t.2.2 then t else
      if t.1 ≤ t.2.2 then (t.1, t.2.2, t.2.1) else (t.2.2, t.1, t.2.1)
  else
    if t.1 ≤ t.2.2 then (t.2.1, t.1, t.2.2) else
      if t.2.1 ≤ t.2.2 then (t.2.1, t.2.2, t.1) else (t.2.2, t.2.1, t.1)

def monomial {A : Type*} (w : A → ℂ) (t : A × A × A) : ℂ :=
  w t.1 * w t.2.1 * w t.2.2

theorem monomial_sort3 {A : Type*} [LinearOrder A] (w : A → ℂ) (t : A × A × A) :
    monomial w (sort3 t) = monomial w t := by
  unfold sort3
  split_ifs <;> simp only [monomial] <;> ring

def xor64 (a b : Fin 64) : Fin 64 :=
  ⟨SixQubit.Realize.num (SS.bxor (SixQubit.Realize.nbit a.val) (SixQubit.Realize.nbit b.val)),
    SixQubit.Realize.num_lt _⟩

theorem nbit_xor64 (a b : Fin 64) :
    SixQubit.Realize.nbit (xor64 a b).val =
      SS.bxor (SixQubit.Realize.nbit a.val) (SixQubit.Realize.nbit b.val) :=
  SixQubit.Realize.nbit_num _

def canonicalPair (a b : Fin 64) : Fin 64 × Fin 64 × Fin 64 := sort3 (a, b, xor64 a b)

end MainTheory.CubicTripleCanonical
