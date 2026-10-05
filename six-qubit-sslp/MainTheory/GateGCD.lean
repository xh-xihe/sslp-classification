import MainTheory.Gate

namespace MainTheory.GateGCD

open MainTheory.Gate
open scoped BigOperators

theorem primitive_iff_gcd {n q : ℕ} (a : Fin n → ZMod q) :
    Primitive q a ↔ Nat.gcd q (Finset.univ.gcd fun j => (a j).val) = 1 := by
  constructor
  · intro h
    apply h
    · exact Nat.gcd_dvd_left _ _
    · intro j
      exact dvd_trans (Nat.gcd_dvd_right _ _) (Finset.gcd_dvd (Finset.mem_univ j))
  · intro h d hd hj
    have hdiv : d ∣ Nat.gcd q (Finset.univ.gcd fun j => (a j).val) :=
      Nat.dvd_gcd hd (Finset.dvd_gcd fun j _ => hj j)
    rw [h] at hdiv
    exact Nat.dvd_one.mp hdiv

end MainTheory.GateGCD
