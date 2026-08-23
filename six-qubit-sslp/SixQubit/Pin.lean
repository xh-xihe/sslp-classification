import Mathlib
import SS.HilbertKL
import SixQubit.MacWilliams
import SixQubit.Shadow

/-!
# Pinning an enumerator between a forced stabilizer and the shadow bound

`SixQubit/Shadow.lean` gives `Aco_1 + Aco_2 + Aco_3 <= 4` for every exact
`((6,2,d>=3))` code.  That is an upper bound on a sum of nonnegative numbers, so
a matching lower bound on any single one of them collapses the whole triple.

The lower bound comes free when the code carries a Pauli that fixes both
logical states.  For the projective-order-two orbits with `q = 4`, the diagonal
gate acts logically as `diag(1,-1)`, so its square is scalar on the code; that
square is the `Z`-string on the coordinates where the angle vector is odd, and
on both subset-sum fibers its sign is `+1`, because `sum_{j in S} x_j` and
`A_a(x)` agree modulo two.  Whether that sign really is `+1` is a finite check
over the two supports, so each orbit discharges it by `decide`.

With `Aco_w >= 4` for `w` the weight of that stabilizer, and every coefficient
nonnegative, the triple is forced to `4` at `w` and `0` elsewhere, and the
six-qubit MacWilliams normal form then determines every remaining coefficient.
-/

namespace SixQubit.Pin

open SS.MacWilliams SS.Shadow

variable {n K : ℕ}

/-- Enumerator coefficients are sums of squared norms. -/
lemma Aco_nonneg (psi : Fin K → SS.State n ℂ) (j : ℕ) : 0 ≤ Aco psi j :=
  Finset.sum_nonneg (fun _ _ => Complex.normSq_nonneg _)

/-- A Pauli fixing both logical states contributes exactly `4` to the
coefficient at its own weight, and coefficients are nonnegative, so it is a
lower bound for that coefficient. -/
lemma four_le_Aco (psi : Fin 2 → SS.State n ℂ) (G : SS.PauliString n)
    (hG : ∀ k, SS.pauliAct G (psi k) = psi k)
    (hnorm : ∀ k, SS.innerC (psi k) (psi k) = 1) :
    4 ≤ Aco psi G.wt := by
  classical
  have htr : trProj psi G = 2 := by
    unfold trProj
    rw [Finset.sum_congr rfl (fun k (_ : k ∈ Finset.univ) => by rw [hG k, hnorm k])]
    simp
  have hval : Complex.normSq (trProj psi G) = 4 := by
    rw [htr]
    norm_num [Complex.normSq_apply]
  have hmem : G ∈ Finset.univ.filter (fun P : SS.PauliString n => P.wt = G.wt) := by
    simp
  calc (4 : ℝ) = Complex.normSq (trProj psi G) := hval.symm
    _ ≤ Aco psi G.wt :=
        Finset.single_le_sum
          (f := fun P : SS.PauliString n => Complex.normSq (trProj psi P))
          (fun _ _ => Complex.normSq_nonneg _) hmem

/-- Weight zero pins the Pauli: only the identity has empty support. -/
lemma wt_eq_zero_iff (P : SS.PauliString n) :
    P.wt = 0 ↔ P = (⟨fun _ => false, fun _ => false⟩ : SS.PauliString n) := by
  classical
  rw [wt_eq_card_supp, Finset.card_eq_zero, supp, Finset.filter_eq_empty_iff]
  constructor
  · intro h
    have key : ∀ i, P.x i = false ∧ P.z i = false := by
      intro i
      have hi := h (Finset.mem_univ i)
      simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at hi
      exact hi
    cases P with
    | mk x z =>
        simp only [SS.PauliString.mk.injEq]
        exact ⟨funext (fun i => (key i).1), funext (fun i => (key i).2)⟩
  · intro h
    subst h
    intro i _
    simp

/-- The weight-zero coefficient is `4` for any normalized pair: the only Pauli of
weight zero is the identity, whose projector trace is `2`.  So the hypothesis
`macwilliams_six` and `shadow_bound` take is exactly normalization. -/
theorem Aco_zero (psi : Fin 2 → SS.State 6 ℂ)
    (hnorm : ∀ k, SS.innerC (psi k) (psi k) = 1) : Aco psi 0 = 4 := by
  classical
  have hfil : (Finset.univ.filter (fun P : SS.PauliString 6 => P.wt = 0))
      = {(⟨fun _ => false, fun _ => false⟩ : SS.PauliString 6)} := by
    ext P
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    exact wt_eq_zero_iff P
  have hid : ∀ k, SS.pauliAct
      (⟨fun _ => false, fun _ => false⟩ : SS.PauliString 6) (psi k) = psi k := by
    intro k
    funext t
    have hnumY : (⟨fun _ => false, fun _ => false⟩ : SS.PauliString 6).numY = 0 := by
      simp [SS.PauliString.numY]
    simp only [SS.pauliAct, hnumY, pow_zero, one_mul, SS.bxor_zero]
    rw [show SS.bdot (fun _ => false) t = false from by simp [SS.bdot],
      SS.signC_false]
  have htr : trProj psi (⟨fun _ => false, fun _ => false⟩ : SS.PauliString 6) = 2 := by
    unfold trProj
    rw [Finset.sum_congr rfl (fun k (_ : k ∈ Finset.univ) => by rw [hid k, hnorm k])]
    simp
  rw [Aco, hfil, Finset.sum_singleton, htr]
  norm_num [Complex.normSq_apply]

/-- A pure `Z`-string whose mask has even overlap with every word of the support
fixes the state.  This is what makes the forced-stabilizer hypothesis a finite
check: an orbit supplies the mask and discharges the overlap condition over its
two support lists by `decide`. -/
lemma zstring_fixes (c : SS.State n ℂ) (L : List (SS.BitString n))
    (hv : ∀ s, s ∉ L → c s = 0) (zm : SS.BitString n)
    (hz : ∀ s ∈ L, SS.bdot zm s = false) :
    SS.pauliAct (⟨fun _ => false, zm⟩ : SS.PauliString n) c = c := by
  classical
  have hnumY : (⟨fun _ => false, zm⟩ : SS.PauliString n).numY = 0 := by
    simp [SS.PauliString.numY]
  funext t
  simp only [SS.pauliAct, hnumY, pow_zero, one_mul, SS.bxor_zero]
  by_cases h : SS.bdot zm t = true
  · have hnl : t ∉ L := by
      intro hm
      rw [hz t hm] at h
      exact Bool.noConfusion h
    rw [hv t hnl, SS.signC]
    simp
  · rw [Bool.not_eq_true] at h
    rw [h, SS.signC_false]

/-- **The degree-`<=3` coefficients, pinned.**

A forced stabilizer of weight `w` and the shadow bound leave no freedom: the
coefficient at `w` is `4` and the other two vanish. -/
theorem pin_low (psi : Fin 2 → SS.State 6 ℂ) (hd3 : SS.HasDistance psi 3)
    (hA0 : Aco psi 0 = 4) (hnorm : ∀ k, SS.innerC (psi k) (psi k) = 1)
    (G : SS.PauliString 6) (hG : ∀ k, SS.pauliAct G (psi k) = psi k)
    (j : ℕ) (hj : j = 1 ∨ j = 2 ∨ j = 3) (hw : G.wt = j) :
    Aco psi j = 4
      ∧ (∀ i, (i = 1 ∨ i = 2 ∨ i = 3) → i ≠ j → Aco psi i = 0) := by
  have hsum := shadow_bound psi hd3 hA0
  have hlow : 4 ≤ Aco psi j := hw ▸ four_le_Aco psi G hG hnorm
  have h1 := Aco_nonneg psi 1
  have h2 := Aco_nonneg psi 2
  have h3 := Aco_nonneg psi 3
  refine ⟨?_, ?_⟩
  · rcases hj with h | h | h <;> subst h <;> linarith
  · intro i hi hne
    rcases hj with h | h | h <;> subst h <;>
      rcases hi with h' | h' | h' <;> subst h' <;>
        first
          | exact absurd rfl hne
          | linarith

/-- **The full enumerator.**

Once the low coefficients are pinned, the six-qubit MacWilliams normal form
determines the rest. -/
theorem enumerator_of_forced (psi : Fin 2 → SS.State 6 ℂ)
    (hd3 : SS.HasDistance psi 3) (hA0 : Aco psi 0 = 4)
    (hnorm : ∀ k, SS.innerC (psi k) (psi k) = 1)
    (G : SS.PauliString 6) (hG : ∀ k, SS.pauliAct G (psi k) = psi k) :
    (G.wt = 1 →
        Aco psi 1 = 4 ∧ Aco psi 2 = 0 ∧ Aco psi 3 = 0
        ∧ Aco psi 4 = 60 ∧ Aco psi 5 = 60 ∧ Aco psi 6 = 0)
      ∧ (G.wt = 2 →
        Aco psi 1 = 0 ∧ Aco psi 2 = 4 ∧ Aco psi 3 = 0
        ∧ Aco psi 4 = 44 ∧ Aco psi 5 = 64 ∧ Aco psi 6 = 12) := by
  obtain ⟨h4, h5, h6⟩ := macwilliams_six psi hd3 hA0
  constructor
  · intro hw
    obtain ⟨hj, hoth⟩ := pin_low psi hd3 hA0 hnorm G hG 1 (Or.inl rfl) hw
    have e2 := hoth 2 (Or.inr (Or.inl rfl)) (by norm_num)
    have e3 := hoth 3 (Or.inr (Or.inr rfl)) (by norm_num)
    exact ⟨hj, e2, e3, by linarith, by linarith, by linarith⟩
  · intro hw
    obtain ⟨hj, hoth⟩ := pin_low psi hd3 hA0 hnorm G hG 2 (Or.inr (Or.inl rfl)) hw
    have e1 := hoth 1 (Or.inl rfl) (by norm_num)
    have e3 := hoth 3 (Or.inr (Or.inr rfl)) (by norm_num)
    exact ⟨e1, hj, e3, by linarith, by linarith, by linarith⟩

end SixQubit.Pin
