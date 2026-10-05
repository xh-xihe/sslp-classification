import MainTheory.DiagonalMomentBridge

/-! The constant, single-bit and distinct-pair coordinates of the LP feature. -/
namespace MainTheory.BinaryFeatureMoments

open scoped BigOperators
open MainTheory.DiagonalMomentBridge
noncomputable section
variable {n : ℕ}

abbrev Pair (n : ℕ) := {ij : Fin n × Fin n // ij.1 < ij.2}
abbrev Feature (n : ℕ) := Unit ⊕ (Fin n ⊕ Pair n)

def phi2 (x : SS.BitString n) : Feature n → ℝ
  | .inl _ => 1
  | .inr (.inl j) => bitValue x j
  | .inr (.inr ij) => bitValue x ij.val.1 * bitValue x ij.val.2

def average (p : SS.BitString n → ℝ) : Feature n → ℝ :=
  fun f => ∑ x, p x * phi2 x f

theorem average_iff_binary_moments (p r : SS.BitString n → ℝ) :
    average p = average r ↔
      ∀ J : Finset (Fin n), J.card < 3 → moment p bitValue J = moment r bitValue J := by
  classical
  constructor
  · intro h J hJ
    have hz := congrFun h (Sum.inl ())
    have hs (j : Fin n) := congrFun h (Sum.inr (Sum.inl j))
    have hp (i j : Fin n) (hij : i < j) :=
      congrFun h (Sum.inr (Sum.inr ⟨(i, j), hij⟩))
    have hcard : J.card = 0 ∨ J.card = 1 ∨ J.card = 2 := by omega
    rcases hcard with h0 | h1 | h2
    · rw [Finset.card_eq_zero.mp h0]
      simpa [average, phi2, moment] using hz
    · obtain ⟨j, rfl⟩ := Finset.card_eq_one.mp h1
      simpa [average, phi2, moment] using hs j
    · obtain ⟨i, j, hij, rfl⟩ := Finset.card_eq_two.mp h2
      rcases lt_or_gt_of_ne hij with hij' | hji'
      · simpa [average, phi2, moment, hij] using hp i j hij'
      · simpa [average, phi2, moment, hij, mul_comm] using hp j i hji'
  · intro h
    funext f
    rcases f with u | (j | ij)
    · simpa [average, phi2, moment] using h ∅ (by simp)
    · simpa [average, phi2, moment] using h {j} (by simp)
    · have hij : ij.val.1 ≠ ij.val.2 := ne_of_lt ij.property
      simpa [average, phi2, moment, hij] using
        h {ij.val.1, ij.val.2} (by simp [hij])

theorem average_iff_character_moments (p r : SS.BitString n → ℝ) :
    average p = average r ↔
      ∀ J : Finset (Fin n), J.card < 3 → moment p zValue J = moment r zValue J :=
  (average_iff_binary_moments p r).trans (binary_iff_character_moments p r 3)

theorem average_eq_of_distance {K d : ℕ} (psi : Fin K → SS.State n ℂ)
    (hd : SS.HasDistance psi d) (hd3 : 3 ≤ d) (k l : Fin K) :
    average (fun x => Complex.normSq (psi k x)) =
      average (fun x => Complex.normSq (psi l x)) := by
  apply (average_iff_binary_moments _ _).mpr
  intro J hJ
  exact MainTheory.GeneralSectorMoments.wordMoment_eq psi hd
    (lt_of_lt_of_le hJ hd3) k l

theorem average_eq_fiber {q : ℕ} (a : Fin n → ZMod q) (b : ZMod q)
    (v : SS.State n ℂ) (hv : SS.SSConditionState a b v) :
    average (fun x => Complex.normSq (v x)) = fun f =>
      ∑ x ∈ Finset.univ.filter (fun x => SS.weight a x = b),
        Complex.normSq (v x) * phi2 x f := by
  classical
  funext f
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro x _ hx
  have hweight : SS.weight a x ≠ b := by simpa using hx
  have hz : v x = 0 := by
    by_contra hn
    exact hweight (hv x hn)
  rw [hz, map_zero, zero_mul]

end
end MainTheory.BinaryFeatureMoments
