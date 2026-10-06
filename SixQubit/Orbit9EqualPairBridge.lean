import SixQubit.Orbit9K4Bridge
import SixQubit.Orbit9SupportCard

/-!
# Orbit 9: from the active `K₄` to a common equal-bit pair

The two coordinates outside the active `K₄` can occur only together in every
surviving basis word.  This file proves that statement over the complete
uniform fibres, using the actual cross-edge zeros from `Orbit9K4Bridge`.
-/

namespace SixQubit.Orbit9Universal

open SS.MacWilliams

noncomputable section

set_option maxSynthPendingDepth 1000
set_option synthInstance.maxSize 1000000
set_option synthInstance.maxHeartbeats 4000000

theorem mem_S0_shape (x : SS.BitString 6) :
    x ∈ S0 ↔
      (∃ v : Fin 6, x = one v) ∨
      (∃ a b : Fin 6, a ≠ b ∧ x = SS.complement (pair a b)) := by
  revert x
  decide

theorem mem_S1_shape (x : SS.BitString 6) :
    x ∈ S1 ↔
      (∃ a b : Fin 6, a ≠ b ∧ x = pair a b) ∨
      (∃ v : Fin 6, x = SS.complement (one v)) := by
  revert x
  decide

theorem one_bits_differ (v r s : Fin 6) (hrs : r ≠ s)
    (h : one v r ≠ one v s) : v = r ∨ v = s := by
  revert v r s
  decide

theorem complement_one_bits_differ (v r s : Fin 6) (hrs : r ≠ s)
    (h : SS.complement (one v) r ≠ SS.complement (one v) s) :
    v = r ∨ v = s := by
  revert v r s
  decide

theorem six_distinct_cover
    (i j k l r s : Fin 6)
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l)
    (hri : r ≠ i) (hrj : r ≠ j) (hrk : r ≠ k) (hrl : r ≠ l)
    (hsi : s ≠ i) (hsj : s ≠ j) (hsk : s ≠ k) (hsl : s ≠ l)
    (hrs : r ≠ s) :
    ∀ v, v = i ∨ v = j ∨ v = k ∨ v = l ∨ v = r ∨ v = s := by
  intro v
  let T : Finset (Fin 6) := {i, j, k, l, r, s}
  have hcard : T.card = 6 := by
    dsimp [T]
    simp [hij, hik, hil, hjk, hjl, hkl, hrs,
      Ne.symm hri, Ne.symm hrj, Ne.symm hrk, Ne.symm hrl,
      Ne.symm hsi, Ne.symm hsj, Ne.symm hsk, Ne.symm hsl]
  have hv : v ∈ T := by
    by_contra hv
    have hc : (insert v T).card = 7 := by
      simp [hv, hcard]
    have hle := Finset.card_le_card (Finset.subset_univ (insert v T))
    rw [hc] at hle
    norm_num at hle
  simpa [T] using hv

theorem pair_bits_differ_exact (a b r s : Fin 6)
    (hab : a ≠ b) (hrs : r ≠ s)
    (h : pair a b r ≠ pair a b s) :
    (((a = r ∨ b = r) ∧ a ≠ s ∧ b ≠ s) ∨
      ((a = s ∨ b = s) ∧ a ≠ r ∧ b ≠ r)) := by
  revert a b r s
  decide

theorem complement_pair_bits_differ_exact (a b r s : Fin 6)
    (hab : a ≠ b) (hrs : r ≠ s)
    (h : SS.complement (pair a b) r ≠ SS.complement (pair a b) s) :
    (((a = r ∨ b = r) ∧ a ≠ s ∧ b ≠ s) ∨
      ((a = s ∨ b = s) ∧ a ≠ r ∧ b ≠ r)) := by
  revert a b r s
  decide

private lemma member_of_active_four_of_cover
    (i j k l r s u : Fin 6)
    (hcover : ∀ v, v = i ∨ v = j ∨ v = k ∨ v = l ∨ v = r ∨ v = s)
    (hur : u ≠ r) (hus : u ≠ s) :
    u = i ∨ u = j ∨ u = k ∨ u = l := by
  rcases hcover u with h | h | h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr h))
  · exact (hur h).elim
  · exact (hus h).elim

private lemma pair_coefficients_zero_of_cross
    (c d : SS.State 6 ℂ) (t u i j k l : Fin 6)
    (htu : t ≠ u)
    (hu : u = i ∨ u = j ∨ u = k ∨ u = l)
    (hz : (damp c t i = 0 ∧ damp c t j = 0 ∧
        damp c t k = 0 ∧ damp c t l = 0) ∧
      (camp d t i = 0 ∧ camp d t j = 0 ∧
        camp d t k = 0 ∧ camp d t l = 0)) :
    c (SS.complement (pair t u)) = 0 ∧ d (pair t u) = 0 := by
  rcases hu with rfl | rfl | rfl | rfl
  · constructor
    · simpa [damp, htu] using hz.1.1
    · simpa [camp, htu] using hz.2.1
  · constructor
    · simpa [damp, htu] using hz.1.2.1
    · simpa [camp, htu] using hz.2.2.1
  · constructor
    · simpa [damp, htu] using hz.1.2.2.1
    · simpa [camp, htu] using hz.2.2.2.1
  · constructor
    · simpa [damp, htu] using hz.1.2.2.2
    · simpa [camp, htu] using hz.2.2.2.2

/-- The two vertices outside an exact active `K₄` have equal bits on every
basis word carrying a nonzero coefficient, in both uniform fibres. -/
theorem equalBitsSupport_of_activeK4_outside
    (c d : SS.State 6 ℂ) (H : FullKL c d)
    (i j k l r s : Fin 6) (K : ActiveK4 c d i j k l)
    (hex : ActiveExactly4 c i j k l)
    (hri : r ≠ i) (hrj : r ≠ j) (hrk : r ≠ k) (hrl : r ≠ l)
    (hsi : s ≠ i) (hsj : s ≠ j) (hsk : s ≠ k) (hsl : s ≠ l)
    (hrs : r ≠ s) :
    EqualBitsSupport c r s ∧ EqualBitsSupport d r s := by
  have hcover := six_distinct_cover i j k l r s
    K.hij K.hik K.hil K.hjk K.hjl K.hkl
    hri hrj hrk hrl hsi hsj hsk hsl hrs
  have hzr := inactive_cross_both_zero c d H i j k l r K hex
    hri hrj hrk hrl
  have hzs := inactive_cross_both_zero c d H i j k l s K hex
    hsi hsj hsk hsl
  have hnotr : ¬ Active c r := by
    intro hr
    rcases (hex r).mp hr with h | h | h | h
    · exact hri h
    · exact hrj h
    · exact hrk h
    · exact hrl h
  have hnots : ¬ Active c s := by
    intro hs
    rcases (hex s).mp hs with h | h | h | h
    · exact hsi h
    · exact hsj h
    · exact hsk h
    · exact hsl h
  have kill_r (u : Fin 6) (hur : u ≠ r) (hus : u ≠ s) :
      c (SS.complement (pair r u)) = 0 ∧ d (pair r u) = 0 :=
    pair_coefficients_zero_of_cross c d r u i j k l (Ne.symm hur)
      (member_of_active_four_of_cover i j k l r s u hcover hur hus) hzr
  have kill_s (u : Fin 6) (hus : u ≠ s) (hur : u ≠ r) :
      c (SS.complement (pair s u)) = 0 ∧ d (pair s u) = 0 :=
    pair_coefficients_zero_of_cross c d s u i j k l (Ne.symm hus)
      (member_of_active_four_of_cover i j k l r s u hcover hur hus) hzs
  constructor
  · intro x hx
    by_cases hxS : x ∈ S0
    · rcases (mem_S0_shape x).mp hxS with ⟨v, rfl⟩ | ⟨a, b, hab, rfl⟩
      · rcases one_bits_differ v r s hrs hx with hv | hv
        · subst v
          simpa [xamp] using xamp_zero_of_not_active c r hnotr
        · subst v
          simpa [xamp] using xamp_zero_of_not_active c s hnots
      · rcases complement_pair_bits_differ_exact a b r s hab hrs hx with
          ⟨har, has, hbs⟩ | ⟨has, har, hbr⟩
        · rcases har with rfl | rfl
          · exact (kill_r b (Ne.symm hab) hbs).1
          · have hz := (kill_r a hab has).1
            simpa [pair, SS.bxor_comm] using hz
        · rcases has with rfl | rfl
          · exact (kill_s b (Ne.symm hab) hbr).1
          · have hz := (kill_s a hab har).1
            simpa [pair, SS.bxor_comm] using hz
    · exact H.support0 x hxS
  · intro x hx
    by_cases hxS : x ∈ S1
    · rcases (mem_S1_shape x).mp hxS with ⟨a, b, hab, rfl⟩ | ⟨v, rfl⟩
      · rcases pair_bits_differ_exact a b r s hab hrs hx with
          ⟨har, has, hbs⟩ | ⟨has, har, hbr⟩
        · rcases har with rfl | rfl
          · exact (kill_r b (Ne.symm hab) hbs).2
          · have hz := (kill_r a hab has).2
            simpa [pair, SS.bxor_comm] using hz
        · rcases has with rfl | rfl
          · exact (kill_s b (Ne.symm hab) hbr).2
          · have hz := (kill_s a hab har).2
            simpa [pair, SS.bxor_comm] using hz
      · rcases complement_one_bits_differ v r s hrs hx with hv | hv
        · subst v
          exact yamp_zero_of_not_active c d H r hnotr
        · subst v
          exact yamp_zero_of_not_active c d H s hnots
    · exact H.support1 x hxS

/-- The two outside vertices exist canonically as the two-element complement
of the four pairwise-distinct active vertices. -/
theorem exists_equalBits_pair_of_activeK4_exact
    (c d : SS.State 6 ℂ) (H : FullKL c d)
    (i j k l : Fin 6) (K : ActiveK4 c d i j k l)
    (hex : ActiveExactly4 c i j k l) :
    ∃ r s, r ≠ s ∧ r ∈ outside4 i j k l ∧ s ∈ outside4 i j k l ∧
      EqualBitsSupport c r s ∧ EqualBitsSupport d r s := by
  classical
  let V : Finset (Fin 6) := {i, j, k, l}
  have hVcard : V.card = 4 := by
    simp [V, K.hij, K.hik, K.hil, K.hjk, K.hjl, K.hkl]
  have hout : outside4 i j k l = (Finset.univ : Finset (Fin 6)) \ V := by
    ext t
    simp [outside4, V]
  have houtcard : (outside4 i j k l).card = 2 := by
    rw [hout, Finset.card_sdiff]
    simp [hVcard]
  rcases Finset.card_eq_two.mp houtcard with ⟨r, s, hrs, hrsSet⟩
  have hrmem : r ∈ outside4 i j k l := by rw [hrsSet]; simp
  have hsmem : s ∈ outside4 i j k l := by rw [hrsSet]; simp
  have hrne := (Finset.mem_filter.mp hrmem).2
  have hsne := (Finset.mem_filter.mp hsmem).2
  have heq := equalBitsSupport_of_activeK4_outside c d H i j k l r s K hex
    hrne.1 hrne.2.1 hrne.2.2.1 hrne.2.2.2
    hsne.1 hsne.2.1 hsne.2.2.1 hsne.2.2.2 hrs
  exact ⟨r, s, hrs, hrmem, hsmem, heq⟩

/-- Minimal composition interface for an already-labelled exact active
`K₄`; all finite-complement bookkeeping is hidden. -/
theorem equal_pair_of_active_k4_exact
    (c d : SS.State 6 ℂ) (H : FullKL c d)
    (i j k l : Fin 6) (K : ActiveK4 c d i j k l)
    (hex : ActiveExactly4 c i j k l) :
    ∃ r s, r ≠ s ∧ EqualBitsSupport c r s ∧ EqualBitsSupport d r s := by
  rcases exists_equalBits_pair_of_activeK4_exact c d H i j k l K hex with
    ⟨r, s, hrs, _, _, hc, hd⟩
  exact ⟨r, s, hrs, hc, hd⟩

/-- Public `s=4` bridge: genuine `FullKL` data with four active singleton
probabilities supplies a common equal-bit coordinate pair for both fibres. -/
theorem exists_equalBits_pair_of_card_four
    (c d : SS.State 6 ℂ) (H : FullKL c d)
    (hfour : (ActiveSet c).card = 4) :
    ∃ r s, r ≠ s ∧ EqualBitsSupport c r s ∧ EqualBitsSupport d r s := by
  rcases active_k4_exact_of_card_four c d H hfour with
    ⟨i, j, k, l, K, hex⟩
  have hex' : ActiveExactly4 c i j k l := hex
  rcases exists_equalBits_pair_of_activeK4_exact c d H i j k l K hex' with
    ⟨r, s, hrs, _, _, hc, hd⟩
  exact ⟨r, s, hrs, hc, hd⟩

/-- Minimal composition interface from the genuine four-point support
branch. -/
theorem equal_pair_of_card_four
    (c d : SS.State 6 ℂ) (H : FullKL c d)
    (hfour : (ActiveSet c).card = 4) :
    ∃ r s, r ≠ s ∧ EqualBitsSupport c r s ∧ EqualBitsSupport d r s :=
  exists_equalBits_pair_of_card_four c d H hfour

/-- The four-point active-support branch is therefore fully closed to the
orbit-9 enumerator pair. -/
theorem enumerator_of_active_card_four
    (c d : SS.State 6 ℂ) (H : FullKL c d)
    (hfour : (ActiveSet c).card = 4) :
    IsE2A ![c,d] ∧ IsE2B ![c,d] := by
  rcases exists_equalBits_pair_of_card_four c d H hfour with
    ⟨r, s, hrs, hc, hd⟩
  exact enumerator_of_equal_pair c d H.norm0 H.norm1 H.distance
    r s hrs hc hd

end

end SixQubit.Orbit9Universal
