import SixQubit.Orbit9S2
import SixQubit.Orbit9ComponentPhase

/-!
# Orbit 9: relabelling the two-active-vertex exclusion

The uniform fibres are invariant under every physical-coordinate
permutation.  This file transports the canonical `{0,1}` contradiction to
an arbitrary pair of distinct active coordinates.
-/

namespace SixQubit.Orbit9Universal

open scoped BigOperators ComplexConjugate

noncomputable section

def pairTo01 (a b : Fin 6) : Equiv.Perm (Fin 6) :=
  (Equiv.swap a 0).trans (Equiv.swap ((Equiv.swap a 0) b) 1)

lemma pairTo01_apply_left (a b : Fin 6) (hab : a ≠ b) : pairTo01 a b a = 0 := by
  have hu : (Equiv.swap a 0) b ≠ 0 := by
    intro h
    apply hab
    apply (Equiv.swap a 0).injective
    simpa using h.symm
  change (Equiv.swap ((Equiv.swap a 0) b) 1) ((Equiv.swap a 0) a) = 0
  rw [Equiv.swap_apply_left]
  exact Equiv.swap_apply_of_ne_of_ne (Ne.symm hu) (by decide)

lemma pairTo01_apply_right (a b : Fin 6) : pairTo01 a b b = 1 := by
  change (Equiv.swap ((Equiv.swap a 0) b) 1) ((Equiv.swap a 0) b) = 1
  exact Equiv.swap_apply_left _ _

lemma one_eq_stdBasis (i : Fin 6) : one i = SS.stdBasis i := by
  revert i
  decide

lemma permStr_one (sigma : Equiv.Perm (Fin 6)) (i : Fin 6) :
    SixQubit.CodeEquiv.permStr sigma (one i) = one (sigma.symm i) := by
  rw [one_eq_stdBasis, one_eq_stdBasis]
  funext j
  have hij : sigma j = i ↔ j = sigma.symm i := by
    constructor
    · intro h
      simpa using congrArg sigma.symm h
    · intro h
      subst j
      simp
  simp [SixQubit.CodeEquiv.permStr, SS.stdBasis, hij]

lemma p_permAct (sigma : Equiv.Perm (Fin 6)) (c : SS.State 6 ℂ) (i : Fin 6) :
    p (SixQubit.CodeEquiv.permAct sigma c) i = p c (sigma.symm i) := by
  simp [p, SixQubit.CodeEquiv.permAct, permStr_one]

lemma uniform_weight_permStr (sigma : Equiv.Perm (Fin 6)) (x : SS.BitString 6) :
    SS.weight uniformAv (SixQubit.CodeEquiv.permStr sigma x) =
      SS.weight uniformAv x := by
  unfold SS.weight uniformAv SixQubit.CodeEquiv.permStr
  simpa using (Equiv.sum_comp sigma
    (fun i : Fin 6 => (1 : ZMod 3) * SS.bit (m := 3) (x i)))

lemma mem_S0_iff_uniform_weight (x : SS.BitString 6) :
    x ∈ S0 ↔ SS.weight uniformAv x = 1 := by
  rw [← S0_eq_fiber]
  simp

lemma mem_S1_iff_uniform_weight (x : SS.BitString 6) :
    x ∈ S1 ↔ SS.weight uniformAv x = 2 := by
  rw [← S1_eq_fiber]
  simp

lemma permStr_mem_S0_iff (sigma : Equiv.Perm (Fin 6)) (x : SS.BitString 6) :
    SixQubit.CodeEquiv.permStr sigma x ∈ S0 ↔ x ∈ S0 := by
  rw [mem_S0_iff_uniform_weight, mem_S0_iff_uniform_weight,
    uniform_weight_permStr]

lemma permStr_mem_S1_iff (sigma : Equiv.Perm (Fin 6)) (x : SS.BitString 6) :
    SixQubit.CodeEquiv.permStr sigma x ∈ S1 ↔ x ∈ S1 := by
  rw [mem_S1_iff_uniform_weight, mem_S1_iff_uniform_weight,
    uniform_weight_permStr]

lemma support_S0_permAct (sigma : Equiv.Perm (Fin 6)) (c : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x = 0) :
    ∀ x, x ∉ S0 → SixQubit.CodeEquiv.permAct sigma c x = 0 := by
  intro x hx
  unfold SixQubit.CodeEquiv.permAct
  apply hc
  intro hm
  exact hx ((permStr_mem_S0_iff sigma x).mp hm)

lemma support_S1_permAct (sigma : Equiv.Perm (Fin 6)) (d : SS.State 6 ℂ)
    (hd : ∀ x, x ∉ S1 → d x = 0) :
    ∀ x, x ∉ S1 → SixQubit.CodeEquiv.permAct sigma d x = 0 := by
  intro x hx
  unfold SixQubit.CodeEquiv.permAct
  apply hd
  intro hm
  exact hx ((permStr_mem_S1_iff sigma x).mp hm)

lemma innerC_permAct (sigma : Equiv.Perm (Fin 6)) (f g : SS.State 6 ℂ) :
    SS.innerC (SixQubit.CodeEquiv.permAct sigma f)
      (SixQubit.CodeEquiv.permAct sigma g) = SS.innerC f g := by
  unfold SS.innerC SixQubit.CodeEquiv.permAct
  simpa using (Equiv.sum_comp (SixQubit.CodeEquiv.permStrEquiv sigma)
    (fun x : SS.BitString 6 => star (f x) * g x))

lemma hasDistance_permAct (sigma : Equiv.Perm (Fin 6)) (c d : SS.State 6 ℂ)
    (hdist : SS.HasDistance ![c,d] 3) :
    SS.HasDistance ![SixQubit.CodeEquiv.permAct sigma c,
      SixQubit.CodeEquiv.permAct sigma d] 3 := by
  have hraw := (SixQubit.CodeEquiv.hasDistance_iff ![c,d]).mp hdist
  have hraw' := SixQubit.CodeEquiv.detectsRaw_permAct sigma hraw
  apply (SixQubit.CodeEquiv.hasDistance_iff
    ![SixQubit.CodeEquiv.permAct sigma c,
      SixQubit.CodeEquiv.permAct sigma d]).mpr
  simpa using hraw'

/-- The singleton probability is supported at exactly the two labelled
coordinates `a` and `b`.  This is a statement about the actual amplitudes,
not an ansatz on a displayed witness. -/
structure TwoSupportAt (c : SS.State 6 ℂ) (a b : Fin 6) : Prop where
  distinct : a ≠ b
  left_pos : 0 < p c a
  right_pos : 0 < p c b
  other_zero : ∀ i, i ≠ a → i ≠ b → p c i = 0

/-- Relabelling sends an arbitrary exact two-point singleton support to the
canonical `{0,1}` support used by `twoSupport01_impossible`. -/
lemma twoSupport01_permAct_of_twoSupportAt (c : SS.State 6 ℂ)
    (a b : Fin 6) (hs : TwoSupportAt c a b) :
    TwoSupport01 (SixQubit.CodeEquiv.permAct (pairTo01 a b) c) := by
  let sigma := pairTo01 a b
  have hsa : sigma a = 0 := pairTo01_apply_left a b hs.distinct
  have hsb : sigma b = 1 := pairTo01_apply_right a b
  have hsi0 : sigma.symm 0 = a := by
    rw [← hsa]
    simp
  have hsi1 : sigma.symm 1 = b := by
    rw [← hsb]
    simp
  have hzero (i : Fin 6) (hi0 : i ≠ 0) (hi1 : i ≠ 1) :
      p c (sigma.symm i) = 0 := by
    apply hs.other_zero
    · intro h
      have h' := congrArg sigma h
      rw [Equiv.apply_symm_apply, hsa] at h'
      exact hi0 h'
    · intro h
      have h' := congrArg sigma h
      rw [Equiv.apply_symm_apply, hsb] at h'
      exact hi1 h'
  constructor
  · rw [p_permAct, hsi0]
    exact hs.left_pos
  · rw [p_permAct, hsi1]
    exact hs.right_pos
  · rw [p_permAct]
    exact hzero 2 (by decide) (by decide)
  · rw [p_permAct]
    exact hzero 3 (by decide) (by decide)
  · rw [p_permAct]
    exact hzero 4 (by decide) (by decide)
  · rw [p_permAct]
    exact hzero 5 (by decide) (by decide)

/-- No full orbit-9 KL pair can have singleton support concentrated on any
two distinct physical coordinates.  All labels are quantified: the only
finite computation remains inside the already-certified canonical theorem. -/
theorem twoSupportAt_impossible (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x = 0) (hd : ∀ x, x ∉ S1 → d x = 0)
    (hnc : SS.innerC c c = 1) (hnd : SS.innerC d d = 1)
    (hdist : SS.HasDistance ![c,d] 3) (a b : Fin 6)
    (hs : TwoSupportAt c a b) : False := by
  let sigma := pairTo01 a b
  let c' := SixQubit.CodeEquiv.permAct sigma c
  let d' := SixQubit.CodeEquiv.permAct sigma d
  have hc' : ∀ x, x ∉ S0 → c' x = 0 := support_S0_permAct sigma c hc
  have hd' : ∀ x, x ∉ S1 → d' x = 0 := support_S1_permAct sigma d hd
  have hnc' : SS.innerC c' c' = 1 := by
    rw [innerC_permAct]
    exact hnc
  have hnd' : SS.innerC d' d' = 1 := by
    rw [innerC_permAct]
    exact hnd
  have hdist' : SS.HasDistance ![c',d'] 3 :=
    hasDistance_permAct sigma c d hdist
  have hs' : TwoSupport01 c' :=
    twoSupport01_permAct_of_twoSupportAt c a b hs
  exact twoSupport01_impossible c' d' hc' hd' hnc' hnd' hdist' hs'

/-- Exact two-point active support, phrased using the `Active` predicate used
by the component/cardinality layer. -/
def ActiveExactly2 (c : SS.State 6 ℂ) (a b : Fin 6) : Prop :=
  a ≠ b ∧ Active c a ∧ Active c b ∧
    ∀ i, Active c i ↔ i = a ∨ i = b

/-- `FullKL` rules out an exact two-point active support at arbitrary labels.
This wrapper deliberately depends only on `Orbit9ComponentPhase`, so the
support-cardinality file can import it without an import cycle. -/
theorem two_active_impossible (c d : SS.State 6 ℂ) (H : FullKL c d)
    (a b : Fin 6) (hex : ActiveExactly2 c a b) : False := by
  rcases hex with ⟨hab, ha, hb, hsupport⟩
  apply twoSupportAt_impossible c d H.support0 H.support1 H.norm0 H.norm1
    H.distance a b
  exact {
    distinct := hab
    left_pos := ha
    right_pos := hb
    other_zero := by
      intro i hia hib
      apply le_antisymm (le_of_not_gt ?_) (p_nonneg c i)
      intro hi
      rcases (hsupport i).mp hi with h | h
      · exact hia h
      · exact hib h
  }

end

end SixQubit.Orbit9Universal
