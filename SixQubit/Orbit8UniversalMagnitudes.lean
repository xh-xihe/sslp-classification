import SixQubit.Orbit8UniversalHafnian

/-!
# Orbit 8 universal converse, X: weight-four magnitudes

The saturated `Z` and `ZZ` coefficients are converted back into exact
computational-basis probabilities.  All changes of index below are finite
theorems on six bits.
-/

namespace SixQubit.Orbit8Universal

open scoped BigOperators ComplexConjugate
open SixQubit
open SS.MacWilliams

set_option maxRecDepth 20000

noncomputable section

def edgeState (ij : Fin 6 × Fin 6) : SS.BitString 6 :=
  SS.complement (pairMask ij.1 ij.2)

def w (d : SS.BitString 6 → ℂ) (i j : Fin 6) : ℝ :=
  Complex.normSq (v d i j)

def incidentPairs (i : Fin 6) : Finset (Fin 6 × Fin 6) :=
  pairs6.filter (fun ij => ij.1 = i ∨ ij.2 = i)

def awayPairs (i : Fin 6) : Finset (Fin 6 × Fin 6) :=
  pairs6.filter (fun ij => ij.1 ≠ i ∧ ij.2 ≠ i)

def D (d : SS.BitString 6 → ℂ) (i : Fin 6) : ℝ :=
  ∑ ij ∈ incidentPairs i, w d ij.1 ij.2

def oneFiber (i : Fin 6) : Finset (SS.BitString 6) :=
  S1.filter (fun x => x i = true)

theorem shell4_edge_image :
    S1.filter (fun x => SS.hammingWt x = 4) = pairs6.image edgeState := by decide

theorem edgeState_injective_on : Set.InjOn edgeState ↑pairs6 := by decide

theorem oneFiber_image : ∀ i : Fin 6,
    oneFiber i = insert (SS.stdBasis i) ((awayPairs i).image edgeState) := by decide

theorem singleton_not_edge_image : ∀ i : Fin 6,
    SS.stdBasis i ∉ (awayPairs i).image edgeState := by decide

theorem pairs_partition : ∀ i : Fin 6,
    incidentPairs i ∪ awayPairs i = pairs6 := by decide

theorem pairs_disjoint : ∀ i : Fin 6,
    Disjoint (incidentPairs i) (awayPairs i) := by decide

lemma v_edgeState (d : SS.BitString 6 → ℂ) (ij : Fin 6 × Fin 6) :
    d (edgeState ij) = v d ij.1 ij.2 := rfl

lemma shell4_edge_mass (d : SS.BitString 6 → ℂ) :
    shellMass S1 d 4 = ∑ ij ∈ pairs6, w d ij.1 ij.2 := by
  unfold shellMass
  rw [shell4_edge_image]
  rw [Finset.sum_image edgeState_injective_on]
  rfl

lemma edge_mass_partition (d : SS.BitString 6 → ℂ) (i : Fin 6) :
    D d i + ∑ ij ∈ awayPairs i, w d ij.1 ij.2 =
      ∑ ij ∈ pairs6, w d ij.1 ij.2 := by
  unfold D
  rw [← Finset.sum_union (pairs_disjoint i), pairs_partition]

lemma inner_projOne_fiber (d : SS.BitString 6 → ℂ)
    (hd : ∀ x, SS.weight av x ≠ 1 → d x = 0) (i : Fin 6) :
    SS.innerC d (projOne i d) =
      ((p d i + ∑ ij ∈ awayPairs i, w d ij.1 ij.2 : ℝ) : ℂ) := by
  have hdS := full_support1 hd
  unfold SS.innerC projOne
  have hrestrict := Finset.sum_subset (f := fun x : SS.BitString 6 =>
      star (d x) * if x i = true then d x else 0)
    (show S1 ⊆ Finset.univ from Finset.subset_univ _) (fun x hx hnot => by
      change star (d x) * (if x i = true then d x else 0) = 0
      rw [hdS x hnot]
      simp)
  rw [← hrestrict]
  have hif : ∀ x : SS.BitString 6,
      star (d x) * (if x i = true then d x else 0) =
        if x i = true then star (d x) * d x else 0 := by
    intro x
    by_cases hxi : x i = true <;> simp [hxi]
  simp_rw [hif]
  rw [← Finset.sum_filter]
  change (∑ x ∈ oneFiber i, star (d x) * d x) = _
  rw [oneFiber_image, Finset.sum_insert (singleton_not_edge_image i)]
  rw [Finset.sum_image]
  · unfold p w u v edgeState
    push_cast [← SixQubit.star_mul_self]
    rfl
  · apply edgeState_injective_on.mono
    intro ij hij
    have hh : ij ∈ pairs6 ∧ (ij.1 ≠ i ∧ ij.2 ≠ i) := by
      simpa [awayPairs] using hij
    exact hh.1

lemma expect_half_trace (c d : SS.BitString 6 → ℂ)
    (hcode : SS.HasDistance ![c,d] 3) (P : SS.PauliString 6) (hw : P.wt ≤ 2) :
    SS.innerC d (SS.pauliAct P d) = trProj ![c,d] P / 2 := by
  have heq := expect_eq_of_hasDistance c d hcode P hw
  rw [trProj_pair]
  linear_combination (-1/2 : ℂ) * heq

def Pzz (i j : Fin 6) : SS.PauliString 6 := ⟨zero6, pairMask i j⟩

theorem wt_Pzz : ∀ i j : Fin 6, i ≠ j → (Pzz i j).wt = 2 := by decide

theorem Pzz_not_qimage : ∀ i j : Fin 6, i ≠ j →
    Pzz i j ∉ Finset.univ.image qPauli := by decide

lemma act_Pzz (i j : Fin 6)
    (f : SS.BitString 6 → ℂ) (x : SS.BitString 6) :
    SS.pauliAct (Pzz i j) f x =
      if xor (x i) (x j) = true then -f x else f x := by
  unfold SS.pauliAct Pzz
  have hY : (⟨zero6, pairMask i j⟩ : SS.PauliString 6).numY = 0 := by
    simp [SS.PauliString.numY, zero6]
  rw [hY]
  simp only [pow_zero, one_mul]
  rw [show zero6 = (fun _ => false) from rfl, SS.bxor_zero]
  rw [show pairMask i j = SS.bxor (SS.stdBasis i) (SS.stdBasis j) from rfl,
    bdot_stdBasis_pair]
  cases hxi : x i <;> cases hxj : x j <;>
    simp [SS.signC]

theorem D_formula (c d : SS.BitString 6 → ℂ)
    (hc : ∀ x, SS.weight av x ≠ 0 → c x = 0)
    (hd : ∀ x, SS.weight av x ≠ 1 → d x = 0)
    (hnc : SS.innerC c c = 1) (hnd : SS.innerC d d = 1)
    (hcode : SS.HasDistance ![c,d] 3) (i : Fin 6) :
    D d i = 1/3 - 2*p d i := by
  have ht := trace_saturation c d hc hd hnc hnd hcode (Sum.inl i)
  change trProj ![c,d] (Pz i) =
    24 * (-((Complex.normSq (u d i) : ℂ) / 2)) at ht
  have ht' : trProj ![c,d] (Pz i) = (-12 : ℂ) * (p d i : ℂ) := by
    rw [ht]
    unfold p
    ring
  have he := expect_half_trace c d hcode (Pz i) (wt_Pz i)
  rw [ht'] at he
  have hf := inner_projOne_fiber d hd i
  rw [inner_projOne, hnd, he] at hf
  have hfR : p d i + ∑ ij ∈ awayPairs i, w d ij.1 ij.2 =
      1/2 + 3*p d i := by
    have hraw : p d i + ∑ ij ∈ awayPairs i, w d ij.1 ij.2 =
        (1 - (-12 : ℝ) * p d i / 2) / 2 := by
      exact_mod_cast hf.symm
    norm_num at hraw ⊢
    linarith
  obtain ⟨hc0, hm0, hm3, hm6, hn1, hn4⟩ :=
    rigid_shells c d hc hd hnc hnd hcode
  have htot : (∑ ij ∈ pairs6, w d ij.1 ij.2) = 5/6 := by
    rw [← shell4_edge_mass]
    exact hn4
  have hpart := edge_mass_partition d i
  nlinarith

def awayPairs2 (ij : Fin 6 × Fin 6) : Finset (Fin 6 × Fin 6) :=
  pairs6.filter (fun kl =>
    kl.1 ≠ ij.1 ∧ kl.2 ≠ ij.1 ∧ kl.1 ≠ ij.2 ∧ kl.2 ≠ ij.2)

def twoFiber (ij : Fin 6 × Fin 6) : Finset (SS.BitString 6) :=
  S1.filter (fun x => x ij.1 = true ∧ x ij.2 = true)

theorem twoFiber_image : ∀ ij : Fin 6 × Fin 6, ij ∈ pairs6 →
    twoFiber ij = (awayPairs2 ij).image edgeState := by decide

def projTwo (i j : Fin 6) (f : SS.BitString 6 → ℂ) : SS.BitString 6 → ℂ :=
  fun x => if x i = true ∧ x j = true then f x else 0

lemma inner_projTwo_fiber (d : SS.BitString 6 → ℂ)
    (hd : ∀ x, SS.weight av x ≠ 1 → d x = 0)
    (ij : Fin 6 × Fin 6) (hij : ij ∈ pairs6) :
    SS.innerC d (projTwo ij.1 ij.2 d) =
      ((∑ kl ∈ awayPairs2 ij, w d kl.1 kl.2 : ℝ) : ℂ) := by
  have hdS := full_support1 hd
  unfold SS.innerC projTwo
  have hrestrict := Finset.sum_subset (f := fun x : SS.BitString 6 =>
      star (d x) * if x ij.1 = true ∧ x ij.2 = true then d x else 0)
    (show S1 ⊆ Finset.univ from Finset.subset_univ _) (fun x hx hnot => by
      change star (d x) *
        (if x ij.1 = true ∧ x ij.2 = true then d x else 0) = 0
      rw [hdS x hnot]
      simp)
  rw [← hrestrict]
  have hif : ∀ x : SS.BitString 6,
      star (d x) *
          (if x ij.1 = true ∧ x ij.2 = true then d x else 0) =
        if x ij.1 = true ∧ x ij.2 = true then star (d x) * d x else 0 := by
    intro x
    by_cases hxi : x ij.1 = true ∧ x ij.2 = true <;> simp [hxi]
  simp_rw [hif]
  rw [← Finset.sum_filter]
  change (∑ x ∈ twoFiber ij, star (d x) * d x) = _
  rw [twoFiber_image ij hij, Finset.sum_image]
  · unfold w v edgeState
    push_cast [← SixQubit.star_mul_self]
    rfl
  · apply edgeState_injective_on.mono
    intro kl hkl
    change kl ∈ awayPairs2 ij at hkl
    exact (Finset.filter_subset _ _) hkl

lemma inner_Pzz_probability (f : SS.BitString 6 → ℂ)
    (i j : Fin 6) :
    SS.innerC f (SS.pauliAct (Pzz i j) f) =
      SS.innerC f f - 2 * SS.innerC f (projOne i f)
        - 2 * SS.innerC f (projOne j f) + 4 * SS.innerC f (projTwo i j f) := by
  unfold SS.innerC
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun x hx => ?_)
  rw [act_Pzz i j]
  unfold projOne projTwo
  cases hxi : x i <;> cases hxj : x j <;> simp <;> ring

theorem incidence_indicator : ∀ (ij kl : Fin 6 × Fin 6),
    ij ∈ pairs6 → kl ∈ pairs6 →
    ((if kl.1 = ij.1 ∨ kl.2 = ij.1 then 1 else 0) : ℕ) +
      (if kl.1 = ij.2 ∨ kl.2 = ij.2 then 1 else 0) +
      (if kl.1 ≠ ij.1 ∧ kl.2 ≠ ij.1 ∧
          kl.1 ≠ ij.2 ∧ kl.2 ≠ ij.2 then 1 else 0) =
      1 + if kl = ij then 1 else 0 := by decide

theorem edge_inclusion_identity (d : SS.BitString 6 → ℂ) (ij : Pair6) :
    D d ij.1.1 + D d ij.1.2 +
        ∑ kl ∈ awayPairs2 ij.1, w d kl.1 kl.2 =
      (∑ kl ∈ pairs6, w d kl.1 kl.2) + w d ij.1.1 ij.1.2 := by
  rcases ij with ⟨ij,hij⟩
  unfold D incidentPairs awayPairs2
  rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_filter]
  have hdelta : (∑ kl ∈ pairs6,
      if kl = ij then w d kl.1 kl.2 else 0) = w d ij.1 ij.2 := by
    rw [Finset.sum_ite_eq' pairs6 ij]
    simp [hij]
  rw [← hdelta]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun kl hkl => ?_)
  have hc := incidence_indicator ij kl hij hkl
  have hcR :
      ((if kl.1 = ij.1 ∨ kl.2 = ij.1 then 1 else 0) : ℝ) +
        (if kl.1 = ij.2 ∨ kl.2 = ij.2 then 1 else 0) +
        (if kl.1 ≠ ij.1 ∧ kl.2 ≠ ij.1 ∧
            kl.1 ≠ ij.2 ∧ kl.2 ≠ ij.2 then 1 else 0) =
        1 + if kl = ij then 1 else 0 := by
    exact_mod_cast hc
  split_ifs <;> simp_all

lemma projOne_value (c d : SS.BitString 6 → ℂ)
    (hc : ∀ x, SS.weight av x ≠ 0 → c x = 0)
    (hd : ∀ x, SS.weight av x ≠ 1 → d x = 0)
    (hnc : SS.innerC c c = 1) (hnd : SS.innerC d d = 1)
    (hcode : SS.HasDistance ![c,d] 3) (i : Fin 6) :
    SS.innerC d (projOne i d) = ((1/2 + 3*p d i : ℝ) : ℂ) := by
  have ht := trace_saturation c d hc hd hnc hnd hcode (Sum.inl i)
  change trProj ![c,d] (Pz i) =
    24 * (-((Complex.normSq (u d i) : ℂ) / 2)) at ht
  have ht' : trProj ![c,d] (Pz i) = (-12 : ℂ) * (p d i : ℂ) := by
    rw [ht]
    unfold p
    ring
  have he := expect_half_trace c d hcode (Pz i) (wt_Pz i)
  rw [ht'] at he
  rw [inner_projOne, hnd, he]
  push_cast
  ring

lemma Pzz_trace_zero (c d : SS.BitString 6 → ℂ)
    (hc : ∀ x, SS.weight av x ≠ 0 → c x = 0)
    (hd : ∀ x, SS.weight av x ≠ 1 → d x = 0)
    (hnc : SS.innerC c c = 1) (hnd : SS.innerC d d = 1)
    (hcode : SS.HasDistance ![c,d] 3) (i j : Fin 6) (hij : i ≠ j) :
    trProj ![c,d] (Pzz i j) = 0 := by
  apply trace_zero_low_outside c d hc hd hnc hnd hcode
  · have hw := wt_Pzz i j hij
    simp [lowPaulis, hw]
  · exact Pzz_not_qimage i j hij

/-- Exact magnitude of every canonical weight-four edge. -/
theorem w_formula_pair (c d : SS.BitString 6 → ℂ)
    (hc : ∀ x, SS.weight av x ≠ 0 → c x = 0)
    (hd : ∀ x, SS.weight av x ≠ 1 → d x = 0)
    (hnc : SS.innerC c c = 1) (hnd : SS.innerC d d = 1)
    (hcode : SS.HasDistance ![c,d] 3) (ij : Pair6) :
    w d ij.1.1 ij.1.2 = 1/12 - (p d ij.1.1 + p d ij.1.2)/2 := by
  have hijlt := (Finset.mem_filter.mp ij.2).2
  have hij : ij.1.1 ≠ ij.1.2 := ne_of_lt hijlt
  have hz := Pzz_trace_zero c d hc hd hnc hnd hcode ij.1.1 ij.1.2 hij
  have he := expect_half_trace c d hcode (Pzz ij.1.1 ij.1.2)
    (by rw [wt_Pzz ij.1.1 ij.1.2 hij])
  rw [hz] at he
  norm_num at he
  have hprob := inner_Pzz_probability d ij.1.1 ij.1.2
  rw [he, hnd, projOne_value c d hc hd hnc hnd hcode,
    projOne_value c d hc hd hnc hnd hcode,
    inner_projTwo_fiber d hd ij.1 ij.2] at hprob
  have hprobR : (∑ kl ∈ awayPairs2 ij.1, w d kl.1 kl.2) =
      1/4 + (3/2)*(p d ij.1.1 + p d ij.1.2) := by
    have hraw : (0 : ℝ) = 1 - 2*(1/2 + 3*p d ij.1.1)
        - 2*(1/2 + 3*p d ij.1.2) +
          4*(∑ kl ∈ awayPairs2 ij.1, w d kl.1 kl.2) := by
      exact_mod_cast hprob
    nlinarith
  obtain ⟨hc0, hm0, hm3, hm6, hn1, hn4⟩ :=
    rigid_shells c d hc hd hnc hnd hcode
  have htot : (∑ kl ∈ pairs6, w d kl.1 kl.2) = 5/6 := by
    rw [← shell4_edge_mass]
    exact hn4
  have hi := D_formula c d hc hd hnc hnd hcode ij.1.1
  have hj := D_formula c d hc hd hnc hnd hcode ij.1.2
  have hinc := edge_inclusion_identity d ij
  nlinarith

lemma w_swap (d : SS.BitString 6 → ℂ) (i j : Fin 6) :
    w d j i = w d i j := by
  unfold w v
  rw [pairMask_swap]

theorem w_formula (c d : SS.BitString 6 → ℂ)
    (hc : ∀ x, SS.weight av x ≠ 0 → c x = 0)
    (hd : ∀ x, SS.weight av x ≠ 1 → d x = 0)
    (hnc : SS.innerC c c = 1) (hnd : SS.innerC d d = 1)
    (hcode : SS.HasDistance ![c,d] 3) (i j : Fin 6) (hij : i ≠ j) :
    w d i j = 1/12 - (p d i + p d j)/2 := by
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · let ij : Pair6 := ⟨(i,j), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt⟩⟩
    exact w_formula_pair c d hc hd hnc hnd hcode ij
  · let ji : Pair6 := ⟨(j,i), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hgt⟩⟩
    rw [← w_swap d i j]
    have h := w_formula_pair c d hc hd hnc hnd hcode ji
    dsimp [ji] at h
    linarith

end

end SixQubit.Orbit8Universal
