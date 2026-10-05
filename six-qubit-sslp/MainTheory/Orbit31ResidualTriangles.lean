import MainTheory.Orbit31PermanentAlgebra
import MainTheory.Generated.Orbit31PrintedSupportOrbits
import MainTheory.Orbit31PhysicalSupportFilters

/-! Residual SI triangles: actual column synchronization, opposition, and
the propagated type-nine permanent in the literal SI coordinates. -/
set_option autoImplicit false
set_option maxHeartbeats 32000000
namespace MainTheory.Orbit31ResidualTriangles
noncomputable section
open MainTheory.Orbit31PhaseRatios
open MainTheory.Orbit31CanonicalPhase
open MainTheory.Orbit31SignedSupport
open MainTheory.Orbit31PermanentAlgebra
open scoped BigOperators

theorem column_rectangle {c d : Fin 16 → ℂ} (hp : EqualProbabilities c d)
    (hs : CrossSystem c d) (r : Fin 3) (k : Fin 6)
    (hae : c (A (colPairs k).1) ≠ 0) (haf : c (A (colPairs k).2) ≠ 0)
    (hb : ∀ i e, c (B i e) ≠ 0) :
    (sigma c d (A (colPairs k).1)+sigma c d (A (colPairs k).2)) *
      permanent c (rowPairs r).1 (rowPairs r).2 (colPairs k).1 (colPairs k).2=0 := by
  have he := rectangle_phase hp hs r k
  dsimp only at he
  rw [← vertical_phase hp hs _ _ hae (hb _ _),
      ← vertical_phase hp hs _ _ haf (hb _ _),
      ← vertical_phase hp hs _ _ haf (hb _ _),
      ← vertical_phase hp hs _ _ hae (hb _ _)] at he
  unfold permanent
  linear_combination he

theorem column_opposition {c d : Fin 16 → ℂ} (hp : EqualProbabilities c d)
    (hs : CrossSystem c d) (k : Fin 6)
    (hae : c (A (colPairs k).1) ≠ 0) (haf : c (A (colPairs k).2) ≠ 0)
    (hb : ∀ i e, c (B i e) ≠ 0) :
    sigma c d (A (colPairs k).2) = -sigma c d (A (colPairs k).1) := by
  by_contra h
  have hn : sigma c d (A (colPairs k).1)+sigma c d (A (colPairs k).2) ≠ 0 := by
    intro hz
    exact h (eq_neg_of_add_eq_zero_right hz)
  have hpermanent : ∀ r, permanent c (rowPairs r).1 (rowPairs r).2
      (colPairs k).1 (colPairs k).2=0 := fun r =>
    (mul_eq_zero.mp (column_rectangle hp hs r k hae haf hb)).resolve_left hn
  apply odd_permanent_triangle (fun i => c (B i (colPairs k).1))
    (fun i => c (B i (colPairs k).2)) (fun i => hb i _) (fun i => hb i _)
  · exact hpermanent 0
  · exact hpermanent 1
  · exact hpermanent 2

theorem three_column_no_go {c d : Fin 16 → ℂ} (hp : EqualProbabilities c d)
    (hs : CrossSystem c d)
    (ha0 : c (A 0) ≠ 0) (ha1 : c (A 1) ≠ 0) (ha2 : c (A 2) ≠ 0)
    (hb : ∀ i e, c (B i e) ≠ 0) : False := by
  have h01 := column_opposition hp hs (⟨0,by decide⟩ : Fin 6)
    (by simpa [colPairs,A,Fin.succ] using ha0) (by simpa [colPairs,A,Fin.succ] using ha1) hb
  have h02 := column_opposition hp hs (⟨1,by decide⟩ : Fin 6)
    (by simpa [colPairs,A,Fin.succ] using ha0) (by simpa [colPairs,A,Fin.succ] using ha2) hb
  have h12 := column_opposition hp hs (⟨3,by decide⟩ : Fin 6)
    (by simpa [colPairs,A,Fin.succ] using ha1) (by simpa [colPairs,A,Fin.succ] using ha2) hb
  norm_num [colPairs,A,Fin.succ] at h01 h02 h12
  have hz : sigma c d (A 0)=0 := by
    conv_lhs => norm_num [A,Fin.succ]
    linear_combination (1/2)*h01+(1/2)*h02-(1/2)*h12
  exact nonzero hp ha0 hz

def mask (type : Fin 16) : ℕ :=
  (MainTheory.Generated.Orbit31PrintedSupportOrbits.representatives type).val

theorem type14_no_go {c d : Fin 16 → ℂ} (hp : EqualProbabilities c d)
    (hs : CrossSystem c d) (hm : AmplitudeSupport (mask ⟨13,by decide⟩) c) : False := by
  apply three_column_no_go hp hs
  · exact (hm _).mp (by decide +kernel)
  · exact (hm _).mp (by decide +kernel)
  · exact (hm _).mp (by decide +kernel)
  · intro i e
    fin_cases i <;> fin_cases e <;> exact (hm _).mp (by decide +kernel)

theorem type16_no_go {c d : Fin 16 → ℂ} (hp : EqualProbabilities c d)
    (hs : CrossSystem c d) (hm : AmplitudeSupport (mask ⟨15,by decide⟩) c) : False := by
  apply three_column_no_go hp hs
  · exact (hm _).mp (by decide +kernel)
  · exact (hm _).mp (by decide +kernel)
  · exact (hm _).mp (by decide +kernel)
  · intro i e
    fin_cases i <;> fin_cases e <;> exact (hm _).mp (by decide +kernel)

def typeNine : Fin 16 := ⟨8,by decide⟩

theorem type9_B_nonzero {c : Fin 16 → ℂ} (hm : AmplitudeSupport (mask typeNine) c) :
    ∀ i e, c (B i e) ≠ 0 := by
  intro i e
  fin_cases i <;> fin_cases e <;> exact (hm _).mp (by decide +kernel)

theorem type9_A_nonzero {c : Fin 16 → ℂ} (hm : AmplitudeSupport (mask typeNine) c) :
    c (A 0) ≠ 0 ∧ c (A 1) ≠ 0 :=
  ⟨(hm _).mp (by decide +kernel),(hm _).mp (by decide +kernel)⟩

theorem type9_A_zero {c : Fin 16 → ℂ} (hm : AmplitudeSupport (mask typeNine) c) :
    c (A 2)=0 ∧ c (A 3)=0 := by
  constructor
  · by_contra hn
    have h := (hm (A 2)).mpr hn
    have hz : active (mask typeNine) (A 2)=false := by decide +kernel
    rw [hz] at h
    contradiction
  · by_contra hn
    have h := (hm (A 3)).mpr hn
    have hz : active (mask typeNine) (A 3)=false := by decide +kernel
    rw [hz] at h
    contradiction

theorem type9_opposite {c d : Fin 16 → ℂ} (hp : EqualProbabilities c d)
    (hs : CrossSystem c d) (hm : AmplitudeSupport (mask typeNine) c) :
    sigma c d (A 1) = -sigma c d (A 0) := by
  have h := column_opposition hp hs (⟨0,by decide⟩ : Fin 6)
    (by simpa [colPairs,A,Fin.succ] using (type9_A_nonzero hm).1)
    (by simpa [colPairs,A,Fin.succ] using (type9_A_nonzero hm).2) (type9_B_nonzero hm)
  simpa [colPairs,A,Fin.succ] using h

theorem type9_weight_product {c d : Fin 16 → ℂ} (hp : EqualProbabilities c d)
    (hs : CrossSystem c d) (hm : AmplitudeSupport (mask typeNine) c) (i : Fin 3) :
    c (A 0)*c (B i 0)=c (A 1)*c (B i 1) := by
  have h0 := vertical_phase hp hs i 0 (type9_A_nonzero hm).1 (type9_B_nonzero hm i 0)
  have h1 := vertical_phase hp hs i 1 (type9_A_nonzero hm).2 (type9_B_nonzero hm i 1)
  have hz := type9_A_zero hm
  have he := weight_one_phase_sum hp hs i
  norm_num only [Fin.sum_univ_succ,Fin.succ] at he
  simp at he
  rw [hz.1,hz.2] at he
  simp only [mul_zero,zero_mul,add_zero] at he
  rw [← h0,← h1,type9_opposite hp hs hm] at he
  have hf : sigma c d (A 0)*(c (A 0)*c (B i 0)-c (A 1)*c (B i 1))=0 := by
    linear_combination he
  exact sub_eq_zero.mp ((mul_eq_zero.mp hf).resolve_left (nonzero hp (type9_A_nonzero hm).1))

def ratio (c : Fin 16 → ℂ) : ℂ := c (A 1)/c (A 0)

theorem type9_proportional {c d : Fin 16 → ℂ} (hp : EqualProbabilities c d)
    (hs : CrossSystem c d) (hm : AmplitudeSupport (mask typeNine) c) :
    ratio c ≠ 0 ∧ ∀ i, c (B i 0)=ratio c*c (B i 1) := by
  constructor
  · exact div_ne_zero (type9_A_nonzero hm).2 (type9_A_nonzero hm).1
  · intro i
    unfold ratio
    rw [div_mul_eq_mul_div]
    apply (eq_div_iff (type9_A_nonzero hm).1).mpr
    linear_combination type9_weight_product hp hs hm i

theorem type9_propagated {c d : Fin 16 → ℂ} (hp : EqualProbabilities c d)
    (hs : CrossSystem c d) (hm : AmplitudeSupport (mask typeNine) c) (r : Fin 3) :
    (sigma c d (A 0)-sigma c d (A 1))*permanent c (rowPairs r).1 (rowPairs r).2 1 2=0 := by
  have h02 := rectangle_phase hp hs r (⟨1,by decide⟩ : Fin 6)
  have h12 := rectangle_phase hp hs r (⟨3,by decide⟩ : Fin 6)
  dsimp only at h02 h12
  norm_num [colPairs,Fin.succ] at h02 h12
  rw [← vertical_phase hp hs _ _ (type9_A_nonzero hm).1 (type9_B_nonzero hm _ _),
    ← vertical_phase hp hs _ _ (type9_A_nonzero hm).1 (type9_B_nonzero hm _ _)] at h02
  rw [← vertical_phase hp hs _ _ (type9_A_nonzero hm).2 (type9_B_nonzero hm _ _),
    ← vertical_phase hp hs _ _ (type9_A_nonzero hm).2 (type9_B_nonzero hm _ _)] at h12
  have hprop := type9_proportional hp hs hm
  rw [hprop.2 (rowPairs r).1,hprop.2 (rowPairs r).2] at h02
  have he : ratio c*((sigma c d (A 0)-sigma c d (A 1))*
      permanent c (rowPairs r).1 (rowPairs r).2 1 2)=0 := by
    unfold permanent
    linear_combination h02-ratio c*h12
  exact (mul_eq_zero.mp he).resolve_left hprop.1

theorem type9_permanents {c d : Fin 16 → ℂ} (hp : EqualProbabilities c d)
    (hs : CrossSystem c d) (hm : AmplitudeSupport (mask typeNine) c) :
    ∀ r, permanent c (rowPairs r).1 (rowPairs r).2 1 2=0 := by
  have hn : sigma c d (A 0)-sigma c d (A 1) ≠ 0 := by
    rw [type9_opposite hp hs hm]
    intro he
    have hz : sigma c d (A 0)=0 := by linear_combination (1/2)*he
    exact nonzero hp (type9_A_nonzero hm).1 hz
  intro r
  exact (mul_eq_zero.mp (type9_propagated hp hs hm r)).resolve_left hn

theorem type9_no_go {c d : Fin 16 → ℂ} (hp : EqualProbabilities c d)
    (hs : CrossSystem c d) (hm : AmplitudeSupport (mask typeNine) c) : False := by
  apply odd_permanent_triangle (fun i => c (B i 1)) (fun i => c (B i 2))
    (fun i => type9_B_nonzero hm i 1) (fun i => type9_B_nonzero hm i 2)
  · exact type9_permanents hp hs hm 0
  · exact type9_permanents hp hs hm 1
  · exact type9_permanents hp hs hm 2

theorem physical_type9_no_go (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ SixQubit.Orbit31.S0 → c x=0)
    (hd : ∀ x, x ∉ SixQubit.Orbit31.S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
    (hkl : SS.HasDistance ![c,d] 3) (hm : AmplitudeSupport (mask typeNine) (C c)) : False :=
  type9_no_go (physical_equal_probabilities c d hc hd hnc hnd hkl)
    (MainTheory.Orbit31PhysicalSupportFilters.physical_cross_system c d hc hd hkl) hm

theorem physical_type14_no_go (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ SixQubit.Orbit31.S0 → c x=0)
    (hd : ∀ x, x ∉ SixQubit.Orbit31.S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
    (hkl : SS.HasDistance ![c,d] 3)
    (hm : AmplitudeSupport (mask ⟨13,by decide⟩) (C c)) : False :=
  type14_no_go (physical_equal_probabilities c d hc hd hnc hnd hkl)
    (MainTheory.Orbit31PhysicalSupportFilters.physical_cross_system c d hc hd hkl) hm

theorem physical_type16_no_go (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ SixQubit.Orbit31.S0 → c x=0)
    (hd : ∀ x, x ∉ SixQubit.Orbit31.S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
    (hkl : SS.HasDistance ![c,d] 3)
    (hm : AmplitudeSupport (mask ⟨15,by decide⟩) (C c)) : False :=
  type16_no_go (physical_equal_probabilities c d hc hd hnc hnd hkl)
    (MainTheory.Orbit31PhysicalSupportFilters.physical_cross_system c d hc hd hkl) hm

end
end MainTheory.Orbit31ResidualTriangles
