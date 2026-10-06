import QECC.RankTwoCyclicity

namespace QECC

noncomputable section

/-- A chosen additive generator identifies its group with the cyclic group whose
order is the additive order of that generator. -/
def zmodGeneratorHom {G : Type*} [AddGroup G] (U : G) :
  ZMod (addOrderOf U) →+ G :=
  ZMod.lift (addOrderOf U) ⟨zmultiplesHom G U, by
    simp⟩

@[simp] theorem zmodGeneratorHom_intCast {G : Type*} [AddGroup G]
    (U : G) (k : ℤ) :
    zmodGeneratorHom U (k : ZMod (addOrderOf U)) = k • U := by
  simp [zmodGeneratorHom]

noncomputable def zmodAddEquivOfGenerator {G : Type*} [AddGroup G]
    (U : G) (hU : ∀ V : G, V ∈ AddSubgroup.zmultiples U) :
    ZMod (addOrderOf U) ≃+ G := by
  apply AddEquiv.ofBijective (zmodGeneratorHom U)
  constructor
  · apply (ZMod.lift_injective (addOrderOf U)).2
    intro k hk
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact addOrderOf_dvd_iff_zsmul_eq_zero.mpr hk
  · intro V
    obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.mp (hU V)
    refine ⟨(k : ZMod (addOrderOf U)), ?_⟩
    simpa using hk

@[simp] theorem zmodAddEquivOfGenerator_intCast {G : Type*} [AddGroup G]
    (U : G) (hU : ∀ V : G, V ∈ AddSubgroup.zmultiples U) (k : ℤ) :
    zmodAddEquivOfGenerator U hU (k : ZMod (addOrderOf U)) = k • U := by
  change zmodGeneratorHom U (k : ZMod (addOrderOf U)) = k • U
  exact zmodGeneratorHom_intCast U k

@[simp] theorem zmodAddEquivOfGenerator_one {G : Type*} [AddGroup G]
    (U : G) (hU : ∀ V : G, V ∈ AddSubgroup.zmultiples U) :
    zmodAddEquivOfGenerator U hU (1 : ZMod (addOrderOf U)) = U := by
  simpa using zmodAddEquivOfGenerator_intCast U hU (1 : ℤ)

/-- A generator's additive order is the cardinality of its finite group. -/
theorem natCard_eq_addOrderOf_of_generator {G : Type*} [AddGroup G] [Finite G]
    (U : G) (hU : ∀ V : G, V ∈ AddSubgroup.zmultiples U) :
    Nat.card G = addOrderOf U := by
  let e := zmodAddEquivOfGenerator U hU
  rw [← Nat.card_zmod (addOrderOf U)]
  exact Nat.card_congr e.toEquiv.symm

/-- Every finite cyclic additive group has a generator-specific model by
`ZMod` at the exact order of that generator. -/
theorem exists_generator_zmodAddEquiv (G : Type*) [AddGroup G] [Finite G]
    [IsAddCyclic G] :
    ∃ U : G,
      (∀ V : G, V ∈ AddSubgroup.zmultiples U) ∧
      Nonempty (ZMod (addOrderOf U) ≃+ G) ∧
      Nat.card G = addOrderOf U := by
  obtain ⟨U, hU⟩ := IsAddCyclic.exists_generator (α := G)
  exact ⟨U, hU, ⟨zmodAddEquivOfGenerator U hU⟩,
    natCard_eq_addOrderOf_of_generator U hU⟩

namespace CodeProjector

/-- A nontrivial rank-two projective diagonal group is literally a `ZMod m`
for its generator order `m`. -/
theorem exists_projectiveDiagonalGroup_zmod_model
    {n : ℕ} (C : CodeProjector n 2) (hZ : C.DetectsSingleZ)
    (U₀ : C.ProjectiveDiagonalGroup) (hU₀ : U₀ ≠ 0) :
    ∃ (m : ℕ) (U : C.ProjectiveDiagonalGroup),
      U ≠ 0 ∧
      (∀ V : C.ProjectiveDiagonalGroup,
        V ∈ AddSubgroup.zmultiples U) ∧
      m = addOrderOf U ∧
      2 ≤ m ∧
      Nonempty (ZMod m ≃+ C.ProjectiveDiagonalGroup) ∧
      Nat.card C.ProjectiveDiagonalGroup = m := by
  letI : Finite C.ProjectiveDiagonalGroup :=
    C.projectiveDiagonalGroup_finite
      (C.detectsNumberOps_of_detectsSingleZ hZ)
  letI : IsAddCyclic C.ProjectiveDiagonalGroup :=
    C.projectiveDiagonalGroup_isAddCyclic hZ
  obtain ⟨U, hgen⟩ :=
    IsAddCyclic.exists_generator (α := C.ProjectiveDiagonalGroup)
  have hU : U ≠ 0 := by
    intro hzero
    obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.mp (hgen U₀)
    apply hU₀
    simpa [hzero] using hk.symm
  let m := addOrderOf U
  have hmpos : 0 < m := addOrderOf_pos U
  have hmne : m ≠ 1 := by
    intro hm
    apply hU
    exact AddMonoid.addOrderOf_eq_one_iff.mp hm
  have hm : 2 ≤ m := by omega
  let e : ZMod m ≃+ C.ProjectiveDiagonalGroup :=
    zmodAddEquivOfGenerator U hgen
  have hcard : Nat.card C.ProjectiveDiagonalGroup = m := by
    exact natCard_eq_addOrderOf_of_generator U hgen
  exact ⟨m, U, hU, hgen, rfl, hm, ⟨e⟩, hcard⟩

end CodeProjector

end

end QECC
