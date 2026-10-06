import MainTheory.SevenQubitExampleProjector
import MainTheory.SevenQubitCharacterArithmetic
import QECC.FirstTheorem

/-! The projective logical group of the seven-qubit code. -/
namespace MainTheory.SevenQubitLogicalCharacter

open MainTheory.SevenQubitExampleProjector MainTheory.SevenQubitPhaseArithmetic
open MainTheory.SevenQubitCharacterArithmetic
open scoped BigOperators
noncomputable section

theorem scalar_iff (theta : QECC.PhaseVector 7) (hp : projector.Preserves theta) :
    projector.ActsAsScalar theta ↔ supportSum theta (point1 0) = 0 := by
  have h00 : projector.proj (point0 0) (point0 0) ≠ 0 :=
    (edges _ _).mpr (Or.inl ⟨(support0 _).mpr ⟨0, rfl⟩, (support0 _).mpr ⟨0, rfl⟩⟩)
  have h11 : projector.proj (point1 0) (point1 0) ≠ 0 :=
    (edges _ _).mpr (Or.inr ⟨(support1 _).mpr ⟨0, rfl⟩, (support1 _).mpr ⟨0, rfl⟩⟩)
  constructor
  · rintro ⟨c, hc⟩
    have h0 : (0 : QECC.LocalPhase) = c := by
      have he := hc _ _ h00
      change supportSum theta (point0 0) = c at he
      simpa only [supportSum_point0, weights0,
        Matrix.cons_val_zero] using he
    exact (hc _ _ h11).trans h0.symm
  · intro hz
    obtain ⟨h0, h1⟩ := (exact_edges_iff theta).mp hp
    refine ⟨0, fun x y hxy => ?_⟩
    change supportSum theta x = 0
    rcases (edges x y).mp hxy with ⟨hx, _⟩ | ⟨hx, _⟩
    · obtain ⟨k, rfl⟩ := (support0 x).mp hx
      exact (supportSum_point0 theta k).trans (h0 k)
    · obtain ⟨k, rfl⟩ := (support1 x).mp hx
      exact (supportSum_point1 theta k).trans ((h1 k).trans
        ((supportSum_point1 theta 0).symm.trans hz))

def physicalCharacter : projector.preservingPhases →+ QECC.LocalPhase where
  toFun theta := supportSum theta.val (point1 0)
  map_zero' := by simp [supportSum]
  map_add' theta phi := by
    simp only [supportSum, AddSubgroup.coe_add, Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    cases point1 0 j <;> simp

def logicalCharacter : projector.ProjectiveDiagonalGroup →+ QECC.LocalPhase :=
  QuotientAddGroup.lift projector.scalarPhases physicalCharacter (by
    intro theta htheta
    exact (scalar_iff theta.val theta.property).mp htheta)

@[simp] theorem logicalCharacter_class (theta : QECC.PhaseVector 7)
    (hp : projector.Preserves theta) :
    logicalCharacter (projector.projectiveClassMap ⟨theta, hp⟩) =
      supportSum theta (point1 0) := rfl

theorem class_eq_iff (theta phi : projector.preservingPhases) :
    projector.projectiveClassMap theta = projector.projectiveClassMap phi ↔
      physicalCharacter theta = physicalCharacter phi := by
  change (theta : projector.ProjectiveDiagonalGroup) =
    (phi : projector.ProjectiveDiagonalGroup) ↔ _
  rw [QuotientAddGroup.eq_iff_sub_mem]
  change projector.ActsAsScalar (theta - phi).val ↔ _
  rw [scalar_iff (theta - phi).val (theta - phi).property]
  change physicalCharacter (theta - phi) = 0 ↔ _
  rw [map_sub, sub_eq_zero]

theorem logicalCharacter_injective : Function.Injective logicalCharacter := by
  intro U V
  refine QuotientAddGroup.induction_on U ?_
  intro theta
  refine QuotientAddGroup.induction_on V ?_
  intro phi h
  exact (class_eq_iff theta phi).mpr h

theorem pattern_character (alpha beta u : QECC.LocalPhase)
    (hp : projector.Preserves (pattern alpha beta u)) :
    logicalCharacter (projector.projectiveClassMap ⟨pattern alpha beta u, hp⟩) =
      2 • alpha + 2 • beta := by
  rw [logicalCharacter_class, supportSum_point1, pattern_weights1]

theorem character_preimage (U : projector.ProjectiveDiagonalGroup) :
    ∃ a : ZMod 6, ZMod.toAddCircle a = logicalCharacter U := by
  refine QuotientAddGroup.induction_on U ?_
  intro theta
  obtain ⟨alpha, beta, u, he, ha, hb⟩ := (preserving_phases theta.val).mp theta.property
  have hc : physicalCharacter theta = 2 • alpha + 2 • beta := by
    change supportSum theta.val (point1 0) = _
    rw [he, supportSum_point1, pattern_weights1]
  apply torsion_preimage (by decide : 0 < 6)
  change 6 • physicalCharacter theta = 0
  rw [hc, smul_add]
  have ha' : 6 • (2 • alpha) = 3 • (4 • alpha) := by simp only [smul_smul]; norm_num
  have hb' : 6 • (2 • beta) = 4 • (3 • beta) := by simp only [smul_smul]; norm_num
  rw [ha', hb', ha, hb]
  simp

def characterZ6 (U : projector.ProjectiveDiagonalGroup) : ZMod 6 :=
  Classical.choose (character_preimage U)

theorem characterZ6_spec (U : projector.ProjectiveDiagonalGroup) :
    ZMod.toAddCircle (characterZ6 U) = logicalCharacter U :=
  Classical.choose_spec (character_preimage U)

def characterHom : projector.ProjectiveDiagonalGroup →+ ZMod 6 where
  toFun := characterZ6
  map_zero' := by
    apply ZMod.toAddCircle_injective 6
    simp [characterZ6_spec]
  map_add' U V := by
    apply ZMod.toAddCircle_injective 6
    rw [characterZ6_spec, map_add, map_add, characterZ6_spec, characterZ6_spec]

theorem characterHom_injective : Function.Injective characterHom := by
  intro U V h
  apply logicalCharacter_injective
  rw [← characterZ6_spec U, ← characterZ6_spec V]
  exact congrArg ZMod.toAddCircle h

theorem characterHom_surjective : Function.Surjective characterHom := by
  intro c
  obtain ⟨⟨a, b⟩, hab⟩ := chi_surjective c
  let theta := pattern (ZMod.toAddCircle a) (ZMod.toAddCircle b) 0
  have hp : projector.Preserves theta := by
    apply (preserving_phases theta).mpr
    refine ⟨ZMod.toAddCircle a, ZMod.toAddCircle b, 0, rfl, ?_, ?_⟩
    · rw [← map_nsmul]
      rw [show 4 • a = 0 from (by decide +kernel : ∀ a : ZMod 4, 4 • a = 0) a]
      exact map_zero _
    · rw [← map_nsmul]
      rw [show 3 • b = 0 from (by decide +kernel : ∀ b : ZMod 3, 3 • b = 0) b]
      exact map_zero _
  refine ⟨projector.projectiveClassMap ⟨theta, hp⟩, ?_⟩
  apply ZMod.toAddCircle_injective 6
  change ZMod.toAddCircle (characterZ6 _) = _
  rw [characterZ6_spec, pattern_character, circle_character, hab]

def projectiveEquiv : projector.ProjectiveDiagonalGroup ≃+ ZMod 6 :=
  AddEquiv.ofBijective characterHom ⟨characterHom_injective, characterHom_surjective⟩

end
end MainTheory.SevenQubitLogicalCharacter
