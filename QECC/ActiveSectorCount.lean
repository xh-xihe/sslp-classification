import QECC.RankTwoSSLP

namespace QECC

noncomputable section

namespace CodeProjector

variable {n K q : ℕ} (C : CodeProjector n K)

/-- A nontrivial projective modular action has at least two active phase
sectors.  A single active sector would make the action scalar on the code. -/
theorem two_le_card_activeResidue_of_projectiveClass_ne_zero
    [NeZero q] (hq : 0 < q) (a : Fin n → ZMod q)
    (hpres : C.Preserves (phaseHom n q hq a))
    (hne : C.projectiveClassMap ⟨phaseHom n q hq a, hpres⟩ ≠ 0) :
    2 ≤ Fintype.card (C.ActiveResidue a) := by
  classical
  let U : C.ProjectiveDiagonalGroup :=
    C.projectiveClassMap ⟨phaseHom n q hq a, hpres⟩
  have hK : 0 < K := C.rank_pos_of_projectiveClass_ne_zero U hne
  have hsum :
      ∑ b : C.ActiveResidue a,
        Module.finrank ℂ (C.phaseSector a b.1) = K :=
    C.sum_finrank_activeResidue hq a hpres
  have hcard_ne_zero : Fintype.card (C.ActiveResidue a) ≠ 0 := by
    intro hcard
    letI : IsEmpty (C.ActiveResidue a) := Fintype.card_eq_zero_iff.mp hcard
    have hempty :
        (∑ b : C.ActiveResidue a,
          Module.finrank ℂ (C.phaseSector a b.1)) = 0 := by simp
    omega
  have hcard_pos : 0 < Fintype.card (C.ActiveResidue a) :=
    Nat.pos_of_ne_zero hcard_ne_zero
  obtain ⟨b0⟩ := Fintype.card_pos_iff.mp hcard_pos
  have hcard_ne_one : Fintype.card (C.ActiveResidue a) ≠ 1 := by
    intro hcard
    have huniq : ∀ b : C.ActiveResidue a, b = b0 :=
      fun b => Fintype.card_le_one_iff.mp hcard.le b b0
    apply hne
    have hrelative : (1 : ℕ) • C.relativeResidues a b0 = 0 := by
      funext b
      rw [huniq b]
      simp
    simpa using
      (C.nsmul_projectiveClass_eq_zero_iff hq a hpres b0 1).2 hrelative
  omega

end CodeProjector

end

end QECC
