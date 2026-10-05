import MainTheory.Orbit45PhysicalGauge
import MainTheory.Orbit45PhysicalSpinFlip
import SixQubit.Orbit45Family

/-! The printed beta/gamma/sigma parameters are tied directly to the
actual normalized full enumerators, including every boundary support. -/
set_option autoImplicit false
namespace MainTheory.Orbit45PrintedEnumerator
open MainTheory.Orbit45PrintedFibers MainTheory.Orbit45PhysicalPrintedRows
open MainTheory.Orbit45PhysicalGauge MainTheory.Orbit45PhysicalProbabilityDomain
open SixQubit.Orbit45Support MainTheory.Orbit8EnumeratorDisplays
noncomputable section

theorem literal_block_positions : bottom 0=x0 ∧ bottom 1=x2 ∧ bottom 2=x4 := by decide +kernel

theorem printed_block_masses (c d : SS.State 6 ℂ) (H : FullKL c d) :
    SixQubit.Orbit45Universal.BlockMasses c d (4*p c 0) (4*p c 1) (4*p c 2) := by
  obtain ⟨g1,g2,g3,hb⟩ := SixQubit.Orbit45Universal.block_masses c d
    H.support0 H.support1 H.norm0 H.norm1 H.distance
  have hg1 : g1=4*p c 0 := by
    rw [p,literal_block_positions.1]
    linarith [hb.block1.1]
  have hg2 : g2=4*p c 1 := by
    rw [p,literal_block_positions.2.1]
    linarith [hb.block2.1]
  have hg3 : g3=4*p c 2 := by
    rw [p,literal_block_positions.2.2]
    linarith [hb.block3.1]
  simpa only [hg1,hg2,hg3] using hb

theorem physical_A2 (c d : SS.State 6 ℂ) (H : FullKL c d) :
    normalizedA ![c,d] 2=32*Orbit45TrianglePolynomial.R (p c 1) (p c 0) (p c 2) := by
  have hb := printed_block_masses c d H
  have hp := SixQubit.Orbit45Phase.phase_relations c d H.support0 H.support1 H.distance
  have hA := SixQubit.Orbit45A2.Aco_two_value c d (4*p c 0) (4*p c 1) (4*p c 2)
    H.support0 H.support1 H.distance hb hp
  rw [normalizedA,hA]
  unfold Orbit45TrianglePolynomial.R
  ring

theorem physical_A3 (c d : SS.State 6 ℂ) (H : FullKL c d) :
    normalizedA ![c,d] 3=1-32*Orbit45TrianglePolynomial.R (p c 1) (p c 0) (p c 2) := by
  have he := Orbit45PhysicalSpinFlip.physical_A2_A3_line c d
    H.support0 H.support1 H.norm0 H.norm1 H.distance
  rw [physical_A2 c d H] at he
  linarith

theorem physical_full_enumerators (c d : SS.State 6 ℂ) (H : FullKL c d) :
    SixQubit.Orbit45Family.IsFamilyA ![c,d]
      (32*Orbit45TrianglePolynomial.R (p c 1) (p c 0) (p c 2)) ∧
    SixQubit.Orbit45Family.IsFamilyB ![c,d]
      (32*Orbit45TrianglePolynomial.R (p c 1) (p c 0) (p c 2)) := by
  obtain ⟨t,_,_,ha,hb⟩ := SixQubit.Orbit45Family.universal_family c d
    H.support0 H.support1 H.norm0 H.norm1 H.distance
  have hA2 := physical_A2 c d H
  rw [normalizedA,ha.2.2.1] at hA2
  have ht : t=32*Orbit45TrianglePolynomial.R (p c 1) (p c 0) (p c 2) := by linarith
  simpa only [ht] using And.intro ha hb

theorem boundary_permutations (b g s : ℝ) (H : Orbit45TrianglePolynomial.Domain b g s)
    (hz : b*g*s=0) :
    (b=0 ∧ g=1/8 ∧ s=1/8) ∨ (b=1/8 ∧ g=0 ∧ s=1/8) ∨
      (b=1/8 ∧ g=1/8 ∧ s=0) := by
  rcases mul_eq_zero.mp hz with hbg | hs
  · rcases mul_eq_zero.mp hbg with hb | hg
    · exact Or.inl ⟨hb,by linarith [H.sum,H.beta_upper,H.gamma_upper,H.sigma_upper],by linarith [H.sum,H.beta_upper,H.gamma_upper,H.sigma_upper]⟩
    · exact Or.inr (Or.inl ⟨by linarith [H.sum,H.beta_upper,H.gamma_upper,H.sigma_upper],hg,by linarith [H.sum,H.beta_upper,H.gamma_upper,H.sigma_upper]⟩)
  · exact Or.inr (Or.inr ⟨by linarith [H.sum,H.beta_upper,H.gamma_upper,H.sigma_upper],by linarith [H.sum,H.beta_upper,H.gamma_upper,H.sigma_upper],hs⟩)

theorem boundary_R (b g s : ℝ) (H : Orbit45TrianglePolynomial.Domain b g s)
    (hz : b*g*s=0) : Orbit45TrianglePolynomial.R b g s=1/32 := by
  rcases boundary_permutations b g s H hz with (⟨hb,hg,hs⟩ | ⟨hb,hg,hs⟩ | ⟨hb,hg,hs⟩) <;>
    norm_num [Orbit45TrianglePolynomial.R,hb,hg,hs]

theorem physical_boundary (c d : SS.State 6 ℂ) (H : FullKL c d)
    (hz : p c 1*p c 0*p c 2=0) : normalizedA ![c,d] 2=1 ∧ normalizedA ![c,d] 3=0 := by
  have hr := boundary_R _ _ _ (triangle_domain c d H.support0 H.support1 H.norm0 H.norm1 H.distance) hz
  rw [physical_A2 c d H,physical_A3 c d H,hr]
  norm_num
end
end MainTheory.Orbit45PrintedEnumerator
