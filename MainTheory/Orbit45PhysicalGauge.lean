import MainTheory.Orbit45AffineGauge
import MainTheory.Orbit45RelativeLogicalPhase
import MainTheory.Orbit9DiagonalGauge

/-! Physical diagonal and logical phases preserve the actual orbit-45 code.
The seven-anchor phase normalization is therefore available for every code,
with its probabilities and complete physical KL equations retained. -/
set_option autoImplicit false
namespace MainTheory.Orbit45PhysicalGauge
open MainTheory.ClassificationLevels MainTheory.Orbit45PrintedFibers
open MainTheory.Orbit45PhysicalPrintedRows MainTheory.Orbit45AffineGauge
open SixQubit.Orbit45Support
noncomputable section

structure FullKL (c d : SS.State 6 ℂ) : Prop where
  support0 : ∀ x, x ∉ S0 → c x=0
  support1 : ∀ x, x ∉ S1 → d x=0
  norm0 : SS.innerC c c=1
  norm1 : SS.innerC d d=1
  distance : SS.HasDistance ![c,d] 3

def frame (c d : SS.State 6 ℂ) (H : FullKL c d) : CodeSpec.OrthonormalFrame 6 2 where
  vec := ![c,d]
  orthonormal := by
    intro i j
    fin_cases i <;> fin_cases j
    · simpa using H.norm0
    · simpa using SixQubit.innerC_eq_zero_of_disjoint S0 S1 c d
        H.support0 H.support1 S0_disjoint_S1
    · simpa using SixQubit.innerC_eq_zero_of_disjoint S1 S0 d c
        H.support1 H.support0 S0_disjoint_S1.symm
    · simpa using H.norm1

def code (c d : SS.State 6 ℂ) (H : FullKL c d) : CodeSpec.ExactCode 6 2 3 where
  positiveRank := by decide
  frame := frame c d H
  hasDistance := H.distance

theorem diagonal_fullKL (c d : SS.State 6 ℂ) (H : FullKL c d) (u : LocalPhase 6) :
    FullKL (diagonalAction u c) (diagonalAction u d) where
  support0 := by intro x hx; simp [diagonalAction,H.support0 x hx]
  support1 := by intro x hx; simp [diagonalAction,H.support1 x hx]
  norm0 := by rw [Orbit9DiagonalGauge.inner_diagonal,H.norm0]
  norm1 := by rw [Orbit9DiagonalGauge.inner_diagonal,H.norm1]
  distance := by
    have h := DiagonalLocalKernel.hasDistance (code c d H) u
    have he : (fun i => diagonalAction u ((code c d H).frame.vec i))=
        ![diagonalAction u c,diagonalAction u d] := by
      funext i
      fin_cases i <;> rfl
    rwa [he] at h

theorem rephase_fullKL (c d : SS.State 6 ℂ) (H : FullKL c d)
    (a b : ℂ) (ha : star a*a=1) (hb : star b*b=1) : FullKL (a • c) (b • d) where
  support0 := by intro x hx; simp [H.support0 x hx]
  support1 := by intro x hx; simp [H.support1 x hx]
  norm0 := by
    rw [CodeSpec.innerC_smul_left,CodeSpec.innerC_smul_right,H.norm0,mul_one,ha]
  norm1 := by
    rw [CodeSpec.innerC_smul_left,CodeSpec.innerC_smul_right,H.norm1,mul_one,hb]
  distance := by
    have h := Orbit8PhaseNormalization.rephase_distance ![c,d]
      (![a,b] : Fin 2 → ℂ) (by intro i; fin_cases i; exact ha; exact hb) H.distance
    have he : (fun i : Fin 2 => (![a,b] : Fin 2 → ℂ) i • (![c,d] i))=![a • c,b • d] := by
      ext i x
      fin_cases i <;> simp
    rwa [he] at h

theorem global_unit (theta : Fin 7 → ℝ) : star (globalPhase theta)*globalPhase theta=1 :=
  Unitary.coe_star_mul_self (BoundedRepresentation.circlePhase (theta 0))

theorem phaseAction_fullKL (c d : SS.State 6 ℂ) (H : FullKL c d) (theta : Fin 7 → ℝ) :
    FullKL (phaseAction theta c) (phaseAction theta d) :=
  rephase_fullKL _ _ (diagonal_fullKL c d H (localPhases theta))
    (globalPhase theta) (globalPhase theta) (global_unit theta) (global_unit theta)

theorem phaseAction_normSq (theta : Fin 7 → ℝ) (c : SS.State 6 ℂ) (x : SS.BitString 6) :
    Complex.normSq (phaseAction theta c x)=Complex.normSq (c x) := by
  have hg := global_unit theta
  rw [SixQubit.star_mul_self] at hg
  have hg' : Complex.normSq (globalPhase theta)=1 := by exact_mod_cast hg
  rw [phaseAction,diagonalAction,Complex.normSq_mul,Complex.normSq_mul,hg',
    Orbit9DiagonalGauge.diagonal_normSq,one_mul,one_mul]

theorem phaseAction_probabilities (theta : Fin 7 → ℝ) (c d : SS.State 6 ℂ) :
    p (phaseAction theta c)=p c ∧ q (phaseAction theta d)=q d := by
  constructor <;> funext i <;> exact phaseAction_normSq theta _ _

theorem physical_anchor_gauge (c d : SS.State 6 ℂ) (H : FullKL c d) :
    ∃ theta : Fin 7 → ℝ,
      FullKL (phaseAction theta c) (phaseAction theta d) ∧
      p (phaseAction theta c)=p c ∧ q (phaseAction theta d)=q d ∧
      ∀ i : Fin 7, phaseAction theta c (bottom (anchors i))=(‖c (bottom (anchors i))‖ : ℂ) := by
  obtain ⟨theta,hpositive⟩ := anchors_positive c
  obtain ⟨hp,hq⟩ := phaseAction_probabilities theta c d
  exact ⟨theta,phaseAction_fullKL c d H theta,hp,hq,hpositive⟩

theorem physical_relative_gauge (c d : SS.State 6 ℂ) (H : FullKL c d) :
    FullKL c (Orbit45RelativeLogicalPhase.phase c d • d) ∧
      z c (Orbit45RelativeLogicalPhase.phase c d • d) 3=1/8 := by
  have hu := Orbit45RelativeLogicalPhase.phase_unit c d H.support0 H.support1 H.norm0 H.norm1 H.distance
  have hr := Orbit45RelativeLogicalPhase.relative_gauge c d H.support0 H.support1 H.norm0 H.norm1 H.distance
  have he := rephase_fullKL c d H 1 (Orbit45RelativeLogicalPhase.phase c d) (by simp) hu
  simpa only [one_smul] using And.intro he hr.1
end
end MainTheory.Orbit45PhysicalGauge
