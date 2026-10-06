import MainTheory.Orbit7BoundaryMass
import MainTheory.Orbit7FourHafnians

set_option autoImplicit false

namespace MainTheory.Orbit7NormalizedProjectors

open SixQubit.Orbit7Universal MainTheory.Orbit7SpinorCoordinates
open MainTheory.Orbit7FourHafnians

noncomputable def projector (s : Spinor) (k : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  scaledOuter s (k : ℂ)⁻¹

theorem projector_rank (s : Spinor) (k : ℝ) (hk : 0 < k)
    (hs : ∑ i : Fin 2, Complex.normSq (s i)=k) : (projector s k).rank=1 := by
  have hkC : (k : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hk
  obtain ⟨i,hi⟩ : ∃ i : Fin 2,s i ≠ 0 := by
    by_contra h
    push_neg at h
    simp [h] at hs
    linarith
  exact scaledOuter_rank s _ i hi (inv_ne_zero hkC)

theorem projector_idempotent (s : Spinor) (k : ℝ) (hk : 0 < k)
    (hs : ∑ i : Fin 2, Complex.normSq (s i)=k) :
    projector s k * projector s k = projector s k := by
  have hkC : (k : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hk
  have hn : (∑ i : Fin 2, star (s i)*s i)=(k : ℂ) := by
    simp_rw [SixQubit.star_mul_self]
    rw [← Complex.ofReal_sum,hs]
  ext i j
  simp only [Matrix.mul_apply,projector,scaledOuter]
  calc
    (∑ a : Fin 2, ((k : ℂ)⁻¹*(s i*star (s a)))*((k : ℂ)⁻¹*(s a*star (s j)))) =
        (k : ℂ)⁻¹*(k : ℂ)⁻¹*s i*(∑ a : Fin 2,star (s a)*s a)*star (s j) := by
      simp only [Finset.mul_sum,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro a _
      ring
    _ = (k : ℂ)⁻¹*(s i*star (s j)) := by
      rw [hn]
      field_simp

theorem projector_hermitian (s : Spinor) (k : ℝ) :
    (projector s k).conjTranspose=projector s k := by
  ext i j
  simp [projector,scaledOuter,Matrix.conjTranspose_apply,mul_comm]

noncomputable def Pa (c d : ℝ) (t : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  projector (avec c d 1 t) (1+Complex.normSq t)

noncomputable def Pb (p : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  projector (bvec 1 p) (1+Complex.normSq p)

theorem denominator_positive (t : ℂ) : 0 < 1+Complex.normSq t := by
  have h := Complex.normSq_nonneg t
  linarith

theorem Pa_mass (c d : ℝ) (h : c^2+d^2=1) (t : ℂ) :
    (∑ i : Fin 2,Complex.normSq (avec c d 1 t i))=1+Complex.normSq t := by
  simpa only [Fin.sum_univ_two,Complex.normSq_one] using avec_norm c d h 1 t

theorem Pb_mass (p : ℂ) :
    (∑ i : Fin 2,Complex.normSq (bvec 1 p i))=1+Complex.normSq p := by
  simp [bvec,Fin.sum_univ_two]

theorem Pa_properties (c d : ℝ) (h : c^2+d^2=1) (t : ℂ) :
    (Pa c d t).rank=1 ∧ Pa c d t*Pa c d t=Pa c d t ∧
      (Pa c d t).conjTranspose=Pa c d t :=
  ⟨projector_rank _ _ (denominator_positive t) (Pa_mass c d h t),
    projector_idempotent _ _ (denominator_positive t) (Pa_mass c d h t),
    projector_hermitian _ _⟩

theorem Pb_properties (p : ℂ) :
    (Pb p).rank=1 ∧ Pb p*Pb p=Pb p ∧ (Pb p).conjTranspose=Pb p :=
  ⟨projector_rank _ _ (denominator_positive p) (Pb_mass p),
    projector_idempotent _ _ (denominator_positive p) (Pb_mass p),
    projector_hermitian _ _⟩

end MainTheory.Orbit7NormalizedProjectors
