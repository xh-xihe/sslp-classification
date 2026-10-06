import MainTheory.FiniteCubicTensorTrace
import MainTheory.Orbit3CoordinateRealization

/-! Actual normalized three-copy sampling; no amplitude is divided out. -/

namespace MainTheory.Orbit3NormalizedMoment

noncomputable section
open MainTheory.Orbit3ActualSampling MainTheory.Orbit3ScalarCategoryRealization
open MainTheory.FiniteCubicMoments MainTheory.FiniteCubicTensorTrace
open scoped BigOperators

instance : Nonempty ActivePermutation :=
  ⟨⟨Equiv.refl _, by intro j; rfl⟩⟩

def scale : ℝ := (Real.sqrt 2)⁻¹

theorem scale_squared : scale^2=1/2 := by
  unfold scale
  rw [inv_pow, Real.sq_sqrt (by norm_num)]
  norm_num

theorem scale_product : scale*scale=1/2 := by nlinarith [scale_squared]

def vector (W : Encoder) (g : Index) : SS.State 6 ℂ :=
  (scale : ℂ) • wave W g

theorem norm_one (W : Encoder) (g : Index) :
    (∑ s, Complex.normSq (vector W g s))=1 := by
  simp only [vector, Pi.smul_apply, smul_eq_mul, Complex.normSq_mul,
    Complex.normSq_ofReal, ← Finset.mul_sum]
  rw [scale_product, sample_norm]
  norm_num

theorem expectation (W : Encoder) (g : Index) (P : SS.PauliString 6) :
    SS.innerC (vector W g) (SS.pauliAct P (vector W g))=
      (1/2 : ℂ)*SS.innerC (wave W g) (SS.pauliAct P (wave W g)) := by
  rw [vector, MainTheory.CodeSpec.pauliAct_smul,
    MainTheory.CodeSpec.innerC_smul_left, MainTheory.CodeSpec.innerC_smul_right]
  have hs : star (scale : ℂ)*(scale : ℂ)=(1/2 : ℂ) := by
    rw [Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul]
    have h := congrArg (fun x : ℝ => (x : ℂ)) scale_product
    norm_num at h
    simpa only [Complex.ofReal_mul] using h
  rw [← mul_assoc, hs]

theorem constrained_zero (W : Encoder) (g : Index) (P : SS.PauliString 6)
    (hP : MainTheory.Orbit3PauliZeros.Constrained P) :
    SS.innerC (vector W g) (SS.pauliAct P (vector W g))=0 := by
  rw [expectation, sample_constrained_zero W g P hP, mul_zero]

def M3 (W : Encoder) : Matrix
    (SS.BitString 6 × SS.BitString 6 × SS.BitString 6)
    (SS.BitString 6 × SS.BitString 6 × SS.BitString 6) ℝ :=
  MainTheory.FiniteCubicTensorTrace.moment (vector W)

theorem positive (W : Encoder) : (M3 W).PosSemidef :=
  MainTheory.FiniteCubicTensorTrace.positive _

theorem trace_one (W : Encoder) : Matrix.trace (M3 W)=1 := by
  change Matrix.trace (MainTheory.FiniteCubicTensorTrace.moment (vector W))=1
  simpa using MainTheory.FiniteCubicTensorTrace.trace (vector W) 1 (norm_one W)

def factor : ℝ := (Fintype.card Index : ℝ)⁻¹/8

theorem factor_positive : 0 < factor := by
  unfold factor
  have hc : (0 : ℝ) < Fintype.card Index := by exact_mod_cast Fintype.card_pos
  positivity

theorem cubic_scale (W : Encoder) (g : Index)
    (t : SS.BitString 6 × SS.BitString 6 × SS.BitString 6) :
    tensor (vector W) g t=(scale : ℂ)^3*tensor (wave W) g t := by
  simp only [tensor, cubic, id_eq, vector, Pi.smul_apply, smul_eq_mul]
  ring

theorem gram_scale (W : Encoder) :
    realGram (tensor (vector W))=(1/8 : ℝ) • realGram (tensor (wave W)) := by
  ext t u
  simp only [realGram_apply, cubic_scale, Matrix.smul_apply, smul_eq_mul]
  have he (z v : ℂ) :
      (star ((scale : ℂ)^3*z)*((scale : ℂ)^3*v)).re=(1/8 : ℝ)*(star z*v).re := by
    have hs : (scale : ℂ)^3*(scale : ℂ)^3=(1/8 : ℂ) := by
      have hr : scale^3*scale^3=(1/8 : ℝ) := by
        rw [show scale^3*scale^3=(scale^2)^3 by ring, scale_squared]
        norm_num
      have h := congrArg (fun x : ℝ => (x : ℂ)) hr
      norm_num at h
      exact h
    simp only [star_mul, star_pow, Complex.star_def, Complex.conj_ofReal]
    rw [show (starRingEnd ℂ) z*(scale : ℂ)^3*((scale : ℂ)^3*v)=
      ((scale : ℂ)^3*(scale : ℂ)^3)*((starRingEnd ℂ) z*v) by ring, hs]
    simp
  simp_rw [he, ← Finset.mul_sum]

theorem normalized_gram (W : Encoder) :
    M3 W=factor • realGram (tensor (wave W)) := by
  rw [M3, MainTheory.FiniteCubicTensorTrace.moment, gram_scale, smul_smul]
  simp only [factor, div_eq_mul_inv, one_mul]

def coordinates (W : Encoder) : Fin 269 → ℝ :=
  fun c => factor*MainTheory.Orbit3CoordinateRealization.coordinates W c

theorem table_positive (W : Encoder) :
    (MainTheory.Orbit3CoordinateRealization.tableMatrix (coordinates W)).PosSemidef := by
  have he : MainTheory.Orbit3CoordinateRealization.tableMatrix (coordinates W)=
      factor • MainTheory.Orbit3CoordinateRealization.tableMatrix
        (MainTheory.Orbit3CoordinateRealization.coordinates W) := by
    ext i j
    simp only [MainTheory.Orbit3CoordinateRealization.tableMatrix,
      Matrix.smul_apply, smul_eq_mul, coordinates]
    split <;> simp
  rw [he]
  exact (MainTheory.Orbit3CoordinateRealization.tableMatrix_posSemidef W).smul
    (le_of_lt factor_positive)

end
end MainTheory.Orbit3NormalizedMoment
