import MainTheory.UnitarySpectral
import MainTheory.RealGate
import SS.HilbertKL
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# The state space as a Euclidean space

`SS.State n ℂ` is `BitString n → ℂ` with the repository's own inner
product `SS.innerC psi phi = ∑_s star (psi s) * phi s`.  That is exactly the
inner product of `EuclideanSpace ℂ (SS.BitString n)`, but the two are not
interchangeable at the instance level: the default `Pi` norm is the sup norm,
while `EuclideanSpace` is `PiLp 2`.

This file records the identification, so that the unitary spectral theorem can
be applied to operations on the state space.
-/

namespace MainTheory.StateEuclidean

open scoped ComplexConjugate

variable {n : ℕ}

/-- The state space seen as a Euclidean space; the underlying function is
unchanged. -/
def toEuclidean (psi : SS.State n ℂ) : EuclideanSpace ℂ (SS.BitString n) :=
  (WithLp.equiv 2 _).symm psi

/-- The inverse identification. -/
def ofEuclidean (psi : EuclideanSpace ℂ (SS.BitString n)) : SS.State n ℂ :=
  WithLp.equiv 2 _ psi

@[simp] theorem ofEuclidean_toEuclidean (psi : SS.State n ℂ) :
    ofEuclidean (toEuclidean psi) = psi := rfl

@[simp] theorem toEuclidean_ofEuclidean
    (psi : EuclideanSpace ℂ (SS.BitString n)) :
    toEuclidean (ofEuclidean psi) = psi := rfl

/-- **The repository inner product is the Euclidean one.** -/
theorem innerC_eq_inner (psi phi : SS.State n ℂ) :
    SS.innerC psi phi = inner ℂ (toEuclidean psi) (toEuclidean phi) := by
  rw [PiLp.inner_apply]
  simp only [SS.innerC, toEuclidean, RCLike.inner_apply]
  exact Finset.sum_congr rfl fun s _ => mul_comm _ _

/-! ## The real diagonal gate is an isometry -/

/-- Each diagonal entry of the real gate is a unit complex number. -/
theorem star_mul_self_realGate_factor (theta : Fin n → ℝ) (s : SS.BitString n) :
    star (Complex.exp (2 * (Real.pi : ℂ) * Complex.I
        * ((MainTheory.RealGate.angle theta s : ℝ) : ℂ)))
      * Complex.exp (2 * (Real.pi : ℂ) * Complex.I
        * ((MainTheory.RealGate.angle theta s : ℝ) : ℂ)) = 1 := by
  rw [Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add]
  have hconj : (starRingEnd ℂ) (2 * (Real.pi : ℂ) * Complex.I
      * ((MainTheory.RealGate.angle theta s : ℝ) : ℂ))
      = -(2 * (Real.pi : ℂ) * Complex.I
        * ((MainTheory.RealGate.angle theta s : ℝ) : ℂ)) := by
    simp only [map_mul, Complex.conj_I, Complex.conj_ofReal, map_ofNat]
    ring
  rw [hconj, neg_add_cancel, Complex.exp_zero]

/-- **The real diagonal gate preserves the inner product.** -/
theorem innerC_realGate (theta : Fin n → ℝ) (psi phi : SS.State n ℂ) :
    SS.innerC (MainTheory.RealGate.realGate theta psi)
        (MainTheory.RealGate.realGate theta phi)
      = SS.innerC psi phi := by
  simp only [SS.innerC, MainTheory.RealGate.realGate]
  refine Finset.sum_congr rfl fun s _ => ?_
  set e := Complex.exp (2 * (Real.pi : ℂ) * Complex.I
    * ((MainTheory.RealGate.angle theta s : ℝ) : ℂ)) with he
  have h : star e * e = 1 := star_mul_self_realGate_factor theta s
  calc star (e * psi s) * (e * phi s)
      = (star e * e) * (star (psi s) * phi s) := by rw [star_mul']; ring
    _ = star (psi s) * phi s := by rw [h, one_mul]

end MainTheory.StateEuclidean
