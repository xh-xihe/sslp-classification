import Orbit2.PhysicalPauliSupport

namespace Orbit2.Quartic
open scoped BigOperators
open Orbit2.TensorPauli
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

theorem spinSign_basis : ∀ i : Fin 32, spinSign (basis i)=-1 := by decide +kernel

theorem spin_transform_mul (A B : Defects.ActiveMatrix) :
    activeSpin * (A*B).transpose * activeSpin =
      (activeSpin * B.transpose * activeSpin) * (activeSpin * A.transpose * activeSpin) := by
  rw [Matrix.transpose_mul]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc activeSpin activeSpin,activeSpin_square,Matrix.one_mul]

theorem phase_spin_reality (u v : Fin 32) :
    star (phase (basis u) (basis v) : ℂ) =
      (spinSign (product (basis u) (basis v)) : ℂ) * (phase (basis u) (basis v) : ℂ) := by
  have hs : activeSpin * (operator (basis u) * operator (basis v)).transpose * activeSpin =
      operator (basis v) * operator (basis u) := by
    rw [spin_transform_mul,activeSpin_operator,activeSpin_operator,spinSign_basis,spinSign_basis]
    simp
  have hr : operator (basis v) * operator (basis u) =
      star (phase (basis u) (basis v) : ℂ) • operator (product (basis u) (basis v)) := by
    have h := congrArg Matrix.conjTranspose (operator_mul (basis u) (basis v))
    simpa [Matrix.conjTranspose_mul,Matrix.conjTranspose_smul,operator_hermitian] using h
  rw [operator_mul,Matrix.transpose_smul,Matrix.mul_smul,Matrix.smul_mul,activeSpin_operator,
    smul_smul,hr] at hs
  have h := congrArg (fun M => tau (M * operator (product (basis u) (basis v)))) hs
  simp only [Matrix.smul_mul,tau_smul,tau_operator_pair,if_true,mul_one] at h
  simpa [mul_comm] using h.symm

theorem spinSign_square (p : Label 4) : (spinSign p : ℂ) * (spinSign p : ℂ)=1 := by
  have h : ∀ a : Fin 4, (if a=0 then (1 : ℤ) else -1) * (if a=0 then (1 : ℤ) else -1)=1 := by
    intro a; split_ifs <;> norm_num
  have hr : spinSign p * spinSign p=1 := by
    simp only [spinSign,← Finset.prod_mul_distrib,h,Finset.prod_const_one]
  exact_mod_cast hr

theorem phase_product_real (u v x y : Fin 32)
    (h : product (basis u) (basis v)=product (basis x) (basis y)) :
    star ((phase (basis u) (basis v) : ℂ) * (phase (basis x) (basis y) : ℂ)) =
      (phase (basis u) (basis v) : ℂ) * (phase (basis x) (basis y) : ℂ) := by
  rw [star_mul,phase_spin_reality,phase_spin_reality,← h]
  calc
    _ = ((spinSign (product (basis u) (basis v)) : ℂ) * (spinSign (product (basis u) (basis v)) : ℂ)) *
      ((phase (basis u) (basis v) : ℂ) * (phase (basis x) (basis y) : ℂ)) := by ring
    _ = _ := by rw [spinSign_square,one_mul]

theorem phase_product_im_zero (u v x y : Fin 32)
    (h : product (basis u) (basis v)=product (basis x) (basis y)) :
    (phase (basis u) (basis v) * phase (basis x) (basis y)).im=0 := by
  have hr := phase_product_real u v x y h
  have hc : (((phase (basis u) (basis v) * phase (basis x) (basis y) : GaussianInt) : ℂ)).im=0 := by
    rw [GaussianInt.toComplex_mul]
    exact Complex.conj_eq_iff_im.mp hr
  rw [← GaussianInt.intCast_im] at hc
  exact_mod_cast hc

theorem wordTrace_four_real (u v x y : Fin 32) :
    (wordTrace [basis u,basis v,basis x,basis y]).im=0 := by
  have ht : tau (operator (basis u) * operator (basis v) * operator (basis x) * operator (basis y)) =
      (phase (basis u) (basis v) : ℂ) * (phase (basis x) (basis y) : ℂ) *
        (if product (basis u) (basis v)=product (basis x) (basis y) then 1 else 0) := by
    rw [Matrix.mul_assoc _ (operator (basis x)),operator_mul,operator_mul,
      Matrix.smul_mul,Matrix.mul_smul,smul_smul,tau_smul,tau_operator_pair]
  have hw := wordTrace_correct [basis u,basis v,basis x,basis y]
  have he : wordOperator [basis u,basis v,basis x,basis y] =
      operator (basis u) * operator (basis v) * operator (basis x) * operator (basis y) := by
    simp [wordOperator]
  rw [he,ht] at hw
  have hr : star (wordTrace [basis u,basis v,basis x,basis y] : ℂ) =
      (wordTrace [basis u,basis v,basis x,basis y] : ℂ) := by
    rw [← hw]
    by_cases h : product (basis u) (basis v)=product (basis x) (basis y)
    · simp only [h,if_true,mul_one]
      exact phase_product_real u v x y h
    · simp [h]
  have hc := Complex.conj_eq_iff_im.mp hr
  rw [← GaussianInt.intCast_im] at hc
  exact_mod_cast hc

end Orbit2.Quartic
