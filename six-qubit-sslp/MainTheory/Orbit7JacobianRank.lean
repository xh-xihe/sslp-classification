import MainTheory.Orbit7Jacobian

set_option autoImplicit false

namespace MainTheory.Orbit7Jacobian

def selectedColumns : Fin 5 → Fin 10 := ![0,1,2,4,6]

noncomputable def normalPoint (tau omega : ℂ) : Fin 10 → ℂ :=
  ![1,1,1,1,tau,tau*omega,tau*omega^2,tau*omega^2,tau*omega,tau]

theorem selected_minor (x : MainTheory.Orbit7MatchingDisplays.Edge → ℂ) (tau omega : ℂ)
    (hx : ∀ j : Fin 10, x (edges j) = normalPoint tau omega j) :
    (jacobian x).submatrix (Equiv.refl (Fin 5)) selectedColumns = minor tau omega := by
  have h0 := hx 0
  have h1 := hx 1
  have h2 := hx 2
  have h3 := hx 3
  have h4 := hx 4
  have h5 := hx 5
  have h6 := hx 6
  have h7 := hx 7
  have h8 := hx 8
  have h9 := hx 9
  change x (0,1)=1 at h0
  change x (0,2)=1 at h1
  change x (0,3)=1 at h2
  change x (0,4)=1 at h3
  change x (1,2)=tau at h4
  change x (1,3)=tau*omega at h5
  change x (1,4)=tau*omega^2 at h6
  change x (2,3)=tau*omega^2 at h7
  change x (2,4)=tau*omega at h8
  change x (3,4)=tau at h9
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [jacobian,selectedColumns,minor,Matrix.submatrix_apply,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]

theorem minor_nonzero (tau omega : ℂ) (ht : tau ≠ 0) (hw : 1+omega+omega^2=0) :
    (minor tau omega).det ≠ 0 := by
  have hw2 : omega+2 ≠ 0 := by
    intro hz
    have hwv : omega = -2 := by linear_combination hz
    rw [hwv] at hw
    norm_num at hw
  rw [minor_determinant tau omega hw]
  exact mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ ht)) hw2

theorem jacobian_rank_five (x : MainTheory.Orbit7MatchingDisplays.Edge → ℂ) (tau omega : ℂ)
    (hx : ∀ j : Fin 10, x (edges j) = normalPoint tau omega j)
    (ht : tau ≠ 0) (hw : 1+omega+omega^2=0) : (jacobian x).rank = 5 := by
  have hunit : IsUnit (minor tau omega) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr (minor_nonzero tau omega ht hw))
  have hr : (minor tau omega).rank = 5 := by simpa using Matrix.rank_of_isUnit _ hunit
  have hlo := Matrix.rank_submatrix_le selectedColumns (Equiv.refl (Fin 5)) (jacobian x).transpose
  have he : (jacobian x).transpose.submatrix selectedColumns (Equiv.refl (Fin 5)) =
      ((jacobian x).submatrix (Equiv.refl (Fin 5)) selectedColumns).transpose := rfl
  rw [he,Matrix.rank_transpose,Matrix.rank_transpose,selected_minor x tau omega hx,hr] at hlo
  have hhi : (jacobian x).rank ≤ 5 := by simpa using Matrix.rank_le_card_height (jacobian x)
  exact Nat.le_antisymm hhi hlo

end MainTheory.Orbit7Jacobian
