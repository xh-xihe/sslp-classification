import Orbit2.MatrixSteps
import Orbit2.TensorPauli

namespace Orbit2.Frames
open Matrix
open scoped BigOperators

abbrev LogicalFrame := Sum (Fin 4) (Fin 4)

def J : Matrix LogicalFrame LogicalFrame ℂ := fromBlocks 0 1 (-1) 0

theorem J_transpose : J.transpose = -J := by
  ext i j
  rcases i with i|i <;> rcases j with j|j <;> simp [J, Matrix.transpose_apply, Matrix.one_apply, eq_comm]

theorem J_conjTranspose : J.conjTranspose = -J := by
  ext i j
  rcases i with i|i <;> rcases j with j|j <;> simp [J, Matrix.conjTranspose_apply, Matrix.one_apply, eq_comm]

theorem J_unitary : J * J.conjTranspose = 1 ∧ J.conjTranspose * J = 1 := by
  simp only [J, fromBlocks_conjTranspose, conjTranspose_zero, conjTranspose_one,
    conjTranspose_neg, fromBlocks_multiply]
  constructor <;> ext i j <;> rcases i with i|i <;> rcases j with j|j <;> simp [Matrix.one_apply]

section Frame
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (Q : Matrix α LogicalFrame ℂ) (hQ : Q.conjTranspose * Q = 1)

/-- The rank-eight support projector and the common skew form, defined from Q. -/
noncomputable def pi : Matrix α α ℂ := Q * Q.conjTranspose

noncomputable def omega : Matrix α α ℂ := Q * J * Q.transpose

include hQ

theorem transpose_isometry : Q.transpose * Q.map star = 1 := by
  have h := congrArg Matrix.transpose hQ
  simpa [Matrix.transpose_mul, Matrix.transpose_conjTranspose] using h

theorem pi_idempotent : pi Q * pi Q = pi Q := by
  unfold pi
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc Q.conjTranspose, hQ, Matrix.one_mul]

theorem pi_hermitian : (pi Q).conjTranspose = pi Q := by simp [pi, Matrix.conjTranspose_mul]

theorem omega_skew : (omega Q).transpose = -omega Q := by
  simp [omega, Matrix.transpose_mul, J_transpose, Matrix.mul_assoc]

theorem omega_left : omega Q * (omega Q).conjTranspose = pi Q := by
  have ht := transpose_isometry Q hQ
  unfold omega pi
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_transpose]
  calc
    Q * J * Q.transpose * (Q.map star * (J.conjTranspose * Q.conjTranspose)) =
        Q * (J * (Q.transpose * Q.map star) * J.conjTranspose) * Q.conjTranspose := by
          simp only [Matrix.mul_assoc]
    _ = Q * Q.conjTranspose := by rw [ht, Matrix.mul_one, J_unitary.1, Matrix.mul_one]

theorem omega_right : (omega Q).conjTranspose * omega Q = (pi Q).transpose := by
  unfold omega pi
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_transpose,
    Matrix.transpose_mul, Matrix.transpose_conjTranspose]
  calc
    Q.map star * (J.conjTranspose * Q.conjTranspose) * (Q * J * Q.transpose) =
        Q.map star * (J.conjTranspose * (Q.conjTranspose * Q) * J) * Q.transpose := by
          simp only [Matrix.mul_assoc]
    _ = Q.map star * Q.transpose := by rw [hQ, Matrix.mul_one, J_unitary.2, Matrix.mul_one]

theorem pi_omega : pi Q * omega Q = omega Q := by
  unfold pi omega
  calc
    Q * Q.conjTranspose * (Q * J * Q.transpose) =
        Q * (Q.conjTranspose * Q) * J * Q.transpose := by simp only [Matrix.mul_assoc]
    _ = Q * J * Q.transpose := by rw [hQ, Matrix.mul_one]

theorem pi_trace : Matrix.trace (pi Q) = 8 := by
  rw [pi, Matrix.trace_mul_comm, hQ]
  norm_num [Matrix.trace, Matrix.diag, Fintype.sum_sum_type]

/-- The common compression equation lifts to the ambient support projector. -/
theorem lift_commonJ (σ : Matrix α α ℂ) (μ : ℂ)
    (hh : (Q.conjTranspose * σ * Q) * J + J * (Q.conjTranspose * σ * Q).transpose =
      (2*μ) • J) :
    pi Q * σ * omega Q + omega Q * σ.transpose * (pi Q).transpose = (2*μ) • omega Q := by
  have h := congrArg (fun H => Q * H * Q.transpose) hh
  simpa [pi, omega, Matrix.mul_add, Matrix.add_mul, Matrix.transpose_mul,
    Matrix.transpose_conjTranspose, Matrix.mul_assoc, Matrix.mul_smul,
    Matrix.smul_mul] using h

omit hQ in
/-- The compression equation fixes its trace without any additional hypothesis. -/
theorem commonJ_trace (H : Matrix LogicalFrame LogicalFrame ℂ) (μ : ℂ)
    (hh : H * J + J * H.transpose = (2*μ) • J) : Matrix.trace H = 8*μ := by
  have he := congrArg (fun A => Matrix.trace (A * J.conjTranspose)) hh
  have ht : Matrix.trace (J * H.transpose * J.conjTranspose) = Matrix.trace H := by
    rw [Matrix.trace_mul_cycle, J_unitary.2, Matrix.one_mul, Matrix.trace_transpose]
  have hi : Matrix.trace (1 : Matrix LogicalFrame LogicalFrame ℂ) = 8 := by
    norm_num [Matrix.trace, Matrix.diag, Fintype.sum_sum_type]
  simp only [Matrix.add_mul, Matrix.trace_add, Matrix.smul_mul] at he
  rw [Matrix.mul_assoc, J_unitary.1, Matrix.mul_one, ht] at he
  simp only [Matrix.trace_smul, smul_eq_mul, hi] at he
  linear_combination he / 2

theorem pi_sigma_trace (σ : Matrix α α ℂ) (μ : ℂ)
    (hh : (Q.conjTranspose * σ * Q) * J + J * (Q.conjTranspose * σ * Q).transpose =
      (2*μ) • J) : Matrix.trace (σ * pi Q) = 8*μ := by
  have ht := commonJ_trace (Q.conjTranspose * σ * Q) μ hh
  rw [pi, ← Matrix.mul_assoc, Matrix.trace_mul_comm, ← Matrix.mul_assoc]
  exact ht

/-- The right multiplication by the fixed spin flip. -/
noncomputable def t (S : Matrix α α ℂ) : Matrix α α ℂ := omega Q * S

theorem t_left (S : Matrix α α ℂ) (hS : S.conjTranspose = S) (hS2 : S*S = 1) :
    t Q S * (t Q S).conjTranspose = pi Q := by
  unfold t
  rw [Matrix.conjTranspose_mul, hS]
  calc
    omega Q * S * (S * (omega Q).conjTranspose) =
        omega Q * (S*S) * (omega Q).conjTranspose := by simp only [Matrix.mul_assoc]
    _ = pi Q := by rw [hS2, Matrix.mul_one, omega_left Q hQ]

theorem t_right (S : Matrix α α ℂ) (hS : S.conjTranspose = S) :
    (t Q S).conjTranspose * t Q S = S * (pi Q).transpose * S := by
  unfold t
  rw [Matrix.conjTranspose_mul, hS]
  calc
    S * (omega Q).conjTranspose * (omega Q * S) =
        S * ((omega Q).conjTranspose * omega Q) * S := by simp only [Matrix.mul_assoc]
    _ = S * (pi Q).transpose * S := by rw [omega_right Q hQ]

theorem t_cubic (S : Matrix α α ℂ) (hS : S.conjTranspose = S) (hS2 : S*S = 1) :
    t Q S * (t Q S).conjTranspose * t Q S = t Q S := by
  rw [t_left Q hQ S hS hS2, t, ← Matrix.mul_assoc, pi_omega Q hQ]

theorem t_spin_skew (S : Matrix α α ℂ) (hST : S.transpose = S) (hS2 : S*S = 1) :
    S * (t Q S).transpose * S = -t Q S := by
  unfold t
  rw [Matrix.transpose_mul, hST, omega_skew Q hQ]
  calc
    S * (S * -omega Q) * S = (S*S) * -omega Q * S := by simp only [Matrix.mul_assoc]
    _ = -(omega Q * S) := by rw [hS2, Matrix.one_mul, Matrix.neg_mul]

theorem t_commonJ (S σ : Matrix α α ℂ) (μ : ℂ) (hS2 : S*S = 1)
    (hspin : S * σ.transpose * S = -σ)
    (hh : pi Q * σ * omega Q + omega Q * σ.transpose * (pi Q).transpose =
      (2*μ) • omega Q) :
    pi Q * σ * t Q S - t Q S * σ * (S * (pi Q).transpose * S) = (2*μ) • t Q S := by
  have hsign : S * σ * S = -σ.transpose := by
    have h := congrArg (fun A => S * A * S) hspin
    have h' : σ.transpose = -(S * σ * S) := by
      simpa [Matrix.mul_assoc, ← Matrix.mul_assoc S S, hS2] using h
    have hn := congrArg Neg.neg h'
    simpa using hn.symm
  have h := congrArg (fun A => A*S) hh
  have hc : t Q S * σ * (S * (pi Q).transpose * S) =
      -(omega Q * σ.transpose * (pi Q).transpose * S) := by
    unfold t
    calc
      omega Q * S * σ * (S * (pi Q).transpose * S) =
          omega Q * (S * σ * S) * (pi Q).transpose * S := by simp only [Matrix.mul_assoc]
      _ = -(omega Q * σ.transpose * (pi Q).transpose * S) := by rw [hsign]; simp
  rw [hc, sub_neg_eq_add]
  simpa [t, Matrix.add_mul, Matrix.smul_mul, Matrix.mul_assoc] using h

end Frame
end Orbit2.Frames
