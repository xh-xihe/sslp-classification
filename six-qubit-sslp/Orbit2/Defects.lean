import Orbit2.Frames

namespace Orbit2.Defects
open Orbit2.TensorPauli Orbit2.Frames

abbrev Active := Fin 4 → Fin 2
abbrev ActiveMatrix := Matrix Active Active ℂ

noncomputable def normMass (T : ActiveMatrix) : ℂ := tau (T * T.conjTranspose)
noncomputable def correlation (T E : ActiveMatrix) : ℂ := tau (E * T * T.conjTranspose)
noncomputable def projectionDefect (T : ActiveMatrix) : ActiveMatrix :=
  T * T.conjTranspose * T - (2 * normMass T) • T
noncomputable def compressionDefect (T σ : ActiveMatrix) : ActiveMatrix :=
  T * T.conjTranspose * σ * T - T * σ * T.conjTranspose * T -
    (4 * correlation T σ) • T

variable (Q : Matrix Active LogicalFrame ℂ) (hQ : Q.conjTranspose * Q = 1)
variable (S : ActiveMatrix) (hS : S.conjTranspose = S) (hS2 : S*S = 1)
include hQ hS hS2

theorem frame_normMass : normMass (t Q S) = 1/2 := by
  unfold normMass tau
  rw [t_left Q hQ S hS hS2, pi_trace Q hQ]
  norm_num

theorem frame_projectionDefect : projectionDefect (t Q S) = 0 := by
  unfold projectionDefect
  rw [t_cubic Q hQ S hS hS2, frame_normMass Q hQ S hS hS2]
  norm_num

variable (σ : ActiveMatrix) (μ : ℂ)
variable (hh : (Q.conjTranspose * σ * Q) * J + J * (Q.conjTranspose * σ * Q).transpose =
  (2*μ) • J)
include hh

theorem frame_correlation : correlation (t Q S) σ = μ/2 := by
  unfold correlation tau
  rw [Matrix.mul_assoc σ, t_left Q hQ S hS hS2, pi_sigma_trace Q hQ σ μ hh]
  norm_num
  ring

theorem frame_compressionDefect (hspin : S * σ.transpose * S = -σ) :
    compressionDefect (t Q S) σ = 0 := by
  have he := t_commonJ Q hQ S σ μ hS2 hspin (lift_commonJ Q hQ σ μ hh)
  unfold compressionDefect
  rw [frame_correlation Q hQ S hS hS2 σ μ hh]
  have hleft : t Q S * (t Q S).conjTranspose * σ * t Q S = pi Q * σ * t Q S := by
    rw [t_left Q hQ S hS hS2]
  have hright : t Q S * σ * (t Q S).conjTranspose * t Q S =
      t Q S * σ * (S * (pi Q).transpose * S) := by
    rw [Matrix.mul_assoc, t_right Q hQ S hS]
  rw [hleft, hright, he]
  have hm : 4 * (μ/2) = 2*μ := by ring
  rw [hm, sub_self]

end Orbit2.Defects
