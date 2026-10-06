import Orbit2.FrameKL

namespace Orbit2
open scoped BigOperators
open Orbit2.TensorPauli Orbit2.Quartic
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def spectatorOperatorG (p : Label 2) : Matrix SpectatorBits SpectatorBits GaussianInt :=
  fun x y => localG (p 0) (x 0) (y 0) * localG (p 1) (x 1) (y 1)

theorem spectator_operator_map (p : Label 2) :
    operator p = (spectatorOperatorG p).map GaussianInt.toComplex := by
  ext x y
  simp only [operator,tensor,Fin.prod_univ_succ,spectatorOperatorG,Matrix.map_apply,
    GaussianInt.toComplex_mul,localC]
  change (localG (p 0) (x 0) (y 0) : ℂ) * ((localG (p 1) (x 1) (y 1) : ℂ) * 1) = _
  simp

theorem spectator_spin_relation_G : ∀ p : Label 2,
    (∑ i, if p i=0 then 0 else 1 : ℕ) ≠ 1 →
    (spectatorOperatorG p).transpose * spectatorOperatorG (fun _ => 2) =
      spectatorOperatorG (fun _ => 2) * spectatorOperatorG p := by decide +kernel

noncomputable def spectatorSpin : Matrix SpectatorBits SpectatorBits ℂ := operator (fun _ => 2)

theorem spectator_spin_relation (p : Label 2)
    (hp : (∑ i, if p i=0 then 0 else 1 : ℕ) ≠ 1) :
    (operator p).transpose * spectatorSpin = spectatorSpin * operator p := by
  have h := congrArg (fun M => M.map GaussianInt.toComplex) (spectator_spin_relation_G p hp)
  simpa [Matrix.map_mul,Matrix.transpose_map,← spectator_operator_map,spectatorSpin] using h

theorem spin_symmetry_of_odd_traces (M : Matrix SpectatorBits SpectatorBits ℂ)
    (h : ∀ p : Label 2, (∑ i, if p i=0 then 0 else 1 : ℕ)=1 →
      Matrix.trace ((operator p).transpose * M)=0) :
    M * spectatorSpin = spectatorSpin * M.transpose := by
  conv_lhs => rw [matrix_reconstruction_transpose M]
  conv_rhs => rw [matrix_reconstruction_transpose M]
  simp only [Matrix.sum_mul,Matrix.transpose_sum,Matrix.transpose_smul,
    Matrix.transpose_transpose,Matrix.mul_sum,Matrix.smul_mul,Matrix.mul_smul]
  apply Finset.sum_congr rfl
  intro p _
  by_cases hp : (∑ i, if p i=0 then 0 else 1 : ℕ)=1
  · simp [tau,h p hp]
  · rw [spectator_spin_relation p hp]

/-- The required symmetry is derived for every physical active compression
block; it is not an extra hypothesis on the encoder. -/
theorem Encoder.frame_spin_symmetry (V : Encoder) (j k : Fin 2) (i a : Fin 4) (ha : a≠0) :
    ((V.schmidtFrame j).conjTranspose * operator (single i a) * V.schmidtFrame k) * spectatorSpin =
      spectatorSpin * ((V.schmidtFrame j).conjTranspose * operator (single i a) * V.schmidtFrame k).transpose := by
  apply spin_symmetry_of_odd_traces
  intro p hp
  exact V.frame_odd_trace_zero j k p i a ha hp

end Orbit2
