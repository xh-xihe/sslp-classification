import Orbit2.FrameSpin

namespace Orbit2
open scoped BigOperators
open Orbit2.TensorPauli
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

theorem gaussian_two_cast : GaussianInt.toComplex (2 : GaussianInt) = (2 : ℂ) := by
  norm_num [GaussianInt.toComplex_def]

def magicTableG : Matrix (Fin 4) (Fin 4) GaussianInt :=
  ![![⟨0,1⟩,1,0,0],![0,0,1,⟨0,1⟩],![0,0,1,⟨0,-1⟩],![⟨0,1⟩,-1,0,0]]

def magicG : Matrix SpectatorBits (Fin 4) GaussianInt :=
  fun b j => magicTableG (spectatorIndex.symm b) j

theorem magicG_isometry : magicG.conjTranspose * magicG = (2 : GaussianInt) • 1 := by decide +kernel
theorem magicG_unitary : magicG * magicG.conjTranspose = (2 : GaussianInt) • 1 := by decide +kernel
theorem magicG_spin : magicG * magicG.transpose =
    (2 : GaussianInt) • spectatorOperatorG (fun _ => 2) := by decide +kernel

noncomputable def magicUnscaled : Matrix SpectatorBits (Fin 4) ℂ := magicG.map GaussianInt.toComplex
noncomputable def magicScale : ℂ := ((Real.sqrt 2)⁻¹ : ℝ)
noncomputable def magicBasis : Matrix SpectatorBits (Fin 4) ℂ := magicScale • magicUnscaled

theorem magicUnscaled_isometry : magicUnscaled.conjTranspose * magicUnscaled = (2 : ℂ) • 1 := by
  have h := congrArg (fun M => M.map GaussianInt.toComplex) magicG_isometry
  ext j k
  have hjk := congrFun (congrFun h j) k
  simpa only [magicUnscaled,Matrix.map_apply,Matrix.mul_apply,Matrix.conjTranspose_apply,
    map_sum,GaussianInt.toComplex_mul,GaussianInt.toComplex_star,Matrix.smul_apply,
    smul_eq_mul,Matrix.one_apply,starRingEnd_apply,gaussian_two_cast,apply_ite,map_one,map_zero] using hjk

theorem magicScale_square : magicScale * magicScale * 2 = 1 := by
  have h : ((Real.sqrt 2)⁻¹)^2 * 2 = (1 : ℝ) := by
    rw [inv_pow,Real.sq_sqrt (by norm_num)]
    norm_num
  unfold magicScale
  exact_mod_cast (show ((Real.sqrt 2)⁻¹) * ((Real.sqrt 2)⁻¹) * 2 = (1 : ℝ) by simpa [pow_two] using h)

theorem magicScale_star : star magicScale = magicScale := by
  simp [magicScale]

theorem magicBasis_isometry : magicBasis.conjTranspose * magicBasis = 1 := by
  simp only [magicBasis,Matrix.conjTranspose_smul,magicScale_star,
    Matrix.smul_mul,Matrix.mul_smul,smul_smul,magicUnscaled_isometry]
  rw [← mul_assoc,magicScale_square,one_smul]

theorem magicUnscaled_unitary : magicUnscaled * magicUnscaled.conjTranspose = (2 : ℂ) • 1 := by
  have h := congrArg (fun M => M.map GaussianInt.toComplex) magicG_unitary
  ext j k
  have hjk := congrFun (congrFun h j) k
  simpa only [magicUnscaled,Matrix.map_apply,Matrix.mul_apply,Matrix.conjTranspose_apply,
    map_sum,GaussianInt.toComplex_mul,GaussianInt.toComplex_star,Matrix.smul_apply,
    smul_eq_mul,Matrix.one_apply,starRingEnd_apply,gaussian_two_cast,apply_ite,map_one,map_zero] using hjk

theorem magicUnscaled_spin : magicUnscaled * magicUnscaled.transpose = (2 : ℂ) • spectatorSpin := by
  have h := congrArg (fun M => M.map GaussianInt.toComplex) magicG_spin
  ext j k
  have hjk := congrFun (congrFun h j) k
  simpa only [magicUnscaled,Matrix.map_apply,Matrix.mul_apply,Matrix.transpose_apply,
    map_sum,GaussianInt.toComplex_mul,Matrix.smul_apply,smul_eq_mul,
    spectatorSpin,spectator_operator_map,gaussian_two_cast] using hjk

theorem magicBasis_unitary : magicBasis * magicBasis.conjTranspose = 1 := by
  simp only [magicBasis,Matrix.conjTranspose_smul,magicScale_star,
    Matrix.smul_mul,Matrix.mul_smul,smul_smul,magicUnscaled_unitary]
  rw [← mul_assoc,magicScale_square,one_smul]

theorem magicBasis_spin : magicBasis * magicBasis.transpose = spectatorSpin := by
  simp only [magicBasis,Matrix.transpose_smul,
    Matrix.smul_mul,Matrix.mul_smul,smul_smul,magicUnscaled_spin]
  rw [← mul_assoc,magicScale_square,one_smul]

theorem magicBasis_transpose_isometry : magicBasis.transpose * magicBasis.map star = 1 := by
  have h := congrArg Matrix.transpose magicBasis_isometry
  simpa [Matrix.transpose_mul,Matrix.transpose_conjTranspose] using h

/-- Spin symmetry becomes ordinary transpose symmetry in the magic basis. -/
theorem magicBasis_compression_symmetric (H : Matrix SpectatorBits SpectatorBits ℂ)
    (h : H * spectatorSpin = spectatorSpin * H.transpose) :
    (magicBasis.conjTranspose * H * magicBasis).transpose =
      magicBasis.conjTranspose * H * magicBasis := by
  rw [← magicBasis_spin] at h
  have he := congrArg (fun A => magicBasis.conjTranspose * A * magicBasis.map star) h
  dsimp only at he
  have hl : magicBasis.conjTranspose * (H * (magicBasis * magicBasis.transpose)) * magicBasis.map star =
      magicBasis.conjTranspose * H * magicBasis := by
    simp only [Matrix.mul_assoc]
    rw [magicBasis_transpose_isometry,Matrix.mul_one]
  have hr : magicBasis.conjTranspose * (magicBasis * magicBasis.transpose * H.transpose) * magicBasis.map star =
      (magicBasis.conjTranspose * H * magicBasis).transpose := by
    simp only [Matrix.transpose_mul]
    change magicBasis.conjTranspose * (magicBasis * magicBasis.transpose * H.transpose) * magicBasis.map star =
      magicBasis.transpose * (H.transpose * magicBasis.map star)
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc magicBasis.conjTranspose magicBasis,magicBasis_isometry,Matrix.one_mul]
  rw [hl,hr] at he
  exact he.symm

end Orbit2
