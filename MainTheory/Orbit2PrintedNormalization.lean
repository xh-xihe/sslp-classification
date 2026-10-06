import MainTheory.Orbit2PhysicalMarginals
import MainTheory.CodeSpec

/-! The SI's normalized purification and literal conjugated spectator basis. -/

namespace MainTheory.Orbit2PrintedNormalization
noncomputable section
open Orbit2 Orbit2.TensorPauli
open scoped BigOperators

def purification (V : Encoder) : SS.State 7 ℂ := magicScale • V.purification

theorem purification_formula (V : Encoder) (b : Bool) (x : SS.BitString 6) :
    purification V (Fin.cons b x)=magicScale*V.psi (if b then 1 else 0) x := rfl

theorem purification_norm (V : Encoder) :
    SS.innerC (purification V) (purification V)=1 := by
  rw [purification, MainTheory.CodeSpec.innerC_smul_left,
    MainTheory.CodeSpec.innerC_smul_right, magicScale_star, V.purification_norm,
    ← mul_assoc, magicScale_square]

theorem expectation (V : Encoder) (P : SS.PauliString 7) :
    SS.innerC (purification V) (SS.pauliAct P (purification V))=
      (1/2 : ℂ)*SS.innerC V.purification (SS.pauliAct P V.purification) := by
  rw [purification, MainTheory.CodeSpec.pauliAct_smul,
    MainTheory.CodeSpec.innerC_smul_left, MainTheory.CodeSpec.innerC_smul_right,
    magicScale_star, ← mul_assoc]
  have h : magicScale*magicScale=(1/2 : ℂ) := by
    linear_combination magicScale_square/2
  rw [h]

theorem mass (V : Encoder) (P : SS.PauliString 7) :
    Complex.normSq (SS.innerC (purification V) (SS.pauliAct P (purification V)))=
      V.purificationMass P := by
  rw [expectation, Complex.normSq_mul]
  norm_num [Encoder.purificationMass, Complex.normSq_div]
  ring

theorem magic_fixed : spectatorSpin*magicBasis.map star=magicBasis := by
  rw [← magicBasis_spin, Matrix.mul_assoc, magicBasis_transpose_isometry,
    Matrix.mul_one]

theorem conjugate_basis_isometry :
    (magicBasis.map star).conjTranspose*magicBasis.map star=1 := by
  have h := congrArg (fun M => M.map (starRingEnd ℂ)) magicBasis_isometry
  dsimp only at h
  rw [Matrix.map_mul] at h
  change magicBasis.conjTranspose.map star*magicBasis.map star=
    (1 : Matrix (Fin 4) (Fin 4) ℂ).map star at h
  have hc : magicBasis.conjTranspose.map star=(magicBasis.map star).conjTranspose := by
    ext a b
    simp [Matrix.map_apply, Matrix.conjTranspose_apply]
  have hi : (1 : Matrix (Fin 4) (Fin 4) ℂ).map star=1 := by
    ext a b
    simp [Matrix.map_apply, Matrix.one_apply]
  rwa [hc,hi] at h

theorem conjugate_basis_unitary :
    magicBasis.map star*(magicBasis.map star).conjTranspose=1 := by
  have h := congrArg (fun M => M.map (starRingEnd ℂ)) magicBasis_unitary
  dsimp only at h
  rw [Matrix.map_mul] at h
  change magicBasis.map star*magicBasis.conjTranspose.map star=
    (1 : Matrix SpectatorBits SpectatorBits ℂ).map star at h
  have hc : magicBasis.conjTranspose.map star=(magicBasis.map star).conjTranspose := by
    ext a b
    simp [Matrix.map_apply, Matrix.conjTranspose_apply]
  have hi : (1 : Matrix SpectatorBits SpectatorBits ℂ).map star=1 := by
    ext a b
    simp [Matrix.map_apply, Matrix.one_apply]
  rwa [hc,hi] at h

def frame (V : Encoder) (j : Fin 2) : Matrix ActiveBits (Fin 4) ℂ :=
  V.schmidtFrame j*magicBasis.map star

theorem frame_cross (V : Encoder) (j k : Fin 2) :
    (frame V j).conjTranspose*frame V k=if j=k then 1 else 0 := by
  rw [frame, frame, Matrix.conjTranspose_mul]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (V.schmidtFrame j).conjTranspose,
    V.schmidtFrame_cross]
  split_ifs
  · simp only [Matrix.one_mul]
    exact conjugate_basis_isometry
  · simp

theorem frame_projection (V : Encoder) (j : Fin 2) :
    frame V j*(frame V j).conjTranspose=
      MainTheory.Orbit2PhysicalMarginals.parityProjection V j := by
  rw [frame, Matrix.conjTranspose_mul, Matrix.mul_assoc,
    ← Matrix.mul_assoc (magicBasis.map star), conjugate_basis_unitary,
    Matrix.one_mul]
  rfl

def Q (V : Encoder) : Matrix ActiveBits (Fin 4 ⊕ Fin 4) ℂ :=
  Matrix.fromCols (frame V 0) (frame V 1)

theorem Q_isometry (V : Encoder) : (Q V).conjTranspose*Q V=1 := by
  ext a b
  rcases a with a|a <;> rcases b with b|b
  · have h := congrArg (fun M => M a b) (frame_cross V 0 0)
    simpa [Q, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply] using h
  · have h := congrArg (fun M => M a b) (frame_cross V 0 1)
    simpa [Q, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply] using h
  · have h := congrArg (fun M => M a b) (frame_cross V 1 0)
    simpa [Q, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply] using h
  · have h := congrArg (fun M => M a b) (frame_cross V 1 1)
    simpa [Q, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply] using h

theorem Q_projector (V : Encoder) : Q V*(Q V).conjTranspose=V.activeProjector := by
  rw [Q, Matrix.conjTranspose_fromCols_eq_fromRows_conjTranspose,
    Matrix.fromCols_mul_fromRows, frame_projection, frame_projection,
    V.activeProjector_frames]
  rfl

end
end MainTheory.Orbit2PrintedNormalization
