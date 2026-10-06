import MainTheory.Orbit30NormalizedDeterminant
import MainTheory.Orbit30VertexScaling
set_option autoImplicit false
set_option maxHeartbeats 16000000
namespace MainTheory.Orbit30FullSupport
open MainTheory.Orbit30VertexScaling MainTheory.Orbit30NormalizedDeterminant
noncomputable section
theorem normalized_hafnians (c d f g h k : ℂ) (i : Fin 5) :
    hafnian (matrix c d f g h k) i=
      (![1+f*k+g*h,1+c*k+d*h,1+c*g+d*f,k+g+d,h+f+c] : Fin 5 → ℂ) i := by
  fin_cases i <;> simp +decide [hafnian,matrix]
theorem full_hafnian_det_ne_zero (A : Matrix (Fin 5) (Fin 5) ℂ)
    (hsym : ∀ i j,A i j=A j i) (hdiag : ∀ i,A i i=0)
    (h01 : A ⟨0,by decide⟩ ⟨1,by decide⟩≠0)
    (h02 : A ⟨0,by decide⟩ ⟨2,by decide⟩≠0)
    (h12 : A ⟨1,by decide⟩ ⟨2,by decide⟩≠0)
    (h34 : A ⟨3,by decide⟩ ⟨4,by decide⟩≠0)
    (hh : ∀ i,hafnian A i=0) : A.det≠0 := by
  obtain ⟨s,hs,he01,he02,he12,he34⟩ := four_edge_normalization
    (A ⟨0,by decide⟩ ⟨1,by decide⟩) (A ⟨0,by decide⟩ ⟨2,by decide⟩)
    (A ⟨1,by decide⟩ ⟨2,by decide⟩) (A ⟨3,by decide⟩ ⟨4,by decide⟩)
    h01 h02 h12 h34
  let B := scaled A s
  have hbSym : ∀ i j,B i j=B j i := by
    intro i j
    dsimp [B]
    rw [scaled_entry,scaled_entry,hsym i j]
    ring
  have hbDiag : ∀ i,B i i=0 := by
    intro i
    dsimp [B]
    rw [scaled_entry,hdiag i,mul_zero]
  have hb01 : B ⟨0,by decide⟩ ⟨1,by decide⟩=1 := by simpa only [B,scaled_entry] using he01
  have hb02 : B ⟨0,by decide⟩ ⟨2,by decide⟩=1 := by simpa only [B,scaled_entry] using he02
  have hb12 : B ⟨1,by decide⟩ ⟨2,by decide⟩=1 := by simpa only [B,scaled_entry] using he12
  have hb34 : B ⟨3,by decide⟩ ⟨4,by decide⟩=1 := by simpa only [B,scaled_entry] using he34
  have he : B=matrix (B ⟨0,by decide⟩ ⟨3,by decide⟩) (B ⟨0,by decide⟩ ⟨4,by decide⟩) (B ⟨1,by decide⟩ ⟨3,by decide⟩) (B ⟨1,by decide⟩ ⟨4,by decide⟩) (B ⟨2,by decide⟩ ⟨3,by decide⟩) (B ⟨2,by decide⟩ ⟨4,by decide⟩) := by
    ext i j
    fin_cases i <;> fin_cases j
    · change B ⟨0,by decide⟩ ⟨0,by decide⟩=0
      exact hbDiag ⟨0,by decide⟩
    · change B ⟨0,by decide⟩ ⟨1,by decide⟩=1
      exact hb01
    · change B ⟨0,by decide⟩ ⟨2,by decide⟩=1
      exact hb02
    · change B ⟨0,by decide⟩ ⟨3,by decide⟩=B ⟨0,by decide⟩ ⟨3,by decide⟩
      rfl
    · change B ⟨0,by decide⟩ ⟨4,by decide⟩=B ⟨0,by decide⟩ ⟨4,by decide⟩
      rfl
    · change B ⟨1,by decide⟩ ⟨0,by decide⟩=1
      exact (hbSym ⟨1,by decide⟩ ⟨0,by decide⟩).trans hb01
    · change B ⟨1,by decide⟩ ⟨1,by decide⟩=0
      exact hbDiag ⟨1,by decide⟩
    · change B ⟨1,by decide⟩ ⟨2,by decide⟩=1
      exact hb12
    · change B ⟨1,by decide⟩ ⟨3,by decide⟩=B ⟨1,by decide⟩ ⟨3,by decide⟩
      rfl
    · change B ⟨1,by decide⟩ ⟨4,by decide⟩=B ⟨1,by decide⟩ ⟨4,by decide⟩
      rfl
    · change B ⟨2,by decide⟩ ⟨0,by decide⟩=1
      exact (hbSym ⟨2,by decide⟩ ⟨0,by decide⟩).trans hb02
    · change B ⟨2,by decide⟩ ⟨1,by decide⟩=1
      exact (hbSym ⟨2,by decide⟩ ⟨1,by decide⟩).trans hb12
    · change B ⟨2,by decide⟩ ⟨2,by decide⟩=0
      exact hbDiag ⟨2,by decide⟩
    · change B ⟨2,by decide⟩ ⟨3,by decide⟩=B ⟨2,by decide⟩ ⟨3,by decide⟩
      rfl
    · change B ⟨2,by decide⟩ ⟨4,by decide⟩=B ⟨2,by decide⟩ ⟨4,by decide⟩
      rfl
    · change B ⟨3,by decide⟩ ⟨0,by decide⟩=B ⟨0,by decide⟩ ⟨3,by decide⟩
      exact hbSym ⟨3,by decide⟩ ⟨0,by decide⟩
    · change B ⟨3,by decide⟩ ⟨1,by decide⟩=B ⟨1,by decide⟩ ⟨3,by decide⟩
      exact hbSym ⟨3,by decide⟩ ⟨1,by decide⟩
    · change B ⟨3,by decide⟩ ⟨2,by decide⟩=B ⟨2,by decide⟩ ⟨3,by decide⟩
      exact hbSym ⟨3,by decide⟩ ⟨2,by decide⟩
    · change B ⟨3,by decide⟩ ⟨3,by decide⟩=0
      exact hbDiag ⟨3,by decide⟩
    · change B ⟨3,by decide⟩ ⟨4,by decide⟩=1
      exact hb34
    · change B ⟨4,by decide⟩ ⟨0,by decide⟩=B ⟨0,by decide⟩ ⟨4,by decide⟩
      exact hbSym ⟨4,by decide⟩ ⟨0,by decide⟩
    · change B ⟨4,by decide⟩ ⟨1,by decide⟩=B ⟨1,by decide⟩ ⟨4,by decide⟩
      exact hbSym ⟨4,by decide⟩ ⟨1,by decide⟩
    · change B ⟨4,by decide⟩ ⟨2,by decide⟩=B ⟨2,by decide⟩ ⟨4,by decide⟩
      exact hbSym ⟨4,by decide⟩ ⟨2,by decide⟩
    · change B ⟨4,by decide⟩ ⟨3,by decide⟩=1
      exact (hbSym ⟨4,by decide⟩ ⟨3,by decide⟩).trans hb34
    · change B ⟨4,by decide⟩ ⟨4,by decide⟩=0
      exact hbDiag ⟨4,by decide⟩
  have hhB : ∀ i,hafnian (matrix (B ⟨0,by decide⟩ ⟨3,by decide⟩) (B ⟨0,by decide⟩ ⟨4,by decide⟩) (B ⟨1,by decide⟩ ⟨3,by decide⟩) (B ⟨1,by decide⟩ ⟨4,by decide⟩) (B ⟨2,by decide⟩ ⟨3,by decide⟩) (B ⟨2,by decide⟩ ⟨4,by decide⟩)) i=0 := by
    rw [← he]
    exact preserves_hafnians A s hh
  have hh0 := hhB ⟨0,by decide⟩
  rw [normalized_hafnians] at hh0
  have hh1 := hhB ⟨1,by decide⟩
  rw [normalized_hafnians] at hh1
  have hh2 := hhB ⟨2,by decide⟩
  rw [normalized_hafnians] at hh2
  have hh3 := hhB ⟨3,by decide⟩
  rw [normalized_hafnians] at hh3
  have hh4 := hhB ⟨4,by decide⟩
  rw [normalized_hafnians] at hh4
  have hD : (matrix (B ⟨0,by decide⟩ ⟨3,by decide⟩) (B ⟨0,by decide⟩ ⟨4,by decide⟩) (B ⟨1,by decide⟩ ⟨3,by decide⟩) (B ⟨1,by decide⟩ ⟨4,by decide⟩) (B ⟨2,by decide⟩ ⟨3,by decide⟩) (B ⟨2,by decide⟩ ⟨4,by decide⟩)).det=-32 :=
    determinant_minus32 (B ⟨0,by decide⟩ ⟨3,by decide⟩) (B ⟨0,by decide⟩ ⟨4,by decide⟩) (B ⟨1,by decide⟩ ⟨3,by decide⟩) (B ⟨1,by decide⟩ ⟨4,by decide⟩) (B ⟨2,by decide⟩ ⟨3,by decide⟩) (B ⟨2,by decide⟩ ⟨4,by decide⟩) hh0 hh1 hh2 hh3 hh4
  have hbD : B.det=-32 := by rw [he]; exact hD
  intro hzero
  have hz := (preserves_singularity A s hs).2 hzero
  change B.det=0 at hz
  rw [hbD] at hz
  norm_num at hz
end
end MainTheory.Orbit30FullSupport
