import MainTheory.ParityFourMoments
set_option autoImplicit false
set_option maxHeartbeats 12000000
namespace MainTheory.ParityFourEdgeDeterminant
open scoped Matrix

def other : Fin 4 → Fin 3 → Fin 4 :=
  ![![1,2,3],![0,2,3],![0,1,3],![0,1,2]]
def evenIndex : Fin 8 → Fin 16 := ![0,3,5,6,9,10,12,15]
def evenPoint (j : Fin 8) : SS.BitString 4 := MainTheory.ParityFour.point (evenIndex j)
def rowMask (k : Fin 4) : Fin 8 → SS.BitString 4 :=
  ![fun _ => false,SS.stdBasis k,SS.stdBasis (other k 0),
    SS.bxor (SS.stdBasis k) (SS.stdBasis (other k 0)),SS.stdBasis (other k 1),
    SS.bxor (SS.stdBasis k) (SS.stdBasis (other k 1)),SS.stdBasis (other k 2),
    SS.bxor (SS.stdBasis k) (SS.stdBasis (other k 2))]
def W (k : Fin 4) : Matrix (Fin 8) (Fin 8) ℤ :=
  fun i j => if SS.bdot (rowMask k i) (evenPoint j) then -1 else 1

theorem literal_even_points :
    Finset.univ.image evenPoint=Finset.univ.filter (fun x : SS.BitString 4 =>
      MainTheory.ParityFour.parity x=false) := by decide +kernel

theorem gram_checked : ∀ k : Fin 4,W k*(W k).transpose=(8 : ℤ) • 1 := by
  decide +kernel

theorem absolute_determinant (k : Fin 4) : |(W k).det|=4096 := by
  have hd := congrArg (fun M : Matrix (Fin 8) (Fin 8) ℤ => M.det) (gram_checked k)
  dsimp only at hd
  rw [Matrix.det_mul,Matrix.det_transpose,Matrix.det_smul,Matrix.det_one,mul_one] at hd
  norm_num at hd
  nlinarith [abs_nonneg ((W k).det),sq_abs ((W k).det)]
end MainTheory.ParityFourEdgeDeterminant
