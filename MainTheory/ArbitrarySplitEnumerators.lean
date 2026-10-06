import MainTheory.ArbitrarySplitTrace
import Orbit2.TensorEncoder
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 1000000
namespace MainTheory.ArbitrarySplitEnumerators
open scoped BigOperators Matrix
open Orbit2.TensorPauli Orbit2.HilbertBridge
open MainTheory.ArbitrarySplitSixQubit MainTheory.ArbitrarySplitPerfectCode
noncomputable section

def A (W : Matrix (Fin 4) (Fin 2) ℂ) (w : ℕ) : ℝ :=
  SS.MacWilliams.Aco (words (code W)) w/4

theorem trace_bridge (Q : Matrix (Fin 6 → Fin 2) (Fin 2) ℂ) (p : SS.PauliString 6) :
    SS.MacWilliams.trProj (words Q) p=Matrix.trace (Q.conjTranspose*operator (label p)*Q) := by
  unfold SS.MacWilliams.trProj Matrix.trace Matrix.diag
  apply Finset.sum_congr rfl
  intro j _
  exact Orbit2.HilbertBridge.compression Q p j j

theorem low_trace (W : Matrix (Fin 4) (Fin 2) ℂ) (hW : W.conjTranspose*W=1)
    (p : SS.PauliString 6) (hp : p.wt≤2) :
    SS.MacWilliams.trProj (words (code W)) p=2*scalar W (label p) := by
  rw [trace_bridge,code_KL W hW (label p)
    (by simpa only [weight6,label_weight] using hp)]
  norm_num [Matrix.trace_smul,smul_eq_mul]
  ring

theorem weight_three_trace (W : Matrix (Fin 4) (Fin 2) ℂ) (hW : W.conjTranspose*W=1)
    (p : SS.PauliString 6) (hp : p.wt=3) :
    SS.MacWilliams.trProj (words (code W)) p=0 := by
  rw [trace_bridge,compression_transport]
  exact MainTheory.ArbitrarySplitTrace.split_weight_three_trace W hW (label p)
    (by simpa only [weight6,label_weight] using hp)

theorem A_three (W : Matrix (Fin 4) (Fin 2) ℂ) (hW : W.conjTranspose*W=1) : A W 3=0 := by
  unfold A SS.MacWilliams.Aco
  have hz : (∑ p ∈ Finset.univ.filter (fun p : SS.PauliString 6 => p.wt=3),
      Complex.normSq (SS.MacWilliams.trProj (words (code W)) p))=0 := by
    apply Finset.sum_eq_zero
    intro p hp
    rw [weight_three_trace W hW p (Finset.mem_filter.mp hp).2,Complex.normSq_zero]
  rw [hz,zero_div]

theorem A_zero (W : Matrix (Fin 4) (Fin 2) ℂ) (hW : W.conjTranspose*W=1) : A W 0=1 := by
  have h := SixQubit.Pin.Aco_zero (words (code W))
    (fun j => by simpa only [if_pos rfl] using hilbert_orthonormal W hW j j)
  rw [A,h]
  norm_num

theorem macwilliams (W : Matrix (Fin 4) (Fin 2) ℂ) (hW : W.conjTranspose*W=1) :
    A W 4=15-4*A W 2-3*A W 3 ∧
    A W 5=12+3*A W 1+4*A W 2+3*A W 3 ∧
    A W 6=4-4*A W 1-A W 2-A W 3 := by
  have h0 := SixQubit.Pin.Aco_zero (words (code W))
    (fun j => by simpa only [if_pos rfl] using hilbert_orthonormal W hW j j)
  obtain ⟨h4,h5,h6⟩ := SS.MacWilliams.macwilliams_six (words (code W))
    (hilbert_distance_three W hW) h0
  unfold A
  exact ⟨by linarith,by linarith,by linarith⟩

end
end MainTheory.ArbitrarySplitEnumerators
