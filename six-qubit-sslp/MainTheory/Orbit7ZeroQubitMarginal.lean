import MainTheory.Orbit7PauliPurityDisplay
import MainTheory.Orbit7SpinorCoordinates

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace MainTheory.Orbit7ZeroQubitMarginal

open SixQubit.Orbit7Universal SixQubit.Orbit7DirectMarginal
open MainTheory.Orbit7MatrixDisplays MainTheory.Orbit7SpinorCoordinates
open MainTheory.PairPartialTrace

def activeEquiv (s : Fin 5) : (Fin 2 × Env) ≃ SS.BitString 5 :=
  (Equiv.prodCongr finTwoEquiv (Equiv.refl Env)).trans
    (Fin.insertNthEquiv (fun _ : Fin 5 => Bool) s)

theorem activeEquiv_apply (s : Fin 5) (b : Fin 2) (e : Env) :
    activeEquiv s (b,e)=Fin.insertNth s (finTwoEquiv b) e := rfl

noncomputable def zeroMarginal (code : Fin 2 → SS.State 6 ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j => (1/2 : ℂ)*∑ k : Fin 2,∑ a : SS.BitString 5,
    code k (Fin.cons (finTwoEquiv i) a)*star (code k (Fin.cons (finTwoEquiv j) a))

noncomputable def contract (M : Matrix Pair Pair ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j => ∑ b : Fin 2,M (i,b) (j,b)

theorem contract_direct (code : Fin 2 → SS.State 6 ℂ) (s : Fin 5) :
    contract (directPairMarginal code s)=zeroMarginal code := by
  ext i j
  simp only [contract,directPairMarginal,directPurePairMarginal,zeroMarginal]
  simp_rw [← (activeEquiv s).sum_comp]
  simp only [Fintype.sum_prod_type,activeEquiv_apply,assemblePair,Finset.mul_sum]
  rw [Finset.sum_comm]

theorem normalized_zero_marginal (c d : SS.State 6 ℂ)
    (hc : ∀ x,SS.weight uniformAv x ≠ 0 → c x=0)
    (hd : ∀ x,SS.weight uniformAv x ≠ 2 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
    (hcode : SS.HasDistance ![c,d] 3) :
    zeroMarginal ![c,d]=(1/2 : ℂ) • (Pu c+Pv d) := by
  obtain ⟨s,hs⟩ := MainTheory.Orbit7StructuralDisplay.direct_structure c d hc hd hnc hnd hcode
  rw [← contract_direct ![c,d] s,hs]
  ext i j
  simp [contract,Matrix.blockDiagonal_apply,Fin.sum_univ_two]
  ring

noncomputable def normalizedDensity (c d : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (1/2 : ℂ) • (outer (![1,0])+outer (nvec c d))

theorem density_purity (c d : ℝ) (h : c^2+d^2=1) :
    2*(normalizedDensity c d*normalizedDensity c d).trace-1=(c : ℂ)^2 := by
  have hC : (c : ℂ)^2+(d : ℂ)^2=1 := by exact_mod_cast h
  simp [normalizedDensity,outer,nvec,Matrix.trace,Matrix.diag_apply,Matrix.mul_apply,
    Fin.sum_univ_two]
  linear_combination (((c : ℂ)^2+(d : ℂ)^2+1)/2)*hC

theorem anchor_overlap (c d : ℝ) :
    Complex.normSq (spinInner (![1,0]) (nvec c d))=c^2 := by
  simp [spinInner,nvec,Complex.normSq_ofReal]
  ring

end MainTheory.Orbit7ZeroQubitMarginal
