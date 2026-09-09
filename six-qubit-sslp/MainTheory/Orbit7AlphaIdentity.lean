import MainTheory.Orbit7WeightOneMass
import MainTheory.Orbit7ZeroQubitMarginal
import MainTheory.OneQubitPauliPurity
import MainTheory.PauliFamilyTrace

set_option autoImplicit false
set_option maxRecDepth 100000

namespace MainTheory.Orbit7AlphaIdentity

open SixQubit.Orbit7Universal SixQubit.Orbit7DirectMarginal SS.MacWilliams
open MainTheory.Orbit7MatrixDisplays MainTheory.Orbit7SpinorCoordinates
open MainTheory.Orbit7ZeroQubitMarginal MainTheory.Orbit7EnumeratorDisplays
open MainTheory.PairPauliPurity MainTheory.PauliTransferTwo

def zeroPaulis : Fin 3 → SS.PauliString 6 := ![tPX,tPY,tPZ]

theorem pair_zero_paulis (s : Fin 5) (p : Fin 3) :
    MainTheory.PairPauliSupport.pairString s p.succ 0=zeroPaulis p := by
  apply MainTheory.PauliWordBridge.pauliWordEquiv.injective
  simp only [MainTheory.PairPauliSupport.pairString,Equiv.apply_symm_apply]
  funext i
  fin_cases s <;> fin_cases p <;> fin_cases i <;> rfl

theorem contract_pauli (p : Fin 4) (M : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
    (pairPauli p 0*M).trace=(pauli p*contract M).trace := by
  simp [pairPauli,pauli_zero,contract,Matrix.trace,Matrix.diag_apply,Matrix.mul_apply,
    Matrix.one_apply,Fintype.sum_prod_type,Fin.sum_univ_two]
  ring

theorem zero_pauli_trace (code : Fin 2 → SS.State 6 ℂ) (p : Fin 3) :
    (pauli p.succ*zeroMarginal code).trace=(1/2 : ℂ)*trProj code (zeroPaulis p) := by
  have h := MainTheory.PairPauliTrace.local_global_trace code 0 p.succ 0
  rw [contract_pauli,contract_direct,pair_zero_paulis,MainTheory.PauliFamilyTrace.trace_family] at h
  exact h

theorem zero_hermitian (code : Fin 2 → SS.State 6 ℂ) :
    (zeroMarginal code).conjTranspose=zeroMarginal code := by
  ext i j
  simp [zeroMarginal,Matrix.conjTranspose_apply,mul_comm]

variable (c d : SS.State 6 ℂ)
  (hc : ∀ x,SS.weight uniformAv x ≠ 0 → c x=0)
  (hd : ∀ x,SS.weight uniformAv x ≠ 2 → d x=0)
  (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
  (hcode : SS.HasDistance ![c,d] 3)

include hc hd hnc hnd hcode

theorem A1_zero_traces : normalizedA ![c,d] 1 =
    Complex.normSq ((pauli 1*zeroMarginal ![c,d]).trace)+
    Complex.normSq ((pauli 2*zeroMarginal ![c,d]).trace)+
    Complex.normSq ((pauli 3*zeroMarginal ![c,d]).trace) := by
  have h1 := congrArg Complex.normSq (zero_pauli_trace ![c,d] 0)
  have h2 := congrArg Complex.normSq (zero_pauli_trace ![c,d] 1)
  have h3 := congrArg Complex.normSq (zero_pauli_trace ![c,d] 2)
  norm_num [zeroPaulis,Complex.normSq_mul] at h1 h2 h3
  change Complex.normSq ((pauli 3*zeroMarginal ![c,d]).trace) =
    1/4*Complex.normSq (trProj ![c,d] tPZ) at h3
  rw [normalizedA,MainTheory.Orbit7WeightOneMass.Aco_one c d hc hd hnc hnd hcode]
  linear_combination -h1-h2-h3

theorem A1_purity : (normalizedA ![c,d] 1 : ℂ) =
    2*(zeroMarginal ![c,d]*zeroMarginal ![c,d]).trace-1 := by
  obtain ⟨hu,hv,_⟩ := scalar_normal_form c d hc hd hnc hnd hcode
  obtain ⟨hPu,hPv⟩ := MainTheory.Orbit7PairPurity.extreme_traces c d hu hv
  have ht : (zeroMarginal ![c,d]).trace=1 := by
    rw [normalized_zero_marginal c d hc hd hnc hnd hcode]
    simp [Matrix.trace_smul,Matrix.trace_add,hPu,hPv]
    norm_num
  rw [A1_zero_traces c d hc hd hnc hnd hcode]
  exact MainTheory.OneQubitPauliPurity.nonidentity_purity _ (zero_hermitian _) ht

theorem normalized_alpha (a b : ℝ) (hab : a^2+b^2=1)
    (hPu : Pu c=outer (![1,0])) (hPv : Pv d=outer (nvec a b)) :
    normalizedA ![c,d] 1=a^2 := by
  have h := A1_purity c d hc hd hnc hnd hcode
  rw [normalized_zero_marginal c d hc hd hnc hnd hcode,hPu,hPv] at h
  change (normalizedA ![c,d] 1 : ℂ) =
    2*(normalizedDensity a b*normalizedDensity a b).trace-1 at h
  rw [density_purity a b hab] at h
  exact_mod_cast h

end MainTheory.Orbit7AlphaIdentity
