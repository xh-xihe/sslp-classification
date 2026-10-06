import SixQubit.Orbit8UniversalFinal
import MainTheory.PauliFamilyTrace

set_option autoImplicit false

namespace MainTheory.Orbit8EnumeratorDisplays

open SixQubit.Orbit8Universal SS.MacWilliams

noncomputable def normalizedA (psi : Fin 2 → SS.State 6 ℂ) (j : ℕ) : ℝ := Aco psi j/4
noncomputable def normalizedB (psi : Fin 2 → SS.State 6 ℂ) (j : ℕ) : ℝ := Bco psi j/4
noncomputable def lambda (psi : Fin 2 → SS.State 6 ℂ) (P : SS.PauliString 6) : ℂ :=
  trProj psi P/2

theorem lambda_trace (psi : Fin 2 → SS.State 6 ℂ) (P : SS.PauliString 6) :
    lambda psi P = (1/2 : ℂ)*Matrix.trace
      (MainTheory.PairPartialTrace.familyKernel psi*MainTheory.PauliKernelTrace.pauliKernel P) := by
  rw [Matrix.trace_mul_comm,MainTheory.PauliFamilyTrace.trace_family]
  unfold lambda
  ring

theorem A12_lambda (psi : Fin 2 → SS.State 6 ℂ) :
    normalizedA psi 1+normalizedA psi 2=
      ∑ P ∈ lowPaulis,Complex.normSq (lambda psi P) := by
  simp only [lambda,Complex.normSq_div]
  norm_num
  rw [← Finset.sum_div,lowPaulis_sum]
  unfold normalizedA
  ring

variable (c d : SS.State 6 ℂ)
  (hc : ∀ x,SS.weight av x ≠ 0 → c x=0)
  (hd : ∀ x,SS.weight av x ≠ 1 → d x=0)
  (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
  (hcode : SS.HasDistance ![c,d] 3)

include hc hd hnc hnd hcode

theorem lower_A12 : 1 ≤ normalizedA ![c,d] 1+normalizedA ![c,d] 2 := by
  have h := low_bound c d hc hd hnc hnd hcode
  dsimp only [normalizedA]
  linarith

omit hc hd in
theorem shadow_bound : normalizedA ![c,d] 1+normalizedA ![c,d] 2+
    normalizedA ![c,d] 3 ≤ 1 := by
  have h0 := SixQubit.Pin.Aco_zero ![c,d]
    (SixQubit.Orbit8Universal.normalized_pair c d hnc hnd)
  have h := SS.Shadow.shadow_bound ![c,d] hcode h0
  dsimp only [normalizedA]
  linarith

theorem q_dot_lambda : (∑ e : QIndex,qCoeff (u d) e*lambda ![c,d] (qPauli e))=
    (r d : ℂ)/2 := by
  have hr := (rigid_coordinate_norms c d hc hd hnc hnd hcode).2.1
  simp only [lambda,← mul_div_assoc,← Finset.sum_div]
  rw [q_dot_trace c d hc hd hnc hnd hcode,hr]
  norm_num

theorem norm_blocks : (∑ i,Complex.normSq (u d i))=(1/6 : ℝ) ∧
    (∑ ij ∈ pairs6,Complex.normSq (v d ij.1 ij.2))=(5/6 : ℝ) := by
  have h := rigid_shells c d hc hd hnc hnd hcode
  constructor
  · simpa only [shellMass_S1_one_eq_r,r,p] using h.2.2.2.2.1
  · simpa only [shell4_edge_mass,w] using h.2.2.2.2.2

theorem line_identities : normalizedA ![c,d] 1+normalizedA ![c,d] 2=1 ∧
    normalizedA ![c,d] 3=0 := by
  obtain ⟨h12,h3,_,_,_⟩ := universal_pin_line c d hc hd hnc hnd hcode
  dsimp only [normalizedA]
  constructor <;> linarith

theorem A1_concentration : normalizedA ![c,d] 1=36*∑ i,(p d i)^2 := by
  have h := Aco_one_p c d hc hd hnc hnd hcode
  dsimp only [normalizedA]
  linarith

theorem signature_saturation (e : QIndex) :
    lambda ![c,d] (qPauli e)=2*qCoeff (u d) e/(r d : ℂ) := by
  have hr := (rigid_coordinate_norms c d hc hd hnc hnd hcode).2.1
  rw [lambda,trace_saturation c d hc hd hnc hnd hcode,hr]
  push_cast
  ring

theorem Z_signature (i : Fin 6) :
    lambda ![c,d] (Pz i)= -6*(p d i : ℂ) := by
  have h := signature_saturation c d hc hd hnc hnd hcode (.inl i)
  have hr := (rigid_coordinate_norms c d hc hd hnc hnd hcode).2.1
  simp [qPauli,qCoeff,hr] at h
  unfold p
  linear_combination h

theorem ZZ_signature (i j : Fin 6) (hij : i ≠ j) :
    lambda ![c,d] (Pzz i j)=0 := by
  have h := trace_zero_low_outside c d hc hd hnc hnd hcode (Pzz i j)
    (by simp [lowPaulis,wt_Pzz i j hij]) (Pzz_not_qimage i j hij)
  simp [lambda,h]

end MainTheory.Orbit8EnumeratorDisplays
