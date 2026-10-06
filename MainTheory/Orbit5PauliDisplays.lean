import MainTheory.Orbit5MatrixRows
set_option autoImplicit false
set_option maxHeartbeats 12000000
namespace MainTheory.Orbit5PauliDisplays
open scoped Matrix BigOperators
open SixQubit.Orbit5 SixQubit.Trace5 MainTheory.Orbit5Displays MainTheory.Orbit5MatrixRows
noncomputable section

def scale : ℂ := ((Real.sqrt 2)⁻¹ : ℝ)
theorem scale_square : scale^2=1/2 := by
  have h : ((Real.sqrt (2 : ℝ))⁻¹)^2=1/2 := by
    rw [inv_pow,Real.sq_sqrt (by norm_num)]
    norm_num
  unfold scale
  rw [← Complex.ofReal_pow,h]
  norm_num
theorem scale_star : star scale=scale := by simp [scale]

def pauli : Fin 3 → Matrix (Fin 2) (Fin 2) ℂ :=
  ![![![0,1],![1,0]],![![0,-Complex.I],![Complex.I,0]],![![1,0],![0,-1]]]
def tau (r : Fin 3) : Matrix (Fin 2) (Fin 2) ℂ := scale • pauli r
def hsInner (A B : Matrix (Fin 2) (Fin 2) ℂ) : ℂ :=
  ∑ r : Fin 2,∑ t : Fin 2,star (A r t)*B r t
def matrixNormSq (A : Matrix (Fin 2) (Fin 2) ℂ) : ℝ :=
  Complex.normSq (A 0 0)+Complex.normSq (A 0 1)+Complex.normSq (A 1 0)+Complex.normSq (A 1 1)
def coordinates (A : Matrix (Fin 2) (Fin 2) ℂ) : Fin 3 → ℂ :=
  ![scale*(A 0 1+A 1 0),scale*Complex.I*(A 0 1-A 1 0),2*scale*A 0 0]
def coordinatesNormSq (z : Fin 3 → ℂ) : ℝ :=
  Complex.normSq (z 0)+Complex.normSq (z 1)+Complex.normSq (z 2)
def frame (z : Fin 4 → Fin 3 → ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  fun r t => ∑ i : Fin 4,z i r*star (z i t)

theorem tau_orthonormal (r t : Fin 3) : hsInner (tau r) (tau t)=if r=t then 1 else 0 := by
  fin_cases r <;> fin_cases t
  all_goals norm_num [hsInner,tau,pauli,Fin.sum_univ_two,Pi.smul_apply,smul_eq_mul,
    Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,scale_star]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,scale_square]

theorem tau_traceless (r : Fin 3) : Matrix.trace (tau r)=0 := by
  fin_cases r <;> norm_num [tau,pauli,Matrix.trace,Matrix.diag,Fin.sum_univ_two,
    Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail]

theorem coordinate_expansion (A : Matrix (Fin 2) (Fin 2) ℂ) (h : Matrix.trace A=0) :
    A=∑ r : Fin 3,coordinates A r • tau r := by
  have hd : A 0 0+A 1 1=0 := by
    simpa only [Matrix.trace,Matrix.diag,Fin.sum_univ_two] using h
  ext i j
  fin_cases i <;> fin_cases j
  all_goals norm_num [coordinates,tau,pauli,Matrix.sum_apply,Pi.smul_apply,smul_eq_mul,
    Fin.sum_univ_succ,Fin.succ,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,scale_square]
  · ring
  · ring
  · ring
  · calc
      A 1 1=-A 0 0 := by linear_combination hd
      _ = -(1/2*A 0 0*2) := by ring

theorem coordinate_norm (A : Matrix (Fin 2) (Fin 2) ℂ) (h : Matrix.trace A=0) :
    coordinatesNormSq (coordinates A)=matrixNormSq A := by
  have hd : A 1 1=-A 0 0 := by
    have hh : A 0 0+A 1 1=0 := by simpa only [Matrix.trace,Matrix.diag,Fin.sum_univ_two] using h
    linear_combination hh
  have hkc : (Complex.normSq scale : ℂ)=1/2 := by
    simp only [Complex.normSq_eq_conj_mul_self,← Complex.star_def,scale_star]
    linear_combination scale_square
  have hkr : Complex.normSq scale=1/2 := by
    have hh := congrArg Complex.re hkc
    norm_num at hh
    exact hh
  unfold coordinatesNormSq coordinates matrixNormSq
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.vecHead,Matrix.vecTail,map_mul,Complex.normSq_I,
    Complex.normSq_neg,hd,hkr]
  norm_num
  rw [Complex.normSq_add,Complex.normSq_sub]
  rw [hkr]
  ring

theorem physical_coordinate_expansions (c : SS.State 6 ℂ)
    (htrace : ∀ i : Fin 4,Matrix.trace (coefficientMatrix (bottomVector c i))=0) :
    ∀ i : Fin 4,coefficientMatrix (bottomVector c i)=
      ∑ r : Fin 3,coordinates (coefficientMatrix (bottomVector c i)) r • tau r :=
  fun i => coordinate_expansion _ (htrace i)

theorem physical_coordinates_norms (c d : SS.State 6 ℂ)
    (hc : ∀ x,x∉S0 → c x=0) (hd : ∀ x,x∉S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
    (hkl : SS.HasDistance ![c,d] 3)
    (htrace : ∀ i : Fin 4,Matrix.trace (coefficientMatrix (bottomVector c i))=0) :
    ∀ i : Fin 4,coordinatesNormSq (coordinates (coefficientMatrix (bottomVector c i)))=1/6 := by
  obtain ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17,h18,h19,h20,h21,h22,h23,h24,h25,h26,h27,h28,h29,h30,h31,h32,h33,h34,h35,h36,h37,h38,h39,h40,h41,h42,h43,h44,h45,h46,h47,h48,h49,h50,h51,h52⟩ :=
    MainTheory.Orbit5PhysicalRowData.physical_row_data c d hc hd hnc hnd hkl
  intro i
  rw [coordinate_norm _ (htrace i)]
  fin_cases i
  · exact h2
  · exact h3
  · exact h4
  · exact h5

theorem frame_trace (z : Fin 4 → Fin 3 → ℂ)
    (h : ∀ i,coordinatesNormSq (z i)=1/6) : Matrix.trace (frame z)=(2/3 : ℂ) := by
  have h0 := congrArg (fun x : ℝ => (x : ℂ)) (h 0)
  have h1 := congrArg (fun x : ℝ => (x : ℂ)) (h 1)
  have h2 := congrArg (fun x : ℝ => (x : ℂ)) (h 2)
  have h3 := congrArg (fun x : ℝ => (x : ℂ)) (h 3)
  simp only [coordinatesNormSq] at h0 h1 h2 h3
  push_cast at h0 h1 h2 h3
  simp only [Complex.normSq_eq_conj_mul_self,← Complex.star_def] at h0 h1 h2 h3
  simp only [frame,Matrix.trace,Matrix.diag,Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero]
  change z 0 0*star (z 0 0)+(z 1 0*star (z 1 0)+(z 2 0*star (z 2 0)+(z 3 0*star (z 3 0))))+(z 0 1*star (z 0 1)+(z 1 1*star (z 1 1)+(z 2 1*star (z 2 1)+(z 3 1*star (z 3 1))))+(z 0 2*star (z 0 2)+(z 1 2*star (z 1 2)+(z 2 2*star (z 2 2)+(z 3 2*star (z 3 2))))))=2/3
  linear_combination h0+h1+h2+h3

theorem physical_frame_trace (c d : SS.State 6 ℂ)
    (hc : ∀ x,x∉S0 → c x=0) (hd : ∀ x,x∉S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
    (hkl : SS.HasDistance ![c,d] 3)
    (htrace : ∀ i : Fin 4,Matrix.trace (coefficientMatrix (bottomVector c i))=0) :
    Matrix.trace (frame (fun i => coordinates (coefficientMatrix (bottomVector c i))))=2/3 :=
  frame_trace _ (physical_coordinates_norms c d hc hd hnc hnd hkl htrace)

end
end MainTheory.Orbit5PauliDisplays
