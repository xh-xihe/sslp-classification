import MainTheory.Orbit5PhysicalRowData
set_option autoImplicit false
set_option maxHeartbeats 16000000
namespace MainTheory.Orbit5Displays
open scoped BigOperators Matrix
open SixQubit.Orbit5 SixQubit.Trace5 MainTheory.Orbit5PhysicalRowData
noncomputable section

theorem marginal_expectation (u v a1 a2 a3 a4 b1 b2 b3 b4 : Fin 4 → ℂ)
    (hq1 : ip u b1=0) (hq2 : ip u b2=0) (hq3 : ip u b3=0) (hq4 : ip u b4=0)
    (hf : ∀ k l : Fin 4,u k*star (u l)+fr a1 a2 a3 a4 k l=
      fr b1 b2 b3 b4 k l+v k*star (v l)) :
    (nsq u)^2+(Complex.normSq (ip u a1)+Complex.normSq (ip u a2)+
      Complex.normSq (ip u a3)+Complex.normSq (ip u a4))=Complex.normSq (ip u v) := by
  simp only [fr] at hf
  have key : ip u u * ip u u + (ip u a1 * ip a1 u + ip u a2 * ip a2 u + ip u a3 * ip a3 u
        + ip u a4 * ip a4 u
      ) = (ip u b1 * ip b1 u + ip u b2 * ip b2 u + ip u b3 * ip b3 u + ip u b4 * ip b4 u) + ip u v * ip v u := by
    simp only [ip]
    linear_combination (star (u 0) * u 0) * hf 0 0 + (star (u 0) * u 1) * hf 0 1
      + (star (u 0) * u 2) * hf 0 2 + (star (u 0) * u 3) * hf 0 3 + (star (u 1) * u 0) * hf 1 0
      + (star (u 1) * u 1) * hf 1 1 + (star (u 1) * u 2) * hf 1 2 + (star (u 1) * u 3) * hf 1 3
      + (star (u 2) * u 0) * hf 2 0 + (star (u 2) * u 1) * hf 2 1 + (star (u 2) * u 2) * hf 2 2
      + (star (u 2) * u 3) * hf 2 3 + (star (u 3) * u 0) * hf 3 0 + (star (u 3) * u 1) * hf 3 1
      + (star (u 3) * u 2) * hf 3 2 + (star (u 3) * u 3) * hf 3 3
  rw [ip_mul_ip u u, ip_mul_ip u a1, ip_mul_ip u a2, ip_mul_ip u a3, ip_mul_ip u a4,
    ip_mul_ip u b1, ip_mul_ip u b2, ip_mul_ip u b3, ip_mul_ip u b4, ip_mul_ip u v] at key
  have keyR : Complex.normSq (ip u u) + (Complex.normSq (ip u a1) + Complex.normSq (ip u a2)
        + Complex.normSq (ip u a3) + Complex.normSq (ip u a4)
      ) = (Complex.normSq (ip u b1) + Complex.normSq (ip u b2) + Complex.normSq (ip u b3)
        + Complex.normSq (ip u b4)) + Complex.normSq (ip u v) := by
    exact_mod_cast key

  rw [ip_self,Complex.normSq_ofReal] at keyR
  simp only [hq1,hq2,hq3,hq4,Complex.normSq_zero,zero_add,add_zero] at keyR
  nlinarith only [keyR]

theorem physical_marginal_expectation (c d : SS.State 6 ℂ)
    (hc : ∀ x,x∉S0 → c x=0) (hd : ∀ x,x∉S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
    (hkl : SS.HasDistance ![c,d] 3) :
    (nsq (uu c))^2+(Complex.normSq (ip (uu c) (aa1 c))+
      Complex.normSq (ip (uu c) (aa2 c))+Complex.normSq (ip (uu c) (aa3 c))+
      Complex.normSq (ip (uu c) (aa4 c)))=Complex.normSq (ip (uu c) (vv d)) := by
  obtain ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17,h18,h19,h20,h21,h22,h23,h24,h25,h26,h27,h28,h29,h30,h31,h32,h33,h34,h35,h36,h37,h38,h39,h40,h41,h42,h43,h44,h45,h46,h47,h48,h49,h50,h51,h52⟩ := physical_row_data c d hc hd hnc hnd hkl
  exact marginal_expectation _ _ _ _ _ _ _ _ _ _ h10 h11 h12 h13 h14

def coord (r s : Fin 2) : Fin 4 := ⟨2*r.val+s.val,by omega⟩
def coefficientMatrix (x : Fin 4 → ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  fun r s => x (coord r s)
def traceSecond (x y : Fin 4 → ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  fun r t => ∑ s : Fin 2,x (coord r s)*star (y (coord t s))
def traceFirst (x y : Fin 4 → ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  fun s t => ∑ r : Fin 2,x (coord r s)*star (y (coord r t))

theorem vectorization_second (x y : Fin 4 → ℂ) :
    traceSecond x y=coefficientMatrix x*(coefficientMatrix y).conjTranspose := by
  ext r t
  simp [traceSecond,coefficientMatrix,Matrix.mul_apply,Matrix.conjTranspose_apply]
theorem vectorization_first (x y : Fin 4 → ℂ) :
    traceFirst x y=(coefficientMatrix x).transpose*(coefficientMatrix y).map star := by
  ext s t
  simp [traceFirst,coefficientMatrix,Matrix.mul_apply,Matrix.transpose_apply]

def Omega : SS.BitString 4 := fun _ => true
def hat (i : Fin 4) : SS.BitString 4 := SS.bxor Omega (SS.stdBasis i)
def tail (x : SS.BitString 6) : SS.BitString 4 := fun i => x i.succ.succ
def actualBottomTail : Fin 5 → SS.BitString 4 := ![tail y0,tail y4,tail y8,tail y12,tail y16]
def actualTopTail : Fin 5 → SS.BitString 4 := ![tail z0,tail z4,tail z8,tail z12,tail z16]
theorem actual_tail_notation :
    actualBottomTail 0=(fun _ => false) ∧ actualTopTail 4=Omega ∧
    (∀ i : Fin 4,actualBottomTail ⟨i.val+1,by omega⟩=hat i) ∧
    (∀ i : Fin 4,actualTopTail i.castSucc=SS.stdBasis i) := by decide +kernel

theorem literal_coefficient_matrix (a b c d : ℂ) :
    coefficientMatrix ![a,b,c,d]=![![a,b],![c,d]] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

end
end MainTheory.Orbit5Displays
