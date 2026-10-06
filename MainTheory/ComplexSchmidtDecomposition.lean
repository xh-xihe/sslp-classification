import MainTheory.ComplexSchmidtStep
set_option autoImplicit false
set_option maxHeartbeats 12000000
namespace MainTheory.ComplexSchmidtDecomposition
open scoped Matrix BigOperators
open MainTheory.ComplexSchmidtStep MainTheory.Orbit26DependentAnchors
noncomputable section

def swap : M2 := !![0,1;1,0]

theorem swap_unitary : unitary swap := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [swap,Matrix.mul_apply,Fin.sum_univ_two,Matrix.conjTranspose_apply]

theorem rowNorm_nonneg (Y : M2) (i : Fin 2) : 0≤rowNorm Y i := by
  unfold rowNorm nsq
  exact Finset.sum_nonneg (fun j _ => Complex.normSq_nonneg (Y i j))

theorem rowNorm_zero (Y : M2) (i : Fin 2) (h : rowNorm Y i=0) : ∀ j,Y i j=0 := by
  simp only [rowNorm,nsq,Fin.sum_univ_two] at h
  intro j
  apply Complex.normSq_eq_zero.mp
  fin_cases j
  · change Complex.normSq (Y i 0)=0
    nlinarith [Complex.normSq_nonneg (Y i 0),Complex.normSq_nonneg (Y i 1)]
  · change Complex.normSq (Y i 1)=0
    nlinarith [Complex.normSq_nonneg (Y i 0),Complex.normSq_nonneg (Y i 1)]

theorem orthogonal_rows (Y : M2)
    (ho : star (Y 0 0)*Y 1 0+star (Y 0 1)*Y 1 1=0) :
    ∃ R : M2,∃ s t : ℝ,unitary R ∧ 0≤s ∧ 0≤t ∧
      Y*R=Matrix.diagonal ![(s : ℂ),(t : ℂ)] := by
  by_cases hpos : 0<rowNorm Y 0
  · exact orthogonal_rows_positive Y hpos ho
  have hzero : rowNorm Y 0=0 := le_antisymm (le_of_not_gt hpos) (rowNorm_nonneg Y 0)
  have hz := rowNorm_zero Y 0 hzero
  by_cases hpos1 : 0<rowNorm Y 1
  · let Y' : M2 := swap*Y
    have hy' : ∀ j,Y' 0 j=Y 1 j ∧ Y' 1 j=Y 0 j := by
      intro j
      dsimp [Y']
      simp only [Matrix.mul_apply,Fin.sum_univ_two]
      change 0*Y 0 j+1*Y 1 j=Y 1 j ∧ 1*Y 0 j+0*Y 1 j=Y 0 j
      simp only [zero_mul,one_mul,zero_add,add_zero,and_self]
    have hn' : 0<rowNorm Y' 0 := by
      have he : Y' 0=Y 1 := funext (fun j => (hy' j).1)
      simpa only [rowNorm,he] using hpos1
    have ho' : star (Y' 0 0)*Y' 1 0+star (Y' 0 1)*Y' 1 1=0 := by
      rw [(hy' 0).2,(hy' 1).2,hz 0,hz 1]
      simp
    obtain ⟨R,s,t,hR,hs,ht,hd⟩ := orthogonal_rows_positive Y' hn' ho'
    have ht0 : t=0 := by
      have hh := congrArg (fun A : M2 => A 1 1) hd
      simp only [Matrix.mul_apply,Fin.sum_univ_two,(hy' 0).2,(hy' 1).2,hz 0,hz 1,
        zero_mul,zero_add,Matrix.diagonal_apply_eq,Matrix.cons_val_one,Matrix.cons_val_fin_one] at hh
      exact_mod_cast hh.symm
    refine ⟨R*swap,0,s,unitary_mul _ _ hR swap_unitary,le_rfl,hs,?_⟩
    have hsY : swap*Y'=Y := by
      dsimp [Y']
      have hss : swap*swap=1 := by
        ext i j
        fin_cases i <;> fin_cases j <;> norm_num [swap,Matrix.mul_apply,Fin.sum_univ_two]
      rw [← Matrix.mul_assoc,hss]
      simp only [Matrix.one_mul]
    rw [← hsY]
    calc
      (swap*Y')*(R*swap)=swap*(Y'*R)*swap := by noncomm_ring
      _=Matrix.diagonal ![(0 : ℂ),(s : ℂ)] := by
        rw [hd,ht0]
        ext i j
        fin_cases i <;> fin_cases j <;>
          norm_num [swap,Matrix.mul_apply,Fin.sum_univ_two,Matrix.diagonal,
            Matrix.of_apply,Matrix.vecHead,Matrix.vecTail]
  · have hz1 := rowNorm_zero Y 1
      (le_antisymm (le_of_not_gt hpos1) (rowNorm_nonneg Y 1))
    have hY : Y=0 := by
      ext i j
      fin_cases i
      · exact hz j
      · exact hz1 j
    refine ⟨1,0,0,?_,le_rfl,le_rfl,?_⟩
    · constructor <;> simp [Matrix.conjTranspose_one]
    · rw [hY,Matrix.zero_mul]
      ext i j
      fin_cases i <;> fin_cases j <;> rfl

theorem left_orthogonal_rows (X : M2) : ∃ L : M2,unitary L ∧
    star ((L*X) 0 0)*(L*X) 1 0+star ((L*X) 0 1)*(L*X) 1 1=0 := by
  let G : M2 := X*X.conjTranspose
  have hG : G.IsHermitian := Matrix.isHermitian_mul_conjTranspose_self X
  let E : M2 := hG.eigenvectorUnitary
  let L : M2 := E.conjTranspose
  have hE : unitary E := ⟨Unitary.coe_mul_star_self hG.eigenvectorUnitary,
    Unitary.coe_star_mul_self hG.eigenvectorUnitary⟩
  have hL : unitary L := by
    constructor
    · simpa only [L,Matrix.conjTranspose_conjTranspose] using hE.2
    · simpa only [L,Matrix.conjTranspose_conjTranspose] using hE.1
  refine ⟨L,hL,?_⟩
  have hd := hG.conjStarAlgAut_star_eigenvectorUnitary
  rw [Unitary.conjStarAlgAut_star_apply] at hd
  have he : (L*X)*(L*X).conjTranspose=Matrix.diagonal (RCLike.ofReal ∘ hG.eigenvalues) := by
    rw [Matrix.conjTranspose_mul]
    calc
      (L*X)*(X.conjTranspose*L.conjTranspose)=L*G*E := by
        dsimp [L,G]
        rw [Matrix.conjTranspose_conjTranspose]
        noncomm_ring
      _=_ := hd
  have hh := congrArg (fun A : M2 => A 0 1) he
  dsimp only at hh
  rw [Matrix.diagonal_apply_ne _ (by decide : (0 : Fin 2)≠1)] at hh
  simp only [Matrix.mul_apply,Fin.sum_univ_two,Matrix.conjTranspose_apply] at hh
  have hc := congrArg star hh
  simp only [star_add,star_mul,star_star,star_zero] at hc
  simp only [Matrix.mul_apply,Fin.sum_univ_two,star_add,star_mul]
  linear_combination hc

theorem schmidt (X : M2) : ∃ L R : M2,∃ s t : ℝ,
    unitary L ∧ unitary R ∧ 0≤s ∧ 0≤t ∧
    L*X*R=Matrix.diagonal ![(s : ℂ),(t : ℂ)] := by
  obtain ⟨L,hL,ho⟩ := left_orthogonal_rows X
  obtain ⟨R,s,t,hR,hs,ht,hd⟩ := orthogonal_rows (L*X) ho
  exact ⟨L,R,s,t,hL,hR,hs,ht,hd⟩

end
end MainTheory.ComplexSchmidtDecomposition
