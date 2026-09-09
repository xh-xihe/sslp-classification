import SixQubit.Orbit7DirectMarginal
import MainTheory.PairPauliPurity

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace MainTheory.PairPartialTrace

open SixQubit.Orbit7DirectMarginal

abbrev Pair := Fin 2 × Fin 2
abbrev Env := SS.BitString 4

def assemblyEquiv (s : Fin 5) : (Pair × Env) ≃ SS.BitString 6 :=
  (Equiv.prodAssoc (Fin 2) (Fin 2) Env).trans
    ((Equiv.prodCongr finTwoEquiv
      ((Equiv.prodCongr finTwoEquiv (Equiv.refl Env)).trans
        (Fin.insertNthEquiv (fun _ : Fin 5 => Bool) s))).trans
      (Fin.consEquiv (fun _ : Fin 6 => Bool)))

theorem assembly_apply (s : Fin 5) (p : Pair) (e : Env) :
    assemblyEquiv s (p,e)=assemblePair s p e := rfl

noncomputable def embed (s : Fin 5) (A : Matrix Pair Pair ℂ) :
    Matrix (SS.BitString 6) (SS.BitString 6) ℂ :=
  fun x y => if ((assemblyEquiv s).symm x).2=((assemblyEquiv s).symm y).2 then
    A ((assemblyEquiv s).symm x).1 ((assemblyEquiv s).symm y).1 else 0

theorem embed_assembled (s : Fin 5) (A : Matrix Pair Pair ℂ)
    (p q : Pair) (e f : Env) :
    embed s A (assemblePair s p e) (assemblePair s q f) = if e=f then A p q else 0 := by
  change embed s A (assemblyEquiv s (p,e)) (assemblyEquiv s (q,f)) = _
  simp [embed]

noncomputable def familyKernel (code : Fin 2 → SS.State 6 ℂ) :
    Matrix (SS.BitString 6) (SS.BitString 6) ℂ := fun x y =>
  ∑ k : Fin 2,code k x*star (code k y)

theorem partial_trace_identity (code : Fin 2 → SS.State 6 ℂ) (s : Fin 5)
    (A : Matrix Pair Pair ℂ) :
    (A*directPairMarginal code s).trace =
      (1/2 : ℂ)*(embed s A*familyKernel code).trace := by
  classical
  simp only [Matrix.trace,Matrix.diag_apply,Matrix.mul_apply]
  rw [← (assemblyEquiv s).sum_comp]
  simp only [Fintype.sum_prod_type,assembly_apply]
  simp_rw [← (assemblyEquiv s).sum_comp]
  simp only [Fintype.sum_prod_type,assembly_apply,embed_assembled]
  simp only [ite_mul,zero_mul,Finset.sum_ite_eq,Finset.mem_univ,if_true]
  simp only [directPairMarginal,directPurePairMarginal,familyKernel,Finset.mul_sum]
  simp only [mul_left_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  conv_rhs =>
    rw [Finset.sum_comm]
    arg 2
    ext c
    rw [Finset.sum_comm]
    arg 2
    ext d
    rw [Finset.sum_comm]

end MainTheory.PairPartialTrace
