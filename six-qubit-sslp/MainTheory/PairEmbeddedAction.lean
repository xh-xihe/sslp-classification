import MainTheory.PairPartialTrace

set_option autoImplicit false

namespace MainTheory.PairEmbeddedAction

open MainTheory.PairPartialTrace SixQubit.Orbit7DirectMarginal

theorem action_assembled (s : Fin 5) (A : Matrix Pair Pair ℂ) (f : SS.State 6 ℂ)
    (p : Pair) (e : Env) :
    (embed s A).mulVec f (assemblePair s p e)=∑ q : Pair,A p q*f (assemblePair s q e) := by
  classical
  simp only [Matrix.mulVec,dotProduct]
  rw [← (assemblyEquiv s).sum_comp]
  rw [Fintype.sum_prod_type]
  simp only [assembly_apply,embed_assembled,ite_mul,zero_mul]
  simp

end MainTheory.PairEmbeddedAction
