import MainTheory.PairPartialTrace
import MainTheory.PauliWordBridge

set_option autoImplicit false

namespace MainTheory.PairTensorEmbedding

open MainTheory.ClassificationLevels MainTheory.LocalTensorKernel
open MainTheory.PairPartialTrace SixQubit.Orbit7DirectMarginal

abbrev Mat := Matrix (Fin 2) (Fin 2) ℂ

noncomputable def localMatrices (s : Fin 5) (U V : Mat) : Fin 6 → Mat :=
  Fin.cons U (Function.update (fun _ : Fin 5 => 1) s V)

noncomputable def pairMatrix (U V : Mat) : Matrix Pair Pair ℂ :=
  fun p q => U p.1 q.1*V p.2 q.2

theorem bitIndex_finTwo (a : Fin 2) : bitIndex (finTwoEquiv a)=a := by
  fin_cases a <;> rfl

theorem tensor_assembled (s : Fin 5) (U V : Mat) (p q : Pair) (e f : Env) :
    tensorKernel (localMatrices s U V) (assemblePair s p e) (assemblePair s q f) =
      if e=f then pairMatrix U V p q else 0 := by
  simp only [tensorKernel,localMatrices,assemblePair]
  rw [Fin.prod_univ_succ]
  simp only [Fin.cons_zero,Fin.cons_succ,bitIndex_finTwo]
  rw [Fin.prod_univ_succAbove _ s]
  simp only [Function.update_self,Fin.insertNth_apply_same,bitIndex_finTwo,
    Function.update_of_ne (Fin.succAbove_ne _ _),Fin.insertNth_apply_succAbove]
  have he : (∏ i : Fin 4,(1 : Mat) (bitIndex (e i)) (bitIndex (f i))) =
      if e=f then (1 : ℂ) else 0 := by
    change tensorKernel (fun _ : Fin 4 => (1 : Mat)) e f = _
    rw [tensorKernel_one,Matrix.one_apply]
  rw [he]
  split_ifs <;> simp [pairMatrix]

theorem tensor_eq_embed (s : Fin 5) (U V : Mat) :
    tensorKernel (localMatrices s U V)=embed s (pairMatrix U V) := by
  ext x y
  obtain ⟨⟨p,e⟩,rfl⟩ := (assemblyEquiv s).surjective x
  obtain ⟨⟨q,f⟩,rfl⟩ := (assemblyEquiv s).surjective y
  rw [assembly_apply,assembly_apply,tensor_assembled,embed_assembled]

end MainTheory.PairTensorEmbedding
