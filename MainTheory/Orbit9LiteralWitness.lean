import MainTheory.SixthRootCoefficients
import SixQubit.Orbit9Real

set_option autoImplicit false

namespace MainTheory.Orbit9LiteralWitness

open SixQubit.Realize MainTheory.SixthRootCoefficients

/-- Binary words are encoded by their usual displayed integer value;
`Realize.num` assigns qubit zero to the rightmost displayed bit. -/
def bottom : List (ℕ × Fin 6 × ℕ) :=
  [(0,5,12),(7,2,12),(14,3,12),(22,3,12),(25,2,6),(33,0,12),
   (40,3,12),(47,2,12),(48,5,12),(55,0,12),(62,5,12)]

def top : List (ℕ × Fin 6 × ℕ) :=
  [(1,5,12),(8,4,12),(15,5,12),(16,2,12),(23,1,12),(30,4,12),
   (38,5,6),(41,1,12),(49,1,12),(56,2,12),(63,5,12)]

def dataAt : List (ℕ × Fin 6 × ℕ) → ℕ → ZQ
  | [],_ => ZQ.zero
  | (word,k,d)::rows,n => if n=word then
      if d=6 then largeData k else smallData k else dataAt rows n

noncomputable def valueAt : List (ℕ × Fin 6 × ℕ) → ℕ → ℂ
  | [],_ => 0
  | (word,k,d)::rows,n => if n=word then
      root^(k : ℕ)/(Real.sqrt d : ℂ) else valueAt rows n

theorem bottom_data : ∀ x : SS.BitString 6,
    SixQubit.Orbit9Real.c0z x=dataAt bottom (num x) := by decide +kernel

theorem top_data : ∀ x : SS.BitString 6,
    SixQubit.Orbit9Real.c1z x=dataAt top (num x) := by decide +kernel

theorem data_semantics (rows : List (ℕ × Fin 6 × ℕ))
    (hrows : ∀ row ∈ rows,row.2.2=6 ∨ row.2.2=12) (n : ℕ) :
    toC (dataAt rows n)/12=valueAt rows n := by
  induction rows with
  | nil => simp [dataAt,valueAt,toC_zero]
  | cons row rows ih =>
    obtain ⟨word,k,d⟩ := row
    have hd : d=6 ∨ d=12 := hrows _ List.mem_cons_self
    have ht : ∀ row ∈ rows,row.2.2=6 ∨ row.2.2=12 :=
      fun row hr => hrows row (List.mem_cons_of_mem _ hr)
    by_cases hn : n=word
    · rcases hd with rfl | rfl <;>
        simp [dataAt,valueAt,hn,small_coefficient,large_coefficient]
    · simp [dataAt,valueAt,hn,ih ht]

theorem actual_words :
    SixQubit.Orbit9Real.w0=(fun x => valueAt bottom (num x)) ∧
    SixQubit.Orbit9Real.w1=(fun x => valueAt top (num x)) := by
  have hb : ∀ row ∈ bottom,row.2.2=6 ∨ row.2.2=12 := by decide
  have ht : ∀ row ∈ top,row.2.2=6 ∨ row.2.2=12 := by decide
  constructor <;> funext x
  · change (1/12 : ℂ)*toC (SixQubit.Orbit9Real.c0z x)=_
    rw [bottom_data]
    have h := data_semantics bottom hb (num x)
    convert h using 1; ring
  · change (1/12 : ℂ)*toC (SixQubit.Orbit9Real.c1z x)=_
    rw [top_data]
    have h := data_semantics top ht (num x)
    convert h using 1; ring

theorem literal_code : SS.HasDistance
    ![(fun x => valueAt bottom (num x)),(fun x => valueAt top (num x))] 3 := by
  rw [← actual_words.1,← actual_words.2]
  exact SixQubit.Orbit9Real.is_code

theorem literal_normalized :
    SS.innerC (fun x => valueAt bottom (num x)) (fun x => valueAt bottom (num x))=1 ∧
    SS.innerC (fun x => valueAt top (num x)) (fun x => valueAt top (num x))=1 := by
  rw [← actual_words.1,← actual_words.2]
  exact ⟨SixQubit.Orbit9Real.w0_normalized,SixQubit.Orbit9Real.w1_normalized⟩

end MainTheory.Orbit9LiteralWitness
