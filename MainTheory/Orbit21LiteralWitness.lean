import MainTheory.Orbit21LiteralData

set_option autoImplicit false

namespace MainTheory.Orbit21LiteralWitness

open SixQubit.Realize MainTheory.Orbit21LiteralData

def bottomSign (x : SS.BitString 6) : ℤ :=
  if x=bits 0 ∨ x=bits 9 ∨ x=bits 23 ∨ x=bits 28 ∨ x=bits 44 ∨ x=bits 59 then 1
  else if x=bits 39 ∨ x=bits 50 then -1 else 0

def topSign (x : SS.BitString 6) : ℤ :=
  if x=bits 4 ∨ x=bits 24 ∨ x=bits 54 ∨ x=bits 63 then 1
  else if x=bits 13 ∨ x=bits 19 ∨ x=bits 35 ∨ x=bits 40 then -1 else 0

theorem bottom_data : ∀ x : SS.BitString 6,c0z x=z8 0 (bottomSign x) 0 0 0 0 0 0 := by
  decide +kernel
theorem top_data : ∀ x : SS.BitString 6,c1z x=z8 0 (topSign x) 0 0 0 0 0 0 := by
  decide +kernel

theorem coefficient (n : ℤ) :
    (1/4 : ℂ)*toC (z8 0 n 0 0 0 0 0 0)=(n : ℂ)/(Real.sqrt 8 : ℂ) := by
  have h8 : Real.sqrt 8=2*Real.sqrt 2 := by
    rw [show (8 : ℝ)=4*2 by norm_num,Real.sqrt_mul (by norm_num)]
    norm_num
  have h2 : (Real.sqrt 2 : ℂ)^2=2 := by exact_mod_cast Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hn : (Real.sqrt 2 : ℂ) ≠ 0 := by
    exact_mod_cast Real.sqrt_ne_zero'.mpr (by norm_num : (0 : ℝ) < 2)
  have he : toC (z8 0 n 0 0 0 0 0 0)=(n : ℂ)*(Real.sqrt 2 : ℂ) := by
    apply Complex.ext <;> simp [toC,toCre,toCim,rz,SS.rp,z8]
  rw [he,h8]
  push_cast
  field_simp
  linear_combination 2*(n : ℂ)*h2

noncomputable def w0 : SS.State 6 ℂ := fun x => (bottomSign x : ℂ)/(Real.sqrt 8 : ℂ)
noncomputable def w1 : SS.State 6 ℂ := fun x => (topSign x : ℂ)/(Real.sqrt 8 : ℂ)

theorem actual_words : w0=stC (1/4) c0z ∧ w1=stC (1/4) c1z := by
  constructor <;> funext x
  · rw [w0,stC,bottom_data,coefficient]
  · rw [w1,stC,top_data,coefficient]

theorem is_code : SS.HasDistance ![w0,w1] 3 := by
  rw [actual_words.1,actual_words.2]
  exact is_code_of_check (1/4) c0z c1z L0 L1 L0_nodup L1_nodup vanishes0 vanishes1 check_all

theorem normalized : SS.innerC w0 w0=1 ∧ SS.innerC w1 w1=1 := by
  have hsc : star (1/4 : ℂ)*(1/4 : ℂ)*(16 : ℂ)=1 := by norm_num [Complex.star_def]
  rw [actual_words.1,actual_words.2]
  exact ⟨normalized_of (1/4) c0z L0 L0_nodup vanishes0 16 norm0 hsc,
    normalized_of (1/4) c1z L1 L1_nodup vanishes1 16 norm1 hsc⟩

theorem fibers :
    (∀ x,SS.weight SixQubit.Orbit21Cert.av x ≠ 0 → w0 x=0) ∧
    (∀ x,SS.weight SixQubit.Orbit21Cert.av x ≠ 2 → w1 x=0) := by
  constructor
  · intro x hx
    rw [actual_words.1]
    apply stC_vanishes (1/4) c0z L0 vanishes0 x
    exact fun h => hx (support0 x h)
  · intro x hx
    rw [actual_words.2]
    apply stC_vanishes (1/4) c1z L1 vanishes1 x
    exact fun h => hx (support1 x h)

end MainTheory.Orbit21LiteralWitness
