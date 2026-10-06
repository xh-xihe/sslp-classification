import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 16000000
namespace MainTheory.Orbit30ProperGraphTables
noncomputable section
def Missing (z : Fin 10 → ℂ) (m : Fin 1024) : Prop :=
  ∀ e,z e=0 ↔ Nat.testBit m.val e.val=true
def hafnian (z : Fin 10 → ℂ) : Fin 5 → ℂ :=
  ![z ⟨4,by decide⟩*z ⟨9,by decide⟩ + z ⟨5,by decide⟩*z ⟨8,by decide⟩ + z ⟨6,by decide⟩*z ⟨7,by decide⟩,z ⟨1,by decide⟩*z ⟨9,by decide⟩ + z ⟨2,by decide⟩*z ⟨8,by decide⟩ + z ⟨3,by decide⟩*z ⟨7,by decide⟩,z ⟨0,by decide⟩*z ⟨9,by decide⟩ + z ⟨2,by decide⟩*z ⟨6,by decide⟩ + z ⟨3,by decide⟩*z ⟨5,by decide⟩,z ⟨0,by decide⟩*z ⟨8,by decide⟩ + z ⟨1,by decide⟩*z ⟨6,by decide⟩ + z ⟨3,by decide⟩*z ⟨4,by decide⟩,z ⟨0,by decide⟩*z ⟨7,by decide⟩ + z ⟨1,by decide⟩*z ⟨5,by decide⟩ + z ⟨2,by decide⟩*z ⟨4,by decide⟩]
theorem odd_product_contradiction (a b c d e f : ℂ)
    (h1 : a+d=0) (h2 : b+e=0) (h3 : c+f=0)
    (he : a*b*c=d*e*f) (hn : d*e*f≠0) : False := by
  have ha : a=-d := by linear_combination h1
  have hb : b=-e := by linear_combination h2
  have hc : c=-f := by linear_combination h3
  rw [ha,hb,hc] at he
  have hz : d*e*f=0 := by linear_combination (-1/2 : ℂ)*he
  exact hn hz
theorem monomial0 (z : Fin 10 → ℂ) (hm : Missing z ⟨220,by decide⟩)
    (hh : hafnian z ⟨0,by decide⟩=0) : False := by
  have hn0 : z ⟨0,by decide⟩≠0 := by
    intro h
    have hf := (hm ⟨0,by decide⟩).1 h
    contradiction
  have hn1 : z ⟨1,by decide⟩≠0 := by
    intro h
    have hf := (hm ⟨1,by decide⟩).1 h
    contradiction
  have hz2 : z ⟨2,by decide⟩=0 := (hm ⟨2,by decide⟩).2 (by decide +kernel)
  have hz3 : z ⟨3,by decide⟩=0 := (hm ⟨3,by decide⟩).2 (by decide +kernel)
  have hz4 : z ⟨4,by decide⟩=0 := (hm ⟨4,by decide⟩).2 (by decide +kernel)
  have hn5 : z ⟨5,by decide⟩≠0 := by
    intro h
    have hf := (hm ⟨5,by decide⟩).1 h
    contradiction
  have hz6 : z ⟨6,by decide⟩=0 := (hm ⟨6,by decide⟩).2 (by decide +kernel)
  have hz7 : z ⟨7,by decide⟩=0 := (hm ⟨7,by decide⟩).2 (by decide +kernel)
  have hn8 : z ⟨8,by decide⟩≠0 := by
    intro h
    have hf := (hm ⟨8,by decide⟩).1 h
    contradiction
  have hn9 : z ⟨9,by decide⟩≠0 := by
    intro h
    have hf := (hm ⟨9,by decide⟩).1 h
    contradiction
  change z ⟨4,by decide⟩*z ⟨9,by decide⟩ + z ⟨5,by decide⟩*z ⟨8,by decide⟩ + z ⟨6,by decide⟩*z ⟨7,by decide⟩=0 at hh
  rw [hz4,hz6,hz7] at hh
  have he : z ⟨5,by decide⟩*z ⟨8,by decide⟩=0 := by linear_combination hh
  exact (mul_ne_zero hn5 hn8) he
theorem monomial1 (z : Fin 10 → ℂ) (hm : Missing z ⟨480,by decide⟩)
    (hh : hafnian z ⟨0,by decide⟩=0) : False := by
  have hn0 : z ⟨0,by decide⟩≠0 := by
    intro h
    have hf := (hm ⟨0,by decide⟩).1 h
    contradiction
  have hn1 : z ⟨1,by decide⟩≠0 := by
    intro h
    have hf := (hm ⟨1,by decide⟩).1 h
    contradiction
  have hn2 : z ⟨2,by decide⟩≠0 := by
    intro h
    have hf := (hm ⟨2,by decide⟩).1 h
    contradiction
  have hn3 : z ⟨3,by decide⟩≠0 := by
    intro h
    have hf := (hm ⟨3,by decide⟩).1 h
    contradiction
  have hn4 : z ⟨4,by decide⟩≠0 := by
    intro h
    have hf := (hm ⟨4,by decide⟩).1 h
    contradiction
  have hz5 : z ⟨5,by decide⟩=0 := (hm ⟨5,by decide⟩).2 (by decide +kernel)
  have hz6 : z ⟨6,by decide⟩=0 := (hm ⟨6,by decide⟩).2 (by decide +kernel)
  have hz7 : z ⟨7,by decide⟩=0 := (hm ⟨7,by decide⟩).2 (by decide +kernel)
  have hz8 : z ⟨8,by decide⟩=0 := (hm ⟨8,by decide⟩).2 (by decide +kernel)
  have hn9 : z ⟨9,by decide⟩≠0 := by
    intro h
    have hf := (hm ⟨9,by decide⟩).1 h
    contradiction
  change z ⟨4,by decide⟩*z ⟨9,by decide⟩ + z ⟨5,by decide⟩*z ⟨8,by decide⟩ + z ⟨6,by decide⟩*z ⟨7,by decide⟩=0 at hh
  rw [hz5,hz6,hz7,hz8] at hh
  have he : z ⟨4,by decide⟩*z ⟨9,by decide⟩=0 := by linear_combination hh
  exact (mul_ne_zero hn4 hn9) he
theorem monomial2 (z : Fin 10 → ℂ) (hm : Missing z ⟨424,by decide⟩)
    (hh : hafnian z ⟨0,by decide⟩=0) : False := by
  have hn0 : z ⟨0,by decide⟩≠0 := by
    intro h
    have hf := (hm ⟨0,by decide⟩).1 h
    contradiction
  have hn1 : z ⟨1,by decide⟩≠0 := by
    intro h
    have hf := (hm ⟨1,by decide⟩).1 h
    contradiction
  have hn2 : z ⟨2,by decide⟩≠0 := by
    intro h
    have hf := (hm ⟨2,by decide⟩).1 h
    contradiction
  have hz3 : z ⟨3,by decide⟩=0 := (hm ⟨3,by decide⟩).2 (by decide +kernel)
  have hn4 : z ⟨4,by decide⟩≠0 := by
    intro h
    have hf := (hm ⟨4,by decide⟩).1 h
    contradiction
  have hz5 : z ⟨5,by decide⟩=0 := (hm ⟨5,by decide⟩).2 (by decide +kernel)
  have hn6 : z ⟨6,by decide⟩≠0 := by
    intro h
    have hf := (hm ⟨6,by decide⟩).1 h
    contradiction
  have hz7 : z ⟨7,by decide⟩=0 := (hm ⟨7,by decide⟩).2 (by decide +kernel)
  have hz8 : z ⟨8,by decide⟩=0 := (hm ⟨8,by decide⟩).2 (by decide +kernel)
  have hn9 : z ⟨9,by decide⟩≠0 := by
    intro h
    have hf := (hm ⟨9,by decide⟩).1 h
    contradiction
  change z ⟨4,by decide⟩*z ⟨9,by decide⟩ + z ⟨5,by decide⟩*z ⟨8,by decide⟩ + z ⟨6,by decide⟩*z ⟨7,by decide⟩=0 at hh
  rw [hz5,hz7,hz8] at hh
  have he : z ⟨4,by decide⟩*z ⟨9,by decide⟩=0 := by linear_combination hh
  exact (mul_ne_zero hn4 hn9) he
theorem monomial3 (z : Fin 10 → ℂ) (hm : Missing z ⟨704,by decide⟩)
    (hh : hafnian z ⟨0,by decide⟩=0) : False := by
  have hn0 : z ⟨0,by decide⟩≠0 := by
    intro h
    have hf := (hm ⟨0,by decide⟩).1 h
    contradiction
  have hn1 : z ⟨1,by decide⟩≠0 := by
    intro h
    have hf := (hm ⟨1,by decide⟩).1 h
    contradiction
  have hn2 : z ⟨2,by decide⟩≠0 := by
    intro h
    have hf := (hm ⟨2,by decide⟩).1 h
    contradiction
  have hn3 : z ⟨3,by decide⟩≠0 := by
    intro h
    have hf := (hm ⟨3,by decide⟩).1 h
    contradiction
  have hn4 : z ⟨4,by decide⟩≠0 := by
    intro h
    have hf := (hm ⟨4,by decide⟩).1 h
    contradiction
  have hn5 : z ⟨5,by decide⟩≠0 := by
    intro h
    have hf := (hm ⟨5,by decide⟩).1 h
    contradiction
  have hz6 : z ⟨6,by decide⟩=0 := (hm ⟨6,by decide⟩).2 (by decide +kernel)
  have hz7 : z ⟨7,by decide⟩=0 := (hm ⟨7,by decide⟩).2 (by decide +kernel)
  have hn8 : z ⟨8,by decide⟩≠0 := by
    intro h
    have hf := (hm ⟨8,by decide⟩).1 h
    contradiction
  have hz9 : z ⟨9,by decide⟩=0 := (hm ⟨9,by decide⟩).2 (by decide +kernel)
  change z ⟨4,by decide⟩*z ⟨9,by decide⟩ + z ⟨5,by decide⟩*z ⟨8,by decide⟩ + z ⟨6,by decide⟩*z ⟨7,by decide⟩=0 at hh
  rw [hz6,hz7,hz9] at hh
  have he : z ⟨5,by decide⟩*z ⟨8,by decide⟩=0 := by linear_combination hh
  exact (mul_ne_zero hn5 hn8) he
theorem monomial4 (z : Fin 10 → ℂ) (hm : Missing z ⟨200,by decide⟩)
    (hh : hafnian z ⟨2,by decide⟩=0) : False := by
  have hn0 : z ⟨0,by decide⟩≠0 := by
    intro h
    have hf := (hm ⟨0,by decide⟩).1 h
    contradiction
  have hn1 : z ⟨1,by decide⟩≠0 := by
    intro h
    have hf := (hm ⟨1,by decide⟩).1 h
    contradiction
  have hn2 : z ⟨2,by decide⟩≠0 := by
    intro h
    have hf := (hm ⟨2,by decide⟩).1 h
    contradiction
  have hz3 : z ⟨3,by decide⟩=0 := (hm ⟨3,by decide⟩).2 (by decide +kernel)
  have hn4 : z ⟨4,by decide⟩≠0 := by
    intro h
    have hf := (hm ⟨4,by decide⟩).1 h
    contradiction
  have hn5 : z ⟨5,by decide⟩≠0 := by
    intro h
    have hf := (hm ⟨5,by decide⟩).1 h
    contradiction
  have hz6 : z ⟨6,by decide⟩=0 := (hm ⟨6,by decide⟩).2 (by decide +kernel)
  have hz7 : z ⟨7,by decide⟩=0 := (hm ⟨7,by decide⟩).2 (by decide +kernel)
  have hn8 : z ⟨8,by decide⟩≠0 := by
    intro h
    have hf := (hm ⟨8,by decide⟩).1 h
    contradiction
  have hn9 : z ⟨9,by decide⟩≠0 := by
    intro h
    have hf := (hm ⟨9,by decide⟩).1 h
    contradiction
  change z ⟨0,by decide⟩*z ⟨9,by decide⟩ + z ⟨2,by decide⟩*z ⟨6,by decide⟩ + z ⟨3,by decide⟩*z ⟨5,by decide⟩=0 at hh
  rw [hz3,hz6] at hh
  have he : z ⟨0,by decide⟩*z ⟨9,by decide⟩=0 := by linear_combination hh
  exact (mul_ne_zero hn0 hn9) he
theorem monomial5 (z : Fin 10 → ℂ) (hm : Missing z ⟨768,by decide⟩)
    (hh : hafnian z ⟨0,by decide⟩=0) : False := by
  have hn0 : z ⟨0,by decide⟩≠0 := by
    intro h
    have hf := (hm ⟨0,by decide⟩).1 h
    contradiction
  have hn1 : z ⟨1,by decide⟩≠0 := by
    intro h
    have hf := (hm ⟨1,by decide⟩).1 h
    contradiction
  have hn2 : z ⟨2,by decide⟩≠0 := by
    intro h
    have hf := (hm ⟨2,by decide⟩).1 h
    contradiction
  have hn3 : z ⟨3,by decide⟩≠0 := by
    intro h
    have hf := (hm ⟨3,by decide⟩).1 h
    contradiction
  have hn4 : z ⟨4,by decide⟩≠0 := by
    intro h
    have hf := (hm ⟨4,by decide⟩).1 h
    contradiction
  have hn5 : z ⟨5,by decide⟩≠0 := by
    intro h
    have hf := (hm ⟨5,by decide⟩).1 h
    contradiction
  have hn6 : z ⟨6,by decide⟩≠0 := by
    intro h
    have hf := (hm ⟨6,by decide⟩).1 h
    contradiction
  have hn7 : z ⟨7,by decide⟩≠0 := by
    intro h
    have hf := (hm ⟨7,by decide⟩).1 h
    contradiction
  have hz8 : z ⟨8,by decide⟩=0 := (hm ⟨8,by decide⟩).2 (by decide +kernel)
  have hz9 : z ⟨9,by decide⟩=0 := (hm ⟨9,by decide⟩).2 (by decide +kernel)
  change z ⟨4,by decide⟩*z ⟨9,by decide⟩ + z ⟨5,by decide⟩*z ⟨8,by decide⟩ + z ⟨6,by decide⟩*z ⟨7,by decide⟩=0 at hh
  rw [hz8,hz9] at hh
  have he : z ⟨6,by decide⟩*z ⟨7,by decide⟩=0 := by linear_combination hh
  exact (mul_ne_zero hn6 hn7) he
theorem binomial0 (z : Fin 10 → ℂ) (hm : Missing z ⟨184,by decide⟩)
    (hh : ∀ i,hafnian z i=0) : False := by
  have hn0 : z ⟨0,by decide⟩≠0 := by
    intro h
    have hf := (hm ⟨0,by decide⟩).1 h
    contradiction
  have hn1 : z ⟨1,by decide⟩≠0 := by
    intro h
    have hf := (hm ⟨1,by decide⟩).1 h
    contradiction
  have hn2 : z ⟨2,by decide⟩≠0 := by
    intro h
    have hf := (hm ⟨2,by decide⟩).1 h
    contradiction
  have hz3 : z ⟨3,by decide⟩=0 := (hm ⟨3,by decide⟩).2 (by decide +kernel)
  have hz4 : z ⟨4,by decide⟩=0 := (hm ⟨4,by decide⟩).2 (by decide +kernel)
  have hz5 : z ⟨5,by decide⟩=0 := (hm ⟨5,by decide⟩).2 (by decide +kernel)
  have hn6 : z ⟨6,by decide⟩≠0 := by
    intro h
    have hf := (hm ⟨6,by decide⟩).1 h
    contradiction
  have hz7 : z ⟨7,by decide⟩=0 := (hm ⟨7,by decide⟩).2 (by decide +kernel)
  have hn8 : z ⟨8,by decide⟩≠0 := by
    intro h
    have hf := (hm ⟨8,by decide⟩).1 h
    contradiction
  have hn9 : z ⟨9,by decide⟩≠0 := by
    intro h
    have hf := (hm ⟨9,by decide⟩).1 h
    contradiction
  have he0 := hh ⟨1,by decide⟩
  change z ⟨1,by decide⟩*z ⟨9,by decide⟩ + z ⟨2,by decide⟩*z ⟨8,by decide⟩ + z ⟨3,by decide⟩*z ⟨7,by decide⟩=0 at he0
  rw [hz3,hz7] at he0
  have hs0 : z ⟨1,by decide⟩*z ⟨9,by decide⟩+z ⟨2,by decide⟩*z ⟨8,by decide⟩=0 := by linear_combination he0
  have he1 := hh ⟨2,by decide⟩
  change z ⟨0,by decide⟩*z ⟨9,by decide⟩ + z ⟨2,by decide⟩*z ⟨6,by decide⟩ + z ⟨3,by decide⟩*z ⟨5,by decide⟩=0 at he1
  rw [hz3,hz5] at he1
  have hs1 : z ⟨2,by decide⟩*z ⟨6,by decide⟩+z ⟨0,by decide⟩*z ⟨9,by decide⟩=0 := by linear_combination he1
  have he2 := hh ⟨3,by decide⟩
  change z ⟨0,by decide⟩*z ⟨8,by decide⟩ + z ⟨1,by decide⟩*z ⟨6,by decide⟩ + z ⟨3,by decide⟩*z ⟨4,by decide⟩=0 at he2
  rw [hz3,hz4] at he2
  have hs2 : z ⟨0,by decide⟩*z ⟨8,by decide⟩+z ⟨1,by decide⟩*z ⟨6,by decide⟩=0 := by linear_combination he2
  apply odd_product_contradiction (z ⟨1,by decide⟩*z ⟨9,by decide⟩) (z ⟨2,by decide⟩*z ⟨6,by decide⟩) (z ⟨0,by decide⟩*z ⟨8,by decide⟩) (z ⟨2,by decide⟩*z ⟨8,by decide⟩) (z ⟨0,by decide⟩*z ⟨9,by decide⟩) (z ⟨1,by decide⟩*z ⟨6,by decide⟩) hs0 hs1 hs2
  · ring
  · exact mul_ne_zero (mul_ne_zero (mul_ne_zero hn2 hn8) (mul_ne_zero hn0 hn9)) (mul_ne_zero hn1 hn6)
theorem binomial1 (z : Fin 10 → ℂ) (hm : Missing z ⟨896,by decide⟩)
    (hh : ∀ i,hafnian z i=0) : False := by
  have hn0 : z ⟨0,by decide⟩≠0 := by
    intro h
    have hf := (hm ⟨0,by decide⟩).1 h
    contradiction
  have hn1 : z ⟨1,by decide⟩≠0 := by
    intro h
    have hf := (hm ⟨1,by decide⟩).1 h
    contradiction
  have hn2 : z ⟨2,by decide⟩≠0 := by
    intro h
    have hf := (hm ⟨2,by decide⟩).1 h
    contradiction
  have hn3 : z ⟨3,by decide⟩≠0 := by
    intro h
    have hf := (hm ⟨3,by decide⟩).1 h
    contradiction
  have hn4 : z ⟨4,by decide⟩≠0 := by
    intro h
    have hf := (hm ⟨4,by decide⟩).1 h
    contradiction
  have hn5 : z ⟨5,by decide⟩≠0 := by
    intro h
    have hf := (hm ⟨5,by decide⟩).1 h
    contradiction
  have hn6 : z ⟨6,by decide⟩≠0 := by
    intro h
    have hf := (hm ⟨6,by decide⟩).1 h
    contradiction
  have hz7 : z ⟨7,by decide⟩=0 := (hm ⟨7,by decide⟩).2 (by decide +kernel)
  have hz8 : z ⟨8,by decide⟩=0 := (hm ⟨8,by decide⟩).2 (by decide +kernel)
  have hz9 : z ⟨9,by decide⟩=0 := (hm ⟨9,by decide⟩).2 (by decide +kernel)
  have he0 := hh ⟨2,by decide⟩
  change z ⟨0,by decide⟩*z ⟨9,by decide⟩ + z ⟨2,by decide⟩*z ⟨6,by decide⟩ + z ⟨3,by decide⟩*z ⟨5,by decide⟩=0 at he0
  rw [hz9] at he0
  have hs0 : z ⟨2,by decide⟩*z ⟨6,by decide⟩+z ⟨3,by decide⟩*z ⟨5,by decide⟩=0 := by linear_combination he0
  have he1 := hh ⟨3,by decide⟩
  change z ⟨0,by decide⟩*z ⟨8,by decide⟩ + z ⟨1,by decide⟩*z ⟨6,by decide⟩ + z ⟨3,by decide⟩*z ⟨4,by decide⟩=0 at he1
  rw [hz8] at he1
  have hs1 : z ⟨3,by decide⟩*z ⟨4,by decide⟩+z ⟨1,by decide⟩*z ⟨6,by decide⟩=0 := by linear_combination he1
  have he2 := hh ⟨4,by decide⟩
  change z ⟨0,by decide⟩*z ⟨7,by decide⟩ + z ⟨1,by decide⟩*z ⟨5,by decide⟩ + z ⟨2,by decide⟩*z ⟨4,by decide⟩=0 at he2
  rw [hz7] at he2
  have hs2 : z ⟨1,by decide⟩*z ⟨5,by decide⟩+z ⟨2,by decide⟩*z ⟨4,by decide⟩=0 := by linear_combination he2
  apply odd_product_contradiction (z ⟨2,by decide⟩*z ⟨6,by decide⟩) (z ⟨3,by decide⟩*z ⟨4,by decide⟩) (z ⟨1,by decide⟩*z ⟨5,by decide⟩) (z ⟨3,by decide⟩*z ⟨5,by decide⟩) (z ⟨1,by decide⟩*z ⟨6,by decide⟩) (z ⟨2,by decide⟩*z ⟨4,by decide⟩) hs0 hs1 hs2
  · ring
  · exact mul_ne_zero (mul_ne_zero (mul_ne_zero hn3 hn5) (mul_ne_zero hn1 hn6)) (mul_ne_zero hn2 hn4)
theorem binomial2 (z : Fin 10 → ℂ) (hm : Missing z ⟨192,by decide⟩)
    (hh : ∀ i,hafnian z i=0) : False := by
  have hn0 : z ⟨0,by decide⟩≠0 := by
    intro h
    have hf := (hm ⟨0,by decide⟩).1 h
    contradiction
  have hn1 : z ⟨1,by decide⟩≠0 := by
    intro h
    have hf := (hm ⟨1,by decide⟩).1 h
    contradiction
  have hn2 : z ⟨2,by decide⟩≠0 := by
    intro h
    have hf := (hm ⟨2,by decide⟩).1 h
    contradiction
  have hn3 : z ⟨3,by decide⟩≠0 := by
    intro h
    have hf := (hm ⟨3,by decide⟩).1 h
    contradiction
  have hn4 : z ⟨4,by decide⟩≠0 := by
    intro h
    have hf := (hm ⟨4,by decide⟩).1 h
    contradiction
  have hn5 : z ⟨5,by decide⟩≠0 := by
    intro h
    have hf := (hm ⟨5,by decide⟩).1 h
    contradiction
  have hz6 : z ⟨6,by decide⟩=0 := (hm ⟨6,by decide⟩).2 (by decide +kernel)
  have hz7 : z ⟨7,by decide⟩=0 := (hm ⟨7,by decide⟩).2 (by decide +kernel)
  have hn8 : z ⟨8,by decide⟩≠0 := by
    intro h
    have hf := (hm ⟨8,by decide⟩).1 h
    contradiction
  have hn9 : z ⟨9,by decide⟩≠0 := by
    intro h
    have hf := (hm ⟨9,by decide⟩).1 h
    contradiction
  have he0 := hh ⟨0,by decide⟩
  change z ⟨4,by decide⟩*z ⟨9,by decide⟩ + z ⟨5,by decide⟩*z ⟨8,by decide⟩ + z ⟨6,by decide⟩*z ⟨7,by decide⟩=0 at he0
  rw [hz6,hz7] at he0
  have hs0 : z ⟨4,by decide⟩*z ⟨9,by decide⟩+z ⟨5,by decide⟩*z ⟨8,by decide⟩=0 := by linear_combination he0
  have he1 := hh ⟨1,by decide⟩
  change z ⟨1,by decide⟩*z ⟨9,by decide⟩ + z ⟨2,by decide⟩*z ⟨8,by decide⟩ + z ⟨3,by decide⟩*z ⟨7,by decide⟩=0 at he1
  rw [hz7] at he1
  have hs1 : z ⟨2,by decide⟩*z ⟨8,by decide⟩+z ⟨1,by decide⟩*z ⟨9,by decide⟩=0 := by linear_combination he1
  have he2 := hh ⟨4,by decide⟩
  change z ⟨0,by decide⟩*z ⟨7,by decide⟩ + z ⟨1,by decide⟩*z ⟨5,by decide⟩ + z ⟨2,by decide⟩*z ⟨4,by decide⟩=0 at he2
  rw [hz7] at he2
  have hs2 : z ⟨1,by decide⟩*z ⟨5,by decide⟩+z ⟨2,by decide⟩*z ⟨4,by decide⟩=0 := by linear_combination he2
  apply odd_product_contradiction (z ⟨4,by decide⟩*z ⟨9,by decide⟩) (z ⟨2,by decide⟩*z ⟨8,by decide⟩) (z ⟨1,by decide⟩*z ⟨5,by decide⟩) (z ⟨5,by decide⟩*z ⟨8,by decide⟩) (z ⟨1,by decide⟩*z ⟨9,by decide⟩) (z ⟨2,by decide⟩*z ⟨4,by decide⟩) hs0 hs1 hs2
  · ring
  · exact mul_ne_zero (mul_ne_zero (mul_ne_zero hn5 hn8) (mul_ne_zero hn1 hn9)) (mul_ne_zero hn2 hn4)
theorem binomial3 (z : Fin 10 → ℂ) (hm : Missing z ⟨512,by decide⟩)
    (hh : ∀ i,hafnian z i=0) : False := by
  have hn0 : z ⟨0,by decide⟩≠0 := by
    intro h
    have hf := (hm ⟨0,by decide⟩).1 h
    contradiction
  have hn1 : z ⟨1,by decide⟩≠0 := by
    intro h
    have hf := (hm ⟨1,by decide⟩).1 h
    contradiction
  have hn2 : z ⟨2,by decide⟩≠0 := by
    intro h
    have hf := (hm ⟨2,by decide⟩).1 h
    contradiction
  have hn3 : z ⟨3,by decide⟩≠0 := by
    intro h
    have hf := (hm ⟨3,by decide⟩).1 h
    contradiction
  have hn4 : z ⟨4,by decide⟩≠0 := by
    intro h
    have hf := (hm ⟨4,by decide⟩).1 h
    contradiction
  have hn5 : z ⟨5,by decide⟩≠0 := by
    intro h
    have hf := (hm ⟨5,by decide⟩).1 h
    contradiction
  have hn6 : z ⟨6,by decide⟩≠0 := by
    intro h
    have hf := (hm ⟨6,by decide⟩).1 h
    contradiction
  have hn7 : z ⟨7,by decide⟩≠0 := by
    intro h
    have hf := (hm ⟨7,by decide⟩).1 h
    contradiction
  have hn8 : z ⟨8,by decide⟩≠0 := by
    intro h
    have hf := (hm ⟨8,by decide⟩).1 h
    contradiction
  have hz9 : z ⟨9,by decide⟩=0 := (hm ⟨9,by decide⟩).2 (by decide +kernel)
  have he0 := hh ⟨0,by decide⟩
  change z ⟨4,by decide⟩*z ⟨9,by decide⟩ + z ⟨5,by decide⟩*z ⟨8,by decide⟩ + z ⟨6,by decide⟩*z ⟨7,by decide⟩=0 at he0
  rw [hz9] at he0
  have hs0 : z ⟨5,by decide⟩*z ⟨8,by decide⟩+z ⟨6,by decide⟩*z ⟨7,by decide⟩=0 := by linear_combination he0
  have he1 := hh ⟨1,by decide⟩
  change z ⟨1,by decide⟩*z ⟨9,by decide⟩ + z ⟨2,by decide⟩*z ⟨8,by decide⟩ + z ⟨3,by decide⟩*z ⟨7,by decide⟩=0 at he1
  rw [hz9] at he1
  have hs1 : z ⟨3,by decide⟩*z ⟨7,by decide⟩+z ⟨2,by decide⟩*z ⟨8,by decide⟩=0 := by linear_combination he1
  have he2 := hh ⟨2,by decide⟩
  change z ⟨0,by decide⟩*z ⟨9,by decide⟩ + z ⟨2,by decide⟩*z ⟨6,by decide⟩ + z ⟨3,by decide⟩*z ⟨5,by decide⟩=0 at he2
  rw [hz9] at he2
  have hs2 : z ⟨2,by decide⟩*z ⟨6,by decide⟩+z ⟨3,by decide⟩*z ⟨5,by decide⟩=0 := by linear_combination he2
  apply odd_product_contradiction (z ⟨5,by decide⟩*z ⟨8,by decide⟩) (z ⟨3,by decide⟩*z ⟨7,by decide⟩) (z ⟨2,by decide⟩*z ⟨6,by decide⟩) (z ⟨6,by decide⟩*z ⟨7,by decide⟩) (z ⟨2,by decide⟩*z ⟨8,by decide⟩) (z ⟨3,by decide⟩*z ⟨5,by decide⟩) hs0 hs1 hs2
  · ring
  · exact mul_ne_zero (mul_ne_zero (mul_ne_zero hn6 hn7) (mul_ne_zero hn2 hn8)) (mul_ne_zero hn3 hn5)
end
end MainTheory.Orbit30ProperGraphTables
