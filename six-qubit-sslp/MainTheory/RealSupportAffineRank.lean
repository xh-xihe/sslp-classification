import MainTheory.SixQubitSemanticEntrance

/-!
# Real affine rank of actual supports at arbitrary length

The rank used here is the dimension of the direction of the affine span of
the actual nonzero computational support, embedded in real coordinates.
It is invariant under local X operations and physical-qubit permutations.
When the zero word is supported, it is exactly the rank of the supported
Boolean basis used by the sparse finite-lift construction.
-/

namespace MainTheory.RealSupportAffineRank

open MainTheory
open MainTheory.CodeAffineSpanBridge
open MainTheory.SixQubitSemanticEntrance

variable {n : ℕ}

def supportPointSet (c : SS.State n ℂ) : Set (Fin n → ℝ) :=
  bitPoint '' actualSupport c

noncomputable def supportAffineRank (c : SS.State n ℂ) : ℕ :=
  Module.finrank ℝ (affineSpan ℝ (supportPointSet c)).direction

theorem supportAffineRank_le (c : SS.State n ℂ) : supportAffineRank c ≤ n := by
  have h := Submodule.finrank_le (affineSpan ℝ (supportPointSet c)).direction
  simpa [supportAffineRank] using h

/-- A supported zero word makes the affine direction equal to the linear
span; no additional dimension is lost or introduced. -/
theorem supportAffineRank_eq_finrank_span {c : SS.State n ℂ}
    (hzero : c (fun _ => false) ≠ 0) :
    supportAffineRank c = Module.finrank ℝ (Submodule.span ℝ (supportPointSet c)) := by
  have h0 : (0 : Fin n → ℝ) ∈ supportPointSet c :=
    ⟨fun _ => false, hzero, bitPoint_zeroBitString⟩
  have hset : (fun p => p -ᵥ (0 : Fin n → ℝ)) '' supportPointSet c
      = supportPointSet c := by
    ext v
    constructor
    · rintro ⟨w, hw, rfl⟩
      simpa using hw
    · intro hv
      exact ⟨v, hv, by simp⟩
  unfold supportAffineRank
  rw [direction_affineSpan, vectorSpan_eq_span_vsub_set_right ℝ h0, hset]

theorem SupportedBitBasis.rank_eq_finrank_span {c : SS.State n ℂ}
    (B : SixQubitSemanticEntrance.SupportedBitBasis c) :
    B.rank = Module.finrank ℝ (Submodule.span ℝ (supportPointSet c)) := by
  have h := finrank_span_eq_card B.independent
  rw [B.span_eq] at h
  simpa [supportPointSet] using h.symm

/-- The sparse construction's basis size is the paper's real affine rank
when the local X normalization has put zero in the actual support. -/
theorem SupportedBitBasis.rank_eq_supportAffineRank {c : SS.State n ℂ}
    (B : SixQubitSemanticEntrance.SupportedBitBasis c)
    (hzero : c (fun _ => false) ≠ 0) :
    B.rank = supportAffineRank c := by
  rw [supportAffineRank_eq_finrank_span hzero]
  exact SupportedBitBasis.rank_eq_finrank_span B

theorem supportAffineRank_eq_of_commonAffineSpan {c e : SS.State n ℂ}
    (H : CommonAffineSpanCertificate c e) :
    supportAffineRank c = supportAffineRank e := by
  unfold supportAffineRank supportPointSet
  rw [H.affineSpan_eq]

/-- The direction of an affine span transports by the linear part of an
invertible affine transformation. -/
theorem vectorSpan_image_affine {V : Type*} [AddCommGroup V] [Module ℝ V]
    (L : V ≃ₗ[ℝ] V) (a : V) (S : Set V) :
    vectorSpan ℝ ((fun v => a + L v) '' S)
      = Submodule.map (L : V →ₗ[ℝ] V) (vectorSpan ℝ S) := by
  rw [vectorSpan_def, vectorSpan_def, Submodule.map_span]
  congr 1
  ext w
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, _, ⟨y, hy, rfl⟩, rfl⟩
    refine ⟨x - y, ⟨x, hx, y, hy, rfl⟩, ?_⟩
    simp only [vsub_eq_sub, map_sub, LinearEquiv.coe_coe]
    abel
  · rintro ⟨u, ⟨x, hx, y, hy, rfl⟩, rfl⟩
    refine ⟨a + L x, ⟨x, hx, rfl⟩, a + L y, ⟨y, hy, rfl⟩, ?_⟩
    simp only [vsub_eq_sub, map_sub, LinearEquiv.coe_coe]
    abel

theorem finrank_direction_image_affine {V : Type*} [AddCommGroup V] [Module ℝ V]
    (L : V ≃ₗ[ℝ] V) (a : V) (S : Set V) :
    Module.finrank ℝ (affineSpan ℝ ((fun v => a + L v) '' S)).direction
      = Module.finrank ℝ (affineSpan ℝ S).direction := by
  rw [direction_affineSpan, direction_affineSpan, vectorSpan_image_affine,
    LinearEquiv.finrank_map_eq]

def flipLin (f : SS.BitString n) : (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ) where
  toFun v := fun j => if f j then -v j else v j
  invFun v := fun j => if f j then -v j else v j
  map_add' x y := by
    funext j
    by_cases h : f j
    · simp [h]; ring
    · simp [h]
  map_smul' a v := by funext j; by_cases h : f j <;> simp [h]
  left_inv v := by funext j; by_cases h : f j <;> simp [h]
  right_inv v := by funext j; by_cases h : f j <;> simp [h]

theorem bitPoint_bxor (s f : SS.BitString n) :
    bitPoint (SS.bxor s f) = bitPoint f + flipLin f (bitPoint s) := by
  funext j
  cases hf : f j <;> cases hs : s j <;> simp [bitPoint, flipLin, SS.bxor, hf, hs]

theorem actualSupport_bxor (c : SS.State n ℂ) (f : SS.BitString n) :
    actualSupport (fun s => c (SS.bxor s f))
      = (fun s => SS.bxor s f) '' actualSupport c := by
  ext s
  constructor
  · intro hs
    exact ⟨SS.bxor s f, hs, SS.bxor_bxor_cancel s f⟩
  · rintro ⟨s, hs, rfl⟩
    change c (SS.bxor (SS.bxor s f) f) ≠ 0
    rw [SS.bxor_bxor_cancel]
    exact hs

theorem supportAffineRank_bxor (c : SS.State n ℂ) (f : SS.BitString n) :
    supportAffineRank (fun s => c (SS.bxor s f)) = supportAffineRank c := by
  have himg : supportPointSet (fun s => c (SS.bxor s f))
      = (fun v => bitPoint f + flipLin f v) '' supportPointSet c := by
    unfold supportPointSet
    rw [actualSupport_bxor]
    ext v
    constructor
    · rintro ⟨_, ⟨s, hs, rfl⟩, rfl⟩
      exact ⟨bitPoint s, ⟨s, hs, rfl⟩, (bitPoint_bxor s f).symm⟩
    · rintro ⟨_, ⟨s, hs, rfl⟩, rfl⟩
      exact ⟨SS.bxor s f, ⟨s, hs, rfl⟩, bitPoint_bxor s f⟩
  unfold supportAffineRank
  rw [himg, finrank_direction_image_affine]

def permLin (σ : Equiv.Perm (Fin n)) : (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ) where
  toFun v := fun j => v (σ j)
  invFun v := fun j => v (σ.symm j)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv v := by funext j; simp
  right_inv v := by funext j; simp

theorem bitPoint_permStr (σ : Equiv.Perm (Fin n)) (s : SS.BitString n) :
    bitPoint (SixQubit.CodeEquiv.permStr σ s) = permLin σ (bitPoint s) := rfl

theorem actualSupport_permAct (σ : Equiv.Perm (Fin n)) (c : SS.State n ℂ) :
    actualSupport (SixQubit.CodeEquiv.permAct σ c)
      = SixQubit.CodeEquiv.permStr σ.symm '' actualSupport c := by
  ext s
  constructor
  · intro hs
    refine ⟨SixQubit.CodeEquiv.permStr σ s, hs, ?_⟩
    funext j
    simp [SixQubit.CodeEquiv.permStr]
  · rintro ⟨s, hs, rfl⟩
    change c (SixQubit.CodeEquiv.permStr σ
      (SixQubit.CodeEquiv.permStr σ.symm s)) ≠ 0
    have heq : SixQubit.CodeEquiv.permStr σ
        (SixQubit.CodeEquiv.permStr σ.symm s) = s := by
      funext j
      simp [SixQubit.CodeEquiv.permStr]
    rw [heq]
    exact hs

theorem supportAffineRank_permAct (σ : Equiv.Perm (Fin n)) (c : SS.State n ℂ) :
    supportAffineRank (SixQubit.CodeEquiv.permAct σ c) = supportAffineRank c := by
  have himg : supportPointSet (SixQubit.CodeEquiv.permAct σ c)
      = (fun v => (0 : Fin n → ℝ) + permLin σ.symm v) '' supportPointSet c := by
    unfold supportPointSet
    rw [actualSupport_permAct]
    ext v
    constructor
    · rintro ⟨_, ⟨s, hs, rfl⟩, rfl⟩
      exact ⟨bitPoint s, ⟨s, hs, rfl⟩, by simp [bitPoint_permStr]⟩
    · rintro ⟨_, ⟨s, hs, rfl⟩, rfl⟩
      exact ⟨SixQubit.CodeEquiv.permStr σ.symm s, ⟨s, hs, rfl⟩,
        by simp [bitPoint_permStr]⟩
  unfold supportAffineRank
  rw [himg, finrank_direction_image_affine]

end MainTheory.RealSupportAffineRank
