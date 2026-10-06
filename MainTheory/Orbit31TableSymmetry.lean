import MainTheory.Orbit31SupportBase
import MainTheory.Orbit31PhaseRatios
import MainTheory.Orbit31SignedSupport
import MainTheory.PermutationSemanticTransport

/-! Every S3 x S4 table action is realized by physical permutations and
even-weight local X translations on the last triple. -/
set_option autoImplicit false
set_option maxHeartbeats 128000000
set_option maxRecDepth 1000000
namespace MainTheory.Orbit31TableSymmetry
open MainTheory.Orbit31SupportBase
open MainTheory.Orbit31SignedSupport (A B active)
open MainTheory.OrderEightSupportDisplays (bits)
open scoped BigOperators
noncomputable section

def rowFunctions : Fin 6 → Fin 3 → Fin 3 := ![![⟨0,by decide⟩,⟨1,by decide⟩,⟨2,by decide⟩],![⟨0,by decide⟩,⟨2,by decide⟩,⟨1,by decide⟩],![⟨1,by decide⟩,⟨0,by decide⟩,⟨2,by decide⟩],![⟨1,by decide⟩,⟨2,by decide⟩,⟨0,by decide⟩],![⟨2,by decide⟩,⟨0,by decide⟩,⟨1,by decide⟩],![⟨2,by decide⟩,⟨1,by decide⟩,⟨0,by decide⟩]]
def colFunctions : Fin 24 → Fin 4 → Fin 4 := ![![⟨0,by decide⟩,⟨1,by decide⟩,⟨2,by decide⟩,⟨3,by decide⟩],![⟨0,by decide⟩,⟨1,by decide⟩,⟨3,by decide⟩,⟨2,by decide⟩],![⟨0,by decide⟩,⟨2,by decide⟩,⟨1,by decide⟩,⟨3,by decide⟩],![⟨0,by decide⟩,⟨2,by decide⟩,⟨3,by decide⟩,⟨1,by decide⟩],![⟨0,by decide⟩,⟨3,by decide⟩,⟨1,by decide⟩,⟨2,by decide⟩],![⟨0,by decide⟩,⟨3,by decide⟩,⟨2,by decide⟩,⟨1,by decide⟩],![⟨1,by decide⟩,⟨0,by decide⟩,⟨2,by decide⟩,⟨3,by decide⟩],![⟨1,by decide⟩,⟨0,by decide⟩,⟨3,by decide⟩,⟨2,by decide⟩],![⟨1,by decide⟩,⟨2,by decide⟩,⟨0,by decide⟩,⟨3,by decide⟩],![⟨1,by decide⟩,⟨2,by decide⟩,⟨3,by decide⟩,⟨0,by decide⟩],![⟨1,by decide⟩,⟨3,by decide⟩,⟨0,by decide⟩,⟨2,by decide⟩],![⟨1,by decide⟩,⟨3,by decide⟩,⟨2,by decide⟩,⟨0,by decide⟩],![⟨2,by decide⟩,⟨0,by decide⟩,⟨1,by decide⟩,⟨3,by decide⟩],![⟨2,by decide⟩,⟨0,by decide⟩,⟨3,by decide⟩,⟨1,by decide⟩],![⟨2,by decide⟩,⟨1,by decide⟩,⟨0,by decide⟩,⟨3,by decide⟩],![⟨2,by decide⟩,⟨1,by decide⟩,⟨3,by decide⟩,⟨0,by decide⟩],![⟨2,by decide⟩,⟨3,by decide⟩,⟨0,by decide⟩,⟨1,by decide⟩],![⟨2,by decide⟩,⟨3,by decide⟩,⟨1,by decide⟩,⟨0,by decide⟩],![⟨3,by decide⟩,⟨0,by decide⟩,⟨1,by decide⟩,⟨2,by decide⟩],![⟨3,by decide⟩,⟨0,by decide⟩,⟨2,by decide⟩,⟨1,by decide⟩],![⟨3,by decide⟩,⟨1,by decide⟩,⟨0,by decide⟩,⟨2,by decide⟩],![⟨3,by decide⟩,⟨1,by decide⟩,⟨2,by decide⟩,⟨0,by decide⟩],![⟨3,by decide⟩,⟨2,by decide⟩,⟨0,by decide⟩,⟨1,by decide⟩],![⟨3,by decide⟩,⟨2,by decide⟩,⟨1,by decide⟩,⟨0,by decide⟩]]
theorem row_bijective : ∀ r, Function.Bijective (rowFunctions r) := by decide +kernel
theorem col_bijective : ∀ r, Function.Bijective (colFunctions r) := by decide +kernel
theorem row_distinct : Function.Injective rowFunctions := by decide +kernel
theorem col_distinct : Function.Injective colFunctions := by decide +kernel

def rowPerm (r : Fin 6) : Equiv.Perm (Fin 3) := Equiv.ofBijective (rowFunctions r) (row_bijective r)
def colPerm (r : Fin 24) : Equiv.Perm (Fin 4) := Equiv.ofBijective (colFunctions r) (col_bijective r)

theorem all_row_permutations : Function.Surjective rowPerm := by
  apply ((Fintype.bijective_iff_injective_and_card rowPerm).mpr ⟨?_,?_⟩).2
  · intro r s h
    exact row_distinct (congrArg (fun p : Equiv.Perm (Fin 3) => p.toFun) h)
  · norm_num [Fintype.card_perm]
theorem all_col_permutations : Function.Surjective colPerm := by
  apply ((Fintype.bijective_iff_injective_and_card colPerm).mpr ⟨?_,?_⟩).2
  · intro r s h
    exact col_distinct (congrArg (fun p : Equiv.Perm (Fin 4) => p.toFun) h)
  · norm_num [Fintype.card_perm]

def modelTable (g : Fin 144) (v : Fin 16) : Fin 16 :=
  if h : v.val < 4 then A (colFunctions ⟨g.val%24,by omega⟩ ⟨v.val,h⟩)
  else B (rowFunctions ⟨g.val/24,by omega⟩ ⟨(v.val-4)/4,by omega⟩)
    (colFunctions ⟨g.val%24,by omega⟩ ⟨(v.val-4)%4,by omega⟩)
def tablePermutation : Fin 144 → Fin 16 → Fin 16 := modelTable
theorem table_model : tablePermutation = modelTable := rfl
theorem table_bijective : ∀ g, Function.Bijective (tablePermutation g) := by decide +kernel

def rowInverse : Fin 6 → Fin 3 → Fin 3 := ![![⟨0,by decide⟩,⟨1,by decide⟩,⟨2,by decide⟩],![⟨0,by decide⟩,⟨2,by decide⟩,⟨1,by decide⟩],![⟨1,by decide⟩,⟨0,by decide⟩,⟨2,by decide⟩],![⟨2,by decide⟩,⟨0,by decide⟩,⟨1,by decide⟩],![⟨1,by decide⟩,⟨2,by decide⟩,⟨0,by decide⟩],![⟨2,by decide⟩,⟨1,by decide⟩,⟨0,by decide⟩]]
def colInput : Fin 24 → Fin 3 → Fin 3 := ![![⟨0,by decide⟩,⟨1,by decide⟩,⟨2,by decide⟩],![⟨0,by decide⟩,⟨2,by decide⟩,⟨1,by decide⟩],![⟨1,by decide⟩,⟨0,by decide⟩,⟨2,by decide⟩],![⟨2,by decide⟩,⟨0,by decide⟩,⟨1,by decide⟩],![⟨1,by decide⟩,⟨2,by decide⟩,⟨0,by decide⟩],![⟨2,by decide⟩,⟨1,by decide⟩,⟨0,by decide⟩],![⟨0,by decide⟩,⟨2,by decide⟩,⟨1,by decide⟩],![⟨0,by decide⟩,⟨1,by decide⟩,⟨2,by decide⟩],![⟨1,by decide⟩,⟨2,by decide⟩,⟨0,by decide⟩],![⟨2,by decide⟩,⟨1,by decide⟩,⟨0,by decide⟩],![⟨1,by decide⟩,⟨0,by decide⟩,⟨2,by decide⟩],![⟨2,by decide⟩,⟨0,by decide⟩,⟨1,by decide⟩],![⟨2,by decide⟩,⟨0,by decide⟩,⟨1,by decide⟩],![⟨1,by decide⟩,⟨0,by decide⟩,⟨2,by decide⟩],![⟨2,by decide⟩,⟨1,by decide⟩,⟨0,by decide⟩],![⟨1,by decide⟩,⟨2,by decide⟩,⟨0,by decide⟩],![⟨0,by decide⟩,⟨1,by decide⟩,⟨2,by decide⟩],![⟨0,by decide⟩,⟨2,by decide⟩,⟨1,by decide⟩],![⟨2,by decide⟩,⟨1,by decide⟩,⟨0,by decide⟩],![⟨1,by decide⟩,⟨2,by decide⟩,⟨0,by decide⟩],![⟨2,by decide⟩,⟨0,by decide⟩,⟨1,by decide⟩],![⟨1,by decide⟩,⟨0,by decide⟩,⟨2,by decide⟩],![⟨0,by decide⟩,⟨2,by decide⟩,⟨1,by decide⟩],![⟨0,by decide⟩,⟨1,by decide⟩,⟨2,by decide⟩]]
def colShift : Fin 24 → ℕ := ![0,0,0,0,0,0,3,3,3,3,3,3,5,5,5,5,5,5,6,6,6,6,6,6]
def qubitInput (g : Fin 144) (k : Fin 6) : Fin 6 :=
  if h : k.val < 3 then ⟨(rowInverse ⟨g.val/24,by omega⟩ ⟨k.val,h⟩).val,by omega⟩
  else ⟨3+(colInput ⟨g.val%24,by omega⟩ ⟨k.val-3,by omega⟩).val,by omega⟩
def shiftWord (g : Fin 144) : ℕ := colShift ⟨g.val%24,by omega⟩
def shift (g : Fin 144) : SS.BitString 6 := bits (shiftWord g)
theorem qubit_bijective : ∀ g, Function.Bijective (qubitInput g) := by decide +kernel
def qubitPermutation (g : Fin 144) : Equiv.Perm (Fin 6) :=
  Equiv.ofBijective (qubitInput g) (qubit_bijective g)

def physicalAction (g : Fin 144) (x : SS.BitString 6) : SS.BitString 6 :=
  fun k => xor (x (qubitInput g k)) (shift g k)
theorem actual_bottom : ∀ g v, physicalAction g (bottom v) = bottom (tablePermutation g v) := by decide +kernel
theorem actual_top : ∀ g v, physicalAction g (MainTheory.Orbit31PhaseRatios.top v) =
    MainTheory.Orbit31PhaseRatios.top (tablePermutation g v) := by decide +kernel
def physicalEquiv (g : Fin 144) : SS.BitString 6 ≃ SS.BitString 6 :=
  (SixQubit.CodeEquiv.permStrEquiv (qubitPermutation g)).trans (SS.bxorEquiv (shift g))

theorem physicalEquiv_apply (g : Fin 144) (x : SS.BitString 6) : physicalEquiv g x = physicalAction g x := rfl

theorem bottom_image (g : Fin 144) : SixQubit.Orbit31.S0.image (physicalAction g) = SixQubit.Orbit31.S0 := by
  calc
    _ = Finset.univ.image (fun v => physicalAction g (bottom v)) := by rw [← bottom_fiber,Finset.image_image]; rfl
    _ = Finset.univ.image (fun v => bottom (tablePermutation g v)) := by simp_rw [actual_bottom g]
    _ = (Finset.univ.image (tablePermutation g)).image bottom := by rw [Finset.image_image]; rfl
    _ = Finset.univ.image bottom := by rw [Finset.image_univ_of_surjective (table_bijective g).2]
    _ = SixQubit.Orbit31.S0 := bottom_fiber

theorem top_image (g : Fin 144) : SixQubit.Orbit31.S1.image (physicalAction g) = SixQubit.Orbit31.S1 := by
  have ht : Finset.univ.image MainTheory.Orbit31PhaseRatios.top = SixQubit.Orbit31.S1 := top_fiber
  calc
    _ = Finset.univ.image (fun v => physicalAction g (MainTheory.Orbit31PhaseRatios.top v)) := by rw [← ht,Finset.image_image]; rfl
    _ = Finset.univ.image (fun v => MainTheory.Orbit31PhaseRatios.top (tablePermutation g v)) := by simp_rw [actual_top g]
    _ = (Finset.univ.image (tablePermutation g)).image MainTheory.Orbit31PhaseRatios.top := by rw [Finset.image_image]; rfl
    _ = Finset.univ.image MainTheory.Orbit31PhaseRatios.top := by rw [Finset.image_univ_of_surjective (table_bijective g).2]
    _ = SixQubit.Orbit31.S1 := ht

theorem mem_iff_of_image_fixed (g : Fin 144) (S : Finset (SS.BitString 6))
    (hs : S.image (physicalAction g) = S) (x : SS.BitString 6) : physicalAction g x ∈ S ↔ x ∈ S := by
  constructor
  · intro hx
    rw [← hs] at hx
    obtain ⟨y,hy,he⟩ := Finset.mem_image.mp hx
    have hyx : y = x := (physicalEquiv g).injective he
    simpa only [hyx] using hy
  · intro hx
    rw [← hs]
    exact Finset.mem_image.mpr ⟨x,hx,rfl⟩

theorem fibres_preserved (g : Fin 144) (x : SS.BitString 6) :
    (physicalAction g x ∈ SixQubit.Orbit31.S0 ↔ x ∈ SixQubit.Orbit31.S0) ∧
    (physicalAction g x ∈ SixQubit.Orbit31.S1 ↔ x ∈ SixQubit.Orbit31.S1) :=
  ⟨mem_iff_of_image_fixed g _ (bottom_image g) x,mem_iff_of_image_fixed g _ (top_image g) x⟩

def stateAction (g : Fin 144) (c : SS.State 6 ℂ) : SS.State 6 ℂ := fun x => c (physicalAction g x)

theorem inner_preserved (g : Fin 144) (c d : SS.State 6 ℂ) :
    SS.innerC (stateAction g c) (stateAction g d) = SS.innerC c d := by
  unfold SS.innerC stateAction
  exact Equiv.sum_comp (physicalEquiv g) (fun x => star (c x) * d x)

theorem distance_preserved (g : Fin 144) (p : Fin 2 → SS.State 6 ℂ) (d : ℕ)
    (h : SS.HasDistance p d) : SS.HasDistance (fun k => stateAction g (p k)) d := by
  change SS.HasDistance (fun k => SixQubit.CodeEquiv.permAct (qubitPermutation g)
    (SixQubit.CodeEquiv.flipAct (shift g) (p k))) d
  apply MainTheory.PermutationSemanticTransport.hasDistance_permAct
  change SS.Detects (fun k => SixQubit.CodeEquiv.flipAct (shift g) (p k)) (d-1)
  apply (MainTheory.RankTwoGlobal.detects_iff_raw _ _).mpr
  exact SixQubit.CodeEquiv.detectsRaw_flipAct (shift g)
    ((MainTheory.RankTwoGlobal.detects_iff_raw _ _).mp h)

def actionNat (g : Fin 144) (mask : ℕ) : ℕ :=
  ∑ v : Fin 16, if active mask v then 2^(tablePermutation g v).val else 0

theorem power_sum : (∑ v : Fin 16, 2^v.val) = 65535 := by decide +kernel

theorem action_bound (g : Fin 144) (mask : ℕ) : actionNat g mask < 65536 := by
  have he := Equiv.sum_comp (Equiv.ofBijective (tablePermutation g) (table_bijective g))
    (fun v : Fin 16 => (2 : ℕ)^v.val)
  change (∑ v : Fin 16, 2^(tablePermutation g v).val) = ∑ v : Fin 16, 2^v.val at he
  have hl : actionNat g mask ≤ ∑ v : Fin 16, 2^(tablePermutation g v).val := by
    apply Finset.sum_le_sum
    intro v _
    split_ifs
    · exact le_refl _
    · exact Nat.zero_le _
  rw [he,power_sum] at hl
  omega

def action (g : Fin 144) (mask : Fin 65536) : Fin 65536 :=
  ⟨actionNat g mask.val,action_bound g mask.val⟩

end
end MainTheory.Orbit31TableSymmetry
