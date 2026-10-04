import Mathlib

-- Preserve upstream proofs; suppress only the recorded style linters.
set_option linter.unusedSimpArgs false

namespace Orbit2.TensorPauli
open scoped BigOperators
open Matrix

/-- A tensor product defined entry by entry in the computational basis. -/
def tensor {n : ℕ} (A : Fin n → Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ := fun x y => ∏ i, A i (x i) (y i)

theorem tensor_mul {n : ℕ} (A B : Fin n → Matrix (Fin 2) (Fin 2) ℂ) :
    tensor A * tensor B = tensor (fun i => A i * B i) := by
  ext x z
  simp only [tensor, Matrix.mul_apply]
  simp_rw [← Finset.prod_mul_distrib]
  simpa using (Finset.prod_univ_sum (fun _ : Fin n => (Finset.univ : Finset (Fin 2)))
    (fun i y => A i (x i) y * B i y (z i))).symm

theorem tensor_smul {n : ℕ} (s : Fin n → ℂ) (A : Fin n → Matrix (Fin 2) (Fin 2) ℂ) :
    tensor (fun i => s i • A i) = (∏ i, s i) • tensor A := by
  ext x y
  simp [tensor, Finset.prod_mul_distrib]

theorem trace_tensor {n : ℕ} (A : Fin n → Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix.trace (tensor A) = ∏ i, Matrix.trace (A i) := by
  simp only [Matrix.trace, Matrix.diag, tensor]
  simpa using (Finset.prod_univ_sum (fun _ : Fin n => (Finset.univ : Finset (Fin 2)))
    (fun i x => A i x x)).symm

theorem tensor_conjTranspose {n : ℕ} (A : Fin n → Matrix (Fin 2) (Fin 2) ℂ) :
    (tensor A).conjTranspose = tensor (fun i => (A i).conjTranspose) := by
  ext x y
  simp [tensor, Matrix.conjTranspose_apply]

/-- Exact Gaussian integer matrices for I, X, Y, Z. -/
def localG : Fin 4 → Matrix (Fin 2) (Fin 2) GaussianInt :=
  ![![![1,0],![0,1]], ![![0,1],![1,0]],
    ![![0,⟨0,-1⟩],![⟨0,1⟩,0]], ![![1,0],![0,-1]]]

def localMul : Fin 4 → Fin 4 → Fin 4 :=
  ![![0,1,2,3], ![1,0,3,2], ![2,3,0,1], ![3,2,1,0]]

def localPhase : Fin 4 → Fin 4 → GaussianInt :=
  ![![1,1,1,1], ![1,1,⟨0,1⟩,⟨0,-1⟩],
    ![1,⟨0,-1⟩,1,⟨0,1⟩], ![1,⟨0,1⟩,⟨0,-1⟩,1]]

theorem localG_mul : ∀ a b, localG a * localG b = localPhase a b • localG (localMul a b) := by
  decide +kernel

theorem localG_trace : ∀ a, Matrix.trace (localG a) = if a = 0 then 2 else 0 := by
  decide +kernel

theorem localG_hermitian : ∀ a, (localG a).conjTranspose = localG a := by
  decide +kernel

def localC (a : Fin 4) : Matrix (Fin 2) (Fin 2) ℂ := (localG a).map GaussianInt.toComplex

theorem local_mul (a b : Fin 4) :
    localC a * localC b = (localPhase a b : ℂ) • localC (localMul a b) := by
  unfold localC
  rw [← Matrix.map_mul, localG_mul]
  ext x y
  simp [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, GaussianInt.toComplex_mul]

theorem local_trace (a : Fin 4) : Matrix.trace (localC a) = if a = 0 then 2 else 0 := by
  fin_cases a <;> norm_num [localC, localG, Matrix.trace, Matrix.diag,
    GaussianInt.toComplex_def]

theorem local_hermitian (a : Fin 4) : (localC a).conjTranspose = localC a := by
  ext x y
  have h := congrArg (fun M => (M x y : GaussianInt)) (localG_hermitian a)
  have hc := congrArg GaussianInt.toComplex h
  simpa [localC, Matrix.conjTranspose_apply, Matrix.map_apply, GaussianInt.toComplex_star] using hc

abbrev Label (n : ℕ) := Fin n → Fin 4

def operator {n : ℕ} (p : Label n) := tensor (fun i => localC (p i))

def product {n : ℕ} (p q : Label n) : Label n := fun i => localMul (p i) (q i)

def phase {n : ℕ} (p q : Label n) : GaussianInt := ∏ i, localPhase (p i) (q i)

theorem localMul_zero_left : ∀ a, localMul 0 a = a := by decide +kernel
theorem localMul_zero_right : ∀ a, localMul a 0 = a := by decide +kernel
theorem localMul_comm : ∀ a b, localMul a b = localMul b a := by decide +kernel
theorem localMul_eq_zero : ∀ a b, localMul a b = 0 ↔ a = b := by decide +kernel
theorem localPhase_self : ∀ a, localPhase a a = 1 := by decide +kernel
theorem localMul_assoc : ∀ a b c, localMul (localMul a b) c = localMul a (localMul b c) := by
  decide +kernel
theorem localMul_four_zero : ∀ a b c d,
    localMul (localMul (localMul a b) c) d = 0 ↔ localMul a c = localMul b d := by
  decide +kernel
theorem localMul_pair_exchange : ∀ a b c d,
    localMul b a = localMul d c → localMul a c = localMul b d := by
  decide +kernel
theorem localMul_cross_exchange : ∀ a b c d,
    localMul b c = localMul a d → localMul a c = localMul b d := by
  decide +kernel

theorem product_zero_left {n : ℕ} (p : Label n) : product (fun _ => 0) p = p := by
  funext i; exact localMul_zero_left _

theorem product_comm {n : ℕ} (p q : Label n) : product p q = product q p := by
  funext i; exact localMul_comm _ _

theorem pair_exchange {n : ℕ} (a b c d : Label n)
    (h : product b a = product d c) : product a c = product b d := by
  funext i
  exact localMul_pair_exchange _ _ _ _ (congrFun h i)

theorem cross_exchange {n : ℕ} (a b c d : Label n)
    (h : product b c = product a d) : product a c = product b d := by
  funext i
  exact localMul_cross_exchange _ _ _ _ (congrFun h i)

theorem operator_mul {n : ℕ} (p q : Label n) :
    operator p * operator q = (phase p q : ℂ) • operator (product p q) := by
  rw [operator, operator, tensor_mul]
  simp_rw [local_mul]
  rw [tensor_smul]
  simp [phase, operator, product, map_prod]

theorem operator_hermitian {n : ℕ} (p : Label n) : (operator p).conjTranspose = operator p := by
  simp [operator, tensor_conjTranspose, local_hermitian]

theorem operator_trace {n : ℕ} (p : Label n) :
    Matrix.trace (operator p) = if p = (fun _ => 0) then (2 : ℂ)^n else 0 := by
  rw [operator, trace_tensor]
  simp_rw [local_trace]
  by_cases hp : p = fun _ => 0
  · simp [hp]
  · simp only [hp, if_false]
    obtain ⟨i, hi⟩ : ∃ i, p i ≠ 0 := by
      by_contra h
      push_neg at h
      exact hp (funext h)
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [hi]

noncomputable def tau {n : ℕ} (A : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ) : ℂ :=
  Matrix.trace A / (2 : ℂ)^n

theorem tau_operator {n : ℕ} (p : Label n) :
    tau (operator p) = if p = (fun _ => 0) then 1 else 0 := by
  unfold tau
  rw [operator_trace]
  split_ifs <;> simp

theorem product_eq_zero_iff {n : ℕ} (p q : Label n) :
    product p q = (fun _ => 0) ↔ p = q := by
  constructor
  · intro h
    funext i
    exact (localMul_eq_zero _ _).mp (congrFun h i)
  · rintro rfl
    funext i
    exact (localMul_eq_zero _ _).mpr rfl

theorem phase_self {n : ℕ} (p : Label n) : phase p p = 1 := by
  simp [phase, localPhase_self]

theorem tau_operator_pair {n : ℕ} (p q : Label n) :
    tau (operator p * operator q) = if p = q then 1 else 0 := by
  rw [operator_mul]
  unfold tau
  rw [Matrix.trace_smul, operator_trace]
  by_cases h : p=q
  · subst q
    simp [phase_self, product_eq_zero_iff]
  · simp [product_eq_zero_iff, h]

theorem tau_smul {n : ℕ} (a : ℂ) (M : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ) :
    tau (a • M) = a * tau M := by simp [tau, Matrix.trace_smul]; ring

theorem tau_add {n : ℕ} (A B : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ) :
    tau (A+B) = tau A + tau B := by simp [tau, add_div]

theorem tau_sum {n : ℕ} {ι : Type*} (s : Finset ι)
    (A : ι → Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ) :
    tau (∑ i ∈ s, A i) = ∑ i ∈ s, tau (A i) := by simp [tau, Finset.sum_div]

theorem localC_zero : localC 0 = 1 := by
  ext x y
  fin_cases x <;> fin_cases y <;> norm_num [localC, localG, GaussianInt.toComplex_def]

theorem operator_zero {n : ℕ} : operator (fun _ : Fin n => 0) = 1 := by
  ext x y
  simp only [operator, tensor, localC_zero, Matrix.one_apply]
  by_cases hxy : x = y
  · subst y
    simp
  · obtain ⟨i,hi⟩ : ∃ i, x i ≠ y i := by
      by_contra h
      push_neg at h
      exact hxy (funext h)
    simp only [hxy, if_false]
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [hi]

/-- Exact multiplication state of a Pauli word. -/
def wordData {n : ℕ} (ps : List (Label n)) : GaussianInt × Label n :=
  ps.foldl (fun s q => (s.1 * phase s.2 q, product s.2 q)) (1, fun _ => 0)

def wordTrace {n : ℕ} (ps : List (Label n)) : GaussianInt :=
  let s := wordData ps
  if s.2 = (fun _ => 0) then s.1 else 0

theorem wordData_four_label {n : ℕ} (a b c d : Label n) :
    (wordData [a,b,c,d]).2 = product (product (product a b) c) d := by
  simp [wordData, List.foldl_cons, product_zero_left]

/-- Different quadratic Pauli characters cannot contribute to a four-word trace. -/
theorem wordTrace_four_zero {n : ℕ} (a b c d : Label n)
    (h : product a c ≠ product b d) : wordTrace [a,b,c,d] = 0 := by
  have hn : (wordData [a,b,c,d]).2 ≠ (fun _ => 0) := by
    intro hz
    apply h
    funext i
    have hi := congrFun (wordData_four_label a b c d) i
    rw [hz] at hi
    exact (localMul_four_zero _ _ _ _).mp hi.symm
  simp [wordTrace, hn]

noncomputable def wordOperator {n : ℕ} (ps : List (Label n)) :
    Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ :=
  ps.foldl (fun M q => M * operator q) 1

theorem fold_operator {n : ℕ} (ps : List (Label n)) (a : GaussianInt) (p : Label n) :
    let s := ps.foldl (fun s q => (s.1 * phase s.2 q, product s.2 q)) (a,p)
    (s.1 : ℂ) • operator s.2 = ps.foldl (fun M q => M * operator q) ((a : ℂ) • operator p) := by
  induction ps generalizing a p with
  | nil => rfl
  | cons q ps ih =>
    simp only [List.foldl_cons]
    rw [ih]
    congr 1
    rw [Matrix.smul_mul, operator_mul, smul_smul]
    simp [GaussianInt.toComplex_mul]

theorem wordData_operator {n : ℕ} (ps : List (Label n)) :
    ((wordData ps).1 : ℂ) • operator (wordData ps).2 = wordOperator ps := by
  simpa [wordData, wordOperator, operator_zero] using fold_operator ps 1 (fun _ => 0)

/-- The finite exact word-trace algorithm agrees with actual matrix traces. -/
theorem wordTrace_correct {n : ℕ} (ps : List (Label n)) :
    tau (wordOperator ps) = (wordTrace ps : ℂ) := by
  rw [← wordData_operator, tau_smul, tau_operator]
  by_cases h : (wordData ps).2 = (fun _ => 0) <;> simp [wordTrace, h]

/-- A sparse Pauli expansion with genuinely complex coefficients. -/
noncomputable def expansion {n : ℕ} {ι : Type*} [Fintype ι]
    (labels : ι → Label n) (t : ι → ℂ) := ∑ i, t i • operator (labels i)

theorem expansion_conjTranspose {n : ℕ} {ι : Type*} [Fintype ι]
    (labels : ι → Label n) (t : ι → ℂ) :
    (expansion labels t).conjTranspose = expansion labels (fun i => star (t i)) := by
  simp [expansion, Matrix.conjTranspose_sum, Matrix.conjTranspose_smul, operator_hermitian]

/-- Exact trace expansion for two possibly different sparse Pauli sums. -/
theorem tau_expansion_mul {n : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]
    (p : ι → Label n) (q : κ → Label n) (a : ι → ℂ) (b : κ → ℂ) :
    tau (expansion p a * expansion q b) =
      ∑ j, ∑ i, a i * b j * (wordTrace [p i, q j] : ℂ) := by
  unfold expansion
  simp only [Matrix.sum_mul, Matrix.mul_sum, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, tau_sum, tau_smul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  have hw := wordTrace_correct [p i, q j]
  simpa [wordOperator, mul_assoc, mul_comm, mul_left_comm] using
    congrArg (fun x => a i * b j * x) hw

/-- Bidegree (2,2) traces are obtained by exact four-letter word multiplication. -/
theorem tau_expansion_four {n : ℕ} {ι : Type*} [Fintype ι]
    (p : ι → Label n) (a b c d : ι → ℂ) :
    tau (expansion p a * expansion p b * expansion p c * expansion p d) =
      ∑ l, ∑ k, ∑ j, ∑ i,
        a i * b j * c k * d l * (wordTrace [p i,p j,p k,p l] : ℂ) := by
  unfold expansion
  simp only [Matrix.sum_mul, Matrix.mul_sum, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, tau_sum, tau_smul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l _
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  have hw := wordTrace_correct [p i,p j,p k,p l]
  simpa [wordOperator, mul_assoc, mul_comm, mul_left_comm] using
    congrArg (fun x => a i * b j * c k * d l * x) hw

end Orbit2.TensorPauli
