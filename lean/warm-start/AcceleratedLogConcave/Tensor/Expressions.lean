import AcceleratedLogConcave.Tensor.SplitNorm
import Mathlib.Tactic
import Mathlib.Analysis.Calculus.FDeriv.Basic

/-!
# The restricted tensor-expression tree

All slot positions are separate from their physical coordinate values.
Contraction removes one slot in each of two operands, retaining at least one
in each. Adjoint divergence retains at least one slot. The grammar has no
scalar or internal-trace constructor. Repeated occurrences are counted as
separate tree positions, even if their coefficient names or values coincide.
-/

open scoped NNReal

namespace AcceleratedLogConcave.Tensor

/-- Metadata only: analytic values and estimates do not belong to the grammar. -/
structure CoefficientSignature (Name : Type*) where
  arity : Name → ℕ
  size : Name → ℕ
  weight : Name → ℝ≥0
  two_le_arity : ∀ c, 2 ≤ arity c
  arity_le_size : ∀ c, arity c ≤ size c

variable {Name : Type*} (σ : CoefficientSignature Name)

/-- A literal finite formula, indexed by the number of free tensor slots. -/
inductive Expr : ℕ → Type _
  | coefficient (name : Name) : Expr (σ.arity name)
  | permute {r : ℕ} (permutation : Equiv.Perm (Fin r)) (operand : Expr r) : Expr r
  | contract {r s : ℕ} (left : Expr (r+2)) (right : Expr (s+2))
      (leftSlot : Fin (r+2)) (rightSlot : Fin (s+2)) : Expr (r+s+2)
  | derivative {r : ℕ} (operand : Expr r) : Expr (r+1)
  | adjoint {r : ℕ} (slot : Fin (r+2)) (operand : Expr (r+2)) : Expr (r+1)

namespace Expr
variable {σ} {r : ℕ}

/-- Permutations have zero size cost; the three genuine operations cost one. -/
def size : {r : ℕ} → Expr σ r → ℕ
  | _, .coefficient c => σ.size c
  | _, .permute _ e => size e
  | _, .contract e f _ _ => size e + size f + 1
  | _, .derivative e => size e + 1
  | _, .adjoint _ e => size e + 1

/-- Smoothing weights are nonnegative reals, as in the manuscript. -/
def weight : {r : ℕ} → Expr σ r → ℝ≥0
  | _, .coefficient c => σ.weight c
  | _, .permute _ e => weight e
  | _, .contract e f _ _ => weight e + weight f
  | _, .derivative e => weight e + 1
  | _, .adjoint _ e => weight e + 1

/-- The leaf inventory is a list, not a set: repeated names retain multiplicity. -/
def coefficients : {r : ℕ} → Expr σ r → List Name
  | _, .coefficient c => [c]
  | _, .permute _ e => coefficients e
  | _, .contract e f _ _ => coefficients e ++ coefficients f
  | _, .derivative e => coefficients e
  | _, .adjoint _ e => coefficients e

def operationCount : {r : ℕ} → Expr σ r → ℕ
  | _, .coefficient _ => 0
  | _, .permute _ e => operationCount e
  | _, .contract e f _ _ => operationCount e + operationCount f + 1
  | _, .derivative e => operationCount e + 1
  | _, .adjoint _ e => operationCount e + 1

/-- Binary tree addresses distinguish occurrences, including equal operands.
Unary constructors use the `false` child; contraction uses both children. -/
def leafAddresses : {r : ℕ} → Expr σ r → List (List Bool)
  | _, .coefficient _ => [[]]
  | _, .permute _ e => (leafAddresses e).map (List.cons false)
  | _, .contract e f _ _ =>
      (leafAddresses e).map (List.cons false) ++ (leafAddresses f).map (List.cons true)
  | _, .derivative e => (leafAddresses e).map (List.cons false)
  | _, .adjoint _ e => (leafAddresses e).map (List.cons false)

/-- Every grammar expression has at least one free slot. -/
theorem arity_pos (e : Expr σ r) : 0 < r := by
  induction e with
  | coefficient c => exact lt_of_lt_of_le (by decide : 0 < 2) (σ.two_le_arity c)
  | permute p e ih => exact ih
  | contract e f i j ih₁ ih₂ => omega
  | derivative e ih => omega
  | adjoint i e ih => omega

/-- There is no hidden scalar expression, even under arbitrarily nested adjoints. -/
instance : IsEmpty (Expr σ 0) := ⟨fun e => Nat.not_lt_zero _ (arity_pos e)⟩

theorem arity_le_size (e : Expr σ r) : r ≤ e.size := by
  induction e with
  | coefficient c => exact σ.arity_le_size c
  | permute p e ih => exact ih
  | contract e f i j ih₁ ih₂ => simp only [size]; omega
  | derivative e ih => simp only [size]; omega
  | adjoint i e ih => simp only [size]; omega

theorem size_eq (e : Expr σ r) :
    e.size = (e.coefficients.map σ.size).sum + e.operationCount := by
  induction e with
  | coefficient c => simp [size, coefficients, operationCount]
  | permute p e ih => exact ih
  | contract e f i j ih₁ ih₂ =>
    simp only [size, coefficients, operationCount, List.map_append, List.sum_append]
    omega
  | derivative e ih => simp only [size, coefficients, operationCount]; omega
  | adjoint i e ih => simp only [size, coefficients, operationCount]; omega

theorem leafAddresses_length (e : Expr σ r) :
    e.leafAddresses.length = e.coefficients.length := by
  induction e <;> simp_all [leafAddresses, coefficients]

private lemma nodup_prefix {α : Type*} (b : α) {l : List (List α)}
    (h : l.Nodup) : (l.map (List.cons b)).Nodup :=
  h.map (fun _ _ hh => List.cons.inj hh |>.2)

private lemma disjoint_prefix {α : Type*} {a b : α} (hab : a ≠ b)
    (l m : List (List α)) :
    List.Disjoint (l.map (List.cons a)) (m.map (List.cons b)) := by
  intro p hp hq
  obtain ⟨x, _, hx⟩ := List.mem_map.mp hp
  obtain ⟨y, _, hy⟩ := List.mem_map.mp hq
  exact hab (List.cons.inj (hx.trans hy.symm)).1

/-- A tree address is an injective identifier for each coefficient occurrence. -/
theorem leafAddresses_nodup (e : Expr σ r) : e.leafAddresses.Nodup := by
  induction e with
  | coefficient c => simp [leafAddresses]
  | permute p e ih => exact nodup_prefix _ ih
  | contract e f i j ih₁ ih₂ =>
    refine List.nodup_append.mpr ⟨nodup_prefix _ ih₁, nodup_prefix _ ih₂, ?_⟩
    intro a ha b hb hab
    subst b
    exact disjoint_prefix (by decide : false ≠ true) _ _ ha hb
  | derivative e ih => exact nodup_prefix _ ih
  | adjoint i e ih => exact nodup_prefix _ ih

/-- Occurrences are positions in the leaf inventory, not distinct coefficient names. -/
abbrev Occurrence (e : Expr σ r) := Fin e.coefficients.length

def occurrenceName (e : Expr σ r) (i : e.Occurrence) : Name := e.coefficients[i]

def occurrenceAddress (e : Expr σ r) (i : e.Occurrence) : List Bool :=
  e.leafAddresses.get ⟨i.val, by rw [e.leafAddresses_length]; exact i.isLt⟩

@[simp] theorem coefficient_size (c : Name) : (coefficient (σ := σ) c).size = σ.size c := rfl
@[simp] theorem coefficient_weight (c : Name) : (coefficient (σ := σ) c).weight = σ.weight c := rfl
@[simp] theorem permute_size (p : Equiv.Perm (Fin r)) (e : Expr σ r) :
    (permute p e).size = e.size := rfl
@[simp] theorem permute_weight (p : Equiv.Perm (Fin r)) (e : Expr σ r) :
    (permute p e).weight = e.weight := rfl
@[simp] theorem contract_size {s : ℕ} (e : Expr σ (r+2)) (f : Expr σ (s+2))
    (i : Fin (r+2)) (j : Fin (s+2)) :
    (contract e f i j).size = e.size + f.size + 1 := rfl
@[simp] theorem contract_weight {s : ℕ} (e : Expr σ (r+2)) (f : Expr σ (s+2))
    (i : Fin (r+2)) (j : Fin (s+2)) :
    (contract e f i j).weight = e.weight + f.weight := rfl
@[simp] theorem derivative_size (e : Expr σ r) : (derivative e).size = e.size + 1 := rfl
@[simp] theorem derivative_weight (e : Expr σ r) : (derivative e).weight = e.weight + 1 := rfl
@[simp] theorem adjoint_size (e : Expr σ (r+2)) (i : Fin (r+2)) :
    (adjoint i e).size = e.size + 1 := rfl
@[simp] theorem adjoint_weight (e : Expr σ (r+2)) (i : Fin (r+2)) :
    (adjoint i e).weight = e.weight + 1 := rfl

end Expr
end AcceleratedLogConcave.Tensor


noncomputable section
open WithLp
open scoped BigOperators Classical
namespace AcceleratedLogConcave.Tensor

variable {Name : Type*} (σ : CoefficientSignature Name) (D : ℕ)

/-- Values of named coefficient fields, separate from syntactic metadata. -/
abbrev CoefficientEnvironment := ∀ c : Name,
  EuclideanSpace ℝ (Fin D) → Coeff (Fin (σ.arity c)) D

/-- A coordinate direction in the physical Euclidean space. -/
def coordinateDirection (k : Fin D) : EuclideanSpace ℝ (Fin D) := toLp 2 (Pi.single k 1)

/-- Coordinate contraction of one distinct slot in each operand. -/
def crossContract {r s : ℕ} (A : Coeff (Fin (r+2)) D) (B : Coeff (Fin (s+2)) D)
    (i : Fin (r+2)) (j : Fin (s+2)) : Coeff (Fin (r+s+2)) D :=
  toLp 2 (fun a => ∑ k : Fin D,
    A (Fin.insertNth i k (fun t : Fin (r+1) =>
      a (Fin.cast (by omega : (r+1)+(s+1) = r+s+2) (Fin.castAdd (s+1) t)))) *
    B (Fin.insertNth j k (fun t : Fin (s+1) =>
      a (Fin.cast (by omega : (r+1)+(s+1) = r+s+2) (Fin.natAdd (r+1) t)))))

/-- An optional literal Hessian coefficient. This records metadata and actual
coordinate equality only; it assumes no derivative or split-norm estimate. -/
structure HessianCoefficient (ρ : CoefficientEnvironment σ D)
    (H : EuclideanSpace ℝ (Fin D) → ℝ) where
  name : Name
  arity_eq : σ.arity name = 2
  size_eq : σ.size name = 2
  weight_eq : σ.weight name = 0
  value_eq : ∀ (x : EuclideanSpace ℝ (Fin D)) (a : Fin 2 → Fin D),
    ρ name x (fun i => a (Fin.cast arity_eq i)) =
      fderiv ℝ (fderiv ℝ H) x (coordinateDirection D (a 0)) (coordinateDirection D (a 1))

namespace Expr
variable {σ D} {r : ℕ}

/-- The two operations which increase smoothing weight. -/
def weightedOperationCount : {r : ℕ} → Expr σ r → ℕ
  | _, .coefficient _ => 0
  | _, .permute _ e => weightedOperationCount e
  | _, .contract e f _ _ => weightedOperationCount e + weightedOperationCount f
  | _, .derivative e => weightedOperationCount e + 1
  | _, .adjoint _ e => weightedOperationCount e + 1

theorem weight_eq (e : Expr σ r) :
    e.weight = (e.coefficients.map σ.weight).sum + e.weightedOperationCount := by
  induction e with
  | coefficient c => simp [weight,coefficients,weightedOperationCount]
  | permute p e ih => exact ih
  | contract e f i j ih₁ ih₂ =>
    simp only [weight,coefficients,weightedOperationCount,List.map_append,List.sum_append,Nat.cast_add]
    rw [ih₁,ih₂]
    ring
  | derivative e ih => simp only [weight,coefficients,weightedOperationCount,Nat.cast_add,Nat.cast_one]; rw [ih]; ring
  | adjoint i e ih => simp only [weight,coefficients,weightedOperationCount,Nat.cast_add,Nat.cast_one]; rw [ih]; ring

theorem coefficients_nonempty (e : Expr σ r) : e.coefficients ≠ [] := by
  induction e <;> simp_all [coefficients]

theorem occurrenceAddress_injective (e : Expr σ r) : Function.Injective e.occurrenceAddress := by
  intro i j h
  have hh := e.leafAddresses_nodup.injective_get h
  apply Fin.ext
  exact congrArg (fun z : Fin e.leafAddresses.length => z.val) hh

/-- Literal coordinate interpretation. Differentiation uses Mathlib's total
Fréchet derivative; later analytic theorems must supply differentiability.
Adjoints use exactly `-∂V + (∂H)V`, with no integration-by-parts assumption. -/
def evaluate (ρ : CoefficientEnvironment σ D) (H : EuclideanSpace ℝ (Fin D) → ℝ) :
    {r : ℕ} → Expr σ r → EuclideanSpace ℝ (Fin D) → Coeff (Fin r) D
  | _, .coefficient c, x => ρ c x
  | _, .permute p e, x => toLp 2 (fun a => evaluate ρ H e x (a ∘ p))
  | _, .contract e f i j, x => crossContract D (evaluate ρ H e x) (evaluate ρ H f x) i j
  | r+1, .derivative e, x => toLp 2 (fun a =>
      fderiv ℝ (fun y => evaluate ρ H e y (a ∘ Fin.castSucc)) x
        (coordinateDirection D (a (Fin.last r))))
  | _r+1, .adjoint i e, x => toLp 2 (fun a => ∑ k : Fin D, (
      - fderiv ℝ (fun y => evaluate ρ H e y (Fin.insertNth i k a)) x
          (coordinateDirection D k) +
        fderiv ℝ H x (coordinateDirection D k) * evaluate ρ H e x (Fin.insertNth i k a)))

@[simp] lemma evaluate_coefficient (ρ : CoefficientEnvironment σ D)
    (H : EuclideanSpace ℝ (Fin D) → ℝ) (c : Name) (x : EuclideanSpace ℝ (Fin D)) :
    evaluate ρ H (.coefficient c) x = ρ c x := rfl

lemma evaluate_adjoint (ρ : CoefficientEnvironment σ D)
    (H : EuclideanSpace ℝ (Fin D) → ℝ) (e : Expr σ (r+2)) (i : Fin (r+2))
    (x : EuclideanSpace ℝ (Fin D)) (a : Fin (r+1) → Fin D) :
    evaluate ρ H (.adjoint i e) x a = ∑ k : Fin D, (
      - fderiv ℝ (fun y => evaluate ρ H e y (Fin.insertNth i k a)) x
          (coordinateDirection D k) +
        fderiv ℝ H x (coordinateDirection D k) * evaluate ρ H e x (Fin.insertNth i k a)) := rfl

end Expr
end AcceleratedLogConcave.Tensor
