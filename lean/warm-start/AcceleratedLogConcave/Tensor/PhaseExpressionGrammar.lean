import AcceleratedLogConcave.Tensor.Expressions

/-! The phase grammar uses the existing connected expression syntax.
There is no tensor-product, internal trace, scalar, or unrestricted Wick node.
These are structural statements only, not an analytic moment theorem. -/
open scoped NNReal
namespace AcceleratedLogConcave.Tensor.PhaseExpression

inductive Primitive
  | transport
  | scoreHessian
  | observableGradient
  | positionProjection
  deriving DecidableEq

def signature : CoefficientSignature Primitive where
  arity _ := 2
  size _ := 2
  weight c := match c with
    | .observableGradient => 1
    | _ => 0
  two_le_arity _ := le_refl _
  arity_le_size _ := le_refl _

abbrev B : Expr signature 2 := .coefficient .transport
abbrev F : Expr signature 2 := .coefficient .observableGradient
abbrev P : Expr signature 2 := .coefficient .positionProjection

/-- The first generator application contracts the derivative slot (slot one)
of the observable gradient, retaining the observable output (slot zero). -/
def first (f : Expr signature 2) : Expr signature 1 :=
  .adjoint 0 (.contract B f 1 1)

/-- Successive applications differentiate a whole vector expression before
contracting its derivative with B and taking the weighted adjoint. -/
def next (e : Expr signature 1) : Expr signature 1 :=
  .adjoint 0 (.contract B (.derivative e) 1 1)

/-- Index zero denotes the first, rather than zeroth, generator application. -/
def jet (f : Expr signature 2) : ℕ → Expr signature 1
  | 0 => first f
  | k+1 => next (jet f k)

@[simp] theorem first_size (f : Expr signature 2) : (first f).size = f.size + 4 := by
  simp [first, B, Expr.size, signature]
  omega

@[simp] theorem next_size (e : Expr signature 1) : (next e).size = e.size + 5 := by
  simp [next, B, Expr.size, signature]
  omega

@[simp] theorem first_weight (f : Expr signature 2) :
    (first f).weight = f.weight + 1 := by
  simp [first, B, Expr.weight, signature]

@[simp] theorem next_weight (e : Expr signature 1) :
    (next e).weight = e.weight + 2 := by
  simp [next, B, Expr.weight, signature]
  ring

theorem jet_size (f : Expr signature 2) (k : ℕ) :
    (jet f k).size = f.size + 4 + 5*k := by
  induction k with
  | zero => simp [jet]
  | succ k ih => rw [jet, next_size, ih]; omega

theorem jet_weight (f : Expr signature 2) (k : ℕ) :
    (jet f k).weight = f.weight + 1 + 2*(k : ℝ≥0) := by
  induction k with
  | zero => simp [jet]
  | succ k ih => rw [jet, next_weight, ih]; push_cast; ring

/-- The kth positive order is k+1: size 5(k+1)+1, weight 2(k+1). -/
theorem observable_jet_budgets (k : ℕ) :
    (jet F k).size = 5*(k+1)+1 ∧ (jet F k).weight = 2*((k : ℝ≥0)+1) := by
  constructor
  · rw [jet_size]; simp [Expr.size, signature]; omega
  · rw [jet_weight]; simp [Expr.weight, signature]; ring

/-- Position starts at weight zero, saving one smoothing power at every order. -/
theorem position_jet_budgets (k : ℕ) :
    (jet P k).size = 5*(k+1)+1 ∧ (jet P k).weight = 2*(k : ℝ≥0)+1 := by
  constructor
  · rw [jet_size]; simp [Expr.size, signature]; omega
  · rw [jet_weight]; simp [Expr.weight, signature]; ring
end AcceleratedLogConcave.Tensor.PhaseExpression
