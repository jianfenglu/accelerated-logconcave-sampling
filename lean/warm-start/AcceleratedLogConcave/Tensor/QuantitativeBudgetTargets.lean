import AcceleratedLogConcave.Conditional.ScaledJetSplitNorm
import AcceleratedLogConcave.Conditional.ScaledJetSpatialTransition
import AcceleratedLogConcave.Conditional.Transport.KernelRegularity
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Tactic

/-!

-/
noncomputable section
open scoped BigOperators ContDiff RealInnerProductSpace
open Set
namespace AcceleratedLogConcave.Tensor.QuantitativeKernel
open Conditional

/-- All proper rectangular Hilbert cuts, including the output slot. -/
def AllProper {Slot : Type*} [Fintype Slot] [DecidableEq Slot]
    (D : ℕ) (T : Coeff Slot D) (C : ℝ) : Prop :=
  ∀ S : Finset Slot, NontrivialSplit S → splitNorm D S T ≤ C

/-- The two endpoint external slot sets are nonempty. A global proper cut
admits one of the two opposite labels on the single contracted edge. -/
theorem edge_orientation (ar ac br bc : Prop)
    (ha : ar ∨ ac) (hb : br ∨ bc)
    (hrow : ar ∨ br) (hcol : ac ∨ bc) :
    (ac ∧ br) ∨ (ar ∧ bc) := by tauto

/-- Literal use of the already-present primitive all-cut supplier. -/
theorem primitive_allProper {D : ℕ}
    (d : PositiveVarianceFlowData (EuclideanSpace ℝ (Fin D)))
    (q : ℕ) {t : ℝ} (ht : -1 < t ∧ t < 1)
    (y : EuclideanSpace ℝ (Fin D)) :
    AllProper D (scaledJetCoefficient q d.F d.x d.r t y)
      (((conditionalVariance t ^ q)⁻¹ * (d.r*d.ell)) *
        ((q.factorial : ℝ) * (Real.sqrt (2*conditionalVariance t))^(q+1))) := by
  intro S hS
  exact d.scaledJetCoefficient_splitNorm_le q ht y S hS

/-- Retain every derivative index and the actual vector output index. -/
def vectorJetCoeff {D : ℕ} (n : ℕ)
    (f : EuclideanSpace ℝ (Fin D) → EuclideanSpace ℝ (Fin D))
    (y : EuclideanSpace ℝ (Fin D)) : Coeff (Fin n ⊕ Unit) D :=
  WithLp.toLp 2 (fun a => inner ℝ
    (EuclideanSpace.basisFun (Fin D) ℝ (a (.inr ())))
    (iteratedFDeriv ℝ n f y
      (fun i => EuclideanSpace.basisFun (Fin D) ℝ (a (.inl i)))))

/-- Slot order: derivative slots, original operator input, operator output. -/
def operatorJetCoeff {D : ℕ} (n : ℕ)
    (f : EuclideanSpace ℝ (Fin D) →
      (EuclideanSpace ℝ (Fin D) →L[ℝ] EuclideanSpace ℝ (Fin D)))
    (y : EuclideanSpace ℝ (Fin D)) : Coeff (Fin n ⊕ (Unit ⊕ Unit)) D :=
  WithLp.toLp 2 (fun a => inner ℝ
    (EuclideanSpace.basisFun (Fin D) ℝ (a (.inr (.inr ()))))
    ((iteratedFDeriv ℝ n f y
      (fun i => EuclideanSpace.basisFun (Fin D) ℝ (a (.inl i))))
      (EuclideanSpace.basisFun (Fin D) ℝ (a (.inr (.inl ()))))))

def primitiveConstant (q : ℕ) : ℝ :=
  if q = 1 then 1 else (q.factorial : ℝ) * (Real.sqrt 2)^(q+1)

def universalExp : ℝ := Real.exp (1/4)

/-- Finite tabulation avoids hiding well-founded recursion on partition sizes.
Only entries below N+1 occur in blocks of a partition with >=2 blocks. -/
def flowTable : ℕ → (ℕ → ℝ)
  | 0 => fun _ => 0
  | N+1 => fun j => if j = N+1 then
      if N = 0 then universalExp else
        universalExp * ∑ p : OrderedFinpartition (N+1),
          if 2 ≤ p.length then primitiveConstant p.length *
            ∏ i : Fin p.length, flowTable N (p.partSize i) else 0
    else flowTable N j

def flowConstant (n : ℕ) : ℝ := flowTable n n

def inverseTable : ℕ → (ℕ → ℝ)
  | 0 => fun j => if j = 0 then universalExp else 0
  | N+1 => fun j => if j = N+1 then
      universalExp * ∑ i ∈ Finset.range (N+1),
        ((N+1).choose (i+1) : ℝ) * flowConstant (i+2) * inverseTable N (N-i)
    else inverseTable N j

def inverseConstant (n : ℕ) : ℝ := inverseTable n n

def compositionConstant (n : ℕ) : ℝ :=
  if n = 0 then 1 else ∑ p : OrderedFinpartition n,
    primitiveConstant (p.length+1) * ∏ i : Fin p.length, flowConstant (p.partSize i)

def kernelConstant (n : ℕ) : ℝ :=
  universalExp * compositionConstant n + (1/4) * ∑ i ∈ Finset.range n,
    (n.choose (i+1) : ℝ) * inverseConstant (i+1) * compositionConstant (n-(i+1))

def spatialScale (b : ℝ) : ℝ := b / Real.sqrt (1-b^2)
def curvatureTime (r ell b t : ℝ) : ℝ := r^2 * ell * (b^2-t^2) / 2

variable {D : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin D)

def actualY (d : PositiveVarianceFlowData E) (t : ℝ) : E → E :=
  backwardProbabilityTransport d.hF d.hell d.hlo d.hhi d.x d.hr d.hb0 d.hb1 t

def actualB (d : PositiveVarianceFlowData E) (t : ℝ) : E → (E →L[ℝ] E) :=
  transportedJacobian d.hF d.hell d.hlo d.hhi d.x d.hr d.hb0 d.hb1 t

def actualK (d : PositiveVarianceFlowData E) : E → (E →L[ℝ] E) :=
  transportedSteinKernelTranspose d.hF d.hell d.hlo d.hhi d.x d.hr d.hb0 d.hb1

/-- Formalization target, NOT an asserted theorem. Includes D=0, b=0, ell=0. -/
def ActualFlowBudgetStatement : Prop :=
  ∀ (D : ℕ) (d : PositiveVarianceFlowData (EuclideanSpace ℝ (Fin D))),
    d.r^2 * d.ell ≤ 1/2 → ∀ t ∈ Icc 0 d.b, ∀ y,
      AllProper D (vectorJetCoeff 1 (actualY d t) y)
        (Real.exp (curvatureTime d.r d.ell d.b t)) ∧
      ∀ n : ℕ, 2 ≤ n → AllProper D (vectorJetCoeff n (actualY d t) y)
        (curvatureTime d.r d.ell d.b t * spatialScale d.b^(n-1) * flowConstant n)

/-- No compact-inverse or full-HS hypothesis is present. -/
def ActualInverseBudgetStatement : Prop :=
  ∀ (D : ℕ) (d : PositiveVarianceFlowData (EuclideanSpace ℝ (Fin D))),
    d.r^2 * d.ell ≤ 1/2 → ∀ t ∈ Icc 0 d.b, ∀ y,
      AllProper D (operatorJetCoeff 0 (actualB d t) y)
        (Real.exp (curvatureTime d.r d.ell d.b t)) ∧
      ∀ n : ℕ, 1 ≤ n → AllProper D (operatorJetCoeff n (actualB d t) y)
        (curvatureTime d.r d.ell d.b t * spatialScale d.b^n * inverseConstant n)

/-- The actual source K, with beta=r*ell rather than an invented r^2*ell gain. -/
def ActualKernelBudgetStatement : Prop :=
  ∀ (D : ℕ) (d : PositiveVarianceFlowData (EuclideanSpace ℝ (Fin D))),
    d.r^2 * d.ell ≤ 1/2 → ∀ (n : ℕ) y,
      AllProper D (operatorJetCoeff n (actualK d) y)
        ((d.r*d.ell) * d.b * spatialScale d.b^n * kernelConstant n)

-- Future external compiler/axiom inspection targets. NOT RUN.
#check primitive_allProper
#check edge_orientation
#print ActualFlowBudgetStatement
#print ActualInverseBudgetStatement
#print ActualKernelBudgetStatement
end AcceleratedLogConcave.Tensor.QuantitativeKernel
