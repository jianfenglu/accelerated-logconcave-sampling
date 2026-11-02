import AcceleratedLogConcave.Conditional.MaterialJetNormalization
import AcceleratedLogConcave.Tensor.ActualCoefficientTerminal

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped ContDiff RealInnerProductSpace BigOperators NNReal
namespace AcceleratedLogConcave.Tensor.ActualCoefficientIntegrability
open Conditional AdjointReduction

/-- Principal replacement of J_(n+1), with the fresh derivative slot
used as the actual divergence slot. -/
def materialJetPrincipalExpr (n : ℕ) : Expr signature (n+2) :=
  .adjoint (1 : Fin (n+3)) (.coefficient (Sum.inl (n+1)))

/-- Product replacement before the positional route's free-slot permutation.
The left output contracts with the first right input. -/
def materialJetContractExpr (n m : ℕ) : Expr signature (n+m+2) :=
  .contract (.coefficient (Sum.inl n)) (.coefficient (Sum.inl m))
    (0 : Fin (n+2)) (1 : Fin (m+2))

theorem materialJetPrincipalExpr_size (n : ℕ) :
    (materialJetPrincipalExpr n).size = n+4 := rfl

theorem materialJetPrincipalExpr_weight (n : ℕ) :
    (materialJetPrincipalExpr n).weight = (n+2 : ℝ≥0) := by
  simp [materialJetPrincipalExpr,Expr.weight]
  ring

theorem materialJetContractExpr_size (n m : ℕ) :
    (materialJetContractExpr n m).size = n+m+5 := by
  change n+2+(m+2)+1=n+m+5
  omega

theorem materialJetContractExpr_weight (n m : ℕ) :
    (materialJetContractExpr n m).weight = (n+m : ℝ≥0) := rfl

private theorem insert_divergence {D n : ℕ} (a : Fin (n+2) → Fin D) (k : Fin D) :
    Fin.insertNth (1 : Fin (n+3)) k a = (show Fin (n+3) → Fin D from Fin.cons (a 0) (Fin.cons k (Fin.tail a))) := by
  conv_lhs => rw [←Fin.cons_self_tail a]
  rw [show (1 : Fin (n+3)) = (0 : Fin (n+2)).succ from rfl,
    Fin.insertNth_succ_cons,Fin.insertNth_zero']

private theorem ofFn_tensor_apply {E F : Type*} (T : ∀ n : ℕ, (Fin n → E) → F)
    {n : ℕ} (v : Fin n → E) :
    T (List.ofFn v).length (fun i => (List.ofFn v).get i) = T n v := by
  have hn : (List.ofFn v).length = n := List.length_ofFn
  generalize he : List.ofFn v = l at hn ⊢
  subst n
  have hv : (fun i => l.get i) = v := by
    apply List.ofFn_injective
    rw [List.ofFn_get,he]
  rw [hv]

/-- A canonical coefficient is the actual normalized jet at the same
output and ordered input directions. -/
theorem coefficient_eq_normalizedJetList {D : ℕ}
    (d : PositiveVarianceFlowData (EuclideanSpace ℝ (Fin D)))
    (n : ℕ) (t : ℝ) (y : EuclideanSpace ℝ (Fin D)) (a : Fin (n+2) → Fin D) :
    coefficientEnvironment d.F d.x d.ell d.r t (Sum.inl n) y a =
      d.normalizedJetList (coordinateDirection D (a 0))
        (List.ofFn (fun i : Fin (n+1) => coordinateDirection D (a i.succ))) (t,y) := by
  unfold PositiveVarianceFlowData.normalizedJetList PositiveVarianceFlowData.scaledJetList
    PositiveVarianceFlowData.scaledJetCoordinate coefficientEnvironment
  simp only [List.length_ofFn]
  congr 2
  exact (ofFn_tensor_apply (fun q v => scaledJet q d.F d.x d.r t y v)
    (fun i : Fin (n+1) => coordinateDirection D (a i.succ))).symm

/-- Literal grammar semantics of the normalized principal adjoint, not
an assumed value certificate. All original zero-time/zero-curvature cases remain. -/
theorem materialJetPrincipalExpr_evaluate {D : ℕ}
    (d : PositiveVarianceFlowData (EuclideanSpace ℝ (Fin D)))
    (n : ℕ) {t : ℝ} (ht : -1<t ∧ t<1) (y : EuclideanSpace ℝ (Fin D))
    (a : Fin (n+2) → Fin D) :
    Expr.evaluate (coefficientEnvironment d.F d.x d.ell d.r t)
      (interpolationPotential d.F d.x d.r t) (materialJetPrincipalExpr n) y a =
    (d.ell*d.r*((n+2).factorial:ℝ))⁻¹ *
      d.scaledJetAdjoint (n+1) (coordinateDirection D (a 0))
        (fun i => coordinateDirection D (a i.succ)) t y := by
  let c := (d.ell*d.r*((n+2).factorial:ℝ))⁻¹
  let row (k : Fin D) (z : EuclideanSpace ℝ (Fin D)) :=
    d.scaledJetCoordinate (n+2) (coordinateDirection D (a 0))
      (Fin.cons (coordinateDirection D k) (fun i => coordinateDirection D (a i.succ))) (t,z)
  have hrow (k : Fin D) : Differentiable ℝ (row k) :=
    ((innerSL ℝ (coordinateDirection D (a 0))).contDiff.comp
      ((ScaledJetPolynomial.tensorEvaluation (n+2)
        (Fin.cons (coordinateDirection D k) (fun i => coordinateDirection D (a i.succ)))).contDiff.comp
          (contDiff_scaledJet_spatial (n+2) d.hF d.hlo d.hhi d.x d.r ht.1 ht.2))).differentiable (by simp)
  have hc (k : Fin D) : (fun z => coefficientEnvironment d.F d.x d.ell d.r t
      (Sum.inl (n+1)) z (Fin.insertNth (1 : Fin (n+3)) k a)) = fun z => c*row k z := by
    funext z
    simp only [coefficientEnvironment,insert_divergence]
    change (d.ell*d.r*((n+2).factorial:ℝ))⁻¹ *
      inner ℝ (coordinateDirection D (a 0))
        (scaledJet (n+2) d.F d.x d.r t z
          (fun i => coordinateDirection D ((Fin.cons k (Fin.tail a)) i))) = _
    congr 2
  change (∑ k : Fin D, (
    -fderiv ℝ (fun z => coefficientEnvironment d.F d.x d.ell d.r t
      (Sum.inl (n+1)) z (Fin.insertNth (1 : Fin (n+3)) k a)) y (coordinateDirection D k) +
    fderiv ℝ (interpolationPotential d.F d.x d.r t) y (coordinateDirection D k) *
      coefficientEnvironment d.F d.x d.ell d.r t (Sum.inl (n+1)) y
        (Fin.insertNth (1 : Fin (n+3)) k a))) = _
  simp_rw [hc]
  unfold PositiveVarianceFlowData.scaledJetAdjoint adjointField adjointComponent
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [fderiv_const_mul (hrow k y)]
  simp only [smul_apply,smul_eq_mul]
  change -(c * dir (coordinateDirection D k) (row k) y) +
    dir (coordinateDirection D k) (interpolationPotential d.F d.x d.r t) y * (c*row k y) =
    c * (-dir (coordinateDirection D k) (row k) y +
      dir (coordinateDirection D k) (interpolationPotential d.F d.x d.r t) y * row k y)
  ring

/-- Actual normalized values of the two literal contract operands under
the canonical crossContract assignment. No unspecified child field is supplied. -/
theorem materialJetContractExpr_evaluate {D : ℕ}
    (d : PositiveVarianceFlowData (EuclideanSpace ℝ (Fin D)))
    (n m : ℕ) (t : ℝ) (y : EuclideanSpace ℝ (Fin D))
    (a : Fin (n+m+2) → Fin D) :
    Expr.evaluate (coefficientEnvironment d.F d.x d.ell d.r t)
      (interpolationPotential d.F d.x d.r t) (materialJetContractExpr n m) y a =
    ∑ k : Fin D,
      d.normalizedJetList
        (coordinateDirection D ((CoordinateReduction.leftAssignment (0: Fin (n+2)) a k) 0))
        (List.ofFn (fun i : Fin (n+1) => coordinateDirection D
          ((CoordinateReduction.leftAssignment (0: Fin (n+2)) a k) i.succ))) (t,y) *
      d.normalizedJetList
        (coordinateDirection D ((CoordinateReduction.rightAssignment (1: Fin (m+2)) a k) 0))
        (List.ofFn (fun i : Fin (m+1) => coordinateDirection D
          ((CoordinateReduction.rightAssignment (1: Fin (m+2)) a k) i.succ))) (t,y) := by
  change (∑ k : Fin D,
    coefficientEnvironment d.F d.x d.ell d.r t (Sum.inl n) y
      (CoordinateReduction.leftAssignment (0: Fin (n+2)) a k) *
    coefficientEnvironment d.F d.x d.ell d.r t (Sum.inl m) y
      (CoordinateReduction.rightAssignment (1: Fin (m+2)) a k)) = _
  simp_rw [coefficient_eq_normalizedJetList]

end AcceleratedLogConcave.Tensor.ActualCoefficientIntegrability
