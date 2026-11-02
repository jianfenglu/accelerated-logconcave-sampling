import AcceleratedLogConcave.Tensor.MaterialExpressionSmooth
import AcceleratedLogConcave.Tensor.MaterialMeanExpression

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped ContDiff RealInnerProductSpace BigOperators Topology
namespace AcceleratedLogConcave.Tensor.ActualCoefficientIntegrability
open Conditional Analysis Analysis.CoupledVelocityPolynomial CoordinateReduction Kinetic

/-- Reconstitute the one contracted tensor slot as an actual Euclidean field. -/
def materialExpressionRow {D r : ℕ}
    (d : PositiveVarianceFlowData (EuclideanSpace ℝ (Fin D)))
    (e : Expr signature (r+2)) (i : Fin (r+2)) (a : Fin (r+1) → Fin D)
    (p : ℝ × EuclideanSpace ℝ (Fin D)) : EuclideanSpace ℝ (Fin D) :=
  ∑ k : Fin D, materialExpressionValue d e (Fin.insertNth i k a) p • coordinateDirection D k

private theorem coordinate_inner {D : ℕ} (k : Fin D) (v : EuclideanSpace ℝ (Fin D)) :
    inner ℝ (coordinateDirection D k) v = v k := by
  simpa [coordinateDirection,EuclideanSpace.single] using
    EuclideanSpace.inner_single_left k (1:ℝ) v

theorem materialExpressionRow_coordinate {D r : ℕ}
    (d : PositiveVarianceFlowData (EuclideanSpace ℝ (Fin D)))
    (e : Expr signature (r+2)) (i : Fin (r+2)) (a : Fin (r+1) → Fin D)
    (p : ℝ × EuclideanSpace ℝ (Fin D)) (k : Fin D) :
    inner ℝ (coordinateDirection D k) (materialExpressionRow d e i a p) =
      materialExpressionValue d e (Fin.insertNth i k a) p := by
  rw [coordinate_inner]
  simp [materialExpressionRow,coordinateDirection,Pi.single_apply]

theorem contDiffOn_materialExpressionRow {D r : ℕ}
    (d : PositiveVarianceFlowData (EuclideanSpace ℝ (Fin D)))
    (e : Expr signature (r+2)) (he : IsMaterialExpression e)
    (i : Fin (r+2)) (a : Fin (r+1) → Fin D) :
    ContDiffOn ℝ ∞ (materialExpressionRow d e i a)
      (openDomain (EuclideanSpace ℝ (Fin D))) :=
  ContDiffOn.sum (fun _k _ => (contDiffOn_materialExpressionValue d e he _).smul contDiffOn_const)

private theorem weightedAdjoint_coordinates {D : ℕ}
    (score V : EuclideanSpace ℝ (Fin D) → EuclideanSpace ℝ (Fin D))
    (y : EuclideanSpace ℝ (Fin D)) (hV : DifferentiableAt ℝ V y) :
    weightedAdjoint score V y = ∑ k : Fin D,
      (- fderiv ℝ (fun z => inner ℝ (coordinateDirection D k) (V z)) y
          (coordinateDirection D k) +
        inner ℝ (score y) (coordinateDirection D k) *
          inner ℝ (coordinateDirection D k) (V y)) := by
  let b := EuclideanSpace.basisFun (Fin D) ℝ
  have hb (k : Fin D) : b k = coordinateDirection D k := by
    simp [b,EuclideanSpace.basisFun_apply,coordinateDirection,EuclideanSpace.single]
  have hd (k : Fin D) : fderiv ℝ (fun z => inner ℝ (coordinateDirection D k) (V z)) y =
      (innerSL ℝ (coordinateDirection D k)).comp (fderiv ℝ V y) :=
    ((innerSL ℝ (coordinateDirection D k)).hasFDerivAt.comp y hV.hasFDerivAt).fderiv
  unfold weightedAdjoint
  rw [fluxDivergence_eq_sum_basis b hV,←b.sum_inner_mul_inner (score y) (V y)]
  simp only [hb,hd,ContinuousLinearMap.comp_apply,innerSL_apply_apply,
    Finset.sum_add_distrib,Finset.sum_neg_distrib]

/-- Literal Expr adjoint equals the already-verified actual space-time
weighted adjoint, with no supplied field-value certificate. -/
theorem materialExpressionValue_adjoint {D r : ℕ}
    (d : PositiveVarianceFlowData (EuclideanSpace ℝ (Fin D)))
    (e : Expr signature (r+2)) (he : IsMaterialExpression e)
    (i : Fin (r+2)) (a : Fin (r+1) → Fin D)
    {t : ℝ} (ht : -1<t ∧ t<1) (y : EuclideanSpace ℝ (Fin D)) :
    materialExpressionValue d (.adjoint i e) a (t,y) =
      d.spacetimeAdjoint (materialExpressionRow d e i a) (t,y) := by
  have hd := ((contDiffOn_materialExpressionRow d e he i a).contDiffAt
    ((isOpen_openDomain _).mem_nhds (show (t,y) ∈ openDomain _ from ht))).differentiableAt (by simp)
  rw [d.spacetimeAdjoint_eq_weightedAdjoint hd]
  have hs := hd.comp y
    (((hasFDerivAt_const (𝕜 := ℝ) t y).prodMk (hasFDerivAt_id (𝕜 := ℝ) y)).differentiableAt)
  change DifferentiableAt ℝ (fun z => materialExpressionRow d e i a (t,z)) y at hs
  rw [weightedAdjoint_coordinates _ _ y hs]
  simp_rw [materialExpressionRow_coordinate]
  change (∑ k : Fin D, (-fderiv ℝ _ y (coordinateDirection D k) +
    fderiv ℝ (interpolationPotential d.F d.x d.r t) y (coordinateDirection D k) * _)) = _
  apply Finset.sum_congr rfl
  intro k _
  congr 2
  change fderiv ℝ (interpolationPotential d.F d.x d.r t) y (coordinateDirection D k) =
    inner ℝ (y+(d.r*t) • conditionalMean d.F d.x d.r t y) (coordinateDirection D k)
  rw [← gradient_interpolationPotential d.hF d.hlo d.hhi d.x d.r ht.1 ht.2 y]
  simp

/-- Apply the existing actual adjoint commutator to the literal Expr row.
This is the differential identity before its correction is re-encoded as J1 contraction. -/
theorem material_expression_adjoint_row_commutator {D r : ℕ}
    (d : PositiveVarianceFlowData (EuclideanSpace ℝ (Fin D)))
    (e : Expr signature (r+2)) (he : IsMaterialExpression e)
    (i : Fin (r+2)) (a : Fin (r+1) → Fin D)
    {t : ℝ} (ht : -1<t ∧ t<1) (y : EuclideanSpace ℝ (Fin D)) :
    materialDerivative d.materialVelocity (materialExpressionValue d (.adjoint i e) a) (t,y) =
      d.spacetimeAdjoint
        (materialDerivative d.materialVelocity (materialExpressionRow d e i a)) (t,y) +
      (d.r*t) * weightedAdjoint (fun z => d.scoreField (t,z))
        (fun z => firstScaledJet d.F d.x d.r t z (materialExpressionRow d e i a (t,z))) y := by
  have hloc : materialExpressionValue d (.adjoint i e) a =ᶠ[nhds (t,y)]
      d.spacetimeAdjoint (materialExpressionRow d e i a) := by
    filter_upwards [(isOpen_openDomain _).mem_nhds (show (t,y) ∈ openDomain _ from ht)] with p hp
    exact materialExpressionValue_adjoint d e he i a hp p.2
  unfold materialDerivative
  rw [hloc.fderiv_eq]
  exact d.material_spacetimeAdjoint_commutator
    (contDiffOn_materialExpressionRow d e he i a) ht y

end AcceleratedLogConcave.Tensor.ActualCoefficientIntegrability
