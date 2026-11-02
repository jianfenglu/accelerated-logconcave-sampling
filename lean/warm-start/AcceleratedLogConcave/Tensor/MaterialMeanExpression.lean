import AcceleratedLogConcave.Tensor.ActualCoefficientBudgets
import AcceleratedLogConcave.Conditional.Flow.AdjointProduct

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped RealInnerProductSpace ContDiff BigOperators
namespace AcceleratedLogConcave.Tensor.ActualCoefficientIntegrability
open Conditional Kinetic

/-- The initial whole expression has one exterior adjoint, size three,
and weight one, with no summation over expression alternatives. -/
def materialMeanExpr : Expr signature 1 :=
  .adjoint (1 : Fin 2) (.coefficient (Sum.inl 0))

theorem materialMeanExpr_size : materialMeanExpr.size = 3 := rfl
theorem materialMeanExpr_weight : materialMeanExpr.weight = 1 := by simp [materialMeanExpr,Expr.weight]

private theorem weightedAdjoint_coordinate_sum {D : ℕ}
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

variable {D : ℕ} (d : PositiveVarianceFlowData (EuclideanSpace ℝ (Fin D)))

/-- Restore the physical scale without losing the zero-curvature branch. -/
theorem firstJet_coordinate_eq_scaled_coefficient {t : ℝ}
    (ht : -1 < t ∧ t < 1) (y : EuclideanSpace ℝ (Fin D)) (a : Fin 2 → Fin D) :
    inner ℝ (coordinateDirection D (a 0))
      (firstScaledJet d.F d.x d.r t y (coordinateDirection D (a 1))) =
    (d.ell*d.r) * coefficientEnvironment d.F d.x d.ell d.r t (Sum.inl 0) y a := by
  change _ = (d.ell*d.r) * ((d.ell*d.r*((0+1).factorial : ℝ))⁻¹ *
    inner ℝ (coordinateDirection D (a 0))
      (scaledJet 1 d.F d.x d.r t y (fun i => coordinateDirection D (a i.succ))))
  rw [ScaledJetPolynomial.scaledJet_one_apply_eq_firstScaledJet d.hF d.hlo d.hhi d.x d.r ht.1 ht.2]
  norm_num
  rcases lt_or_eq_of_le d.hell with hell | hflat
  · field_simp [hell.ne',d.hr.ne']
  · have hz : firstScaledJet d.F d.x d.r t y = 0 := norm_le_zero_iff.mp
      (by simpa [←hflat] using norm_firstScaledJet_le d.hF d.hell d.hlo d.hhi d.x d.hr ht.1 ht.2 y)
    simp [hz,←hflat]

/-- Exact base of the source material-expression expansion. The exterior
adjoint is literal grammar and the physical scale is L=r*ell. -/
theorem conditionalMaterialMean_eq_expression {t : ℝ}
    (ht : -1 < t ∧ t < 1) (y : EuclideanSpace ℝ (Fin D)) (a : Fin 1 → Fin D) :
    inner ℝ (coordinateDirection D (a 0)) (conditionalMaterialMean d.F d.x d.r t y) =
      (d.ell*d.r) * Expr.evaluate
        (coefficientEnvironment d.F d.x d.ell d.r t)
        (interpolationPotential d.F d.x d.r t) materialMeanExpr y a := by
  let V := firstScaledJetRow d.F d.x (coordinateDirection D (a 0)) d.r t
  let score := fun z => z + (d.r*t) • conditionalMean d.F d.x d.r t z
  let c (k : Fin D) (z : EuclideanSpace ℝ (Fin D)) : ℝ :=
    (show Coeff (Fin 2) D from coefficientEnvironment d.F d.x d.ell d.r t (Sum.inl 0) z)
      (Fin.insertNth (1 : Fin 2) k a)
  have hins (k : Fin D) : Fin.insertNth (1 : Fin 2) k a = (show Fin 2 → Fin D from Fin.cons (a 0) (fun _ : Fin 1 => k)) := by
    funext i
    fin_cases i <;> rfl
  have he (k : Fin D) : (fun z => inner ℝ (coordinateDirection D k) (V z)) =
      fun z => (d.ell*d.r) * c k z := by
    funext z
    change inner ℝ (coordinateDirection D k)
      ((firstScaledJet d.F d.x d.r t z).adjoint (coordinateDirection D (a 0))) = _
    rw [real_inner_comm,ContinuousLinearMap.adjoint_inner_left]
    simpa [c,hins] using firstJet_coordinate_eq_scaled_coefficient d ht z (Fin.insertNth 1 k a)
  have hc (k : Fin D) : DifferentiableAt ℝ (c k) y := by
    have hh := contDiff_scaledJet_spatial 1 d.hF d.hlo d.hhi d.x d.r ht.1 ht.2
    have h : ContDiff ℝ (⊤ : ℕ∞) (fun z => (d.ell*d.r)⁻¹ *
        inner ℝ (coordinateDirection D (a 0))
          (scaledJet 1 d.F d.x d.r t z (fun _ => coordinateDirection D k))) :=
      contDiff_const.mul ((innerSL ℝ (coordinateDirection D (a 0))).contDiff.comp
        ((ScaledJetPolynomial.tensorEvaluation 1 (fun _ => coordinateDirection D k)).contDiff.comp hh))
    exact (show ContDiff ℝ (⊤ : ℕ∞) (c k) by simpa [c,hins,coefficientEnvironment] using h).differentiable (by simp) y
  have hs (k : Fin D) : fderiv ℝ (interpolationPotential d.F d.x d.r t) y (coordinateDirection D k) =
      inner ℝ (score y) (coordinateDirection D k) := by
    rw [←inner_gradient_left,gradient_interpolationPotential d.hF d.hlo d.hhi d.x d.r ht.1 ht.2]
  rw [conditionalMaterialMean_eq_weightedAdjoint d.hF d.hlo d.hhi d.x _ d.hr.ne' ht.1 ht.2 y,
    weightedAdjoint_coordinate_sum _ _ y
      ((contDiff_firstScaledJetRow d.hF d.hlo d.hhi d.x _ d.hr.ne' ht.1 ht.2).differentiable_one y)]
  change (∑ k : Fin D, (-fderiv ℝ (fun z => inner ℝ (coordinateDirection D k) (V z)) y
      (coordinateDirection D k) + inner ℝ (score y) (coordinateDirection D k) *
        inner ℝ (coordinateDirection D k) (V y))) = _
  change _ = (d.ell*d.r) * ∑ k : Fin D, (- fderiv ℝ (c k) y (coordinateDirection D k) +
      fderiv ℝ (interpolationPotential d.F d.x d.r t) y (coordinateDirection D k) * c k y)
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [he,hs]
  rw [fderiv_const_mul (hc k),smul_apply,smul_eq_mul,congrFun (he k) y]
  ring

end AcceleratedLogConcave.Tensor.ActualCoefficientIntegrability
