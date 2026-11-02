import AcceleratedLogConcave.Conditional.ScaledJetHeadSymmetry
import AcceleratedLogConcave.Tensor.ActualHessianCoefficient

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped ContDiff RealInnerProductSpace BigOperators
namespace AcceleratedLogConcave.Conditional.PositiveVarianceFlowData
open Tensor Tensor.AdjointReduction
variable {D : ℕ} (d : PositiveVarianceFlowData (EuclideanSpace ℝ (Fin D)))

/-- Actual adjoint of the next center jet, retaining all free slots. -/
def scaledJetAdjoint (q : ℕ) (w : EuclideanSpace ℝ (Fin D))
    (a : Fin q → EuclideanSpace ℝ (Fin D)) (t : ℝ) : EuclideanSpace ℝ (Fin D) → ℝ :=
  adjointField (interpolationPotential d.F d.x d.r t) (coordinateDirection D)
    (fun k z => d.scaledJetCoordinate (q+1) w (Fin.cons (coordinateDirection D k) a) (t,z))

private theorem coordinate_sum_scaledJet (q : ℕ) (w v : EuclideanSpace ℝ (Fin D))
    (a : Fin q → EuclideanSpace ℝ (Fin D)) (t : ℝ) (y : EuclideanSpace ℝ (Fin D)) :
    (∑ k : Fin D, inner ℝ (coordinateDirection D k) v *
      d.scaledJetCoordinate (q+1) w (Fin.cons (coordinateDirection D k) a) (t,y)) =
      d.scaledJetCoordinate (q+1) w (Fin.cons v a) (t,y) := by
  let b := EuclideanSpace.basisFun (Fin D) ℝ
  let L : EuclideanSpace ℝ (Fin D) →L[ℝ] ℝ := (innerSL ℝ w).comp
    ((ScaledJetPolynomial.tensorEvaluation q a).comp (scaledJet (q+1) d.F d.x d.r t y).curryLeft)
  have hh := congrArg L (b.sum_repr' v)
  simpa [b,EuclideanSpace.basisFun_apply,EuclideanSpace.single,coordinateDirection,L,
    scaledJetCoordinate,ScaledJetPolynomial.tensorEvaluation,map_sum,map_smul,smul_eq_mul] using hh

/-- Remove every spatial derivative from the actual adjoint, retaining
only smooth center-jet fields. This supports the nonsingular time-zero limit. -/
theorem scaledJetAdjoint_eq_explicit (q : ℕ) (w : EuclideanSpace ℝ (Fin D))
    (a : Fin q → EuclideanSpace ℝ (Fin D)) {t : ℝ}
    (ht : -1 < t ∧ t < 1) (y : EuclideanSpace ℝ (Fin D)) :
    d.scaledJetAdjoint q w a t y = ∑ k : Fin D,
      (-t * d.scaledJetCoordinate (q+2) w
          (Fin.cons (coordinateDirection D k) (Fin.cons (coordinateDirection D k) a)) (t,y) +
        inner ℝ (y + (d.r*t) • conditionalMean d.F d.x d.r t y) (coordinateDirection D k) *
          d.scaledJetCoordinate (q+1) w (Fin.cons (coordinateDirection D k) a) (t,y)) := by
  unfold scaledJetAdjoint adjointField adjointComponent dir
  apply Finset.sum_congr rfl
  intro k _
  change - fderiv ℝ (fun z => inner ℝ w (scaledJet (q+1) d.F d.x d.r t z
      (Fin.cons (coordinateDirection D k) a))) y (coordinateDirection D k) + _ = _
  rw [fderiv_scaledJet_coordinate (q+1) d.hF d.hlo d.hhi d.x d.r ht.1 ht.2,
    ←inner_gradient_left,gradient_interpolationPotential d.hF d.hlo d.hhi d.x d.r ht.1 ht.2]
  simp only [scaledJetCoordinate,neg_mul]

/-- The spatial/adjoint half of the actual material leaf induction. The
linear score-Hessian term is the exact cancellation term; the nonlinear
term is the second copy of the material-spatial correction. -/
theorem spatial_scaledJetAdjoint (q : ℕ) (w v : EuclideanSpace ℝ (Fin D))
    (a : Fin q → EuclideanSpace ℝ (Fin D)) {t : ℝ}
    (ht : -1 < t ∧ t < 1) (y : EuclideanSpace ℝ (Fin D)) :
    dir v (d.scaledJetAdjoint q w a t) y =
      t * d.scaledJetAdjoint (q+1) w (Fin.cons v a) t y +
      d.scaledJetCoordinate (q+1) w (Fin.cons v a) (t,y) +
      (d.r*t^2) * d.scaledJetCoordinate (q+1) w
        (Fin.cons (firstScaledJet d.F d.x d.r t y v) a) (t,y) := by
  let row (k : Fin D) (z : EuclideanSpace ℝ (Fin D)) :=
    d.scaledJetCoordinate (q+1) w (Fin.cons (coordinateDirection D k) a) (t,z)
  let next (k : Fin D) (z : EuclideanSpace ℝ (Fin D)) :=
    d.scaledJetCoordinate (q+2) w (Fin.cons (coordinateDirection D k) (Fin.cons v a)) (t,z)
  have hs (n : ℕ) (b : Fin n → EuclideanSpace ℝ (Fin D)) :
      ContDiff ℝ ∞ (fun z => d.scaledJetCoordinate n w b (t,z)) :=
    (innerSL ℝ w).contDiff.comp
      ((ScaledJetPolynomial.tensorEvaluation n b).contDiff.comp
        (contDiff_scaledJet_spatial n d.hF d.hlo d.hhi d.x d.r ht.1 ht.2))
  have hd (k : Fin D) : dir v (row k) = fun z => t * next k z := by
    funext z
    change fderiv ℝ (fun z => inner ℝ w (scaledJet (q+1) d.F d.x d.r t z
      (Fin.cons (coordinateDirection D k) a))) z v = _
    rw [fderiv_scaledJet_coordinate (q+1) d.hF d.hlo d.hhi d.x d.r ht.1 ht.2]
    change t * d.scaledJetCoordinate (q+2) w (Fin.cons v (Fin.cons (coordinateDirection D k) a)) (t,z) = _
    rw [d.scaledJetCoordinate_swap_heads q w v (coordinateDirection D k) a ht z]
  have hH := contDiff_interpolationPotential d.hF d.hlo d.hhi d.x d.r ht.1 ht.2
  have hh := congrFun (decorated_adjointField (fun _ : Unit => v) [()] hH
    (coordinateDirection D) row (fun k => hs _ _)) y
  simp only [partialAlong,scoreRoutes,routes,List.map_cons,List.map_nil,List.sum_cons,
    List.sum_nil,List.nil_append,add_zero] at hh
  change dir v (d.scaledJetAdjoint q w a t) y = _ at hh
  rw [hh]
  simp_rw [hd]
  have ha : adjointField (interpolationPotential d.F d.x d.r t) (coordinateDirection D)
      (fun k z => t * next k z) y = t * d.scaledJetAdjoint (q+1) w (Fin.cons v a) t y := by
    unfold scaledJetAdjoint adjointField
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    unfold adjointComponent dir
    rw [fderiv_const_mul ((hs _ _).differentiable (by simp) y)]
    simp only [smul_apply,smul_eq_mul]
    ring
  rw [ha]
  simp_rw [d.hessian_coordinate_eq_firstJet ht y v]
  simp_rw [add_mul,mul_assoc]
  rw [Finset.sum_add_distrib,←Finset.mul_sum,←Finset.mul_sum]
  rw [coordinate_sum_scaledJet d q w v a t y,
    coordinate_sum_scaledJet d q w (firstScaledJet d.F d.x d.r t y v) a t y]
  ring

end AcceleratedLogConcave.Conditional.PositiveVarianceFlowData
