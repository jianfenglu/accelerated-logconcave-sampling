import AcceleratedLogConcave.Tensor.MaterialMeanTrajectory
import AcceleratedLogConcave.Tensor.MaterialVectorExpressionLp
import AcceleratedLogConcave.Conditional.Flow.MaterialTrajectoryLaw

noncomputable section
open scoped BigOperators
namespace AcceleratedLogConcave.Tensor.ActualCoefficientIntegrability
open Conditional Analysis Analysis.PositiveVarianceSlab MeasureTheory Set
variable {D : ℕ}

def vectorTensor (v : EuclideanSpace ℝ (Fin D)) : FinCoeff 1 D :=
  WithLp.toLp 2 (fun a => inner ℝ (coordinateDirection D (a 0)) v)

 theorem vectorTensor_norm_sq (v : EuclideanSpace ℝ (Fin D)) :
    ‖vectorTensor v‖^2 = ‖v‖^2 := by
  let b := EuclideanSpace.basisFun (Fin D) ℝ
  have hb (i : Fin D) : b i = coordinateDirection D i := by
    simp [b,EuclideanSpace.basisFun_apply,coordinateDirection,EuclideanSpace.single]
  have hc : (∑ i : Fin D, (inner ℝ (coordinateDirection D i) v)^2) = ‖v‖^2 := by
    simpa [hb,Real.norm_eq_abs,sq_abs] using b.sum_sq_norm_inner_right v
  rw [EuclideanSpace.real_norm_sq_eq]
  change (∑ a : Fin 1 → Fin D, (inner ℝ (coordinateDirection D (a 0)) v)^2) = _
  rw [←hc]
  apply Fintype.sum_equiv (Equiv.funUnique (Fin 1) (Fin D))
  intro a
  rfl

 theorem positionJet_tensor_expansion
    (d : PositiveVarianceFlowData (EuclideanSpace ℝ (Fin D)))
    (k : ℕ) {t : ℝ} (ht : t ∈ Ioo (left d.b) (right d.b))
    (y : EuclideanSpace ℝ (Fin D)) :
    vectorTensor (d.positionJet (k+2) t y) = -(d.ell*d.r^2) •
      materialVectorTermsTensor d (materialIterate (d.ell*d.r^2) materialMeanExpr k)
        t (d.state t y).fst := by
  ext a
  change inner ℝ (coordinateDirection D (a 0)) _ = -(d.ell*d.r^2)*
    materialVectorTermsTensor d (materialIterate (d.ell*d.r^2) materialMeanExpr k) t (d.state t y).fst a
  rw [materialVectorTermsTensor_apply]
  exact positionJet_coordinate_expansion d k a ht y

/-- Exact actual reference-law to current-law transfer, preserving the physical scale. -/
theorem positionJet_integral_norm_sq
    (d : PositiveVarianceFlowData (EuclideanSpace ℝ (Fin D)))
    (k : ℕ) {t : ℝ} (ht : t ∈ Icc 0 d.b) :
    (∫ y, ‖d.positionJet (k+2) t y‖^2 ∂d.positionMeasure) =
      (d.ell*d.r^2)^2 * ∫ y,
        ‖materialVectorTermsTensor d (materialIterate (d.ell*d.r^2) materialMeanExpr k) t y‖^2
          ∂interpolationLaw d.F d.x d.r t := by
  have hti := source_subset d.hb0 d.hb1 ht
  have hp := d.state_fst_measurePreserving ht
  have ha := (actualVectorTerms_memLp d (materialIterate (d.ell*d.r^2) materialMeanExpr k)
    ⟨hti.1.le,hti.2.le⟩).aestronglyMeasurable.norm.pow 2
  have hmap := integral_map hp.measurable.aemeasurable (hp.map_eq.symm ▸ ha)
  rw [hp.map_eq] at hmap
  calc
    _ = ∫ y, (d.ell*d.r^2)^2 *
      ‖materialVectorTermsTensor d (materialIterate (d.ell*d.r^2) materialMeanExpr k)
        t (d.state t y).fst‖^2 ∂interpolationLaw d.F d.x d.r d.b := by
      apply integral_congr_ae
      filter_upwards [] with y
      rw [←vectorTensor_norm_sq,positionJet_tensor_expansion d k hti,norm_smul]
      simp [mul_pow,Real.norm_eq_abs,sq_abs]
    _ = _ := by
      rw [integral_const_mul]
      congr 1
      exact hmap.symm

end AcceleratedLogConcave.Tensor.ActualCoefficientIntegrability
