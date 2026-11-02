import AcceleratedLogConcave.Oracle.PrivateSamplingReferenceLaw
import AcceleratedLogConcave.Conditional.TerminalChildrenParentFamily

/-! The literal private sampling reference becomes the prescribed mean position
law after the source prefix's stored-anchor scaling by backwardEnd R. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set
open scoped NNReal
namespace AcceleratedLogConcave.Oracle.MeanPrivateReferenceBridge
open Conditional Numerics.AffineGraph
variable {d m : ℕ} (M : MeanGeometry m)
  (mesh : IntervalMesh 0 (samplingEnd (M.R/backwardEnd M.R)))
  {F : Point d → ℝ} (hF : ContDiff ℝ 2 F)
  (hlo : ∀ z v, 0 ≤ fderiv ℝ (fderiv ℝ F) z v v) (x : Point d) (r : ℝ)

include hF hlo in
/-- Exact source scaling of the full private reference, including its reserve. -/
theorem scaled_forward :
    (Channels.forward (baseLaw F x r)
      ⟨(M.R/backwardEnd M.R)^2,by positivity⟩).map
        (fun y => backwardEnd M.R • y) =
      interpolationLaw F x r (backwardEnd M.R) := by
  let : IsProbabilityMeasure (baseLaw F x r) := baseLaw_isProbabilityMeasure hF hlo x r
  have ht : 0 ≤ M.R/backwardEnd M.R := (div_pos M.R_pos M.backwardEnd_pos).le
  have hn : Channels.noise (ι := Fin d) ⟨(M.R/backwardEnd M.R)^2,by positivity⟩ =
      (stdGaussian (Point d)).map (fun z => (M.R/backwardEnd M.R) • z) := by
    rw [Channels.noise_eq_scaled_stdGaussian]
    change Measure.map (fun z : Point d => Real.sqrt ((M.R/backwardEnd M.R)^2) • z) _ = _
    rw [Real.sqrt_sq ht]
  have hp : (baseLaw F x r).prod ((stdGaussian (Point d)).map
      (fun z => (M.R/backwardEnd M.R) • z)) =
      ((baseLaw F x r).prod (stdGaussian (Point d))).map
        (Prod.map id (fun z => (M.R/backwardEnd M.R) • z)) := by
    simpa only [Measure.map_id] using Measure.map_prod_map (baseLaw F x r)
      (stdGaussian (Point d)) measurable_id (measurable_const_smul (M.R/backwardEnd M.R))
  have hv : Real.sqrt (conditionalVariance (backwardEnd M.R)) = M.R := by
    rw [conditionalVariance,M.backwardEnd_sq]
    have he : 1-(1-M.R^2) = M.R^2 := by ring
    rw [he,Real.sqrt_sq M.R_pos.le]
  unfold Channels.forward
  rw [hn,Measure.conv,hp,Measure.map_map (by fun_prop) (by fun_prop),
    Measure.map_map (by fun_prop) (by fun_prop)]
  unfold interpolationLaw
  congr 1
  funext z
  change backwardEnd M.R • (z.1 + (M.R/backwardEnd M.R) • z.2) =
    backwardEnd M.R • z.1 + Real.sqrt (conditionalVariance (backwardEnd M.R)) • z.2
  rw [hv,smul_add,smul_smul]
  congr 2
  exact mul_div_cancel₀ M.R (ne_of_gt M.backwardEnd_pos)

variable {ell : ℝ} (hell : 0 ≤ ell)
  (hup : ∀ z v, fderiv ℝ (fderiv ℝ F) z v v ≤ ell*‖v‖^2)
  {r : ℝ} (hr : 0 < r)

/-- The actual Gaussian-start private reference readout, then the source
stored-anchor multiplication, has the mean reference's exact position law. -/
theorem reference_anchor_preserving :
    MeasurePreserving (fun z : (Point d × Point d) × Point d =>
      backwardEnd M.R •
        ((PrivateSamplingReferenceLaw.readout (RecursiveExecutable.privateGeometry M mesh)
          hF hell hlo hup x hr z.1.1 + ((M.R/backwardEnd M.R)/Real.sqrt 2) • z.1.2) +
          ((M.R/backwardEnd M.R)/2) • z.2))
      (((stdGaussian (Point d)).prod (stdGaussian (Point d))).prod (stdGaussian (Point d)))
      (interpolationLaw F x r (backwardEnd M.R)) := by
  have hs : MeasurePreserving (fun y : Point d => backwardEnd M.R • y)
      (Channels.forward (baseLaw F x r) ⟨(M.R/backwardEnd M.R)^2,by positivity⟩)
      (interpolationLaw F x r (backwardEnd M.R)) :=
    ⟨by fun_prop,scaled_forward M hF hlo x r⟩
  exact hs.comp (PrivateSamplingReferenceLaw.reference_preserving
    (RecursiveExecutable.privateGeometry M mesh) hF hell hlo hup x hr)

end AcceleratedLogConcave.Oracle.MeanPrivateReferenceBridge
