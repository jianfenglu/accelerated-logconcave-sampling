import AcceleratedLogConcave.Root.OuterRootFlowIdentification
import AcceleratedLogConcave.Root.OuterRootStrongJetLp
import AcceleratedLogConcave.Gibbs.SmoothedPrimitiveScaleMoment
import AcceleratedLogConcave.Kinetic.Mixing.HeatMarginal

/-! Original-data primitive-scale moments at the actual conditional Gaussian-
start root centers, via the proved physical trajectory and marginal transport. -/
noncomputable section
set_option autoImplicit false
set_option Elab.async false
open MeasureTheory ProbabilityTheory Set
open scoped NNReal
namespace AcceleratedLogConcave.Root.OuterRootCenterMoment
open OuterRootFlowIdentification OuterRootStrongJetLp
variable {d : ℕ} {V : EuclideanSpace ℝ (Fin d) → ℝ} (hV : ContDiff ℝ 2 V)
  {m h : ℝ} (hm : 0<m) (hh : 0<h)
  (hlo : ∀ z v,m*‖v‖^2≤fderiv ℝ (fderiv ℝ V) z v v)
  (hup : ∀ z v,fderiv ℝ (fderiv ℝ V) z v v≤‖v‖^2)
local notation "F" => family hV hm hh hlo hup
local notation "E" => EuclideanSpace ℝ (Fin d)

def variance (u : Icc (0:ℝ) (1/2)) : ℝ≥0 :=
  ⟨2*h^2*(1-(u:ℝ)^2),by
    have hu := u.property
    have hs : 0≤1-(u:ℝ)^2 := by nlinarith [hu.1,hu.2]
    exact mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg h)) hs⟩

include hV hm hh hlo hup in
/-- The physical source path's marginal has the exact executed variance. -/
theorem family_law (u : Icc (0:ℝ) (1/2)) :
    (F).law u = Channels.forward (volume.tilted (fun x => -V x)) (variance (h := h) u) := by
  have hZ := Gibbs.integrable_exp_neg_of_hessian_lower hV hm hlo
  let : IsProbabilityMeasure (volume.tilted (fun x => -V x)) := isProbabilityMeasure_tilted hZ
  unfold family RecursiveInnovation.originalPhysicalReference
  rw [Kinetic.Reheating.clockTransportFamily_heated_law _ _ _ u u.property]
  exact Kinetic.Reheating.heatedLaw_eq_forward _ (variance (h := h) u)

def center (u : Icc (0:ℝ) (1/2)) (p : E × E) : E :=
  (Real.sqrt h)⁻¹ • p.1 + (Real.sqrt (2*h)*(u:ℝ)) •
    OuterRootPhysicalPath.rawY hV hh (lower_nonneg hm hlo) hup ((Real.sqrt h)⁻¹ • p.1) p.2 u

/-- Exact equality with the normalized transported position, on the same seed. -/
theorem center_eq_pairFlow (u : Icc (0:ℝ) (1/2)) (p : E × E) :
    center hV hm hh hlo hup u p = (Real.sqrt h)⁻¹ •
      (Kinetic.referenceCoupledPairFlow F (Real.sqrt (2*h^2)) u p).1 := by
  have H := congrArg Prod.fst (conditional_eq_reference_trajectory hV hm hh hlo hup
    ((Real.sqrt h)⁻¹ • p.1) p.2 u.property)
  have hs := (Real.sqrt_pos.mpr hh).ne'
  simp only [smul_smul,mul_inv_cancel₀ hs,one_smul] at H
  change OuterRootPhysicalPath.position hV hh (lower_nonneg hm hlo) hup
    ((Real.sqrt h)⁻¹ • p.1) p.2 u=(Kinetic.referenceCoupledPairFlow F (Real.sqrt (2*h^2)) u p).1 at H
  rw [← H,OuterRootPhysicalPath.position,smul_add,smul_smul,inv_mul_cancel₀ hs,one_smul,
    ← OuterRootPhysicalPath.scale_sqrt hh]
  unfold center
  rw [smul_smul]
  congr 1
  congr 1
  field_simp

/-- No supplied moment bound: source-center primitiveScale² is integrable and
at most 10d throughout the closed physical clock interval. -/
theorem center_scale_square (hsmall : h≤1/2) (u : Icc (0:ℝ) (1/2)) :
    Integrable (fun p => (Gibbs.primitiveScale (Oracle.scaledPotential V (Real.sqrt h))
      (center hV hm hh hlo hup u p))^2) (seedMeasure F) ∧
    (∫ p,(Gibbs.primitiveScale (Oracle.scaledPotential V (Real.sqrt h))
      (center hV hm hh hlo hup u p))^2 ∂seedMeasure F)≤10*(d:ℝ) := by
  have hv : (variance (h := h) u:ℝ)≤1 := by
    change 2*h^2*(1-(u:ℝ)^2)≤1
    have hs := sq_nonneg (u:ℝ)
    have hh2 : h^2≤1/4 := by nlinarith
    nlinarith [mul_nonneg (sq_nonneg h) hs]
  obtain ⟨hi,hb⟩ := Gibbs.SmoothedPrimitiveScaleMoment.primitiveScale_square hV hm hlo hup h hh
    (hsmall.trans (by norm_num)) (variance (h := h) u) hv
  rw [← family_law hV hm hh hlo hup u] at hi hb
  have hp := (measurePreserving_fst (μ := (F).law u) (ν := stdGaussian E)).comp
    (Kinetic.referenceCoupledPairFlow_measurePreserving F (Real.sqrt (2*h^2)) u)
  have he : (fun p : E × E => (Gibbs.primitiveScale (Oracle.scaledPotential V (Real.sqrt h))
      (center hV hm hh hlo hup u p))^2) =
      (fun x : E => (Gibbs.primitiveScale (Oracle.scaledPotential V (Real.sqrt h))
        ((Real.sqrt h)⁻¹ • x))^2) ∘ (fun p => (Kinetic.referenceCoupledPairFlow F (Real.sqrt (2*h^2)) u p).1) := by
    funext p
    rw [center_eq_pairFlow]
    rfl
  rw [he]
  refine ⟨hp.integrable_comp_of_integrable hi,?_⟩
  have hmeas := hi.aestronglyMeasurable
  rw [← hp.map_eq] at hmeas
  have heq := integral_map hp.measurable.aemeasurable hmeas
  rw [hp.map_eq] at heq
  exact heq.symm.trans_le hb

end AcceleratedLogConcave.Root.OuterRootCenterMoment
