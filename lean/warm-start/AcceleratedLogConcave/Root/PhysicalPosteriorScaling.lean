import AcceleratedLogConcave.Root.RecursiveRadiusFamily
import AcceleratedLogConcave.Conditional.RecursiveReferencePosteriorBound

/-! Exact physical posterior and directional score scaling for the root's
potential z ↦ V(sqrt h z). Normalization is preserved by the existing affine
posterior theorem; no heat-Hessian identity is postulated. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory ProbabilityTheory
open scoped ContDiff RealInnerProductSpace
namespace AcceleratedLogConcave.Root.PhysicalPosteriorScaling
open Conditional RecursiveRadiusFamily
variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι

/-- Both the physical center and posterior variance acquire their actual scale. -/
theorem posterior_map {V : E → ℝ} (hV : Measurable V) {h r : ℝ}
    (hh : 0 < h) (hr : 0 < r) (c : E) :
    (Gibbs.heatPosterior (physicalPotential V h) (r^2) c).map
      (fun z ↦ Real.sqrt h • z) =
      Gibbs.heatPosterior V (h*r^2) (Real.sqrt h • c) := by
  have hp := heatPosterior_primitive_map_affine hV
    (Real.sqrt_pos.mpr hh).ne' (sq_pos_of_pos hr).ne' (0 : E) c
  have he : primitivePotential V (0 : E) (Real.sqrt h) = physicalPotential V h := by
    funext z
    simp only [primitivePotential,physicalPotential,zero_add]
  rw [he] at hp
  simpa only [zero_add,Real.sq_sqrt hh.le] using hp

/-- The original gradient is multiplied by the actual physical scale. -/
theorem physicalPotential_gradient {V : E → ℝ} (hV : ContDiff ℝ 2 V) (h : ℝ) (z : E) :
    gradient (physicalPotential V h) z = Real.sqrt h • gradient V (Real.sqrt h • z) := by
  apply ext_inner_right ℝ
  intro v
  rw [inner_gradient_left,real_inner_smul_left,inner_gradient_left]
  change fderiv ℝ (fun w : E ↦ V (Real.sqrt h • w)) z v = _
  have hd := ((hV.differentiable (by norm_num) (Real.sqrt h • z)).hasFDerivAt).comp z
    ((hasFDerivAt_id (𝕜 := ℝ) z).const_smul (Real.sqrt h))
  simpa only [Function.comp_def,ContinuousLinearMap.comp_apply,
    smul_apply,ContinuousLinearMap.id_apply,map_smul,smul_eq_mul] using
      congrArg (fun L : E →L[ℝ] ℝ ↦ L v) hd.fderiv

/-- Exact original-potential posterior variance, with no independence or
curvature assumption used to produce this identity. -/
theorem score_variance {V : E → ℝ} (hV : ContDiff ℝ 2 V) {h r : ℝ}
    (hh : 0 < h) (hr : 0 < r) (c v : E) :
    Var[fun z ↦ ⟪v,gradient (physicalPotential V h) z⟫;
      Gibbs.heatPosterior (physicalPotential V h) (r^2) c] =
      h * Var[fun a ↦ ⟪v,gradient V a⟫;
        Gibbs.heatPosterior V (h*r^2) (Real.sqrt h • c)] := by
  simp_rw [physicalPotential_gradient hV,real_inner_smul_right]
  rw [variance_const_mul,Real.sq_sqrt hh.le]
  congr 1
  have hg : Continuous (fun a : E ↦ ⟪v,gradient V a⟫) :=
    continuous_const.inner ((InnerProductSpace.toDual ℝ E).symm.continuous.comp
      (hV.continuous_fderiv (by norm_num)))
  rw [← posterior_map hV.continuous.measurable hh hr c,
    variance_map hg.measurable.aemeasurable (show AEMeasurable (fun z : E ↦ Real.sqrt h • z) _ by fun_prop)]
  rfl


/-- The physical child posterior covariance is controlled at the same
original-potential center and heat time, using curvature only once. -/
theorem score_variance_le_curvature {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hlo : ∀ z a, 0 ≤ fderiv ℝ (fderiv ℝ V) z a a)
    (hup : ∀ z a, fderiv ℝ (fderiv ℝ V) z a a ≤ ‖a‖^2)
    {h r : ℝ} (hh : 0 < h) (hr : 0 < r) (hsmall : h*r^2 ≤ 1/2) (c v : E) :
    Var[fun z ↦ ⟪v,gradient (physicalPotential V h) z⟫;
      Gibbs.heatPosterior (physicalPotential V h) (r^2) c] ≤
      2*h^2*r^2 * fderiv ℝ (fderiv ℝ (Gibbs.heatPotential V (h*r^2)))
        (Real.sqrt h • c) v v := by
  let theta : SourceParameters E 1 :=
    ⟨(Real.sqrt h • c,Real.sqrt h*r,1),mul_pos (Real.sqrt_pos.mpr hh) hr,
      by norm_num,by simpa only [mul_pow,Real.sq_sqrt hh.le,mul_one] using hsmall⟩
  have hup1 : ∀ z a, fderiv ℝ (fderiv ℝ V) z a a ≤ (1 : ℝ) * ‖a‖^2 := by
    simpa only [one_mul] using hup
  have hb := Conditional.RecursiveReference.posteriorBudget_le_curvature hV
    (by norm_num : (0 : ℝ) ≤ 1) hlo hup1 theta v
  rw [Conditional.RecursiveReference.posteriorBudget,
    RecursiveReferenceCovariance.primitive_budget_eq_variance hV (by norm_num) hlo hup1
      theta.center theta.radius_pos v] at hb
  have hb' : Var[fun a : E ↦ ⟪v,gradient V a⟫;
      Gibbs.heatPosterior V (h*r^2) (Real.sqrt h • c)] ≤
      2*(h*r^2) * fderiv ℝ (fderiv ℝ (Gibbs.heatPotential V (h*r^2)))
        (Real.sqrt h • c) v v := by
    simpa only [theta,SourceParameters.center,SourceParameters.radius,mul_pow,
      Real.sq_sqrt hh.le,mul_one,mul_assoc] using hb
  rw [score_variance hV hh hr]
  exact (mul_le_mul_of_nonneg_left hb' hh.le).trans_eq (by ring)

end AcceleratedLogConcave.Root.PhysicalPosteriorScaling
