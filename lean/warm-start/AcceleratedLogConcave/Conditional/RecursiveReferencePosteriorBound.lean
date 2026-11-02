import AcceleratedLogConcave.Conditional.RecursiveReferenceInnovation
import AcceleratedLogConcave.Conditional.RecursiveReferenceChildMoment
import AcceleratedLogConcave.Conditional.RecursiveReferenceCovariance

/-! Closed directional posterior innovation bound for the actual recursively
constructed reference family. The induction propagates the posterior covariance
budget; curvature is used only after that induction is complete. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open Set MeasureTheory ProbabilityTheory Filter
open scoped ContDiff ENNReal RealInnerProductSpace
namespace AcceleratedLogConcave.Conditional.RecursiveReference
open Numerics Numerics.MeanFlowLp Numerics.AffineGraph MeanReferenceLayer
open TerminalChildrenParentFamily
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ}
local notation "E" => EuclideanSpace ℝ ι
variable {F : EuclideanSpace ℝ ι → ℝ} {ell : ℝ} (hF : ContDiff ℝ 2 F) (hell : 0 ≤ ell)
  (hlo : ∀ z a, 0 ≤ fderiv ℝ (fderiv ℝ F) z a a)
  (hup : ∀ z a, fderiv ℝ (fderiv ℝ F) z a a ≤ ell * ‖a‖ ^ 2)
  (G : MeanGeometry m) (hm : 0 < m) (t : ℝ) (ht : 0 < t)

/-- The actual centered primitive-gradient posterior budget. -/
def posteriorBudget (theta : SourceParameters E ell) (v : E) : ℝ :=
  ∫ z, ⟪v,primitiveObservable F theta.center theta.radius z-
    Gibbs.primitiveMean F theta.center theta.radius⟫^2 ∂baseLaw F theta.center theta.radius

omit [DecidableEq ι] in
lemma posteriorBudget_nonneg (theta : SourceParameters E ell) (v : E) :
    0 ≤ posteriorBudget (F := F) theta v := integral_nonneg (fun _ ↦ sq_nonneg _)

omit [DecidableEq ι] in
lemma directionalMoment_nonneg (C : Family ι ell) (theta : SourceParameters E ell) (v : E) :
    0 ≤ directionalMoment C theta v :=
  integral_nonneg (fun _ ↦ integral_nonneg (fun _ ↦ sq_nonneg _))

omit [DecidableEq ι] in
lemma directionalMoment_terminalFamily (theta : SourceParameters E ell) (v : E) :
    directionalMoment terminalFamily theta v = 0 := by
  simp [directionalMoment,terminalFamily,Kernel.deterministic_apply]

omit [DecidableEq ι] in
lemma conditionalVariance_backwardEnd : conditionalVariance (backwardEnd G.R) = G.R^2 := by
  have h : 0 ≤ 1-G.R^2 := by nlinarith [G.R_pos,G.R_le_half]
  unfold conditionalVariance backwardEnd
  rw [Real.sq_sqrt h]
  ring

/-- Actual recursive posterior directional innovation, uniformly in all
admissible centers, radii and widths. Child budgets are discharged by the
same decreasing-precision induction, including overshoots of the cutoff. -/
theorem referenceFamily_posterior_bound (q : ℝ) :
    ∀ (theta : SourceParameters E ell) (v : E),
    theta.width^2 * directionalMoment (referenceFamily hF hell hlo hup G hm t ht q) theta v ≤
      posteriorBudget (F := F) theta v := by
  induction q using (measure (fun q : ℝ ↦ Oracle.Precision.precisionRank t q)).wf.induction with
  | h q ih =>
    intro theta v
    by_cases hq : Oracle.Precision.terminal q
    · rw [referenceFamily_terminal hF hell hlo hup G hm t ht q hq,
        directionalMoment_terminalFamily,mul_zero]
      exact posteriorBudget_nonneg theta v
    have hq' : 1/2 < q := lt_of_not_ge hq
    let d := data hF hell hlo hup G theta
    let C := sourceChildren hF hell hlo hup G hm
      (referenceFamily hF hell hlo hup G hm t ht (q-t)) theta
    let B : E → ℝ := fun x ↦ Var[fun a ↦ ⟪v,gradient F a⟫;
      Gibbs.heatPosterior F ((theta.radius*G.R)^2) x]
    have hB : StronglyMeasurable B :=
      RecursiveReferenceCovariance.stronglyMeasurable_physical_variance hF hlo (mul_pos theta.radius_pos G.R_pos) v
    have hBi : Integrable (fun y ↦ B (theta.center+(theta.radius*backwardEnd G.R) • y))
        (Numerics.MeanBenchmarkCoupling.positionLaw d) := by
      have h := RecursiveReferenceCovariance.integrable_conditional_variance hF hell hlo hup
        theta.center theta.radius_pos G.backwardEnd_pos.le G.backwardEnd_lt_one v
      rw [conditionalVariance_backwardEnd G] at h
      simpa only [B,d,data,Numerics.MeanBenchmarkCoupling.positionLaw,mul_pow] using h
    have hBm : 0 ≤ ∫ y, B (theta.center+(theta.radius*backwardEnd G.R) • y)
        ∂Numerics.MeanBenchmarkCoupling.positionLaw d :=
      integral_nonneg (fun _ ↦ variance_nonneg _ _)
    have hchild (i : Fin m) :
        (C.scale i)^2 * (∫ z, ⟪v,MeanReferenceVariance.childIncrement d C i z⟫^2
          ∂averagedJoint d C) ≤
        ∫ y, B (theta.center+(theta.radius*backwardEnd G.R) • y)
          ∂Numerics.MeanBenchmarkCoupling.positionLaw d := by
      rw [MeanReferenceVariance.child_second_moment_transfer,
        ← integral_const_mul]
      have heq := integral_stateCenter d i B hB
      change (∫ b, (C.scale i)^2 *
        directionalMoment (referenceFamily hF hell hlo hup G hm t ht (q-t))
          (childParameters hell G theta (stateCenter d i b)) v ∂MeanReferenceLayer.baseLaw d) ≤ _
      apply le_trans ?_ (le_of_eq (by simpa only [d,data] using heq))
      have hBbase : Integrable (fun b ↦ B (stateCenter d i b)) (MeanReferenceLayer.baseLaw d) :=
        (statePosition_preserving d i).integrable_comp_of_integrable hBi
      apply integral_mono_of_nonneg
        (Eventually.of_forall (fun b ↦ mul_nonneg (sq_nonneg _)
          (directionalMoment_nonneg _ _ _))) hBbase
      exact Eventually.of_forall fun b ↦ by
        have h := ih (q-t) (precision_child_lt ht hq')
          (childParameters hell G theta (stateCenter d i b)) v
        rw [posteriorBudget,RecursiveReferenceCovariance.primitive_budget_eq_variance
          hF hell hlo hup _ (childParameters hell G theta (stateCenter d i b)).radius_pos v] at h
        exact h
    rw [referenceFamily_directionalMoment_assembly hF hell hlo hup G hm t ht q hq']
    change (∫ z, ⟪v,d.sigma • (recombine d C z.1 z.2-z.1.1)⟫^2 ∂averagedJoint d C) ≤ _
    rw [MeanReferenceVariance.assemblyTarget d C v]
    calc
      _ ≤ (∫ y, ⟪v,conditionalMean F theta.center theta.radius (backwardEnd G.R) y-
          conditionalMean F theta.center theta.radius 0 0⟫^2
          ∂Numerics.MeanBenchmarkCoupling.positionLaw d) +
          ∑ i, (GaussLegendre.weight m i)^2 *
            (∫ y, B (theta.center+(theta.radius*backwardEnd G.R) • y)
              ∂Numerics.MeanBenchmarkCoupling.positionLaw d) := by
        apply add_le_add (assembly_center_directional_le d C v)
        apply Finset.sum_le_sum
        intro i _
        rw [mul_pow,mul_assoc]
        exact mul_le_mul_of_nonneg_left (hchild i) (sq_nonneg _)
      _ ≤ (∫ y, ⟪v,conditionalMean F theta.center theta.radius (backwardEnd G.R) y-
          conditionalMean F theta.center theta.radius 0 0⟫^2
          ∂Numerics.MeanBenchmarkCoupling.positionLaw d) +
          (∫ y, B (theta.center+(theta.radius*backwardEnd G.R) • y)
            ∂Numerics.MeanBenchmarkCoupling.positionLaw d) := by
        apply add_le_add le_rfl
        rw [← Finset.sum_mul]
        exact mul_le_of_le_one_left hBm (sum_weight_sq_le_one hm)
      _ = posteriorBudget (F := F) theta v := by
        have h := RecursiveReferenceCovariance.total_covariance_centered hF hell hlo hup
          theta.center theta.radius_pos G.backwardEnd_pos.le G.backwardEnd_lt_one v
        rw [conditionalVariance_backwardEnd G] at h
        simpa only [posteriorBudget,B,d,data,Numerics.MeanBenchmarkCoupling.positionLaw,mul_pow] using h.symm


include hF hell hlo hup in
omit [DecidableEq ι] in
/-- Curvature is applied once to the actual posterior budget after the
recursion has closed; it is not propagated between differing centers. -/
theorem posteriorBudget_le_curvature (theta : SourceParameters E ell) (v : E) :
    posteriorBudget (F := F) theta v ≤
      2 * theta.radius^2 * ell *
        fderiv ℝ (fderiv ℝ (Gibbs.heatPotential F (theta.radius^2))) theta.center v v := by
  have hlo0 : ∀ x v, (0 : ℝ) * ‖v‖^2 ≤ fderiv ℝ (fderiv ℝ F) x v v := by
    simpa only [zero_mul] using hlo
  have hs : 0 < theta.radius^2 := sq_pos_of_pos theta.radius_pos
  have htL : theta.radius^2 * ell < 1 := by linarith [theta.small]
  have h := Gibbs.heat_score_covariance_bound hF (m := 0) le_rfl hs hlo0 hup htL theta.center v
  have hmeas : AEMeasurable (fun a : E ↦ fderiv ℝ F a v)
      (Gibbs.heatPosterior F (theta.radius^2) theta.center) :=
    ((hF.continuous_fderiv (by norm_num)).clm_apply continuous_const).measurable.aemeasurable
  rw [covariance_self hmeas] at h
  have hvar : Var[fun a : E ↦ ⟪v,gradient F a⟫;
      Gibbs.heatPosterior F (theta.radius^2) theta.center] ≤
      theta.radius^2 * ell / (1-theta.radius^2 * ell) *
        fderiv ℝ (fderiv ℝ (Gibbs.heatPotential F (theta.radius^2))) theta.center v v := by
    simpa only [inner_gradient_right,conj_trivial] using h
  have hH : 0 ≤ fderiv ℝ (fderiv ℝ (Gibbs.heatPotential F (theta.radius^2))) theta.center v v := by
    have hh := (Gibbs.heat_hessian_curvature hF (m := 0) le_rfl hs hlo0 hup theta.center v).1
    simpa only [zero_mul,zero_div] using hh
  have hcoef : theta.radius^2 * ell / (1-theta.radius^2 * ell) ≤
      2 * theta.radius^2 * ell := by
    have h0 : 0 ≤ theta.radius^2 * ell := mul_nonneg (sq_nonneg _) hell
    apply (div_le_iff₀ (show 0 < 1-theta.radius^2 * ell by linarith [theta.small])).mpr
    nlinarith [mul_nonneg h0 (sub_nonneg.mpr theta.small)]
  rw [posteriorBudget,RecursiveReferenceCovariance.primitive_budget_eq_variance
    hF hell hlo hup theta.center theta.radius_pos v]
  exact hvar.trans (mul_le_mul_of_nonneg_right hcoef hH)

/-- The actual recursively constructed reference has the curvature-weighted
directional innovation required by the normalized root. -/
theorem referenceFamily_curvature_bound (q : ℝ) (theta : SourceParameters E ell) (v : E) :
    theta.width^2 * directionalMoment (referenceFamily hF hell hlo hup G hm t ht q) theta v ≤
      2 * theta.radius^2 * ell *
        fderiv ℝ (fderiv ℝ (Gibbs.heatPotential F (theta.radius^2))) theta.center v v :=
  (referenceFamily_posterior_bound hF hell hlo hup G hm t ht q theta v).trans
    (posteriorBudget_le_curvature hF hell hlo hup theta v)

end AcceleratedLogConcave.Conditional.RecursiveReference
