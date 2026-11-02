import AcceleratedLogConcave.Conditional.Flow.InterpolationDerivative
import AcceleratedLogConcave.Conditional.Flow.MeanIBP
import AcceleratedLogConcave.Conditional.Flow.WeakTransport
import AcceleratedLogConcave.Conditional.JointLaw

/-!
# Actual weak continuity equation for Gaussian interpolation

Differentiate the independent-noise representation, apply the proved Bayes
disintegration, and identify the conditional velocity by posterior integration
by parts. The test domination uses compact support and first latent moments.
-/

noncomputable section
open Set Function Filter MeasureTheory ProbabilityTheory
open scoped Topology

namespace AcceleratedLogConcave.Conditional
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
local notation "E" => EuclideanSpace ℝ ι

/-- The actual interpolation solves the weak continuity equation with drift
`-r M`, on every compact probability-time interval strictly below one. -/
theorem hasWeakContinuityEquation_interpolation
    {F : E → ℝ} (hF : ContDiff ℝ 2 F) {ell : ℝ}
    (hlo : ∀ z a, 0 ≤ fderiv ℝ (fderiv ℝ F) z a a)
    (hup : ∀ z a, fderiv ℝ (fderiv ℝ F) z a a ≤ ell * ‖a‖ ^ 2)
    (x : E) (r : ℝ) {a b : ℝ} (ha : -1 < a) (hb : b < 1) :
    HasWeakContinuityEquationOn (interpolationLaw F x r)
      (probabilityVelocity F x r) a b := by
  let := baseLaw_isProbabilityMeasure hF hlo x r
  have hZ : Integrable (fun z : E => ‖z‖) (baseLaw F x r) := by
    exact (Gibbs.integrable_id_heatPosterior (contDiff_primitivePotential hF x r)
      (m := 0) le_rfl (by norm_num)
      (by simpa using primitivePotential_hessian_nonneg hF hlo x r) 0).norm
  have hN : Integrable (fun n : E => ‖n‖) (stdGaussian E) :=
    IsGaussian.integrable_id.norm
  intro ψ hψ hψd hψK
  obtain ⟨K, hK, hzero⟩ := hψK
  have hmap (s : ℝ) :
      (∫ y, ψ (s, y) ∂interpolationLaw F x r s) =
        ∫ p, ψ (s, interpolationMap s p)
          ∂(baseLaw F x r).prod (stdGaussian E) := by
    rw [interpolationLaw]
    exact integral_map (φ := interpolationMap s) (by unfold interpolationMap; fun_prop)
      (f := fun y : E => ψ (s, y))
      (hψ.comp ((continuous_const : Continuous (fun _ : E => s)).prodMk
        continuous_id)).aestronglyMeasurable
  obtain ⟨C₀, _, hC₀⟩ := compactTest_norm_bound (c := a) (d := b) hψ hK hzero
  have hmeas (s : ℝ) : AEStronglyMeasurable
      (fun p : E × E => ψ (s, interpolationMap s p))
      ((baseLaw F x r).prod (stdGaussian E)) :=
    (hψ.comp (continuous_const.prodMk (by unfold interpolationMap; fun_prop))).aestronglyMeasurable
  have hint (s : ℝ) (hs : s ∈ Icc a b) : Integrable
      (fun p : E × E => ψ (s, interpolationMap s p))
      ((baseLaw F x r).prod (stdGaussian E)) :=
    (integrable_const C₀).mono' (hmeas s)
      (Eventually.of_forall fun p => hC₀ s hs (interpolationMap s p))
  have hcont : ContinuousOn
      (fun s => ∫ p, ψ (s, interpolationMap s p)
        ∂(baseLaw F x r).prod (stdGaussian E)) (Icc a b) := by
    apply continuousOn_of_dominated (fun s _ => hmeas s)
      (fun s hs => Eventually.of_forall fun p => hC₀ s hs (interpolationMap s p))
      (integrable_const C₀)
    exact Eventually.of_forall fun p => (hψ.comp
      (continuous_id.prodMk (by unfold interpolationMap conditionalVariance; fun_prop))).continuousOn
  refine ⟨by simpa only [hmap] using hcont, fun ρ hρ => ?_⟩
  let δ := min (ρ - a) (b - ρ) / 2
  have hδ : 0 < δ := div_pos (lt_min (sub_pos.mpr hρ.1) (sub_pos.mpr hρ.2)) (by norm_num)
  have hsub : Icc (ρ - δ) (ρ + δ) ⊆ Ioo a b := by
    intro s hs
    have h₁ := min_le_left (ρ - a) (b - ρ)
    have h₂ := min_le_right (ρ - a) (b - ρ)
    dsimp [δ] at hs
    constructor <;> linarith [hs.1, hs.2, hρ.1, hρ.2]
  have hρlo : -1 < ρ := ha.trans hρ.1
  have hρhi : ρ < 1 := hρ.2.trans hb
  have hv := conditionalVariance_pos hρlo hρhi
  obtain ⟨C, hC, hbound⟩ := compactTest_fderiv_bound hψd hsub hK hzero
  have hψon : ContDiffOn ℝ 1 ψ (Ioo a b ×ˢ (univ : Set E)) :=
    fun p hp => (hψd p hp.1).contDiffWithinAt
  have hDc : Continuous (fun y : E => fderiv ℝ ψ (ρ, y)) :=
    (hψon.continuousOn_fderiv_of_isOpen (isOpen_Ioo.prod isOpen_univ) le_rfl).comp_continuous
      (continuous_const.prodMk continuous_id) (fun y => ⟨hρ, mem_univ y⟩)
  have hlatent := hasDerivAt_latentInterpolation_integral (baseLaw F x r) (stdGaussian E)
    hZ hN (ha.trans (hsub ⟨le_rfl, by linarith⟩).1)
    ((hsub ⟨by linarith, le_rfl⟩).2.trans hb)
    (by linarith : ρ - δ < ρ) (by linarith : ρ < ρ + δ)
    ψ hψ (fun s hs y => ((hψd (s, y) (hsub hs)).differentiableAt (by norm_num)).hasFDerivAt)
    hDc hC hbound (hint ρ ⟨hρ.1.le, hρ.2.le⟩)
  let g (q : E × E) := fderiv ℝ ψ (ρ, q.1)
    (1, (conditionalVariance ρ)⁻¹ • (q.2 - ρ • q.1))
  have hg : StronglyMeasurable g := by
    apply Continuous.stronglyMeasurable
    exact (hDc.comp continuous_fst).clm_apply (by fun_prop)
  have hgi : Integrable (fun p : E × E => g (interpolationMap ρ p, p.1))
      ((baseLaw F x r).prod (stdGaussian E)) := by
    simpa only [g, interpolationPathVelocity_eq hv] using hlatent.1
  have hBayes := conditional_disintegration_integral hF hlo x r ρ hv g hg hgi
  have hinner (y : E) : (∫ z, g (y, z) ∂conditionalLaw F x r ρ y) =
      fderiv ℝ ψ (ρ, y) (1, probabilityVelocity F x r ρ y) :=
    integral_conditional_spaceTime_velocity hF hlo hup x r hρlo hρhi y
      (fderiv ℝ ψ (ρ, y))
  simp_rw [hinner] at hBayes
  have heq : (∫ p, fderiv ℝ ψ (ρ, interpolationMap ρ p)
      (1, interpolationPathVelocity ρ p) ∂(baseLaw F x r).prod (stdGaussian E)) =
      ∫ y, fderiv ℝ ψ (ρ, y) (1, probabilityVelocity F x r ρ y)
        ∂interpolationLaw F x r ρ := by
    simpa only [g, interpolationPathVelocity_eq hv] using hBayes.symm
  rw [show (fun s => ∫ y, ψ (s, y) ∂interpolationLaw F x r s) =
    (fun s => ∫ p, ψ (s, interpolationMap s p)
      ∂(baseLaw F x r).prod (stdGaussian E)) from funext hmap, ← heq]
  exact hlatent.2

end AcceleratedLogConcave.Conditional
