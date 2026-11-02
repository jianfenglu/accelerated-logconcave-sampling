import AcceleratedLogConcave.Conditional.Flow.InterpolationPath
import AcceleratedLogConcave.Conditional.Flow.TestBounds
import Mathlib.MeasureTheory.Integral.Prod

/-! Dominated differentiation of the independent-noise interpolation. The
dominator uses only first moments of the two latent variables. -/

noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology

namespace AcceleratedLogConcave.Conditional
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- A moving test can be differentiated through the actual interpolation map.
The derivative bound is supplied by `compactTest_fderiv_bound` for compact
space-time tests. No differentiation of the base potential is involved. -/
theorem hasDerivAt_latentInterpolation_integral
    (μ ν : Measure E) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hZ : Integrable (fun z : E => ‖z‖) μ)
    (hN : Integrable (fun n : E => ‖n‖) ν)
    {c d ρ : ℝ} (hc : -1 < c) (hd : d < 1) (hρc : c < ρ) (hρd : ρ < d)
    (ψ : ℝ × E → ℝ) (hψ : Continuous ψ)
    (hψd : ∀ s ∈ Icc c d, ∀ y,
      HasFDerivAt ψ (fderiv ℝ ψ (s, y)) (s, y))
    (hDc : Continuous (fun y => fderiv ℝ ψ (ρ, y)))
    {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ s ∈ Icc c d, ∀ y, ‖fderiv ℝ ψ (s, y)‖ ≤ C)
    (hint : Integrable (fun p : E × E => ψ (ρ, interpolationMap ρ p)) (μ.prod ν)) :
    Integrable (fun p : E × E => fderiv ℝ ψ (ρ, interpolationMap ρ p)
      (1, interpolationPathVelocity ρ p)) (μ.prod ν) ∧
    HasDerivAt (fun s => ∫ p, ψ (s, interpolationMap s p) ∂μ.prod ν)
      (∫ p, fderiv ℝ ψ (ρ, interpolationMap ρ p)
        (1, interpolationPathVelocity ρ p) ∂μ.prod ν) ρ := by
  have hv (s : ℝ) (hs : s ∈ Icc c d) : 0 < conditionalVariance s :=
    conditionalVariance_pos (hc.trans_le hs.1) (hs.2.trans_lt hd)
  have hk : ContinuousOn (fun s : ℝ => s / Real.sqrt (conditionalVariance s))
      (Icc c d) :=
    continuousOn_id.div (Real.continuous_sqrt.comp
      (continuous_const.sub (continuous_id.pow 2))).continuousOn
      (fun s hs => (Real.sqrt_pos.mpr (hv s hs)).ne')
  obtain ⟨K, hK⟩ := isCompact_Icc.exists_bound_of_continuousOn hk
  let B := max K 0
  have hB : 0 ≤ B := le_max_right _ _
  have hcoeff (s : ℝ) (hs : s ∈ Icc c d) :
      ‖s / Real.sqrt (conditionalVariance s)‖ ≤ B :=
    (hK s hs).trans (le_max_left _ _)
  have hvel (s : ℝ) (hs : s ∈ Icc c d) (p : E × E) :
      ‖interpolationPathVelocity s p‖ ≤ ‖p.1‖ + B * ‖p.2‖ := by
    change ‖p.1 - (s / Real.sqrt (conditionalVariance s)) • p.2‖ ≤ _
    apply (norm_sub_le _ _).trans
    rw [norm_smul]
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_right (hcoeff s hs) (norm_nonneg p.2))
  have hpairs (s : ℝ) (hs : s ∈ Icc c d) (p : E × E) :
      ‖((1 : ℝ), interpolationPathVelocity s p)‖ ≤ 1 + ‖p.1‖ + B * ‖p.2‖ := by
    simp only [Prod.norm_def, norm_one]
    apply max_le
    · linarith [norm_nonneg p.1, mul_nonneg hB (norm_nonneg p.2)]
    · linarith [hvel s hs p]
  have hdom : Integrable (fun p : E × E => C * (1 + ‖p.1‖ + B * ‖p.2‖))
      (μ.prod ν) :=
    (((integrable_const 1).add (hZ.comp_fst ν)).add
      ((hN.comp_snd μ).const_mul B)).const_mul C
  have hDmeas : AEStronglyMeasurable (fun p : E × E =>
      fderiv ℝ ψ (ρ, interpolationMap ρ p) (1, interpolationPathVelocity ρ p))
      (μ.prod ν) := by
    apply Continuous.aestronglyMeasurable
    apply (hDc.comp (by unfold interpolationMap; fun_prop)).clm_apply
    unfold interpolationPathVelocity
    fun_prop
  exact hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun s p => ψ (s, interpolationMap s p))
    (F' := fun s p => fderiv ℝ ψ (s, interpolationMap s p)
      (1, interpolationPathVelocity s p))
    (Icc_mem_nhds hρc hρd)
    (Eventually.of_forall fun s => (hψ.comp (continuous_const.prodMk
      (by unfold interpolationMap; fun_prop))).aestronglyMeasurable)
    hint hDmeas
    (Eventually.of_forall fun p s hs =>
      ((fderiv ℝ ψ (s, interpolationMap s p)).le_opNorm _).trans
        (mul_le_mul (hbound s hs _) (hpairs s hs p) (norm_nonneg _) hC))
    hdom
    (Eventually.of_forall fun p s hs =>
      (hψd s hs _).comp_hasDerivAt s
        ((hasDerivAt_id s).prodMk (hasDerivAt_interpolationMap (hv s hs) p)))

end AcceleratedLogConcave.Conditional
