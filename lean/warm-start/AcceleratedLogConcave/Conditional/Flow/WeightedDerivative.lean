import AcceleratedLogConcave.Conditional.Flow.InterpolationDerivative

/-! Weighted latent differentiation for the observable-weighted continuity
equation. Only a weighted first moment is needed. -/
noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology

namespace AcceleratedLogConcave.Conditional
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem hasDerivAt_weightedLatentInterpolation_integral
    (μ ν : Measure E) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {w : E → ℝ} (hw : Continuous w)
    (hW : Integrable (fun z => ‖w z‖) μ)
    (hWZ : Integrable (fun z : E => ‖w z‖ * ‖z‖) μ)
    (hN : Integrable (fun n : E => ‖n‖) ν)
    {c d ρ : ℝ} (hc : -1 < c) (hd : d < 1) (hρc : c < ρ) (hρd : ρ < d)
    (ψ : ℝ × E → ℝ) (hψ : Continuous ψ)
    (hψd : ∀ s ∈ Icc c d, ∀ y,
      HasFDerivAt ψ (fderiv ℝ ψ (s, y)) (s, y))
    (hDc : Continuous (fun y => fderiv ℝ ψ (ρ, y)))
    {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ s ∈ Icc c d, ∀ y, ‖fderiv ℝ ψ (s, y)‖ ≤ C)
    (hint : Integrable (fun p : E × E => w p.1 * ψ (ρ, interpolationMap ρ p)) (μ.prod ν)) :
    Integrable (fun p : E × E => w p.1 * fderiv ℝ ψ (ρ, interpolationMap ρ p)
      (1, interpolationPathVelocity ρ p)) (μ.prod ν) ∧
    HasDerivAt (fun s => ∫ p, w p.1 * ψ (s, interpolationMap s p) ∂μ.prod ν)
      (∫ p, w p.1 * fderiv ℝ ψ (ρ, interpolationMap ρ p)
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
  have hdom : Integrable
      (fun p : E × E => ‖w p.1‖ * (C * (1 + ‖p.1‖ + B * ‖p.2‖))) (μ.prod ν) := by
    convert (((hW.comp_fst ν).add (hWZ.comp_fst ν)).add
      ((hW.mul_prod hN).const_mul B)).const_mul C using 1
    funext p
    simp only [Pi.add_apply]
    ring
  have hDmeas : AEStronglyMeasurable (fun p : E × E => w p.1 *
      fderiv ℝ ψ (ρ, interpolationMap ρ p) (1, interpolationPathVelocity ρ p))
      (μ.prod ν) := by
    apply Continuous.aestronglyMeasurable
    apply (hw.comp continuous_fst).mul
    apply (hDc.comp (by unfold interpolationMap; fun_prop)).clm_apply
    unfold interpolationPathVelocity
    fun_prop
  exact hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun s p => w p.1 * ψ (s, interpolationMap s p))
    (F' := fun s p => w p.1 * fderiv ℝ ψ (s, interpolationMap s p)
      (1, interpolationPathVelocity s p))
    (Icc_mem_nhds hρc hρd)
    (Eventually.of_forall fun s => ((hw.comp continuous_fst).mul
      (hψ.comp (continuous_const.prodMk
        (by unfold interpolationMap; fun_prop)))).aestronglyMeasurable)
    hint hDmeas
    (Eventually.of_forall fun p s hs => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left
        (((fderiv ℝ ψ (s, interpolationMap s p)).le_opNorm _).trans
          (mul_le_mul (hbound s hs _) (hpairs s hs p) (norm_nonneg _) hC)) (norm_nonneg _))
    hdom
    (Eventually.of_forall fun p s hs => by
      have h := (hψd s hs _).comp_hasDerivAt s
        ((hasDerivAt_id s).prodMk (hasDerivAt_interpolationMap (hv s hs) p))
      simpa only [zero_mul, zero_add, id_eq, Pi.mul_apply, Function.comp_apply] using! (hasDerivAt_const s (w p.1)).mul h)

end AcceleratedLogConcave.Conditional
