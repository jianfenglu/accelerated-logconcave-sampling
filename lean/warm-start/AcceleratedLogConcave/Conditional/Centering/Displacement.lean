import AcceleratedLogConcave.Conditional.Centering.LocalFlow
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Prod

/-! The deterministic squared-displacement inequality used before averaging
against the stationary phase law. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology

namespace AcceleratedLogConcave.Conditional.Centering
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [FiniteDimensional ℝ H]

omit [FiniteDimensional ℝ H] in
/-- Cauchy--Schwarz for the integral of a continuous curve on a positive interval. -/
theorem norm_intervalIntegral_sq_le {v : ℝ → H} (hv : Continuous v) {t : ℝ} (ht : 0 ≤ t) :
    ‖∫ τ in (0 : ℝ)..t, v τ‖ ^ 2 ≤ t * ∫ τ in (0 : ℝ)..t, ‖v τ‖ ^ 2 := by
  let μ := volume.restrict (Ioc (0 : ℝ) t)
  have hmem : MemLp (fun τ => ‖v τ‖) 2 μ := by
    apply (memLp_two_iff_integrable_sq hv.norm.aestronglyMeasurable).mpr
    exact (hv.norm.pow 2).intervalIntegrable 0 t |>.1
  have hconst : MemLp (fun _ : ℝ => (1 : ℝ)) 2 μ := memLp_const 1
  have hcs := integral_mul_le_Lp_mul_Lq_of_nonneg
    Real.HolderConjugate.two_two
    (Eventually.of_forall (fun τ => norm_nonneg (v τ)))
    (Eventually.of_forall (fun _ : ℝ => (by norm_num : (0 : ℝ) ≤ 1)))
    (by simpa using hmem) (by simpa using hconst)
  have hμ : μ.real univ = t := by simp [μ, ht]
  have hcs' : (∫ τ, ‖v τ‖ ∂μ) ≤ Real.sqrt (∫ τ, ‖v τ‖ ^ 2 ∂μ) * Real.sqrt t := by
    simpa only [mul_one, Real.rpow_two, one_pow, integral_const, smul_eq_mul, mul_one,
      hμ, Real.sqrt_eq_rpow] using hcs
  have hn := norm_integral_le_integral_norm (fun τ => v τ) (μ := μ)
  have hs0 : 0 ≤ ∫ τ, ‖v τ‖ ^ 2 ∂μ := integral_nonneg (fun _ => sq_nonneg _)
  have hs := Real.sq_sqrt hs0
  have hts := Real.sq_sqrt ht
  have h0 := norm_nonneg (∫ τ, v τ ∂μ)
  have hsq : ‖∫ τ, v τ ∂μ‖ ^ 2 ≤ t * ∫ τ, ‖v τ‖ ^ 2 ∂μ := by
    nlinarith [Real.sqrt_nonneg (∫ τ, ‖v τ‖ ^ 2 ∂μ), Real.sqrt_nonneg t]
  simpa only [intervalIntegral.integral_of_le ht] using hsq

/-- Squared displacement is bounded by time times integrated squared speed. -/
theorem completeCurve_displacement_sq_le {f : H → H} (hf : ContDiff ℝ 1 f)
    {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hgrowth : ∀ z, ‖f z‖ ≤ C * ‖z‖ + D) (x : H) {t : ℝ} (ht : 0 ≤ t) :
    ‖completeCurve hf hC hD hgrowth x t - x‖ ^ 2 ≤
      t * ∫ τ in (0 : ℝ)..t, ‖f (completeCurve hf hC hD hgrowth x τ)‖ ^ 2 := by
  have hc := hf.continuous.comp (completeCurve_continuous hf hC hD hgrowth x)
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun τ _ => completeCurve_deriv hf hC hD hgrowth x τ) (hc.intervalIntegrable 0 t)
  rw [completeCurve_initial] at hi
  rw [← hi]
  exact norm_intervalIntegral_sq_le hc ht

variable [MeasurableSpace H] [BorelSpace H]

/-- Averaging the actual trajectory estimate against a stationary measure
uses only its squared-speed moment. -/
theorem integral_completeCurve_displacement_sq_le {f : H → H} (hf : ContDiff ℝ 1 f)
    {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hgrowth : ∀ z, ‖f z‖ ≤ C * ‖z‖ + D)
    {μ : Measure H} [IsProbabilityMeasure μ]
    (hstation : ∀ τ, MeasurePreserving (completeFlowHomeomorph hf hC hD hgrowth τ) μ μ)
    (hspeed : Integrable (fun z => ‖f z‖ ^ 2) μ) {t : ℝ} (ht : 0 ≤ t) :
    (∫ z, ‖completeCurve hf hC hD hgrowth z t - z‖ ^ 2 ∂μ) ≤
      t ^ 2 * ∫ z, ‖f z‖ ^ 2 ∂μ := by
  let ν := volume.restrict (Ioc (0 : ℝ) t)
  let F : ℝ × H → ℝ := fun q => ‖f (completeCurve hf hC hD hgrowth q.2 q.1)‖ ^ 2
  have hcF : Continuous F := (hf.continuous.comp (completeCurve_joint_continuous hf hC hD hgrowth)).norm.pow 2
  have hFs (τ : ℝ) : Integrable (fun z => F (τ, z)) μ := by
    exact (hstation τ).integrable_comp_of_integrable hspeed
  have hFi (τ : ℝ) : (∫ z, F (τ, z) ∂μ) = ∫ z, ‖f z‖ ^ 2 ∂μ := by
    exact (hstation τ).integral_comp
      (completeFlowHomeomorph hf hC hD hgrowth τ).toMeasurableEquiv.measurableEmbedding (fun z : H => ‖f z‖ ^ 2)
  have hF : Integrable F (ν.prod μ) := by
    apply (integrable_prod_iff hcF.aestronglyMeasurable).mpr
    refine ⟨Eventually.of_forall hFs, ?_⟩
    have he : (fun τ => ∫ z, ‖F (τ,z)‖ ∂μ) = fun _ => ∫ z, ‖f z‖ ^ 2 ∂μ := by
      funext τ
      simp only [F, Real.norm_eq_abs, abs_pow, abs_norm]
      exact hFi τ
    rw [he]
    exact integrable_const _
  have hboundint : Integrable (fun z => t * ∫ τ, F (τ,z) ∂ν) μ :=
    hF.integral_prod_right.const_mul t
  calc
    _ ≤ ∫ z, t * ∫ τ, F (τ,z) ∂ν ∂μ := by
      apply integral_mono_of_nonneg (Eventually.of_forall (fun _ => sq_nonneg _)) hboundint
      exact Eventually.of_forall fun z => by
        simpa only [intervalIntegral.integral_of_le ht] using completeCurve_displacement_sq_le hf hC hD hgrowth z ht
    _ = t * ∫ τ, ∫ z, F (τ,z) ∂μ ∂ν := by
      rw [integral_const_mul]
      congr 1
      exact (integral_integral_swap hF).symm
    _ = t ^ 2 * ∫ z, ‖f z‖ ^ 2 ∂μ := by
      simp only [hFi, integral_const, smul_eq_mul]
      have hν : ν.real univ = t := by simp [ν, ht]
      rw [hν]
      ring

end AcceleratedLogConcave.Conditional.Centering
