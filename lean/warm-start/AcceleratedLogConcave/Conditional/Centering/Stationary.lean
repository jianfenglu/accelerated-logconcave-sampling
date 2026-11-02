import AcceleratedLogConcave.Conditional.Centering.LocalFlow
import AcceleratedLogConcave.Conditional.Centering.Liouville
import AcceleratedLogConcave.Conditional.Centering.DensityTransport
import AcceleratedLogConcave.Analysis.Poisson.ReferenceTransportFlow

/-! Stationarity of a complete C1 field with linear growth and zero weighted
divergence. The Jacobian argument is localized along the actual trajectories;
the auxiliary compact cutoff is not assumed to preserve the density. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric Filter MeasureTheory MeasureTheory.Measure
open scoped Topology NNReal

namespace AcceleratedLogConcave.Conditional.Centering
open OAI.LogConcaveSampling.GlobalODE
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [FiniteDimensional ℝ H] [MeasurableSpace H] [BorelSpace H]

omit [MeasurableSpace H] [BorelSpace H] in
/-- The actual complete flow preserves its density-weighted Jacobian. -/
theorem completeCurve_density_det {f : H → H} (hf : ContDiff ℝ 1 f)
    {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hgrowth : ∀ z, ‖f z‖ ≤ C * ‖z‖ + D)
    {p : H → ℝ} (hp : ContDiff ℝ 1 p)
    (hdiv : ∀ z, fderiv ℝ p z (f z) + p z * LinearMap.trace ℝ H (fderiv ℝ f z).toLinearMap = 0)
    {t : ℝ} (ht : 0 ≤ t) (x : H) :
    p (completeCurve hf hC hD hgrowth x t) *
      (fderiv ℝ (fun y => completeCurve hf hC hD hgrowth y t) x).det = p x := by
  let T := t+1
  have hT : 0 < T := by dsimp [T]; linarith
  obtain ⟨g, hg, K, hK, heq, hagree, _⟩ := exists_local_cutoff_flow hf hC hD hgrowth x hT
  let hc : Continuous (Function.uncurry (fun (_ : ℝ) z => g z)) :=
    hK.continuous.comp continuous_snd
  let hL : ∀ τ ∈ Icc (0 : ℝ) T, LipschitzWith K (fun z => g z) := fun _ _ => hK
  let Dg : ℝ → H → H →L[ℝ] H := fun _ z => fderiv ℝ g z
  have hDg : Continuous (Function.uncurry Dg) :=
    (hg.continuous_fderiv (by norm_num)).comp continuous_snd
  have hdg (τ : ℝ) (z : H) : HasFDerivAt g (Dg τ z) z :=
    (hg.differentiable_one z).hasFDerivAt
  let s : Icc (0 : ℝ) T := ⟨0, le_rfl, hT.le⟩
  let X := flow hL hc s x
  let J := flowLinearization hT.le hc hL hDg hdg x
  have hXeq (y : H) (hy : y ∈ ball x 1) (τ : ℝ) (hτ : τ ∈ Icc (0 : ℝ) T) :
      completeCurve hf hC hD hgrowth y τ = flow hL hc s y τ := by
    rw [heq y hy τ ⟨by linarith [hτ.1], hτ.2⟩]
    symm
    exact flow_eq_on_subinterval (f := fun (_ : ℝ) z => g z) (hK.continuous.comp continuous_snd) (fun _ _ => hK)
      (fun u hu => ⟨by linarith [hu.1], hu.2⟩ : Icc (0 : ℝ) T ⊆ Icc (-T) T)
      (⟨0, le_rfl, hT.le⟩ : Icc (0 : ℝ) T) ⟨τ, hτ⟩ y
  have hxball : x ∈ ball x 1 := mem_ball_self (by norm_num)
  have hXoriginal (τ : ℝ) (hτ : τ ∈ Icc (0 : ℝ) T) :
      g (X τ) = f (X τ) ∧ fderiv ℝ g (X τ) = fderiv ℝ f (X τ) := by
    have hh := hagree x hxball τ ⟨by linarith [hτ.1], hτ.2⟩
    rw [hXeq x hxball τ hτ] at hh
    exact hh
  have hcons : p (X t) * (J t).det = p (X 0) * (J 0).det := by
    apply density_det_eq_of_weighted_divergence ht
    · exact (hp.continuous.comp (flow_continuous hL hc s x)).mul
        ((ContinuousLinearMap.continuous_det).comp
          (fundamental_continuous s
            (flowSpatialCoefficient_continuous hT.le hc hL hDg x)
            (flowSpatialCoefficient_bound hT.le hc hL hdg x))) |>.continuousOn
    · intro τ hτ
      have hτT : τ ∈ Icc (0 : ℝ) T := ⟨hτ.1.le, by dsimp [T]; linarith [hτ.2]⟩
      refine ⟨g (X τ), Dg τ (X τ), fderiv ℝ p (X τ), ?_, ?_,
        (hp.differentiable_one _).hasFDerivAt, ?_⟩
      · exact (flow_deriv hL hc s x τ hτT).hasDerivAt
          (Icc_mem_nhds hτ.1 (by dsimp [T]; linarith [hτ.2]))
      · exact (fundamental_deriv s
          (flowSpatialCoefficient_continuous hT.le hc hL hDg x)
          (flowSpatialCoefficient_bound hT.le hc hL hdg x) τ hτT).hasDerivAt
          (Icc_mem_nhds hτ.1 (by dsimp [T]; linarith [hτ.2]))
      · dsimp [Dg]
        rw [(hXoriginal τ hτT).1, (hXoriginal τ hτT).2]
        exact hdiv (X τ)
  have hJ0 : J 0 = ContinuousLinearMap.id ℝ H :=
    fundamental_initial s _ _
  have hX0 : X 0 = x := flow_initial hL hc s x
  simp only [hJ0, hX0, ContinuousLinearMap.det, ContinuousLinearMap.coe_id, LinearMap.det_id, mul_one] at hcons
  have htime : t ∈ Icc (0 : ℝ) T := ⟨ht, by dsimp [T]; linarith⟩
  have hloc : (fun y => completeCurve hf hC hD hgrowth y t) =ᶠ[𝓝 x]
      (fun y => flow hL hc s y t) := by
    filter_upwards [ball_mem_nhds x (by norm_num : (0 : ℝ) < 1)] with y hy
    exact hXeq y hy t htime
  have hderiv := (flow_hasFDerivAt_left hT.le hc hL hDg hdg x ⟨t, htime⟩).congr_of_eventuallyEq hloc
  rw [hderiv.fderiv, hXeq x hxball t htime]
  exact hcons

/-- A complete C1 field of linear growth preserves a density when its actual
weighted divergence vanishes. -/
theorem completeFlowHomeomorph_measurePreserving_of_nonneg {f : H → H} (hf : ContDiff ℝ 1 f)
    {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hgrowth : ∀ z, ‖f z‖ ≤ C * ‖z‖ + D)
    (μ : Measure H) [IsAddHaarMeasure μ] {p : H → ℝ} (hp : ContDiff ℝ 1 p)
    (hpi : Integrable p μ) (hp0 : ∀ z, 0 ≤ p z)
    (hdiv : ∀ z, fderiv ℝ p z (f z) + p z * LinearMap.trace ℝ H (fderiv ℝ f z).toLinearMap = 0)
    {t : ℝ} (ht : 0 ≤ t) :
    MeasurePreserving (completeFlowHomeomorph hf hC hD hgrowth t)
      (μ.withDensity (fun z => ENNReal.ofReal (p z)))
      (μ.withDensity (fun z => ENNReal.ofReal (p z))) := by
  apply measurePreserving_of_density_det μ
    (completeFlowHomeomorph hf hC hD hgrowth t).toMeasurableEquiv
    (fun x => fderiv ℝ (fun y => completeCurve hf hC hD hgrowth y t) x) p hpi hp0
  · intro x
    exact ((completeCurve_contDiff_one hf hC hD hgrowth t).differentiable_one x).hasFDerivAt
  · intro x
    change |(fderiv ℝ (fun y => completeCurve hf hC hD hgrowth y t) x).det| *
      p (completeCurve hf hC hD hgrowth x t) = p x
    have hh := congrArg abs (completeCurve_density_det hf hC hD hgrowth hp hdiv ht x)
    simpa only [abs_mul, abs_of_nonneg (hp0 _), mul_comm] using hh

/-- Weighted stationarity holds in both time directions. -/
theorem completeFlowHomeomorph_measurePreserving {f : H → H} (hf : ContDiff ℝ 1 f)
    {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hgrowth : ∀ z, ‖f z‖ ≤ C * ‖z‖ + D)
    (μ : Measure H) [IsAddHaarMeasure μ] {p : H → ℝ} (hp : ContDiff ℝ 1 p)
    (hpi : Integrable p μ) (hp0 : ∀ z, 0 ≤ p z)
    (hdiv : ∀ z, fderiv ℝ p z (f z) + p z * LinearMap.trace ℝ H (fderiv ℝ f z).toLinearMap = 0)
    (t : ℝ) :
    MeasurePreserving (completeFlowHomeomorph hf hC hD hgrowth t)
      (μ.withDensity (fun z => ENNReal.ofReal (p z)))
      (μ.withDensity (fun z => ENNReal.ofReal (p z))) := by
  by_cases ht : 0 ≤ t
  · exact completeFlowHomeomorph_measurePreserving_of_nonneg hf hC hD hgrowth μ hp hpi hp0 hdiv ht
  · have hpos : MeasurePreserving (completeFlowHomeomorph hf hC hD hgrowth (-t)).toMeasurableEquiv
        (μ.withDensity (fun z => ENNReal.ofReal (p z)))
        (μ.withDensity (fun z => ENNReal.ofReal (p z))) :=
      completeFlowHomeomorph_measurePreserving_of_nonneg hf hC hD hgrowth μ hp hpi hp0 hdiv (by linarith)
    convert! hpos.symm using 1
    ext x
    change completeCurve hf hC hD hgrowth x t = completeCurve hf hC hD hgrowth x (- -t)
    rw [neg_neg]

end AcceleratedLogConcave.Conditional.Centering
