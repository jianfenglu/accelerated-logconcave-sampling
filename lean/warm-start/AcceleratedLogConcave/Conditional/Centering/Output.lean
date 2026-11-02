import AcceleratedLogConcave.Conditional.Centering.Field
import Mathlib.Probability.Distributions.Gaussian.Multivariate

/-! Exact integrated output identities for solutions of the centering ODE. -/
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped Topology

namespace AcceleratedLogConcave.Conditional.Centering
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]

/-- Integration of the actual momentum equation, on an arbitrary time interval. -/
theorem integrated_output {Kt : E → E →L[ℝ] E} {M : E → E} {u : E} {s : ℝ}
    (hs : s ≠ 0) {Z : ℝ → Phase E} {a b : ℝ}
    (hZ : ∀ t ∈ uIcc a b, HasDerivAt Z (velocity Kt M u s (Z t)) t)
    (hM : Continuous M) (hc : Continuous Z) :
    s • (Z a).snd + ∫ t in a..b, M (Z t).fst =
      (b - a) • u + s • (Z b).snd := by
  have hd (t : ℝ) (ht : t ∈ uIcc a b) :
      HasDerivAt (fun v => s • (Z v).snd) (M (Z t).fst - u) t := by
    have hh := HasDerivAt.const_smul s ((WithLp.sndL 2 ℝ E E).hasFDerivAt.comp_hasDerivAt
      t (hZ t ht))
    convert! hh using 1
    simp [velocity_snd, smul_smul, hs]
  have hmi : IntervalIntegrable (fun t => M (Z t).fst) volume a b := by
    exact (hM.comp ((WithLp.prod_continuous_ofLp 2 E E).comp hc).fst).intervalIntegrable a b
  have hi : IntervalIntegrable (fun t => M (Z t).fst - u) volume a b :=
    ((hM.comp (((WithLp.prod_continuous_ofLp 2 E E).comp hc).fst)).sub continuous_const).intervalIntegrable a b
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi
  rw [intervalIntegral.integral_sub
    hmi
    (continuous_const.intervalIntegrable a b), intervalIntegral.integral_const] at h
  rw [sub_eq_iff_eq_add] at h
  rw [h]
  abel

/-- The source's unit-time identity retains the original supplied momentum. -/
theorem integrated_output_unit {Kt : E → E →L[ℝ] E} {M : E → E} {u : E} {s : ℝ}
    (hs : s ≠ 0) {Z : ℝ → Phase E}
    (hZ : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt Z (velocity Kt M u s (Z t)) t)
    (hM : Continuous M) (hc : Continuous Z) :
    s • (Z 0).snd + ∫ t in (0 : ℝ)..1, M (Z t).fst = u + s • (Z 1).snd := by
  simpa only [sub_zero, one_smul] using integrated_output hs
    (a := 0) (b := 1) (by simpa only [uIcc_of_le zero_le_one] using hZ) hM hc

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [CompleteSpace E] in
/-- If an endpoint has the invariant product law, its momentum has the standard
Gaussian law. This lemma makes the stationarity input completely explicit. -/
theorem endpoint_momentum_law {ξ : Measure E} [IsProbabilityMeasure ξ]
    {T : Phase E → Phase E}
    (hT : MeasurePreserving T
      ((ξ.prod (stdGaussian E)).map (WithLp.toLp 2))
      ((ξ.prod (stdGaussian E)).map (WithLp.toLp 2))) :
    (((ξ.prod (stdGaussian E)).map (WithLp.toLp 2)).map (fun z => (T z).snd)) =
      stdGaussian E := by
  have hsnd : Measurable (fun z : Phase E => z.snd) := (WithLp.prod_continuous_ofLp 2 E E).snd.measurable
  change Measure.map ((fun z : Phase E => z.snd) ∘ T) _ = _
  rw [← Measure.map_map hsnd hT.measurable, hT.map_eq,
    Measure.map_map hsnd (WithLp.prod_continuous_toLp 2 E E).measurable]
  change Measure.map Prod.snd (ξ.prod (stdGaussian E)) = _
  simp only [Measure.map_snd_prod, measure_univ, one_smul]

omit [CompleteSpace E] in
/-- A shifted and scaled endpoint momentum has exactly the shifted Gaussian law. -/
theorem endpoint_shiftedGaussian_law {ξ : Measure E} [IsProbabilityMeasure ξ]
    {T : Phase E → Phase E}
    (hT : MeasurePreserving T
      ((ξ.prod (stdGaussian E)).map (WithLp.toLp 2))
      ((ξ.prod (stdGaussian E)).map (WithLp.toLp 2))) (u : E) (s : ℝ) :
    (((ξ.prod (stdGaussian E)).map (WithLp.toLp 2)).map
      (fun z => u + s • (T z).snd)) = (stdGaussian E).map (fun g => u + s • g) := by
  conv_rhs => rw [← endpoint_momentum_law hT]
  convert!
    (Measure.map_map (by fun_prop : Measurable (fun g : E => u + s • g))
      ((WithLp.prod_continuous_ofLp 2 E E).snd.measurable.comp hT.measurable)).symm using 1

end AcceleratedLogConcave.Conditional.Centering
