import AcceleratedLogConcave.Numerics.SmoothConditionalReference
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.Calculus.FDeriv.CompCLM

/-! Isometric coordinate changes used by the conditional-only adapter. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped ContDiff Topology RealInnerProductSpace ENNReal
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace AcceleratedLogConcave.Numerics.ConditionalSmoothing
variable {E V : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace V] [BorelSpace V]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ V] in
theorem hessian_comp_isometry (e : V ≃ₗᵢ[ℝ] E) {F : E → ℝ}
    (hF : ContDiff ℝ 2 F) (z v w : V) :
    fderiv ℝ (fderiv ℝ (fun y => F (e y))) z v w =
      fderiv ℝ (fderiv ℝ F) (e z) (e v) (e w) := by
  have hd := hF.differentiable (by norm_num)
  have hd' := (hF.fderiv_right (by norm_num : (1:ℕ∞ω)+1 ≤ 2)).differentiable
    (by norm_num)
  have he : fderiv ℝ (fun y => F (e y)) =
      fun y => (fderiv ℝ F (e y)).comp e.toContinuousLinearEquiv.toContinuousLinearMap := by
    funext y
    exact ((hd (e y)).hasFDerivAt.comp y e.toContinuousLinearEquiv.hasFDerivAt).fderiv
  have hh := ((hd' (e z)).hasFDerivAt.comp z e.toContinuousLinearEquiv.hasFDerivAt).clm_comp
    (hasFDerivAt_const e.toContinuousLinearEquiv.toContinuousLinearMap z)
  dsimp only [Function.comp_def] at hh
  rw [he, hh.fderiv]
  simp

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace V] [BorelSpace V] in
theorem gradient_comp_isometry (e : V ≃ₗᵢ[ℝ] E) {F : E → ℝ}
    (hF : Differentiable ℝ F) (z : V) :
    gradient (fun y => F (e y)) z = e.symm (gradient F (e z)) := by
  have hh := ((hF (e z)).hasGradientAt.hasFDerivAt.comp z
    e.toContinuousLinearEquiv.hasFDerivAt)
  have he : (InnerProductSpace.toDual ℝ E (gradient F (e z))).comp
      e.toContinuousLinearEquiv.toContinuousLinearMap =
      InnerProductSpace.toDual ℝ V (e.symm (gradient F (e z))) := by
    ext v
    simp only [ContinuousLinearMap.comp_apply, InnerProductSpace.toDual_apply_apply]
    exact (e.symm.inner_map_eq_flip (gradient F (e z)) v).symm
  rw [he] at hh
  exact (hasGradientAt_iff_hasFDerivAt.mpr hh).gradient

theorem heatPosterior_map_isometry (e : E ≃ₗᵢ[ℝ] V) {F : E → ℝ}
    (hF : Measurable F) (t : ℝ) (y : E) :
    (Gibbs.heatPosterior F t y).map e =
      Gibbs.heatPosterior (fun z => F (e.symm z)) t (e y) := by
  let w : V → ℝ≥0∞ := fun z => ENNReal.ofReal
    (Real.exp (-(F (e.symm z)+‖z-e y‖^2/(2*t))))
  have hw : Measurable w := by fun_prop
  have he (z : E) : w (e z) =
      ENNReal.ofReal (Real.exp (-(F z+‖z-y‖^2/(2*t)))) := by
    simp only [w, e.symm_apply_apply, ← map_sub, e.norm_map]
  have hh := Gibbs.map_normalized_withDensity_comp (volume : Measure E)
    (volume : Measure V) e.continuous.measurable hw (c := 1) (by norm_num) (by norm_num)
    (by simpa only [one_smul] using e.measurePreserving.map_eq)
  simpa only [he, w, Gibbs.heatPosterior] using hh

theorem conditionalMean_map_isometry (e : E ≃ₗᵢ[ℝ] V) {F : E → ℝ}
    (hF : ContDiff ℝ 2 F) (x : E) (r t : ℝ) (y : E) :
    Conditional.conditionalMean (fun z => F (e.symm z)) (e x) r t (e y) =
      e (Conditional.conditionalMean F x r t y) := by
  have hl : Conditional.conditionalLaw (fun z => F (e.symm z)) (e x) r t (e y) =
      (Conditional.conditionalLaw F x r t y).map e := by
    have hh := heatPosterior_map_isometry e
      (F := Conditional.primitivePotential F x r)
      (hF.continuous.measurable.comp (by fun_prop))
      (Conditional.conditionalVariance t) (t • y)
    unfold Conditional.primitivePotential at hh
    unfold Conditional.conditionalLaw Conditional.primitivePotential
    simpa only [map_smul, map_add, e.symm_apply_apply] using hh.symm
  have hc : Continuous (fun z : V =>
      gradient (fun a => F (e.symm a)) (e x+r • z)) := by
    have h : Continuous (gradient (fun a => F (e.symm a))) := by
      unfold gradient
      exact (InnerProductSpace.toDual ℝ V).symm.continuous.comp
        ((hF.comp e.symm.toContinuousLinearEquiv.contDiff).continuous_fderiv (by norm_num))
    exact h.comp (continuous_const.add (continuous_const.smul continuous_id))
  unfold Conditional.conditionalMean Conditional.primitiveObservable
  rw [hl, integral_map e.continuous.measurable.aemeasurable hc.aestronglyMeasurable]
  simp only [gradient_comp_isometry e.symm
    (hF.differentiable (by norm_num)), LinearIsometryEquiv.symm_symm,
    map_add, map_smul, e.symm_apply_apply]
  exact e.toLinearIsometry.integral_comp_comm _

end AcceleratedLogConcave.Numerics.ConditionalSmoothing
