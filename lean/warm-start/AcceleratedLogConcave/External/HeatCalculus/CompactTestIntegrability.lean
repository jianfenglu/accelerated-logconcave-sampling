import AcceleratedLogConcave.External.HeatCalculus.CompactTest

/-! # Integrability of actual compact-test signal and noise terms

The auxiliary finite-measure adapters are applied below to the literal fixed
prior/Gaussian product. All signal moments come from the actual prior L² premise.
-/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace AcceleratedLogConcave.HeatCalculus
variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

 theorem integrable_compactTest_comp [IsFiniteMeasure μ] {f : E → ℝ}
    (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f) {z : Ω → E} (hz : Measurable z) :
    Integrable (fun w => f (z w)) μ := by
  obtain ⟨C₀,C₁,C₂,h₀,h₁,h₂,b₀,b₁,b₂⟩ := compactTest_bounds hf hc
  apply (integrable_const C₀).mono' (hf.continuous.measurable.comp hz).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun w => b₀ (z w)

 theorem integrable_compactTestLaplacian_comp [IsFiniteMeasure μ] {f : E → ℝ}
    (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f) {z : Ω → E} (hz : Measurable z) :
    Integrable (fun w => compactTestLaplacian f (z w)) μ := by
  obtain ⟨C₀,C₁,C₂,h₀,h₁,h₂,b₀,b₁,b₂⟩ := compactTest_bounds hf hc
  apply (integrable_const ((Fintype.card ι : ℝ)*C₂)).mono'
    ((continuous_compactTestLaplacian hf).measurable.comp hz).aestronglyMeasurable
  filter_upwards [] with w
  exact (compactTestLaplacian_norm_le f (z w)).trans
    (mul_le_mul_of_nonneg_left (b₂ (z w)) (by positivity))

 theorem integrable_compactTest_fderiv_apply {f : E → ℝ}
    (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f)
    {z g : Ω → E} (hz : Measurable z) (hg : Integrable g μ) :
    Integrable (fun w => fderiv ℝ f (z w) (g w)) μ := by
  obtain ⟨C₀,C₁,C₂,h₀,h₁,h₂,b₀,b₁,b₂⟩ := compactTest_bounds hf hc
  have hm : AEStronglyMeasurable (fun w => fderiv ℝ f (z w) (g w)) μ := by
    have he : Continuous (fun p : (E →L[ℝ] ℝ) × E => p.1 p.2) := by fun_prop
    exact he.comp_aestronglyMeasurable
      (((continuous_compactTest_fderiv hf).measurable.comp hz).aestronglyMeasurable.prodMk
        hg.aestronglyMeasurable)
  apply (hg.norm.const_mul C₁).mono' hm
  filter_upwards [] with w
  exact ((fderiv ℝ f (z w)).le_opNorm (g w)).trans
    (mul_le_mul_of_nonneg_right (b₁ (z w)) (norm_nonneg _))

end AcceleratedLogConcave.HeatCalculus
