import AcceleratedLogConcave.Kinetic.Reheating.HeatEvolution.Bounds

/-! Uniform bounds for the actual smoothed numerator and its derivatives.
Compact input support supplies relative density bounds before averaging, so
these estimates remain uniform at the zero-variance endpoint. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace
open scoped RealInnerProductSpace
namespace AcceleratedLogConcave.Kinetic.Reheating
open Analysis.Poisson AcceleratedLogConcave.HeatCalculus
variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι

theorem compactTestLaplacian_compactSupport {h : E → ℝ} (hc : HasCompactSupport h) :
    HasCompactSupport (compactTestLaplacian h) := by
  classical
  exact ((hc.fderiv ℝ).fderiv ℝ).comp_left
    (g := fun H : E →L[ℝ] (E →L[ℝ] ℝ) =>
      ∑ i, H (EuclideanSpace.basisFun ι ℝ i) (EuclideanSpace.basisFun ι ℝ i)) (by simp)

/-- Numerator, first derivative and actual Laplacian are uniformly bounded
relative to the moving reference density, including zero elapsed time. -/
theorem compactHeatNumerator_derivative_bounds {a b : ℝ}
    (F : ReferencePoissonFamily E a b) {f : E → ℝ}
    (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f)
    (hheat : ∀ t ∈ Icc a b, F.law t = heatedLaw (F.law a) (t-a)) :
    ∃ C₀ C₁ C₂ : ℝ, 0 ≤ C₀ ∧ 0 ≤ C₁ ∧ 0 ≤ C₂ ∧
      ∀ t ∈ Icc a b, ∀ x,
        ‖compactHeatNumerator F f t x‖ ≤ C₀ * F.density t x ∧
        ‖fderiv ℝ (compactHeatNumerator F f t) x‖ ≤ C₁ * F.density t x ∧
        ‖compactTestLaplacian (compactHeatNumerator F f t) x‖ ≤ C₂ * F.density t x := by
  have ha : a ∈ Icc a b := ⟨le_rfl,F.ordered⟩
  let h : E → ℝ := fun x => f x * F.density a x
  have h2 : ContDiff ℝ 2 h := hf.mul (reference_density_C2 F a ha)
  have hh : HasCompactSupport h := hc.mul_right
  have hp := (reference_density_C2 F a ha).continuous
  obtain ⟨B,hB⟩ := reference_density_bounded F a ha
  obtain ⟨C₀,h₀,b₀⟩ := compact_norm_le_density h2.continuous hh hp (reference_density_pos F a ha)
  obtain ⟨C₁,h₁,b₁⟩ := compact_norm_le_density (continuous_compactTest_fderiv h2)
    (hh.fderiv ℝ) hp (reference_density_pos F a ha)
  obtain ⟨C₂,h₂,b₂⟩ := compact_norm_le_density (continuous_compactTestLaplacian h2)
    (compactTestLaplacian_compactSupport hh) hp (reference_density_pos F a ha)
  refine ⟨C₀,C₁,C₂,h₀,h₁,h₂,fun t ht x => ?_⟩
  have e := reference_density_eq_heatAverage F t ht (hheat t ht)
  have n₀ := gaussianAverage_norm_le_density h2.continuous hh hp hB b₀ (t-a) x
  have n₁ := gaussianAverage_norm_le_density (continuous_compactTest_fderiv h2)
    (hh.fderiv ℝ) hp hB b₁ (t-a) x
  have n₂ := gaussianAverage_norm_le_density (continuous_compactTestLaplacian h2)
    (compactTestLaplacian_compactSupport hh) hp hB b₂ (t-a) x
  rw [← e] at n₀ n₁ n₂
  refine ⟨n₀, ?_, ?_⟩
  · change ‖fderiv ℝ (heatAverage h (t-a)) x‖ ≤ _
    rw [heatAverage_fderiv h2 hh]
    exact n₁
  · change ‖compactTestLaplacian (heatAverage h (t-a)) x‖ ≤ _
    rw [heatAverage_laplacian h2 hh]
    exact n₂

/-- The gradient of the quotient is the normalized numerator derivative plus
its score correction, derived from differentiating the true numerator identity. -/
theorem compactHeatQuotient_fderiv {a b : ℝ} (F : ReferencePoissonFamily E a b)
    {f : E → ℝ} (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f)
    (t : ℝ) (ht : t ∈ Icc a b) (x : E) :
    fderiv ℝ (compactHeatQuotient F f t) x =
      (F.density t x)⁻¹ • fderiv ℝ (compactHeatNumerator F f t) x +
        compactHeatQuotient F f t x • fderiv ℝ (F.potential t) x := by
  have hp := reference_density_hasFDerivAt F t ht x
  have hq := compactTest_hasFDerivAt (compactHeatQuotient_C2 F hf hc t ht) x
  have he : compactHeatNumerator F f t =
      fun y => F.density t y * compactHeatQuotient F f t y := by
    exact compactHeatNumerator_eq_density_mul F f t ht
  have hd := (hp.mul hq).fderiv
  change fderiv ℝ (fun y => F.density t y * compactHeatQuotient F f t y) x = _ at hd
  rw [← he] at hd
  ext v
  have hdv := congrArg (fun L : E →L[ℝ] ℝ => L v) hd
  simp only [add_apply, smul_apply, smul_eq_mul] at hdv ⊢
  have hp0 := (reference_density_pos F t ht x).ne'
  field_simp [hp0]
  nlinarith

end AcceleratedLogConcave.Kinetic.Reheating
