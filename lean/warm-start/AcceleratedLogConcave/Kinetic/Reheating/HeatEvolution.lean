import AcceleratedLogConcave.Kinetic.Reheating.HeatEvolution.Channel
import AcceleratedLogConcave.External.HeatCalculus.GaussianAverageCompactTest

/-!
# Signed evolution of the actual heat channel

The weak heat equation below is proved for every signed L2 input of the actual
Gaussian transition. The time derivative is derived by Gaussian calculus and
dominated convergence, not supplied as a PDE premise. The variance is `t`, so
the generator is one half of the actual coordinate Laplacian.
-/
noncomputable section
open MeasureTheory ProbabilityTheory InnerProductSpace Set Filter
open scoped Topology RealInnerProductSpace
namespace AcceleratedLogConcave.Kinetic.Reheating
open AcceleratedLogConcave.HeatCalculus
variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι

/-- Actual Gaussian test expectation at physical variance `t`. -/
def heatAverage (φ : E → ℝ) (t : ℝ) (x : E) : ℝ :=
  ∫ g, φ (x + Real.sqrt t • g) ∂stdGaussian E

private theorem heatAverage_eq_half (φ : E → ℝ) (t : ℝ) (x : E) :
    heatAverage φ t x = heatCompactTest φ (t / 2) x := by
  simp only [heatAverage, heatCompactTest, gaussianScaleCompactTest, show (2:ℝ) * (t / 2) = t by ring]

/-- Correct physical-time heat derivative, derived from the actual Gaussian average. -/
theorem heatAverage_hasDerivAt {φ : E → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hc : HasCompactSupport φ) {t : ℝ} (ht : 0 < t) (x : E) :
    HasDerivAt (fun s => heatAverage φ s x)
      ((1/2:ℝ) * heatAverage (compactTestLaplacian φ) t x) t := by
  have h := (hasDerivAt_heatCompactTest hφ hc (show 0 < t / 2 by positivity) x).comp t
    ((hasDerivAt_id t).div_const 2)
  convert h using 1
  · funext s
    exact heatAverage_eq_half φ s x
  · simp only [heatAverage, show (2:ℝ) * (t / 2) = t by ring]
    ring

/-- Literal bounds pass through the actual Gaussian averaging operator. -/
theorem heatAverage_norm_le {φ : E → ℝ} {C : ℝ} (hC : ∀ x, ‖φ x‖ ≤ C)
    (t : ℝ) (x : E) : ‖heatAverage φ t x‖ ≤ C := by
  simpa [heatAverage] using (norm_integral_le_of_norm_le_const (μ := stdGaussian E)
    (Eventually.of_forall fun g => hC (x + Real.sqrt t • g)))

theorem heatAverage_continuous_of_bounded {φ : E → ℝ} (hφ : Continuous φ)
    {C : ℝ} (hC : ∀ x, ‖φ x‖ ≤ C) : Continuous (Function.uncurry (heatAverage φ)) :=
  (continuous_gaussianScaleCompactTest_joint_of_bounded hφ hC).comp
    ((Real.continuous_sqrt.comp continuous_fst).prodMk continuous_snd)

/-- Signed test expectations of the actual heat transition satisfy the heat
equation for every L2 input, without a differentiability premise on that input. -/
theorem signed_heat_test_hasDerivAt (μ : Measure E) [IsProbabilityMeasure μ]
    (f : Lp ℝ 2 μ) {φ : E → ℝ} (hφ : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ)
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s => ∫ x, f x * heatAverage φ s x ∂μ)
      ((1/2:ℝ) * ∫ x, f x * heatAverage (compactTestLaplacian φ) t x ∂μ) t := by
  obtain ⟨C₀,C₁,C₂,h₀,h₁,h₂,b₀,b₁,b₂⟩ := compactTest_bounds hφ hc
  let B := (Fintype.card ι : ℝ) * C₂
  have hb : ∀ x, ‖compactTestLaplacian φ x‖ ≤ B := fun x =>
    (compactTestLaplacian_norm_le φ x).trans (mul_le_mul_of_nonneg_left (b₂ x) (Nat.cast_nonneg _))
  have hA := heatAverage_continuous_of_bounded hφ.continuous b₀
  have hΔ := heatAverage_continuous_of_bounded (continuous_compactTestLaplacian hφ) hb
  have hf : Integrable f μ := (Lp.memLp f).integrable (by norm_num)
  have hmeas (s : ℝ) : AEStronglyMeasurable (fun x => f x * heatAverage φ s x) μ :=
    (Lp.aestronglyMeasurable f).mul
      (hA.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  have hi : Integrable (fun x => f x * heatAverage φ t x) μ :=
    (hf.norm.mul_const C₀).mono' (hmeas t) (Eventually.of_forall fun x => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (heatAverage_norm_le b₀ t x) (norm_nonneg _))
  have hd := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun s x => f x * heatAverage φ s x)
    (F' := fun s x => f x * ((1/2:ℝ) * heatAverage (compactTestLaplacian φ) s x))
    (bound := fun x => ‖f x‖ * (B / 2)) (s := Ioi 0) (Ioi_mem_nhds ht)
    (Eventually.of_forall hmeas) hi
    ((Lp.aestronglyMeasurable f).mul ((hΔ.comp (continuous_const.prodMk continuous_id)).const_mul
      (1/2:ℝ)).aestronglyMeasurable)
    (Eventually.of_forall fun x s _ => by
      simp only [norm_mul, Real.norm_of_nonneg (by norm_num : (0:ℝ) ≤ 1/2)]
      exact mul_le_mul_of_nonneg_left (by
        have h := heatAverage_norm_le hb s x
        linarith) (norm_nonneg _))
    (hf.norm.mul_const (B / 2))
    (Eventually.of_forall fun x s hs =>
      (heatAverage_hasDerivAt hφ hc hs x).const_mul (f x))).2
  convert hd using 1
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with x
  ring

/-- The weak heat equation is a statement about the actual signed relative
density operator and moving reference law, not an unrelated scalar evolution. -/
theorem scalarHeatDensity_weak_heat (μ : Measure E) [IsProbabilityMeasure μ]
    (f : Lp ℝ 2 μ) {φ : E → ℝ} (hφ : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ)
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s => ∫ x, scalarHeatDensity μ s f x * φ x ∂heatedLaw μ s)
      ((1/2:ℝ) * ∫ x, scalarHeatDensity μ t f x * compactTestLaplacian φ x ∂heatedLaw μ t) t := by
  obtain ⟨C₀,C₁,C₂,h₀,h₁,h₂,b₀,b₁,b₂⟩ := compactTest_bounds hφ hc
  have hLap : MemLp (compactTestLaplacian φ) 2 (heatedLaw μ t) :=
    MemLp.of_bound (continuous_compactTestLaplacian hφ).aestronglyMeasurable
      ((Fintype.card ι : ℝ) * C₂) (Eventually.of_forall fun x =>
        (compactTestLaplacian_norm_le φ x).trans
          (mul_le_mul_of_nonneg_left (b₂ x) (Nat.cast_nonneg _)))
  have he (s : ℝ) := scalarHeatDensity_integral_test μ s f φ
    (compactTest_memLp (heatedLaw μ s) φ hφ.continuous hc)
  have hΔ := scalarHeatDensity_integral_test μ t f (compactTestLaplacian φ) hLap
  change ∀ s, _ = ∫ x, f x * heatAverage φ s x ∂μ at he
  change _ = ∫ x, f x * heatAverage (compactTestLaplacian φ) t x ∂μ at hΔ
  simp_rw [he, hΔ]
  exact signed_heat_test_hasDerivAt μ f hφ hc ht

end AcceleratedLogConcave.Kinetic.Reheating
