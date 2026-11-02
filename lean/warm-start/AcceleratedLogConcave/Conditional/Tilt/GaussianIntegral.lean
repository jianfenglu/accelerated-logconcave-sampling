import AcceleratedLogConcave.Gibbs.HeatHessian
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps

/-!
# All-order differentiation of Gaussian weighted integrals

Only the Gaussian parameter is differentiated. The integrated base potential
and observable need continuity and Gaussian weighted moments, not higher
regularity. Every derivative exchange uses a common integrable Gaussian bound.
-/

noncomputable section

namespace AcceleratedLogConcave.Conditional.Tilt

open MeasureTheory Set Filter
open scoped RealInnerProductSpace ContDiff Topology

universe u v

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Natural Gaussian parameters: positive quadratic precision and linear tilt. -/
def gaussianDomain : Set (ℝ × E) := {p | 0 < p.1}

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem isOpen_gaussianDomain : IsOpen (gaussianDomain (E := E)) :=
  isOpen_lt continuous_const continuous_fst

/-- The linear statistic whose exponential supplies the Gaussian weight. -/
def gaussianStatistic (z : E) : (ℝ × E) →L[ℝ] ℝ :=
  (-‖z‖ ^ 2) • ContinuousLinearMap.fst ℝ ℝ E +
    (innerSL ℝ z).comp (ContinuousLinearMap.snd ℝ ℝ E)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
@[simp] theorem gaussianStatistic_apply (z : E) (p : ℝ × E) :
    gaussianStatistic z p = -p.1 * ‖z‖ ^ 2 + inner ℝ z p.2 := by
  simp [gaussianStatistic]
  ring

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Operator norm growth of the actual Gaussian statistic. -/
theorem norm_gaussianStatistic_le (z : E) :
    ‖gaussianStatistic z‖ ≤ ‖z‖ ^ 2 + ‖z‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro p
  rw [gaussianStatistic_apply]
  calc
    _ ≤ ‖-p.1 * ‖z‖ ^ 2‖ + ‖inner ℝ z p.2‖ := norm_add_le _ _
    _ ≤ ‖p.1‖ * ‖z‖ ^ 2 + ‖z‖ * ‖p.2‖ := by
      rw [norm_mul, norm_neg, Real.norm_eq_abs (‖z‖ ^ 2),
        abs_of_nonneg (sq_nonneg _)]
      gcongr
      exact norm_inner_le_norm _ _
    _ ≤ ‖p‖ * ‖z‖ ^ 2 + ‖z‖ * ‖p‖ := by
      gcongr
      · exact norm_fst_le p
      · exact norm_snd_le p
    _ = _ := by ring

/-- Gaussian weighted absolute moments of a fixed observable. -/
def HasGaussianMoments {G : Type v} [NormedAddCommGroup G]
    (B : E → ℝ) (g : E → G) : Prop :=
  ∀ (a : ℝ), 0 < a → ∀ n : ℕ,
    Integrable (fun z ↦ ‖z‖ ^ n * Real.exp (-(B z + a * ‖z‖ ^ 2)) * ‖g z‖)

/-- Raw Gaussian weighted integral in natural parameters. -/
def gaussianIntegral {G : Type v} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (B : E → ℝ) (g : E → G) (p : ℝ × E) : G :=
  ∫ z, Real.exp (-B z + gaussianStatistic z p) • g z

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The local envelope absorbs bounded linear tilts by sacrificing half of
one positive quadratic coefficient. -/
theorem gaussian_weight_le (B : E → ℝ) (p q : ℝ × E) (hp : 0 < p.1)
    (hq : ‖q - p‖ < min (p.1 / 2) 1) (z : E) :
    Real.exp (-B z + gaussianStatistic z q) ≤
      Real.exp ((‖p.2‖ + 1) ^ 2 / p.1) *
        Real.exp (-(B z + (p.1 / 4) * ‖z‖ ^ 2)) := by
  have hfst : |q.1 - p.1| < p.1 / 2 :=
    (le_trans (by exact le_max_left _ _) (le_refl ‖q - p‖)).trans_lt
      (hq.trans_le (min_le_left _ _))
  have hsnd : ‖q.2 - p.2‖ < 1 :=
    (le_max_right |q.1 - p.1| ‖q.2 - p.2‖).trans_lt
      (hq.trans_le (min_le_right _ _))
  have hqa : p.1 / 2 ≤ q.1 := by
    have := (abs_lt.mp hfst).1
    linarith
  have hqb : ‖q.2‖ ≤ ‖p.2‖ + 1 := by
    linarith [norm_le_norm_sub_add q.2 p.2]
  have hi : inner ℝ z q.2 ≤ ‖z‖ * (‖p.2‖ + 1) :=
    (real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left hqb (norm_nonneg _))
  have hy : ‖z‖ * (‖p.2‖ + 1) ≤
      (p.1 / 4) * ‖z‖ ^ 2 + (‖p.2‖ + 1) ^ 2 / p.1 := by
    apply (mul_le_mul_iff_of_pos_left hp).mp
    have hs := sq_nonneg (p.1 * ‖z‖ / 2 - (‖p.2‖ + 1))
    field_simp
    nlinarith
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  simp only [gaussianStatistic_apply]
  have hcoef := mul_le_mul_of_nonneg_right hqa (sq_nonneg ‖z‖)
  linarith

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem continuous_gaussianStatistic : Continuous (gaussianStatistic (E := E)) := by
  unfold gaussianStatistic
  fun_prop

section Observable

variable {G : Type v} [NormedAddCommGroup G] [NormedSpace ℝ G]
  {B : E → ℝ} {g : E → G}

/-- Multiplication by the Gaussian statistic preserves all weighted moments. -/
theorem HasGaussianMoments.statistic (hg : HasGaussianMoments B g)
    (hB : Continuous B) (hc : Continuous g) :
    HasGaussianMoments B (fun z ↦ (gaussianStatistic z).smulRight (g z)) := by
  have hstat : Continuous (fun z ↦ (gaussianStatistic z).smulRight (g z)) :=
    isBoundedBilinearMap_smulRight.continuous.comp
      (continuous_gaussianStatistic.prodMk hc)
  intro a ha n
  refine ((hg a ha (n + 2)).add (hg a ha (n + 1))).mono' ?_ ?_
  · exact (((continuous_norm.pow n).mul
      ((hB.add ((continuous_norm.pow 2).const_mul a )).neg.rexp)).mul
      (@Continuous.norm E ((ℝ × E) →L[ℝ] G) inferInstance inferInstance _ hstat)).aestronglyMeasurable
  · filter_upwards [] with z
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity),
      ContinuousLinearMap.norm_smulRight_apply]
    have hs := mul_le_mul_of_nonneg_right (norm_gaussianStatistic_le z) (norm_nonneg (g z))
    have ht := mul_le_mul_of_nonneg_left hs
      (show 0 ≤ ‖z‖ ^ n * Real.exp (-(B z + a * ‖z‖ ^ 2)) by positivity)
    convert ht using 1
    simp only [Pi.add_apply, pow_add, pow_one]
    ring

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem norm_gaussian_integrand_le (p q : ℝ × E) (hp : 0 < p.1)
    (hq : ‖q - p‖ < min (p.1 / 2) 1) (z : E) :
    ‖Real.exp (-B z + gaussianStatistic z q) • g z‖ ≤
      Real.exp ((‖p.2‖ + 1) ^ 2 / p.1) *
        (Real.exp (-(B z + (p.1 / 4) * ‖z‖ ^ 2)) * ‖g z‖) := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have h := mul_le_mul_of_nonneg_right (gaussian_weight_le B p q hp hq z)
    (norm_nonneg (g z))
  simpa only [mul_assoc] using h

omit [NormedSpace ℝ G] in
theorem integrable_gaussian_envelope (hg : HasGaussianMoments B g)
    (p : ℝ × E) (hp : 0 < p.1) :
    Integrable (fun z ↦ Real.exp ((‖p.2‖ + 1) ^ 2 / p.1) *
      (Real.exp (-(B z + (p.1 / 4) * ‖z‖ ^ 2)) * ‖g z‖)) := by
  simpa only [pow_zero, one_mul] using
    (hg (p.1 / 4) (by positivity) 0).const_mul
      (Real.exp ((‖p.2‖ + 1) ^ 2 / p.1))

/-- Actual integrability follows from the Gaussian envelope, before any
continuity or differentiation theorem is applied. -/
theorem integrable_gaussian_integrand (hB : Continuous B) (hc : Continuous g)
    (hg : HasGaussianMoments B g) (p : ℝ × E) (hp : 0 < p.1) :
    Integrable (fun z ↦ Real.exp (-B z + gaussianStatistic z p) • g z) := by
  refine (integrable_gaussian_envelope hg p hp).mono' ?_ ?_
  · exact (by fun_prop [gaussianStatistic] : Continuous
      (fun z ↦ Real.exp (-B z + gaussianStatistic z p) • g z)).aestronglyMeasurable
  · filter_upwards [] with z
    exact norm_gaussian_integrand_le p p hp (by simpa using
      (show 0 < min (p.1 / 2) 1 by positivity)) z

/-- Dominated convergence proves continuity in all natural Gaussian parameters. -/
theorem continuousAt_gaussianIntegral (hB : Continuous B) (hc : Continuous g)
    (hg : HasGaussianMoments B g) (p : ℝ × E) (hp : 0 < p.1) :
    ContinuousAt (gaussianIntegral B g) p := by
  apply continuousAt_of_dominated
    (bound := fun z ↦ Real.exp ((‖p.2‖ + 1) ^ 2 / p.1) *
      (Real.exp (-(B z + (p.1 / 4) * ‖z‖ ^ 2)) * ‖g z‖))
  · exact Eventually.of_forall fun q ↦ (by fun_prop [gaussianStatistic] : Continuous
      (fun z ↦ Real.exp (-B z + gaussianStatistic z q) • g z)).aestronglyMeasurable
  · filter_upwards [Metric.ball_mem_nhds p
      (show 0 < min (p.1 / 2) 1 by positivity)] with q hq
    filter_upwards [] with z
    exact norm_gaussian_integrand_le p q hp (by simpa only
      [Metric.mem_ball, dist_eq_norm] using hq) z
  · exact integrable_gaussian_envelope hg p hp
  · exact Eventually.of_forall fun z ↦ (by fun_prop [gaussianStatistic] : Continuous
      (fun q ↦ Real.exp (-B z + gaussianStatistic z q) • g z)).continuousAt

/-- The Fréchet derivative is another Gaussian integral, with the fixed
observable multiplied by the Gaussian sufficient statistic. -/
theorem hasFDerivAt_gaussianIntegral (hB : Continuous B) (hc : Continuous g)
    (hg : HasGaussianMoments B g) (p : ℝ × E) (hp : 0 < p.1) :
    HasFDerivAt (gaussianIntegral B g)
      (gaussianIntegral B (fun z ↦ (gaussianStatistic z).smulRight (g z)) p) p := by
  have hmetric : TopologicalSpace.PseudoMetrizableSpace ((ℝ × E) →L[ℝ] G) :=
    @PseudoEMetricSpace.pseudoMetrizableSpace ((ℝ × E) →L[ℝ] G)
      (inferInstance : PseudoEMetricSpace ((ℝ × E) →L[ℝ] G))
  have hgc : Continuous (fun z ↦ (gaussianStatistic z).smulRight (g z)) :=
    isBoundedBilinearMap_smulRight.continuous.comp
      (continuous_gaussianStatistic.prodMk hc)
  have hgm := hg.statistic hB hc
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F' := fun q z ↦ Real.exp (-B z + gaussianStatistic z q) •
      (gaussianStatistic z).smulRight (g z))
    (s := Metric.ball p (min (p.1 / 2) 1))
    (bound := fun z ↦ Real.exp ((‖p.2‖ + 1) ^ 2 / p.1) *
      (Real.exp (-(B z + (p.1 / 4) * ‖z‖ ^ 2)) *
        ‖(gaussianStatistic z).smulRight (g z)‖))
    (Metric.ball_mem_nhds p (by positivity))
  · exact Eventually.of_forall fun q ↦ (by fun_prop [gaussianStatistic] : Continuous
      (fun z ↦ Real.exp (-B z + gaussianStatistic z q) • g z)).aestronglyMeasurable
  · exact integrable_gaussian_integrand hB hc hg p hp
  · have hdcont : Continuous (fun z : E ↦
        Real.exp (-B z + gaussianStatistic z p) •
          (gaussianStatistic z).smulRight (g z)) :=
      (((hB.neg.add (continuous_gaussianStatistic.clm_apply
        continuous_const)).rexp).smul hgc)
    exact hdcont.aestronglyMeasurable
  · filter_upwards [] with z q hq
    exact norm_gaussian_integrand_le (g := fun z ↦ (gaussianStatistic z).smulRight (g z))
      p q hp (by simpa only [Metric.mem_ball, dist_eq_norm] using hq) z
  · exact integrable_gaussian_envelope hgm p hp
  · filter_upwards [] with z q _
    convert (((gaussianStatistic z).hasFDerivAt.const_add (-B z)).exp).smul_const (g z)
      using 1
    apply ContinuousLinearMap.ext
    intro v
    simp only [ContinuousLinearMap.smulRight_apply, smul_apply, smul_smul, smul_eq_mul]

end Observable

/-- Every finite derivative order follows by the same dominated derivative
recursion, uniformly for every normed vector-valued observable. -/
theorem contDiffOn_gaussianIntegral_nat (n : ℕ)
    (G : Type (max u v)) [NormedAddCommGroup G] [NormedSpace ℝ G]
    {B : E → ℝ} {g : E → G} (hB : Continuous B) (hc : Continuous g)
    (hg : HasGaussianMoments B g) :
    ContDiffOn ℝ n (gaussianIntegral B g) gaussianDomain := by
  induction n generalizing G with
  | zero =>
    apply contDiffOn_zero.mpr
    intro p hp
    exact (continuousAt_gaussianIntegral hB hc hg p hp).continuousWithinAt
  | succ n ih =>
    rw [show (↑(n + 1) : ℕ∞ω) = (n : ℕ∞ω) + 1 by simp]
    apply (contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn
      isOpen_gaussianDomain.uniqueDiffOn).mpr
    refine ⟨by simp, gaussianIntegral B
      (fun z ↦ (gaussianStatistic z).smulRight (g z)), ?_, ?_⟩
    · apply ih
      · exact isBoundedBilinearMap_smulRight.continuous.comp
          (continuous_gaussianStatistic.prodMk hc)
      · exact hg.statistic hB hc
    · intro p hp
      exact (hasFDerivAt_gaussianIntegral hB hc hg p hp).hasFDerivWithinAt

/-- Smoothness in both precision and center, derived from actual Gaussian
moment domination rather than a smooth-integral assumption. -/
theorem contDiffOn_gaussianIntegral
    {G : Type v} [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    {B : E → ℝ} {g : E → G} (hB : Continuous B) (hc : Continuous g)
    (hg : HasGaussianMoments B g) :
    ContDiffOn ℝ ∞ (gaussianIntegral B g) gaussianDomain := by
  let e : ULift.{u} G ≃ₗᵢ[ℝ] G := LinearIsometryEquiv.ulift ℝ G
  let g' : E → ULift.{u} G := fun z ↦ e.symm (g z)
  have hc' : Continuous g' := e.symm.continuous.comp hc
  have hg' : HasGaussianMoments B g' := by
    intro a ha n
    simpa only [g', e.symm.norm_map] using hg a ha n
  have hs : ContDiffOn ℝ ∞ (gaussianIntegral B g') gaussianDomain :=
    contDiffOn_infty.mpr fun n ↦ contDiffOn_gaussianIntegral_nat n _ hB hc' hg'
  have he (p : ℝ × E) (hp : p ∈ gaussianDomain) :
      gaussianIntegral B g p = e (gaussianIntegral B g' p) := by
    have hi := integrable_gaussian_integrand hB hc' hg' p hp
    have heq := e.toContinuousLinearEquiv.toContinuousLinearMap.integral_comp_comm hi
    change (∫ z, Real.exp (-B z + gaussianStatistic z p) • g z) =
      e.toContinuousLinearEquiv.toContinuousLinearMap
        (∫ z, Real.exp (-B z + gaussianStatistic z p) • g' z)
    rw [← heq]
    apply integral_congr_ae
    filter_upwards [] with z
    simp only [ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
      map_smul, g', e.apply_symm_apply]
  exact (e.contDiff.comp_contDiffOn hs).congr he

/-- Polynomial growth and an affine lower base potential imply every Gaussian
weighted moment needed by the differentiation theorem. -/
theorem hasGaussianMoments_of_polynomial_growth
    {G : Type v} [NormedAddCommGroup G]
    {B : E → ℝ} {g : E → G} (hB : Continuous B) (hc : Continuous g)
    (a₀ : ℝ) (b : E) (hlo : ∀ z, a₀ + inner ℝ b z ≤ B z)
    (A C : ℝ) (k : ℕ) (hbound : ∀ z, ‖g z‖ ≤ A + C * ‖z‖ ^ k) :
    HasGaussianMoments B g := by
  intro a ha n
  have hm (j : ℕ) : Integrable (fun z ↦
      ‖z‖ ^ j * Real.exp (-(B z + a * ‖z‖ ^ 2))) := by
    apply Gibbs.integrable_norm_pow_mul_exp_neg_of_quadratic_lower_bound
      (hB.add (by fun_prop)).measurable b ha (a := a₀)
    intro z
    change a₀ + inner ℝ b z + a * ‖z‖ ^ 2 ≤ B z + a * ‖z‖ ^ 2
    linarith [hlo z]
  refine (((hm n).const_mul A).add ((hm (n + k)).const_mul C)).mono' ?_ ?_
  · exact (by fun_prop : Continuous (fun z ↦
      ‖z‖ ^ n * Real.exp (-(B z + a * ‖z‖ ^ 2)) * ‖g z‖)).aestronglyMeasurable
  · filter_upwards [] with z
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have ht := mul_le_mul_of_nonneg_left (hbound z)
      (show 0 ≤ ‖z‖ ^ n * Real.exp (-(B z + a * ‖z‖ ^ 2)) by positivity)
    convert ht using 1
    simp only [Pi.add_apply, pow_add]
    ring

/-- Convenient public form requiring just an affine lower bound for the fixed
base and polynomial growth for the observable. -/
theorem contDiffOn_gaussianIntegral_of_polynomial_growth
    {G : Type v} [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    {B : E → ℝ} {g : E → G} (hB : Continuous B) (hc : Continuous g)
    (a₀ : ℝ) (b : E) (hlo : ∀ z, a₀ + inner ℝ b z ≤ B z)
    (A C : ℝ) (k : ℕ) (hbound : ∀ z, ‖g z‖ ≤ A + C * ‖z‖ ^ k) :
    ContDiffOn ℝ ∞ (gaussianIntegral B g) gaussianDomain :=
  contDiffOn_gaussianIntegral hB hc
    (hasGaussianMoments_of_polynomial_growth hB hc a₀ b hlo A C k hbound)

end AcceleratedLogConcave.Conditional.Tilt
