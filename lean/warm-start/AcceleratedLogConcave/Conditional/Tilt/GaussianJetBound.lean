import AcceleratedLogConcave.Conditional.Tilt.GaussianIntegral
import Mathlib.Analysis.Calculus.ContDiff.Basic

/-!
# Actual Gaussian-integral derivative norms

Only the natural Gaussian parameter is differentiated. The base potential and
observable need continuity and the existing genuine Gaussian moments.

The proof first identifies the recursive derivative with a fixed-observable
Gaussian integral. A universe-uniform induction gives the exact statistic-norm
bound. ULift then gives the public arbitrary-codomain statement, following the
same strategy as contDiffOn_gaussianIntegral. Finally the already proved
statistic growth bound gives a polynomial observable of degree at most 2*n.
All scalar majorants are separately proved integrable.
-/

noncomputable section

namespace AcceleratedLogConcave.Conditional.Tilt

open MeasureTheory Set Filter
open scoped RealInnerProductSpace ContDiff Topology

universe u v

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

section Majorants

variable {G : Type v} [NormedAddCommGroup G]
  {B : E → ℝ} {g : E → G}

/-- Polynomial powers of the statistic majorant preserve the existing genuine
Gaussian moments. No differentiability of the observable is used. -/
theorem HasGaussianMoments.statisticPolynomial (hg : HasGaussianMoments B g)
    (n : ℕ) :
    HasGaussianMoments B (fun z ↦ (‖z‖ ^ 2 + ‖z‖) ^ n * ‖g z‖) := by
  have hnon (k : ℕ) (z : E) : 0 ≤ (‖z‖ ^ 2 + ‖z‖) ^ k * ‖g z‖ := by
    positivity
  intro a ha m
  induction n generalizing m with
  | zero =>
    simpa only [pow_zero, one_mul, norm_norm] using hg a ha m
  | succ n ih =>
    refine ((ih (m + 2)).add (ih (m + 1))).congr ?_
    filter_upwards [] with z
    simp only [Pi.add_apply, Real.norm_eq_abs]
    rw [abs_of_nonneg (hnon n z), abs_of_nonneg (hnon (n + 1) z)]
    simp only [pow_add, pow_one]
    ring

/-- Actual tilted polynomial majorants are integrable, not merely formal
Bochner integrals using the undefined-integral convention. -/
theorem integrable_gaussian_statisticPolynomial (hB : Continuous B) (hc : Continuous g)
    (hg : HasGaussianMoments B g) (n : ℕ) (p : ℝ × E) (hp : 0 < p.1) :
    Integrable (fun z ↦ Real.exp (-B z + gaussianStatistic z p) *
      (‖z‖ ^ 2 + ‖z‖) ^ n * ‖g z‖) := by
  have hpoly : Continuous (fun z ↦ (‖z‖ ^ 2 + ‖z‖) ^ n * ‖g z‖) := by
    fun_prop
  simpa only [smul_eq_mul, mul_assoc] using
    integrable_gaussian_integrand hB hpoly (hg.statisticPolynomial n) p hp

/-- The sharper exact-statistic scalar majorant is also genuinely integrable. -/
theorem integrable_gaussian_statisticNorm (hB : Continuous B) (hc : Continuous g)
    (hg : HasGaussianMoments B g) (n : ℕ) (p : ℝ × E) (hp : 0 < p.1) :
    Integrable (fun z ↦ Real.exp (-B z + gaussianStatistic z p) *
      ‖gaussianStatistic z‖ ^ n * ‖g z‖) := by
  have hstat : Continuous (fun z : E => ‖gaussianStatistic z‖) :=
    (continuous_norm (E := (ℝ × E) →L[ℝ] ℝ)).comp
      (continuous_gaussianStatistic (E := E))
  refine (integrable_gaussian_statisticPolynomial hB hc hg n p hp).mono' ?_ ?_
  · exact ((((hB.neg.add
        (continuous_gaussianStatistic.clm_apply continuous_const)).rexp).mul
        (hstat.pow n)).mul hc.norm).aestronglyMeasurable
  · filter_upwards [] with z
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    gcongr
    exact norm_gaussianStatistic_le z

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The exact-statistic observable fits the posterior supplier's standard
polynomial-growth interface, with degree 2*n + k and the same coefficient A. -/
theorem norm_gaussian_statisticNorm_observable_le
    {A : ℝ} (k n : ℕ)
    (hbound : ∀ z, ‖g z‖ ≤ A * (1 + ‖z‖) ^ k) (z : E) :
    ‖‖gaussianStatistic z‖ ^ n * ‖g z‖‖ ≤
      A * (1 + ‖z‖) ^ (2 * n + k) := by
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hs : ‖gaussianStatistic z‖ ≤ (1 + ‖z‖) ^ 2 :=
    (norm_gaussianStatistic_le z).trans (by nlinarith [norm_nonneg z])
  calc
    ‖gaussianStatistic z‖ ^ n * ‖g z‖ ≤ ((1 + ‖z‖) ^ 2) ^ n * (A * (1 + ‖z‖) ^ k) :=
      mul_le_mul (pow_le_pow_left₀ (norm_nonneg (gaussianStatistic z)) hs n) (hbound z)
        (norm_nonneg _) (by positivity)
    _ = A * (1 + ‖z‖) ^ (2 * n + k) := by rw [← pow_mul, pow_add]; ring

end Majorants

section Recursion

variable {G : Type v} [NormedAddCommGroup G] [NormedSpace ℝ G]
  {B : E → ℝ} {g : E → G}

/-- A useful standalone recursion: after one actual differentiation, the
remaining iterated derivative is that of another fixed-observable integral.
This identity itself has no codomain-universe restriction. -/
theorem norm_iteratedFDerivWithin_gaussianIntegral_succ (n : ℕ)
    (hB : Continuous B) (hc : Continuous g) (hg : HasGaussianMoments B g)
    (p : ℝ × E) (hp : 0 < p.1) :
    ‖iteratedFDerivWithin ℝ (n + 1) (gaussianIntegral B g) gaussianDomain p‖ =
      ‖iteratedFDerivWithin ℝ n
        (gaussianIntegral B (fun z ↦ (gaussianStatistic z).smulRight (g z)))
        gaussianDomain p‖ := by
  have hder : EqOn (fderivWithin ℝ (gaussianIntegral B g) gaussianDomain)
      (gaussianIntegral B (fun z ↦ (gaussianStatistic z).smulRight (g z)))
      gaussianDomain := by
    intro q hq
    exact (hasFDerivAt_gaussianIntegral hB hc hg q hq).hasFDerivWithinAt.fderivWithin
      (isOpen_gaussianDomain.uniqueDiffOn q hq)
  rw [← norm_iteratedFDerivWithin_fderivWithin isOpen_gaussianDomain.uniqueDiffOn (show p ∈ gaussianDomain from hp)]
  exact congrArg norm (iteratedFDerivWithin_congr hder (show p ∈ gaussianDomain from hp) n)

end Recursion

/-- Universe-uniform induction matching contDiffOn_gaussianIntegral_nat.
The constant is exactly one; no combinatorial loss is needed before quotient
normalization. -/
theorem norm_iteratedFDerivWithin_gaussianIntegral_statistic_nat (n : ℕ)
    (G : Type (max u v)) [NormedAddCommGroup G] [NormedSpace ℝ G]
    {B : E → ℝ} {g : E → G} (hB : Continuous B) (hc : Continuous g)
    (hg : HasGaussianMoments B g) (p : ℝ × E) (hp : 0 < p.1) :
    ‖iteratedFDerivWithin ℝ n (gaussianIntegral B g) gaussianDomain p‖ ≤
      ∫ z, Real.exp (-B z + gaussianStatistic z p) *
        ‖gaussianStatistic z‖ ^ n * ‖g z‖ := by
  induction n generalizing G with
  | zero =>
    simpa only [norm_iteratedFDerivWithin_zero, gaussianIntegral, norm_smul,
      Real.norm_eq_abs, Real.abs_exp, pow_zero, mul_one] using
      (norm_integral_le_integral_norm
        (fun z ↦ Real.exp (-B z + gaussianStatistic z p) • g z))
  | succ n ih =>
    have hc' : Continuous (fun z ↦ (gaussianStatistic z).smulRight (g z)) :=
      isBoundedBilinearMap_smulRight.continuous.comp
        (continuous_gaussianStatistic.prodMk hc)
    calc
      ‖iteratedFDerivWithin ℝ (n + 1) (gaussianIntegral B g) gaussianDomain p‖ =
          ‖iteratedFDerivWithin ℝ n
            (gaussianIntegral B (fun z ↦ (gaussianStatistic z).smulRight (g z)))
            gaussianDomain p‖ :=
        norm_iteratedFDerivWithin_gaussianIntegral_succ n hB hc hg p hp
      _ ≤ ∫ z, Real.exp (-B z + gaussianStatistic z p) *
          ‖gaussianStatistic z‖ ^ n * ‖(gaussianStatistic z).smulRight (g z)‖ := by
        apply ih
        · exact hc'
        · exact hg.statistic hB hc
      _ = ∫ z, Real.exp (-B z + gaussianStatistic z p) *
          ‖gaussianStatistic z‖ ^ (n + 1) * ‖g z‖ := by
        apply integral_congr_ae
        filter_upwards [] with z
        rw [ContinuousLinearMap.norm_smulRight_apply, pow_succ]
        ring

/-- Public exact-statistic bound with arbitrary codomain universe. Completeness
is used only in the integral-commuting ULift adapter, as in the existing public
smoothness theorem. -/
theorem norm_iteratedFDerivWithin_gaussianIntegral_statistic
    {G : Type v} [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    {B : E → ℝ} {g : E → G} (hB : Continuous B) (hc : Continuous g)
    (hg : HasGaussianMoments B g) (n : ℕ) (p : ℝ × E) (hp : 0 < p.1) :
    ‖iteratedFDerivWithin ℝ n (gaussianIntegral B g) gaussianDomain p‖ ≤
      ∫ z, Real.exp (-B z + gaussianStatistic z p) *
        ‖gaussianStatistic z‖ ^ n * ‖g z‖ := by
  let e : ULift.{u} G ≃ₗᵢ[ℝ] G := LinearIsometryEquiv.ulift ℝ G
  let g' : E → ULift.{u} G := fun z ↦ e.symm (g z)
  have hc' : Continuous g' := e.symm.continuous.comp hc
  have hg' : HasGaussianMoments B g' := by
    intro a ha j
    simpa only [g', e.symm.norm_map] using hg a ha j
  have he : EqOn (gaussianIntegral B g) (e ∘ gaussianIntegral B g') gaussianDomain := by
    intro q hq
    have hi := integrable_gaussian_integrand hB hc' hg' q hq
    have heq := e.toContinuousLinearEquiv.toContinuousLinearMap.integral_comp_comm hi
    change (∫ z, Real.exp (-B z + gaussianStatistic z q) • g z) =
      e.toContinuousLinearEquiv.toContinuousLinearMap
        (∫ z, Real.exp (-B z + gaussianStatistic z q) • g' z)
    rw [← heq]
    apply integral_congr_ae
    filter_upwards [] with z
    simp only [ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
      map_smul, g', e.apply_symm_apply]
  calc
    ‖iteratedFDerivWithin ℝ n (gaussianIntegral B g) gaussianDomain p‖ =
        ‖iteratedFDerivWithin ℝ n (e ∘ gaussianIntegral B g') gaussianDomain p‖ :=
      congrArg norm (iteratedFDerivWithin_congr he hp n)
    _ = ‖iteratedFDerivWithin ℝ n (gaussianIntegral B g') gaussianDomain p‖ :=
      e.norm_iteratedFDerivWithin_comp_left (gaussianIntegral B g') isOpen_gaussianDomain.uniqueDiffOn (show p ∈ gaussianDomain from hp) n
    _ ≤ ∫ z, Real.exp (-B z + gaussianStatistic z p) *
        ‖gaussianStatistic z‖ ^ n * ‖g' z‖ :=
      norm_iteratedFDerivWithin_gaussianIntegral_statistic_nat n _ hB hc' hg' p hp
    _ = ∫ z, Real.exp (-B z + gaussianStatistic z p) *
        ‖gaussianStatistic z‖ ^ n * ‖g z‖ := by
      apply integral_congr_ae
      filter_upwards [] with z
      simp only [g', e.symm.norm_map]

/-- The requested polynomial-moment supplier for actual iterated Gaussian
parameter derivatives. Both scalar integrals in the comparison are integrable.
The polynomial degree increases by two at each derivative. -/
theorem norm_iteratedFDerivWithin_gaussianIntegral_polynomial
    {G : Type v} [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    {B : E → ℝ} {g : E → G} (hB : Continuous B) (hc : Continuous g)
    (hg : HasGaussianMoments B g) (n : ℕ) (p : ℝ × E) (hp : 0 < p.1) :
    ‖iteratedFDerivWithin ℝ n (gaussianIntegral B g) gaussianDomain p‖ ≤
      ∫ z, Real.exp (-B z + gaussianStatistic z p) *
        (‖z‖ ^ 2 + ‖z‖) ^ n * ‖g z‖ := by
  refine (norm_iteratedFDerivWithin_gaussianIntegral_statistic hB hc hg n p hp).trans ?_
  apply integral_mono
    (integrable_gaussian_statisticNorm hB hc hg n p hp)
    (integrable_gaussian_statisticPolynomial hB hc hg n p hp)
  intro z
  dsimp only
  gcongr
  exact norm_gaussianStatistic_le z

end AcceleratedLogConcave.Conditional.Tilt
