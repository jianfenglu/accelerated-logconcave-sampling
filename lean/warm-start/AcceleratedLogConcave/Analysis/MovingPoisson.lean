import AcceleratedLogConcave.Analysis.Poisson.GradientInverse
import AcceleratedLogConcave.Analysis.Poisson.Reflection
import AcceleratedLogConcave.Analysis.Poisson.MovingForms
import AcceleratedLogConcave.Analysis.Poisson.StrongDerivative

/-!
# The Poisson material coefficient and common-domain differentiation

The weighted operator coefficient below is constructed from the actual
Poisson inverse, actual Hessian multiplier, and canonical gradient reflection.
Its sharp bound follows from the full Bochner theorem, with no inverse gap.
The common-domain differentiation theorem separately records precisely the
coefficient derivatives that a transported reference family must supply.
-/
noncomputable section
open MeasureTheory InnerProductSpace Filter
open scoped ContDiff RealInnerProductSpace Topology
namespace AcceleratedLogConcave.Analysis.Poisson
open WeightedGradient

section Weighted
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable (μ : Measure E) [IsProbabilityMeasure μ] (V : E → ℝ)
  (hV : ContDiff ℝ 2 V) (hI : Integrable (fun x => Real.exp (-V x)))
  (hμ : μ = volume.tilted (fun x => -V x))
  (m : ℝ) (hm : 0 < m)
  (hlower : ∀ x a, m * ‖a‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x a a)
  (hupper : ∀ x a, fderiv ℝ (fderiv ℝ V) x a a ≤ 1 * ‖a‖ ^ 2)

/-- The actual weighted variational projection instantiates the supplied
abstract projection theorem on its genuine unbounded gradient domain. -/
theorem weightedGradientProjection_eq_mathy :
    weightedGradientProjection μ V hV hI hμ m 1 hm hlower hupper =
      gradientProjection (closedGradientRange
        (closedGradient μ V (hV.of_le (by norm_num)) hI hμ).toFun) := by
  apply ContinuousLinearMap.ext
  intro f
  rw [weightedGradientProjection_apply]
  exact poissonGradient_eq_projection _ f
    (vectorPoissonSolution μ V hV hI hμ m 1 hm hlower hupper f)
    (vectorPoissonSolution_spec (μ := μ) (V := V) (hV := hV) (hI := hI) (hμ := hμ)
      (m := m) (L := 1) (hm := hm) (hlower := hlower) (hupper := hupper) f).2

/-- The concrete source coefficient `c (I - 2C) H D R`.
Identification as a time derivative is a separate moving-family theorem. -/
def poissonMaterialOperator (c : ℝ) : Lp ℝ 2 μ →L[ℝ] Lp E 2 μ :=
  c • (gradientReflection (closedGradientRange
    (closedGradient μ V (hV.of_le (by norm_num)) hI hμ).toFun)).toLinearIsometry.toContinuousLinearMap ∘L
      (hessianMultiplier μ V hV m 1 hlower hupper ∘L
        gradientPoissonInverse μ V hV hI hμ m 1 hm hlower hupper)

theorem poissonMaterialOperator_apply (c : ℝ) (g : Lp ℝ 2 μ) :
    poissonMaterialOperator μ V hV hI hμ m hm hlower hupper c g =
      c • (hessianMultiplier μ V hV m 1 hlower hupper
        (gradientPoissonInverse μ V hV hI hμ m 1 hm hlower hupper g) -
        (2 : ℝ) • weightedGradientProjection μ V hV hI hμ m 1 hm hlower hupper
          (hessianMultiplier μ V hV m 1 hlower hupper
            (gradientPoissonInverse μ V hV hI hμ m 1 hm hlower hupper g))) := by
  simp only [poissonMaterialOperator, smul_apply, ContinuousLinearMap.comp_apply,
    LinearIsometry.coe_toContinuousLinearMap, LinearIsometryEquiv.coe_toLinearIsometry]
  rw [gradientReflection_apply, weightedGradientProjection_eq_mathy]

/-- The sharp source material bound; its constant is independent of `m`. -/
theorem poissonMaterialOperator_norm_le (c : ℝ) :
    ‖poissonMaterialOperator μ V hV hI hμ m hm hlower hupper c‖ ≤ |c| := by
  apply ContinuousLinearMap.opNorm_le_bound _ (abs_nonneg c)
  intro g
  simp only [poissonMaterialOperator, smul_apply, ContinuousLinearMap.comp_apply,
    LinearIsometry.coe_toContinuousLinearMap, LinearIsometryEquiv.coe_toLinearIsometry]
  rw [norm_smul, Real.norm_eq_abs, LinearIsometryEquiv.norm_map]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg c)
  have hb := hessianMultiplier_comp_gradientPoissonInverse_norm_le μ V hV hI hμ m hm hlower hupper
  exact ((hessianMultiplier μ V hV m 1 hlower hupper ∘L
    gradientPoissonInverse μ V hV hI hμ m 1 hm hlower hupper).le_opNorm g).trans
      (by simpa using mul_le_mul_of_nonneg_right hb (norm_nonneg g))
end Weighted

section CommonDomain
open MovingForms
variable {V H K : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]

omit [InnerProductSpace ℝ V] [CompleteSpace V] [InnerProductSpace ℝ K] [CompleteSpace K] in
/-- Product differentiation with norm-continuous operators and a strong
operator derivative only on the fixed vector. -/
theorem hasDerivAt_strong_apply [NormedSpace ℝ V] [NormedSpace ℝ K]
    (D : ℝ → V →L[ℝ] K) (u : ℝ → V) (t : ℝ) (u' : V) (v : K)
    (hD : ContinuousAt D t) (hu : HasDerivAt u u' t)
    (hv : HasDerivAt (fun s => D s (u t)) v t) :
    HasDerivAt (fun s => D s (u s)) (D t u' + v) t := by
  rw [hasDerivAt_iff_tendsto_slope]
  have hOp : Tendsto D (𝓝[≠] t) (𝓝 (D t)) := hD.tendsto.mono_left nhdsWithin_le_nhds
  have hprod := (continuous_fst.clm_apply continuous_snd).tendsto (D t, u') |>.comp
    (hOp.prodMk_nhds hu.tendsto_slope)
  have hsum := hprod.add hv.tendsto_slope
  apply hsum.congr'
  filter_upwards [] with s
  simp only [Function.comp_apply, slope, vsub_eq_sub, map_smul, map_sub]
  module

/-- Differentiate the constructed weak inverse and obtain the source reflection
formula on a fixed Hilbert form domain. The two derivative premises concern
only the actual gradient and its energy coefficient along the fixed solution. -/
theorem hasDerivAt_commonDomainGradient
    (D : ℝ → V →L[ℝ] K) (i : V →L[ℝ] H) {k : ℝ} (hk : 0 < k)
    (hD : ∀ t u, k * ‖u‖ ^ 2 ≤ ‖D t u‖ ^ 2)
    (t : ℝ) (hcontD : ContinuousAt D t)
    (hcontB : ContinuousAt (fun s => energyCoefficient (D s)) t)
    (g : H) (c : ℝ) (B : K →L[ℝ] K)
    (hgrad : HasDerivAt (fun s => D s (commonDomainSolution (D t) i hk (hD t) g))
      (c • B (D t (commonDomainSolution (D t) i hk (hD t) g))) t)
    (hform : HasDerivAt (fun s => energyCoefficient (D s)
      (commonDomainSolution (D t) i hk (hD t) g))
      (variationalRHS (D t) ((2 * c) • B (D t (commonDomainSolution (D t) i hk (hD t) g)))) t) :
    HasDerivAt (fun s => D s (commonDomainSolution (D s) i hk (hD s) g))
      (c • gradientReflection (closedGradientRange (D t).toLinearMap)
        (B (D t (commonDomainSolution (D t) i hk (hD t) g)))) t := by
  let z := B (D t (commonDomainSolution (D t) i hk (hD t) g))
  have hu := hasDerivAt_commonDomainSolution D i hk hD hcontB g
    (variationalRHS (D t) ((2 * c) • z)) hform
  have hprod := hasDerivAt_strong_apply D
    (fun s => commonDomainSolution (D s) i hk (hD s) g) t _ _ hcontD hu hgrad
  convert hprod using 1
  have hs := poissonGradient_eq_projection (D t).toLinearMap ((2 * c) • z)
    (commonDomainSolution (D t) (D t) hk (hD t) ((2 * c) • z))
    (commonDomainSolution_weak (D t) (D t) hk (hD t) ((2 * c) • z))
  change c • gradientReflection _ z =
    D t (-commonDomainSolution (D t) (D t) hk (hD t) ((2 * c) • z)) + c • z
  change D t (commonDomainSolution (D t) (D t) hk (hD t) ((2 * c) • z)) = _ at hs
  rw [map_neg, hs, gradientReflection_apply, map_smul]
  module
end CommonDomain
end AcceleratedLogConcave.Analysis.Poisson
