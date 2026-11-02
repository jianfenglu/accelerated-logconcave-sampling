import AcceleratedLogConcave.Conditional.Centering.MeanMoments
import AcceleratedLogConcave.Conditional.PolynomialMoments
import AcceleratedLogConcave.Conditional.SourcePosteriorAffine
import AcceleratedLogConcave.Numerics.AffineBounds
import Mathlib.Probability.Moments.Variance

/-! Directional total covariance for the actual Gaussian posterior family.
The joint law, posterior means and all second moments are the source objects.
The argument uses the proved interpolation disintegration and original C²
Hessian bounds. No covariance estimate or integrability certificate is assumed. -/
noncomputable section
set_option autoImplicit false
open Set MeasureTheory ProbabilityTheory
open scoped ContDiff RealInnerProductSpace
namespace AcceleratedLogConcave.Conditional.RecursiveReferenceCovariance
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
local notation "E" => EuclideanSpace ℝ ι
variable {F : EuclideanSpace ℝ ι → ℝ} {ell : ℝ}
  (hF : ContDiff ℝ 2 F) (hell : 0 ≤ ell)
  (hlo : ∀ z a, 0 ≤ fderiv ℝ (fderiv ℝ F) z a a)
  (hup : ∀ z a, fderiv ℝ (fderiv ℝ F) z a a ≤ ell * ‖a‖ ^ 2)
include hF hlo hup

include hell in
omit [DecidableEq ι] in
/-- A qualitative L² fact on the full positive-variance domain; no small-radius
condition is needed for covariance disintegration. -/
theorem conditionalMean_memLp (x : E) {r b : ℝ} (hr : 0 < r)
    (hb : 0 ≤ b) (hb1 : b < 1) :
    MemLp (conditionalMean F x r b) 2 (interpolationLaw F x r b) := by
  let := interpolationLaw_isProbabilityMeasure hF hlo x r b
  have hid : MemLp (id : E → E) 2 (interpolationLaw F x r b) :=
    (memLp_two_iff_integrable_sq_norm stronglyMeasurable_id.aestronglyMeasurable).mpr
      (interpolationLaw_integrable_norm_pow hF hlo x r b 2)
  have hM := lipschitzWith_conditionalMean hF hell hlo hup x hr (by linarith) hb1
  have hc := (hid.norm.const_mul (r*ell)).add (memLp_const ‖conditionalMean F x r b 0‖)
  apply hc.mono hM.continuous.aestronglyMeasurable
  filter_upwards [] with y
  have hd := hM.dist_le_mul y 0
  simp only [dist_eq_norm, sub_zero] at hd
  change ‖conditionalMean F x r b y - conditionalMean F x r b 0‖ ≤
    (r*ell) * ‖y‖ at hd
  have ht := norm_add_le (conditionalMean F x r b y - conditionalMean F x r b 0)
    (conditionalMean F x r b 0)
  rw [sub_add_cancel] at ht
  change ‖conditionalMean F x r b y‖ ≤ |r*ell*‖y‖ + ‖conditionalMean F x r b 0‖|
  rw [abs_of_nonneg (by positivity)]
  linarith

omit [DecidableEq ι] in
/-- Actual primitive gradient second moments under every conditional law. -/
theorem observable_memLp (x : E) (r : ℝ) {b : ℝ}
    (hb : 0 ≤ b) (hb1 : b < 1) (y : E) :
    MemLp (primitiveObservable F x r) 2 (conditionalLaw F x r b y) := by
  apply Gibbs.memLp_two_heatPosterior_of_affine_bound (contDiff_primitivePotential hF x r)
    (m := 0) le_rfl (conditionalVariance_pos (by linarith) hb1)
    (by simpa using primitivePotential_hessian_nonneg hF hlo x r)
    (b • y) (continuous_primitiveObservable hF x r)
    (‖gradient F 0‖ + |ell| * ‖x‖) (|ell| * |r|)
    (norm_primitiveObservable_le_affine hF hlo hup x r)

omit [DecidableEq ι] in
/-- Directional averaging commutes with the actual posterior mean. -/
theorem integral_directional_observable (x : E) {r b : ℝ} (_hr : 0 < r)
    (hb : 0 ≤ b) (hb1 : b < 1) (v y : E) :
    (∫ z, ⟪v, primitiveObservable F x r z⟫ ∂conditionalLaw F x r b y) =
      ⟪v, conditionalMean F x r b y⟫ := by
  let := conditionalLaw_isProbabilityMeasure hF hlo x r (by linarith) hb1 y
  exact integral_inner ((observable_memLp hF hlo hup x r hb hb1 y).integrable (by norm_num)) v

include hell in
/-- The conditional second moment, integrated against the genuine interpolation
law, is integrable. This follows from the actual joint-law identity. -/
theorem integrable_conditional_second (x : E) {r b : ℝ} (_hr : 0 < r)
    (hb : 0 ≤ b) (hb1 : b < 1) (v : E) :
    Integrable (fun y => ∫ z, ⟪v, primitiveObservable F x r z⟫ ^ 2
      ∂conditionalLaw F x r b y) (interpolationLaw F x r b) := by
  let := baseLaw_isProbabilityMeasure hF hlo x r
  let := interpolationLaw_isProbabilityMeasure hF hlo x r b
  let k := conditionalKernel F x r b (contDiff_primitivePotential hF x r).continuous.measurable
  let : IsMarkovKernel k := conditionalKernel_isMarkov hF hlo x r b
    (conditionalVariance_pos (by linarith) hb1)
  let f : E × E → ℝ := fun p => ⟪v, primitiveObservable F x r p.2⟫ ^ 2
  have hbase : MemLp (fun z => ⟪v, primitiveObservable F x r z⟫) 2 (baseLaw F x r) :=
    (Gibbs.primitive_memLp_two_score hF hell hlo hup x r).const_inner (𝕜 := ℝ) v
  have hj : Integrable f (interpolationLaw F x r b ⊗ₘ k) := by
    rw [show k = conditionalKernel F x r b
      (contDiff_primitivePotential hF x r).continuous.measurable from rfl,
      conditional_joint_eq_map hF hlo x r b (conditionalVariance_pos (by linarith) hb1)]
    apply (integrable_map_measure
      (show AEStronglyMeasurable f _ from (by
        dsimp [f]
        exact (continuous_const.inner ((continuous_primitiveObservable hF x r).comp continuous_snd) |>.pow 2).aestronglyMeasurable))
      (show AEMeasurable (fun p : E × E => (interpolationMap b p, p.1)) _ from by
        unfold interpolationMap
        fun_prop)).mpr
    exact hbase.integrable_sq.comp_fst (stdGaussian E)
  have hi := (Measure.integrable_compProd_iff hj.aestronglyMeasurable).mp hj |>.2
  simpa only [f, Real.norm_eq_abs, abs_sq, conditionalKernel_apply, k] using hi

include hell in
/-- The actual posterior directional variance splits into conditional-mean
variance and the averaged actual conditional variance. -/
theorem total_variance (x : E) {r b : ℝ} (hr : 0 < r)
    (hb : 0 ≤ b) (hb1 : b < 1) (v : E) :
    Var[fun z => ⟪v, primitiveObservable F x r z⟫; baseLaw F x r] =
      Var[fun y => ⟪v, conditionalMean F x r b y⟫; interpolationLaw F x r b] +
      ∫ y, Var[fun z => ⟪v, primitiveObservable F x r z⟫; conditionalLaw F x r b y]
        ∂interpolationLaw F x r b := by
  let := baseLaw_isProbabilityMeasure hF hlo x r
  let := Gibbs.primitiveLaw_isProbabilityMeasure hF hlo x r
  let := interpolationLaw_isProbabilityMeasure hF hlo x r b
  have hbase : MemLp (fun z => ⟪v, primitiveObservable F x r z⟫) 2 (baseLaw F x r) :=
    (Gibbs.primitive_memLp_two_score hF hell hlo hup x r).const_inner (𝕜 := ℝ) v
  have hmean := (conditionalMean_memLp hF hell hlo hup x hr hb hb1).const_inner (𝕜 := ℝ) v
  have hsecond := integrable_conditional_second hF hell hlo hup x hr hb hb1 v
  have heq (y : E) :
      Var[fun z => ⟪v, primitiveObservable F x r z⟫; conditionalLaw F x r b y] =
        (∫ z, ⟪v, primitiveObservable F x r z⟫ ^ 2 ∂conditionalLaw F x r b y) -
          ⟪v, conditionalMean F x r b y⟫ ^ 2 := by
    let := conditionalLaw_isProbabilityMeasure hF hlo x r (by linarith) hb1 y
    rw [variance_eq_sub ((observable_memLp hF hlo hup x r hb hb1 y).const_inner (𝕜 := ℝ) v),
      integral_directional_observable hF hlo hup x hr hb hb1]
    rfl
  simp_rw [heq]
  rw [integral_sub hsecond hmean.integrable_sq]
  have hs := conditional_disintegration_integral hF hlo x r b
    (conditionalVariance_pos (by linarith) hb1)
    (fun p : E × E => ⟪v, primitiveObservable F x r p.2⟫ ^ 2)
    (by exact (continuous_const.inner ((continuous_primitiveObservable hF x r).comp continuous_snd) |>.pow 2).stronglyMeasurable)
    (hbase.integrable_sq.comp_fst (stdGaussian E))
  change (∫ y, ∫ z, ⟪v, primitiveObservable F x r z⟫ ^ 2 ∂conditionalLaw F x r b y
    ∂interpolationLaw F x r b) =
    ∫ p : E × E, ⟪v, primitiveObservable F x r p.1⟫ ^ 2
      ∂((baseLaw F x r).prod (stdGaussian E)) at hs
  have hp := integral_fun_fst (μ := baseLaw F x r) (ν := stdGaussian E)
    (fun z : E => ⟪v, primitiveObservable F x r z⟫ ^ 2)
  simp only [probReal_univ, one_smul] at hp
  rw [hp] at hs
  rw [hs, variance_eq_sub hbase, variance_eq_sub hmean]
  have hm : (∫ y, ⟪v, conditionalMean F x r b y⟫ ∂interpolationLaw F x r b) =
      ∫ z, ⟪v, primitiveObservable F x r z⟫ ∂baseLaw F x r := by
    rw [integral_inner ((conditionalMean_memLp hF hell hlo hup x hr hb hb1).integrable (by norm_num)),
      integral_conditionalMean_eq_base_mean hF hlo hup x r (by linarith) hb1]
    have hi : Integrable (primitiveObservable F x r) (baseLaw F x r) :=
      (Gibbs.primitive_memLp_two_score hF hell hlo hup x r).integrable (by norm_num)
    exact (integral_inner hi v).symm
  rw [hm]
  simp only [Pi.pow_apply]
  ring

omit hell hlo hup in
omit [DecidableEq ι] in
/-- The conditional variance is exactly that of the gradient under the
physical posterior, with its actual center and radius. -/
theorem conditional_variance_eq_physical (x : E) {r b : ℝ} (hr : 0 < r)
    (hb : 0 ≤ b) (hb1 : b < 1) (v y : E) :
    Var[fun z => ⟪v, primitiveObservable F x r z⟫; conditionalLaw F x r b y] =
      Var[fun a => ⟪v, gradient F a⟫;
        Gibbs.heatPosterior F (r ^ 2 * conditionalVariance b) (x + (r*b) • y)] := by
  have hg : Continuous (fun a : E => ⟪v, gradient F a⟫) :=
    continuous_const.inner ((InnerProductSpace.toDual ℝ E).symm.continuous.comp
      (hF.continuous_fderiv (by norm_num)))
  rw [← conditionalLaw_map_affine hF.continuous.measurable hr (by linarith) hb1 x y]
  simpa only [Function.comp_def, primitiveObservable] using
    (variance_map hg.measurable.aemeasurable
      (show AEMeasurable (fun z : E => x + r • z) _ from by fun_prop)).symm

omit hell hlo hup in
omit [DecidableEq ι] in
/-- The base variance is the physical posterior covariance at width r². -/
theorem base_variance_eq_physical (x : E) {r : ℝ} (hr : 0 < r) (v : E) :
    Var[fun z => ⟪v, primitiveObservable F x r z⟫; baseLaw F x r] =
      Var[fun a => ⟪v, gradient F a⟫; Gibbs.heatPosterior F (r ^ 2) x] := by
  have hg : Continuous (fun a : E => ⟪v, gradient F a⟫) :=
    continuous_const.inner ((InnerProductSpace.toDual ℝ E).symm.continuous.comp
      (hF.continuous_fderiv (by norm_num)))
  rw [← baseLaw_map_affine hF.continuous.measurable hr x]
  simpa only [Function.comp_def, primitiveObservable] using
    (variance_map hg.measurable.aemeasurable
      (show AEMeasurable (fun z : E => x + r • z) _ from by fun_prop)).symm

include hell in
omit [DecidableEq ι] in
/-- The precise centered primitive budget used by covariance induction is the
actual physical posterior directional variance. -/
theorem primitive_budget_eq_variance (x : E) {r : ℝ} (hr : 0 < r) (v : E) :
    (∫ z, ⟪v, primitiveObservable F x r z - Gibbs.primitiveMean F x r⟫ ^ 2
      ∂baseLaw F x r) =
      Var[fun a => ⟪v, gradient F a⟫; Gibbs.heatPosterior F (r ^ 2) x] := by
  let := baseLaw_isProbabilityMeasure hF hlo x r
  have hbvec : MemLp (primitiveObservable F x r) 2 (baseLaw F x r) :=
    Gibbs.primitive_memLp_two_score hF hell hlo hup x r
  rw [← base_variance_eq_physical hF x hr v,
    variance_eq_integral (hbvec.const_inner (𝕜 := ℝ) v).aemeasurable,
    integral_inner (hbvec.integrable (by norm_num))]
  simp only [inner_sub_right]
  rfl

include hell in
/-- All actual conditional variances are genuinely integrable on the
interpolation law; this is derived from the actual Bayes second moment. -/
theorem integrable_conditional_variance (x : E) {r b : ℝ} (hr : 0 < r)
    (hb : 0 ≤ b) (hb1 : b < 1) (v : E) :
    Integrable (fun y => Var[fun a => ⟪v, gradient F a⟫;
      Gibbs.heatPosterior F (r ^ 2 * conditionalVariance b) (x + (r*b) • y)])
      (interpolationLaw F x r b) := by
  have hs := integrable_conditional_second hF hell hlo hup x hr hb hb1 v
  have hm := (conditionalMean_memLp hF hell hlo hup x hr hb hb1).const_inner (𝕜 := ℝ) v
  have hi := hs.sub hm.integrable_sq
  apply hi.congr
  filter_upwards [] with y
  rw [← conditional_variance_eq_physical hF x hr hb hb1 v y]
  let := conditionalLaw_isProbabilityMeasure hF hlo x r (by linarith) hb1 y
  rw [variance_eq_sub ((observable_memLp hF hlo hup x r hb hb1 y).const_inner (𝕜 := ℝ) v),
    integral_directional_observable hF hlo hup x hr hb hb1]
  rfl

include hell in
/-- Directional law of total covariance, in the exact centered form used by
the source parent. The second term uses the physical conditional posterior. -/
theorem total_covariance_centered (x : E) {r b : ℝ} (hr : 0 < r)
    (hb : 0 ≤ b) (hb1 : b < 1) (v : E) :
    (∫ z, ⟪v, primitiveObservable F x r z - Gibbs.primitiveMean F x r⟫ ^ 2
      ∂baseLaw F x r) =
      (∫ y, ⟪v, conditionalMean F x r b y - conditionalMean F x r 0 0⟫ ^ 2
        ∂interpolationLaw F x r b) +
      ∫ y, Var[fun a => ⟪v, gradient F a⟫;
        Gibbs.heatPosterior F (r ^ 2 * conditionalVariance b) (x + (r*b) • y)]
        ∂interpolationLaw F x r b := by
  let := interpolationLaw_isProbabilityMeasure hF hlo x r b
  rw [primitive_budget_eq_variance hF hell hlo hup x hr v,
    ← base_variance_eq_physical hF x hr v,
    total_variance hF hell hlo hup x hr hb hb1 v]
  simp_rw [conditional_variance_eq_physical hF x hr hb hb1 v]
  congr 1
  rw [variance_eq_integral
    ((conditionalMean_memLp hF hell hlo hup x hr hb hb1).const_inner (𝕜 := ℝ) v).aemeasurable,
    integral_inner ((conditionalMean_memLp hF hell hlo hup x hr hb hb1).integrable (by norm_num)),
    integral_conditionalMean_eq_base_mean hF hlo hup x r (by linarith) hb1]
  simp only [conditionalMean_zero, inner_sub_right]

omit hell hup in
omit [DecidableEq ι] in
/-- Actual physical covariance is measurable in its posterior center, using
the normalized posterior kernel rather than an assumed parameter theorem. -/
theorem stronglyMeasurable_physical_variance {r : ℝ} (hr : 0 < r) (v : E) :
    StronglyMeasurable (fun x =>
      Var[fun a => ⟪v, gradient F a⟫; Gibbs.heatPosterior F (r ^ 2) x]) := by
  let k := Gibbs.normalizedPosteriorKernel F (fun _ : E => r ^ 2) id
    hF.continuous.measurable measurable_const measurable_id
  let : IsMarkovKernel k := Gibbs.normalizedPosteriorKernel_isMarkov hF (m := 0)
    le_rfl (by simpa using hlo) measurable_const measurable_id (fun _ => sq_pos_of_pos hr)
  have hg : StronglyMeasurable (fun a : E => ⟪v, gradient F a⟫) :=
    (continuous_const.inner ((InnerProductSpace.toDual ℝ E).symm.continuous.comp
      (hF.continuous_fderiv (by norm_num)))).stronglyMeasurable
  have hm : StronglyMeasurable (fun x => ∫ a, ⟪v, gradient F a⟫ ∂k x) :=
    hg.integral_kernel
  have hc : StronglyMeasurable (fun p : E × E =>
      (⟪v, gradient F p.2⟫ - ∫ a, ⟪v, gradient F a⟫ ∂k p.1) ^ 2) :=
    ((hg.comp_measurable measurable_snd).sub (hm.comp_measurable measurable_fst)).pow 2
  have hi := hc.integral_kernel_prod_right' (κ := k)
  change StronglyMeasurable (fun x => ∫ y,
    (⟪v, gradient F y⟫ - ∫ a, ⟪v, gradient F a⟫ ∂Gibbs.heatPosterior F (r^2) x)^2
      ∂Gibbs.heatPosterior F (r^2) x) at hi
  simpa only [variance_eq_integral hg.measurable.aemeasurable] using hi

include hell in
omit [DecidableEq ι] in
/-- Measurability of the source primitive budget in its actual center. -/
theorem stronglyMeasurable_primitive_budget {r : ℝ} (hr : 0 < r) (v : E) :
    StronglyMeasurable (fun x => ∫ z,
      ⟪v, primitiveObservable F x r z - Gibbs.primitiveMean F x r⟫ ^ 2 ∂baseLaw F x r) := by
  simp_rw [primitive_budget_eq_variance hF hell hlo hup _ hr v]
  exact stronglyMeasurable_physical_variance hF hlo hr v

include hell in
/-- The exact source split at b*=sqrt(1-R²), expressed entirely in primitive
budgets at the actual final child center and radius rR. -/
theorem total_covariance_mean {m : ℕ} (G : Numerics.AffineGraph.MeanGeometry m)
    (x : E) {r : ℝ} (hr : 0 < r) (v : E) :
    (∫ z, ⟪v, primitiveObservable F x r z - Gibbs.primitiveMean F x r⟫ ^ 2
      ∂baseLaw F x r) =
      (∫ y, ⟪v, conditionalMean F x r (Numerics.AffineGraph.backwardEnd G.R) y -
        conditionalMean F x r 0 0⟫ ^ 2
        ∂interpolationLaw F x r (Numerics.AffineGraph.backwardEnd G.R)) +
      ∫ y, ∫ z, ⟪v,
        primitiveObservable F (x + (r * Numerics.AffineGraph.backwardEnd G.R) • y) (r*G.R) z -
          Gibbs.primitiveMean F (x + (r * Numerics.AffineGraph.backwardEnd G.R) • y) (r*G.R)⟫ ^ 2
          ∂baseLaw F (x + (r * Numerics.AffineGraph.backwardEnd G.R) • y) (r*G.R)
        ∂interpolationLaw F x r (Numerics.AffineGraph.backwardEnd G.R) := by
  have hs := total_covariance_centered hF hell hlo hup x hr G.backwardEnd_pos.le G.backwardEnd_lt_one v
  have hw : r^2 * conditionalVariance (Numerics.AffineGraph.backwardEnd G.R) = (r*G.R)^2 := by
    rw [conditionalVariance, G.backwardEnd_sq]
    ring
  rw [hw] at hs
  rw [hs]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with y
  exact (primitive_budget_eq_variance hF hell hlo hup _ (mul_pos hr G.R_pos) v).symm

include hell in
/-- The actual final child's primitive covariance budget is integrable on
the parent interpolation law, with no extra analytic premise. -/
theorem integrable_child_budget {m : ℕ} (G : Numerics.AffineGraph.MeanGeometry m)
    (x : E) {r : ℝ} (hr : 0 < r) (v : E) :
    Integrable (fun y => ∫ z, ⟪v,
      primitiveObservable F (x + (r * Numerics.AffineGraph.backwardEnd G.R) • y) (r*G.R) z -
        Gibbs.primitiveMean F (x + (r * Numerics.AffineGraph.backwardEnd G.R) • y) (r*G.R)⟫ ^ 2
        ∂baseLaw F (x + (r * Numerics.AffineGraph.backwardEnd G.R) • y) (r*G.R))
      (interpolationLaw F x r (Numerics.AffineGraph.backwardEnd G.R)) := by
  have hi := integrable_conditional_variance hF hell hlo hup x hr
    G.backwardEnd_pos.le G.backwardEnd_lt_one v
  have hw : r^2 * conditionalVariance (Numerics.AffineGraph.backwardEnd G.R) = (r*G.R)^2 := by
    rw [conditionalVariance, G.backwardEnd_sq]
    ring
  rw [hw] at hi
  apply hi.congr
  filter_upwards [] with y
  exact (primitive_budget_eq_variance hF hell hlo hup _ (mul_pos hr G.R_pos) v).symm

end AcceleratedLogConcave.Conditional.RecursiveReferenceCovariance
