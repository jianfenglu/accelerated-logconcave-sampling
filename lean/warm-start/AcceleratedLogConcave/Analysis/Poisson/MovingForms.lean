import Mathlib.Analysis.InnerProductSpace.LaxMilgram
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps

/-!
# Differentiating coercive variational problems on a fixed Hilbert domain

The inverses below are constructed by Lax–Milgram. Their difference identity,
norm continuity, and strong derivative are consequences of the coefficient
operators and coercivity; no derivative of an inverse is assumed.
-/

noncomputable section
open InnerProductSpace Filter
open scoped RealInnerProductSpace Topology

namespace AcceleratedLogConcave.Analysis.Poisson.MovingForms

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

private def operatorForm (B : V →L[ℝ] V) : V →L[ℝ] V →L[ℝ] ℝ :=
  (innerSL ℝ : V →L[ℝ] V →L[ℝ] ℝ).comp B

omit [CompleteSpace V] in
private theorem operatorForm_coercive (B : V →L[ℝ] V) {c : ℝ} (hc : 0 < c)
    (hB : ∀ u, c * ‖u‖ ^ 2 ≤ inner ℝ (B u) u) : IsCoercive (operatorForm B) := by
  refine ⟨c, hc, fun u => ?_⟩
  change c * ‖u‖ * ‖u‖ ≤ inner ℝ (B u) u
  nlinarith [hB u]

/-- The Lax–Milgram equivalence associated to an actual coercive coefficient operator. -/
def coerciveEquiv (B : V →L[ℝ] V) {c : ℝ} (hc : 0 < c)
    (hB : ∀ u, c * ‖u‖ ^ 2 ≤ inner ℝ (B u) u) : V ≃L[ℝ] V :=
  (operatorForm_coercive B hc hB).continuousLinearEquivOfBilin

@[simp] theorem coerciveEquiv_apply (B : V →L[ℝ] V) {c : ℝ} (hc : 0 < c)
    (hB : ∀ u, c * ‖u‖ ^ 2 ≤ inner ℝ (B u) u) (u : V) :
    coerciveEquiv B hc hB u = B u := by
  apply ext_inner_right ℝ
  intro v
  exact (operatorForm_coercive B hc hB).continuousLinearEquivOfBilin_apply u v

/-- The bounded inverse constructed from coercivity. -/
def coerciveInverse (B : V →L[ℝ] V) {c : ℝ} (hc : 0 < c)
    (hB : ∀ u, c * ‖u‖ ^ 2 ≤ inner ℝ (B u) u) : V →L[ℝ] V :=
  (coerciveEquiv B hc hB).symm.toContinuousLinearMap

@[simp] theorem apply_coerciveInverse (B : V →L[ℝ] V) {c : ℝ} (hc : 0 < c)
    (hB : ∀ u, c * ‖u‖ ^ 2 ≤ inner ℝ (B u) u) (g : V) :
    B (coerciveInverse B hc hB g) = g := by
  rw [← coerciveEquiv_apply B hc hB]
  exact (coerciveEquiv B hc hB).apply_symm_apply g

@[simp] theorem coerciveInverse_apply (B : V →L[ℝ] V) {c : ℝ} (hc : 0 < c)
    (hB : ∀ u, c * ‖u‖ ^ 2 ≤ inner ℝ (B u) u) (u : V) :
    coerciveInverse B hc hB (B u) = u := by
  rw [← coerciveEquiv_apply B hc hB]
  exact (coerciveEquiv B hc hB).symm_apply_apply u

theorem coerciveInverse_bound (B : V →L[ℝ] V) {c : ℝ} (hc : 0 < c)
    (hB : ∀ u, c * ‖u‖ ^ 2 ≤ inner ℝ (B u) u) (g : V) :
    ‖coerciveInverse B hc hB g‖ ≤ c⁻¹ * ‖g‖ := by
  let u := coerciveInverse B hc hB g
  have he : B u = g := apply_coerciveInverse B hc hB g
  have hp := hB u
  rw [he] at hp
  have hi := real_inner_le_norm g u
  rw [← div_eq_inv_mul, le_div_iff₀ hc]
  by_cases hz : ‖u‖ = 0
  · change ‖u‖ * c ≤ ‖g‖
    simp only [hz, zero_mul, norm_nonneg]
  · have hpos : 0 < ‖u‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
    change ‖u‖ * c ≤ ‖g‖
    nlinarith

theorem coerciveInverse_norm_le (B : V →L[ℝ] V) {c : ℝ} (hc : 0 < c)
    (hB : ∀ u, c * ‖u‖ ^ 2 ≤ inner ℝ (B u) u) :
    ‖coerciveInverse B hc hB‖ ≤ c⁻¹ :=
  ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.mpr hc.le) (coerciveInverse_bound B hc hB)

/-- Subtraction of the two actual variational equations gives the resolvent identity. -/
theorem coerciveInverse_sub_apply (A B : V →L[ℝ] V) {c : ℝ} (hc : 0 < c)
    (hA : ∀ u, c * ‖u‖ ^ 2 ≤ inner ℝ (A u) u)
    (hB : ∀ u, c * ‖u‖ ^ 2 ≤ inner ℝ (B u) u) (g : V) :
    coerciveInverse B hc hB g - coerciveInverse A hc hA g =
      -coerciveInverse B hc hB ((B - A) (coerciveInverse A hc hA g)) := by
  simp only [sub_apply, map_sub, apply_coerciveInverse,
    coerciveInverse_apply, neg_sub]

/-- Uniform coercivity turns coefficient perturbations into operator norm perturbations. -/
theorem coerciveInverse_sub_norm_le (A B : V →L[ℝ] V) {c : ℝ} (hc : 0 < c)
    (hA : ∀ u, c * ‖u‖ ^ 2 ≤ inner ℝ (A u) u)
    (hB : ∀ u, c * ‖u‖ ^ 2 ≤ inner ℝ (B u) u) :
    ‖coerciveInverse B hc hB - coerciveInverse A hc hA‖ ≤ (c⁻¹)^2 * ‖B - A‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro g
  rw [sub_apply, coerciveInverse_sub_apply, norm_neg]
  calc
    _ ≤ c⁻¹ * ‖(B - A) (coerciveInverse A hc hA g)‖ := coerciveInverse_bound B hc hB _
    _ ≤ c⁻¹ * (‖B - A‖ * ‖coerciveInverse A hc hA g‖) :=
      mul_le_mul_of_nonneg_left ((B - A).le_opNorm _) (inv_nonneg.mpr hc.le)
    _ ≤ c⁻¹ * (‖B - A‖ * (c⁻¹ * ‖g‖)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
        (coerciveInverse_bound A hc hA g) (norm_nonneg _)) (inv_nonneg.mpr hc.le)
    _ = _ := by ring

/-- Norm continuity of the coefficients implies norm continuity of their coercive inverses. -/
theorem continuousAt_coerciveInverse (B : ℝ → V →L[ℝ] V) {c : ℝ} (hc : 0 < c)
    (hB : ∀ t u, c * ‖u‖ ^ 2 ≤ inner ℝ (B t u) u) {t₀ : ℝ}
    (hcont : ContinuousAt B t₀) :
    ContinuousAt (fun t => coerciveInverse (B t) hc (hB t)) t₀ := by
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  apply squeeze_zero (fun _ => norm_nonneg _)
    (fun t => coerciveInverse_sub_norm_le (B t₀) (B t) hc (hB t₀) (hB t))
  have hn := tendsto_iff_norm_sub_tendsto_zero.mp hcont
  simpa only [mul_zero] using hn.const_mul ((c⁻¹)^2)

/-- Strong differentiation of the inverse solution only needs a coefficient
strong derivative along the fixed solution, plus coefficient norm continuity. -/
theorem hasDerivAt_coerciveInverse_apply (B : ℝ → V →L[ℝ] V) {c : ℝ} (hc : 0 < c)
    (hB : ∀ t u, c * ‖u‖ ^ 2 ≤ inner ℝ (B t u) u) {t₀ : ℝ}
    (hcont : ContinuousAt B t₀) (g q : V)
    (hderiv : HasDerivAt (fun t => B t (coerciveInverse (B t₀) hc (hB t₀) g)) q t₀) :
    HasDerivAt (fun t => coerciveInverse (B t) hc (hB t) g)
      (-coerciveInverse (B t₀) hc (hB t₀) q) t₀ := by
  rw [hasDerivAt_iff_tendsto_slope]
  have hi : Tendsto (fun t => coerciveInverse (B t) hc (hB t)) (𝓝[≠] t₀)
      (𝓝 (coerciveInverse (B t₀) hc (hB t₀))) :=
    (continuousAt_coerciveInverse B hc hB hcont).tendsto.mono_left nhdsWithin_le_nhds
  have happ : Continuous (fun p : (V →L[ℝ] V) × V => p.1 p.2) :=
    continuous_fst.clm_apply continuous_snd
  have hh := ((happ.tendsto _).comp (hi.prodMk_nhds hderiv.tendsto_slope)).neg
  apply hh.congr'
  filter_upwards [] with t
  simp only [Function.comp_apply, slope, vsub_eq_sub, coerciveInverse_sub_apply, sub_apply,
    map_smul, smul_neg]


section CommonDomain
variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [NormedAddCommGroup K] [InnerProductSpace ℝ K]

/-- Riesz representation of the energy form on the fixed Hilbert domain. -/
def energyCoefficient (D : V →L[ℝ] K) : V →L[ℝ] V :=
  continuousLinearMapOfBilin
    ((D.precomp ℝ).comp ((innerSL ℝ : K →L[ℝ] K →L[ℝ] ℝ).comp D))

theorem energyCoefficient_inner (D : V →L[ℝ] K) (u v : V) :
    inner ℝ (energyCoefficient D u) v = inner ℝ (D u) (D v) :=
  continuousLinearMapOfBilin_apply _ u v

theorem energyCoefficient_coercive (D : V →L[ℝ] K) {c : ℝ}
    (hD : ∀ u, c * ‖u‖ ^ 2 ≤ ‖D u‖ ^ 2) :
    ∀ u, c * ‖u‖ ^ 2 ≤ inner ℝ (energyCoefficient D u) u := by
  intro u
  rw [energyCoefficient_inner, real_inner_self_eq_norm_sq]
  exact hD u

/-- The fixed ambient forcing, represented in the common Hilbert domain. -/
def variationalRHS (i : V →L[ℝ] H) (g : H) : V :=
  (toDual ℝ V).symm ((innerSL ℝ g).comp i)

theorem variationalRHS_inner (i : V →L[ℝ] H) (g : H) (v : V) :
    inner ℝ (variationalRHS i g) v = inner ℝ g (i v) := toDual_symm_apply

/-- The solution on a fixed Hilbert domain, with a bounded gradient and inclusion. -/
def commonDomainSolution (D : V →L[ℝ] K) (i : V →L[ℝ] H) {c : ℝ} (hc : 0 < c)
    (hD : ∀ u, c * ‖u‖ ^ 2 ≤ ‖D u‖ ^ 2) (g : H) : V :=
  coerciveInverse (energyCoefficient D) hc (energyCoefficient_coercive D hD)
    (variationalRHS i g)

theorem commonDomainSolution_weak (D : V →L[ℝ] K) (i : V →L[ℝ] H)
    {c : ℝ} (hc : 0 < c) (hD : ∀ u, c * ‖u‖ ^ 2 ≤ ‖D u‖ ^ 2) (g : H) (v : V) :
    inner ℝ (D (commonDomainSolution D i hc hD g)) (D v) = inner ℝ g (i v) := by
  rw [← energyCoefficient_inner]
  change inner ℝ (energyCoefficient D
    (coerciveInverse (energyCoefficient D) hc (energyCoefficient_coercive D hD)
      (variationalRHS i g))) v = _
  rw [apply_coerciveInverse, variationalRHS_inner]

theorem commonDomainSolution_unique (D : V →L[ℝ] K) (i : V →L[ℝ] H)
    {c : ℝ} (hc : 0 < c) (hD : ∀ u, c * ‖u‖ ^ 2 ≤ ‖D u‖ ^ 2) (g : H)
    (u : V) (hu : ∀ v, inner ℝ (D u) (D v) = inner ℝ g (i v)) :
    u = commonDomainSolution D i hc hD g := by
  apply (coerciveEquiv (energyCoefficient D) hc (energyCoefficient_coercive D hD)).injective
  simp only [coerciveEquiv_apply]
  apply ext_inner_right ℝ
  intro v
  rw [energyCoefficient_inner, energyCoefficient_inner, hu v,
    commonDomainSolution_weak]

/-- Differentiation for bounded gradient forms on a fixed common Hilbert domain. -/
theorem hasDerivAt_commonDomainSolution (D : ℝ → V →L[ℝ] K) (i : V →L[ℝ] H)
    {c : ℝ} (hc : 0 < c) (hD : ∀ t u, c * ‖u‖ ^ 2 ≤ ‖D t u‖ ^ 2)
    {t₀ : ℝ} (hcont : ContinuousAt (fun t => energyCoefficient (D t)) t₀)
    (g : H) (q : V)
    (hderiv : HasDerivAt (fun t => energyCoefficient (D t)
      (commonDomainSolution (D t₀) i hc (hD t₀) g)) q t₀) :
    HasDerivAt (fun t => commonDomainSolution (D t) i hc (hD t) g)
      (-coerciveInverse (energyCoefficient (D t₀)) hc
        (energyCoefficient_coercive (D t₀) (hD t₀)) q) t₀ :=
  hasDerivAt_coerciveInverse_apply (fun t => energyCoefficient (D t)) hc
    (fun t => energyCoefficient_coercive (D t) (hD t)) hcont (variationalRHS i g) q hderiv

end CommonDomain

end AcceleratedLogConcave.Analysis.Poisson.MovingForms
