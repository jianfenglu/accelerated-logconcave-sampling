import AcceleratedLogConcave.Analysis.Poisson.WeightedPullback
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Strong derivatives of bounded matrix-field multipliers

Pointwise coefficient derivatives and a local uniform bound on their difference
quotients imply differentiation on every fixed L2 input. The proof uses dominated
convergence, and does not require differentiability in operator norm.
-/

noncomputable section
open MeasureTheory InnerProductSpace Filter
open scoped Topology RealInnerProductSpace

namespace AcceleratedLogConcave.Analysis.Poisson

private theorem tendsto_L2_of_dominated_representatives
    {X F ι : Type*} [MeasurableSpace X] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {μ : Measure X} {l : Filter ι} [l.IsCountablyGenerated]
    (f : ι → Lp F 2 μ) (g : Lp F 2 μ) (a : ι → X → F) (b : X → F)
    (hfa : ∀ t, f t =ᵐ[μ] a t) (hgb : g =ᵐ[μ] b)
    (bound : X → ℝ) (hbound : Integrable (fun x => bound x ^ 2) μ)
    (hdom : ∀ᶠ t in l, ∀ᵐ x ∂μ, ‖a t x - b x‖ ≤ bound x)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun t => a t x) l (𝓝 (b x))) :
    Tendsto f l (𝓝 g) := by
  have hmeas (t : ι) : AEStronglyMeasurable (fun x => ‖a t x - b x‖ ^ 2) μ :=
    (((Lp.aestronglyMeasurable (f t)).congr (hfa t)).sub
      ((Lp.aestronglyMeasurable g).congr hgb)).norm.pow 2
  have hi := tendsto_integral_filter_of_dominated_convergence
    (μ := μ) (F := fun t x => ‖a t x - b x‖ ^ 2) (f := fun _ => (0 : ℝ))
    (fun x => bound x ^ 2) (Eventually.of_forall hmeas) (hdom.mono (fun t ht => by
      filter_upwards [ht] with x hx
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact (sq_le_sq₀ (norm_nonneg _) ((norm_nonneg _).trans hx)).mpr hx)) hbound (by
        filter_upwards [hlim] with x hx
        have hc : Tendsto (fun _ : ι => b x) l (𝓝 (b x)) := tendsto_const_nhds
        simpa using ((hx.sub hc).norm.pow 2))
  have he (t : ι) : ‖f t - g‖ ^ 2 = ∫ x, ‖a t x - b x‖ ^ 2 ∂μ := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (f t) g, hfa t, hgb] with x hx ha hb
    rw [hx]
    simp only [Pi.sub_apply, ha, hb, real_inner_self_eq_norm_sq]
  have hs : Tendsto (fun t => ‖f t - g‖ ^ 2) l (𝓝 0) := by
    simpa only [← he, integral_zero] using hi
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hh := Real.continuous_sqrt.continuousAt.tendsto.comp hs
  change Tendsto (fun t => Real.sqrt (‖f t - g‖ ^ 2)) l (𝓝 (Real.sqrt 0)) at hh
  simpa only [Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using hh


private theorem continuousAt_clm_of_tendsto_opNorm
    {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (T : ℝ → F →L[ℝ] G) (t₀ : ℝ)
    (h : Tendsto (fun t => ‖T t - T t₀‖) (𝓝[≠] t₀) (𝓝 0)) : ContinuousAt T t₀ := by
  rw [continuousAt_iff_punctured_nhds]
  exact tendsto_iff_norm_sub_tendsto_zero.mpr h

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Pointwise matrix differentiation with locally bounded difference quotients
implies a strong derivative of the actual multiplier on each fixed L2 input. -/
theorem hasDerivAt_fieldMultiplier (μ : Measure E)
    (A : ℝ → E → E →L[ℝ] E) (hA : ∀ t, Continuous (A t))
    (M : ℝ → ℝ) (hM : ∀ t x, ‖A t x‖ ≤ M t)
    (A' : E → E →L[ℝ] E) (hA' : Continuous A') (M' : ℝ) (hM' : ∀ x, ‖A' x‖ ≤ M')
    (t₀ C : ℝ)
    (hquot : ∀ᶠ t in 𝓝[≠] t₀, ∀ x, ‖slope (fun s => A s x) t₀ t‖ ≤ C)
    (hderiv : ∀ x, HasDerivAt (fun t => A t x) (A' x) t₀) (G : Lp E 2 μ) :
    HasDerivAt (fun t => fieldMultiplier μ (A t) (hA t) (M t) (hM t) G)
      (fieldMultiplier μ A' hA' M' hM' G) t₀ := by
  rw [hasDerivAt_iff_tendsto_slope]
  let F (t : ℝ) := fieldMultiplier μ (A t) (hA t) (M t) (hM t) G
  let F' := fieldMultiplier μ A' hA' M' hM' G
  let a (t : ℝ) (x : E) := slope (fun s => A s x) t₀ t (G x)
  let b (x : E) := A' x (G x)
  have hrep (t : ℝ) : slope F t₀ t =ᵐ[μ] a t := by
    simp only [slope_def_module]
    filter_upwards [Lp.coeFn_smul ((t - t₀)⁻¹) (F t - F t₀), Lp.coeFn_sub (F t) (F t₀),
      fieldMultiplier_coe μ (A t) (hA t) (M t) (hM t) G,
      fieldMultiplier_coe μ (A t₀) (hA t₀) (M t₀) (hM t₀) G] with x hs hd ht h0
    change (F t) x = A t x (G x) at ht
    change (F t₀) x = A t₀ x (G x) at h0
    rw [hs, Pi.smul_apply, hd, Pi.sub_apply, ht, h0]
    rfl
  apply tendsto_L2_of_dominated_representatives (slope F t₀) F' a b hrep
    (fieldMultiplier_coe μ A' hA' M' hM' G) (fun x => (C + M') * ‖G x‖)
  · have hG := (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable G)).mp (Lp.memLp G)
    simpa only [mul_pow] using hG.const_mul ((C + M') ^ 2)
  · filter_upwards [hquot] with t ht
    exact Eventually.of_forall fun x => by
      change ‖slope (fun s => A s x) t₀ t (G x) - A' x (G x)‖ ≤ _
      calc
        _ ≤ ‖slope (fun s => A s x) t₀ t (G x)‖ + ‖A' x (G x)‖ := norm_sub_le _ _
        _ ≤ C * ‖G x‖ + M' * ‖G x‖ := add_le_add
          (((slope (fun s => A s x) t₀ t).le_opNorm (G x)).trans
            (mul_le_mul_of_nonneg_right (ht x) (norm_nonneg _)))
          (((A' x).le_opNorm (G x)).trans
            (mul_le_mul_of_nonneg_right (hM' x) (norm_nonneg _)))
        _ = _ := by ring
  · exact Eventually.of_forall fun x => by
      have happ : Continuous (fun T : E →L[ℝ] E => T (G x)) := continuous_id.clm_apply continuous_const
      exact (happ.tendsto (A' x)).comp (hderiv x).tendsto_slope


/-- The same local quotient bound gives operator norm continuity, although no
operator norm derivative is required or concluded. -/
theorem continuousAt_fieldMultiplier_of_quotient_bound (μ : Measure E)
    (A : ℝ → E → E →L[ℝ] E) (hA : ∀ t, Continuous (A t))
    (M : ℝ → ℝ) (hM : ∀ t x, ‖A t x‖ ≤ M t) (t₀ C : ℝ)
    (hquot : ∀ᶠ t in 𝓝[≠] t₀, ∀ x, ‖slope (fun s => A s x) t₀ t‖ ≤ C) :
    ContinuousAt (fun t => fieldMultiplier μ (A t) (hA t) (M t) (hM t)) t₀ := by
  have hn : Tendsto (fun t => ‖fieldMultiplier μ (A t) (hA t) (M t) (hM t) -
      fieldMultiplier μ (A t₀) (hA t₀) (M t₀) (hM t₀)‖) (𝓝[≠] t₀) (𝓝 0) := by
    have hlim : Tendsto (fun t : ℝ => ‖t - t₀‖ * C) (𝓝[≠] t₀) (𝓝 0) := by
      have hi : Tendsto (fun t : ℝ => t) (𝓝[≠] t₀) (𝓝 t₀) := nhdsWithin_le_nhds
      have hc : Tendsto (fun _ : ℝ => t₀) (𝓝[≠] t₀) (𝓝 t₀) := tendsto_const_nhds
      simpa using ((hi.sub hc).norm.mul_const C)
    apply squeeze_zero' (Eventually.of_forall (fun t => norm_nonneg
      (fieldMultiplier μ (A t) (hA t) (M t) (hM t) -
        fieldMultiplier μ (A t₀) (hA t₀) (M t₀) (hM t₀)))) _ hlim
    filter_upwards [hquot] with t ht
    have hC : 0 ≤ C := (norm_nonneg (slope (fun s => A s (0 : E)) t₀ t)).trans (ht 0)
    have hcoeff (x : E) : ‖A t x - A t₀ x‖ ≤ ‖t - t₀‖ * C := by
      have he : (t - t₀) • slope (fun s => A s x) t₀ t = A t x - A t₀ x :=
        sub_smul_slope (fun s => A s x) t₀ t
      rw [← he, norm_smul]
      exact mul_le_mul_of_nonneg_left (ht x) (norm_nonneg _)
    apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (norm_nonneg _) hC)
    intro G
    change ‖fieldMultiplier μ (A t) (hA t) (M t) (hM t) G -
      fieldMultiplier μ (A t₀) (hA t₀) (M t₀) (hM t₀) G‖ ≤ _
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [Lp.coeFn_sub
      (fieldMultiplier μ (A t) (hA t) (M t) (hM t) G)
      (fieldMultiplier μ (A t₀) (hA t₀) (M t₀) (hM t₀) G),
      fieldMultiplier_coe μ (A t) (hA t) (M t) (hM t) G,
      fieldMultiplier_coe μ (A t₀) (hA t₀) (M t₀) (hM t₀) G] with x hs ht h0
    rw [hs, Pi.sub_apply, ht, h0]
    change ‖(A t x - A t₀ x) (G x)‖ ≤ _
    exact ((A t x - A t₀ x).le_opNorm (G x)).trans
      (mul_le_mul_of_nonneg_right (hcoeff x) (norm_nonneg _))

  exact continuousAt_clm_of_tendsto_opNorm _ _ hn

end AcceleratedLogConcave.Analysis.Poisson
