import AcceleratedLogConcave.Analysis.Poisson.StrongMultiplier
import Mathlib.Analysis.Calculus.MeanValue

/-! Dominated differentiation of actual L2 representatives on a smooth core.
The convergence proof is factored from W04 StrongMultiplier's private helper. -/
noncomputable section
open MeasureTheory InnerProductSpace Filter Set
open scoped Topology RealInnerProductSpace
namespace AcceleratedLogConcave.Kinetic
theorem tendsto_L2_of_dominated_core_representatives
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


/-- Pointwise core differentiation with a square-integrable envelope. This also
handles the polynomial bounds of heat-evolved compact tests. -/
theorem hasDerivAt_L2_core_of_envelope {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (F : ℝ → Lp ℝ 2 μ) (G : Lp ℝ 2 μ)
    (f : ℝ → X → ℝ) (g : X → ℝ) (t : ℝ)
    (hf : ∀ s, F s =ᵐ[μ] f s) (hg : G =ᵐ[μ] g)
    (hd : ∀ x, HasDerivAt (fun s => f s x) (g x) t)
    (B : X → ℝ) (hB : Integrable (fun x => B x ^ 2) μ)
    (hquot : ∀ᶠ s in 𝓝[≠] t, ∀ᵐ x ∂μ, ‖slope (fun u => f u x) t s - g x‖ ≤ B x) :
    HasDerivAt F G t := by
  rw [hasDerivAt_iff_tendsto_slope]
  have hrep (s : ℝ) : slope F t s =ᵐ[μ] fun x => slope (fun u => f u x) t s := by
    simp only [slope_def_module]
    filter_upwards [Lp.coeFn_smul ((s-t)⁻¹) (F s-F t), Lp.coeFn_sub (F s) (F t),
      hf s, hf t] with x hs hsub hfs hft
    rw [hs, Pi.smul_apply, hsub, Pi.sub_apply, hfs, hft]
  exact tendsto_L2_of_dominated_core_representatives (slope F t) G _ g hrep hg B hB hquot
    (Eventually.of_forall fun x => (hd x).tendsto_slope)

/-- Pointwise core differentiation with a proved local slope bound gives the
strong derivative of its actual L2 classes. -/
theorem hasDerivAt_L2_core {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ]
    (F : ℝ → Lp ℝ 2 μ) (G : Lp ℝ 2 μ)
    (f : ℝ → X → ℝ) (g : X → ℝ) (t C : ℝ)
    (hf : ∀ s, F s =ᵐ[μ] f s) (hg : G =ᵐ[μ] g)
    (hd : ∀ x, HasDerivAt (fun s => f s x) (g x) t)
    (hquot : ∀ᶠ s in 𝓝[≠] t, ∀ x, ‖slope (fun u => f u x) t s‖ ≤ C)
    (hbound : ∀ x, ‖g x‖ ≤ C) : HasDerivAt F G t := by
  rw [hasDerivAt_iff_tendsto_slope]
  have hrep (s : ℝ) : slope F t s =ᵐ[μ] fun x => slope (fun u => f u x) t s := by
    simp only [slope_def_module]
    filter_upwards [Lp.coeFn_smul ((s-t)⁻¹) (F s-F t), Lp.coeFn_sub (F s) (F t),
      hf s, hf t] with x hs hsub hfs hft
    rw [hs, Pi.smul_apply, hsub, Pi.sub_apply, hfs, hft]
  apply tendsto_L2_of_dominated_core_representatives (slope F t) G _ g hrep hg
    (fun _ => 2*C) (integrable_const _)
  · filter_upwards [hquot] with s hs
    exact Eventually.of_forall fun x => (norm_sub_le _ _).trans (by linarith [hs x, hbound x])
  · exact Eventually.of_forall fun x => (hd x).tendsto_slope

/-- On a common compact smooth core the domination needed above is derived
from compactness and the mean value theorem, rather than supplied as a bound. -/
theorem hasDerivAt_L2_of_common_compact_support
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ]
    (F : ℝ → Lp ℝ 2 μ) (G : Lp ℝ 2 μ) (f g : ℝ → X → ℝ)
    {a b t : ℝ} (ht : t ∈ Ioo a b)
    (hf : ∀ s, F s =ᵐ[μ] f s) (hg : G =ᵐ[μ] g t)
    (hgc : ContinuousOn (Function.uncurry g) (Ioo a b ×ˢ (univ : Set X)))
    (hd : ∀ s ∈ Ioo a b, ∀ x, HasDerivAt (fun u => f u x) (g s x) s)
    (K : Set X) (hK : IsCompact K)
    (hzero : ∀ s ∈ Ioo a b, ∀ x ∉ K, f s x = 0) : HasDerivAt F G t := by
  have hz (s : ℝ) (hs : s ∈ Ioo a b) (x : X) (hx : x ∉ K) : g s x = 0 := by
    have he : (fun u => f u x) =ᶠ[𝓝 s] fun _ => (0 : ℝ) := by
      filter_upwards [Ioo_mem_nhds hs.1 hs.2] with u hu
      exact hzero u hu x hx
    exact (hd s hs x).unique ((hasDerivAt_const s (0 : ℝ)).congr_of_eventuallyEq he)
  let δ := min (t-a) (b-t) / 2
  have hδ : 0 < δ := div_pos (lt_min (sub_pos.mpr ht.1) (sub_pos.mpr ht.2)) (by norm_num)
  have hsub : Icc (t-δ) (t+δ) ⊆ Ioo a b := by
    intro s hs
    have hl := min_le_left (t-a) (b-t)
    have hr := min_le_right (t-a) (b-t)
    dsimp [δ] at hs
    constructor <;> linarith [hs.1, hs.2, ht.1, ht.2]
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod hK).exists_bound_of_continuousOn
    (hgc.mono (show Icc (t-δ) (t+δ) ×ˢ K ⊆ Ioo a b ×ˢ (univ : Set X) from
      fun p hp => ⟨hsub hp.1, mem_univ _⟩))
  have hbnd (s : ℝ) (hs : s ∈ Icc (t-δ) (t+δ)) (x : X) : ‖g s x‖ ≤ max C 0 := by
    by_cases hx : x ∈ K
    · exact (hC (s,x) ⟨hs,hx⟩).trans (le_max_left _ _)
    · rw [hz s (hsub hs) x hx, norm_zero]
      exact le_max_right _ _
  have htin : t ∈ Icc (t-δ) (t+δ) := ⟨by linarith, by linarith⟩
  apply hasDerivAt_L2_core μ F G f (g t) t (max C 0) hf hg (hd t ht)
  · filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds
      (Icc_mem_nhds (by linarith : t-δ<t) (by linarith : t<t+δ))] with s hs hst
    intro x
    have hne : s-t ≠ 0 := sub_ne_zero.mpr hs
    have hdiff := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun u hu => (hd u (hsub hu) x).hasDerivWithinAt) (fun u hu => hbnd u hu x)
      (convex_Icc (t-δ) (t+δ)) htin hst
    rw [slope_def_module, norm_smul, norm_inv]
    calc
      _ ≤ ‖s-t‖⁻¹ * (max C 0 * ‖s-t‖) := mul_le_mul_of_nonneg_left hdiff (inv_nonneg.mpr (norm_nonneg _))
      _ = max C 0 := by field_simp
  · exact hbnd t htin

end AcceleratedLogConcave.Kinetic
