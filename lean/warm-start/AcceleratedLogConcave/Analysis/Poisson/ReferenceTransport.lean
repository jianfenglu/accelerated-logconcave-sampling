import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# Density continuity equations tested against moving compact tests

The temporal differentiation theorem uses a common compact spatial support and
continuity only on the open time strip. All integral bounds are derived from
compactness. The spatial identity is genuine Euclidean integration by parts.
-/

noncomputable section
open MeasureTheory InnerProductSpace Set Filter
open scoped RealInnerProductSpace Topology

namespace AcceleratedLogConcave.Analysis.Poisson

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Differentiation of a moving compact integral, with no global derivative bound. -/
theorem hasDerivAt_integral_of_common_compact_support
    (F F' : ℝ → E → ℝ) {a b t : ℝ} (ht : t ∈ Ioo a b)
    (hF : ContinuousOn (Function.uncurry F) (Ioo a b ×ˢ (univ : Set E)))
    (hF' : ContinuousOn (Function.uncurry F') (Ioo a b ×ˢ (univ : Set E)))
    (hd : ∀ s ∈ Ioo a b, ∀ x, HasDerivAt (fun r => F r x) (F' s x) s)
    (K : Set E) (hK : IsCompact K)
    (hzero : ∀ s ∈ Ioo a b, ∀ x ∉ K, F s x = 0) :
    HasDerivAt (fun s => ∫ x, F s x) (∫ x, F' t x) t := by
  have hc (s : ℝ) (hs : s ∈ Ioo a b) : Continuous (F s) :=
    hF.comp_continuous (continuous_const.prodMk continuous_id) (fun x => ⟨hs, mem_univ x⟩)
  have hc' (s : ℝ) (hs : s ∈ Ioo a b) : Continuous (F' s) :=
    hF'.comp_continuous (continuous_const.prodMk continuous_id) (fun x => ⟨hs, mem_univ x⟩)
  have hz' (s : ℝ) (hs : s ∈ Ioo a b) (x : E) (hx : x ∉ K) : F' s x = 0 := by
    have he : (fun r => F r x) =ᶠ[𝓝 s] fun _ => (0 : ℝ) := by
      filter_upwards [Ioo_mem_nhds hs.1 hs.2] with r hr
      exact hzero r hr x hx
    exact (hd s hs x).unique ((hasDerivAt_const s (0 : ℝ)).congr_of_eventuallyEq he)
  let δ := min (t - a) (b - t) / 2
  have hδ : 0 < δ := by
    exact div_pos (lt_min (sub_pos.mpr ht.1) (sub_pos.mpr ht.2)) (by norm_num)
  have hsub : Icc (t - δ) (t + δ) ⊆ Ioo a b := by
    intro s hs
    have h₁ := min_le_left (t - a) (b - t)
    have h₂ := min_le_right (t - a) (b - t)
    dsimp [δ] at hs
    constructor <;> linarith [hs.1, hs.2, ht.1, ht.2]
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod hK).exists_bound_of_continuousOn
    (hF'.mono (show Icc (t - δ) (t + δ) ×ˢ K ⊆ Ioo a b ×ˢ (univ : Set E) from
      fun p hp => ⟨hsub hp.1, mem_univ _⟩))
  have hbound : Integrable (K.indicator (fun _ : E => C)) :=
    (integrable_indicator_iff hK.measurableSet).mpr
      (integrableOn_const (C := C) hK.measure_ne_top)
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Icc_mem_nhds (by linarith : t - δ < t) (by linarith : t < t + δ))
    (by
      filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
      exact (hc s hs).aestronglyMeasurable)
    ((hc t ht).integrable_of_hasCompactSupport (HasCompactSupport.intro hK (hzero t ht)))
    (hc' t ht).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x s hs => by
      by_cases hx : x ∈ K
      · simpa only [Set.indicator_of_mem hx, Function.uncurry_apply_pair] using hC (s, x) ⟨hs, hx⟩
      · simp only [Set.indicator_of_notMem hx, hz' s (hsub hs) x hx, norm_zero, le_refl])
    hbound (Filter.Eventually.of_forall fun x s hs => hd s (hsub hs) x)).2

/-- Endpoint continuity follows from the same common compact support. -/
theorem continuousOn_integral_of_common_compact_support
    (F : ℝ → E → ℝ) {a b : ℝ}
    (hF : ContinuousOn (Function.uncurry F) (Icc a b ×ˢ (univ : Set E)))
    (K : Set E) (hK : IsCompact K)
    (hzero : ∀ s ∈ Icc a b, ∀ x ∉ K, F s x = 0) :
    ContinuousOn (fun s => ∫ x, F s x) (Icc a b) := by
  have hc (s : ℝ) (hs : s ∈ Icc a b) : Continuous (F s) :=
    hF.comp_continuous (continuous_const.prodMk continuous_id) (fun x => ⟨hs, mem_univ x⟩)
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod hK).exists_bound_of_continuousOn
    (hF.mono (show Icc a b ×ˢ K ⊆ Icc a b ×ˢ (univ : Set E) from
      fun p hp => ⟨hp.1, mem_univ _⟩))
  apply continuousOn_of_dominated (bound := K.indicator (fun _ : E => C))
    (fun s hs => (hc s hs).aestronglyMeasurable)
  · intro s hs
    exact Filter.Eventually.of_forall fun x => by
      by_cases hx : x ∈ K
      · simpa only [Set.indicator_of_mem hx, Function.uncurry_apply_pair] using hC (s, x) ⟨hs, hx⟩
      · simp only [Set.indicator_of_notMem hx, hzero s hs x hx, norm_zero, le_refl]
  · exact (integrable_indicator_iff hK.measurableSet).mpr
      (integrableOn_const (C := C) hK.measure_ne_top)
  · exact Filter.Eventually.of_forall fun x => hF.comp
      (continuous_id.prodMk continuous_const).continuousOn (fun s hs => ⟨hs, mem_univ x⟩)

/-- Euclidean divergence written in an actual orthonormal coordinate basis. -/
def fluxDivergence (J : E → E) (x : E) : ℝ :=
  ∑ i, fderiv ℝ (fun y => inner ℝ (stdOrthonormalBasis ℝ E i) (J y)) x
    (stdOrthonormalBasis ℝ E i)

/-- Compact-test integration by parts for the actual Euclidean flux divergence. -/
theorem fluxDivergence_compact_ibp (J : E → E) (η : E → ℝ)
    (hJ : ContDiff ℝ 1 J) (hη : ContDiff ℝ 1 η) (hηK : HasCompactSupport η) :
    Integrable (fun x => fluxDivergence J x * η x) ∧
    Integrable (fun x => fderiv ℝ η x (J x)) ∧
    (∫ x, fluxDivergence J x * η x) = -(∫ x, fderiv ℝ η x (J x)) := by
  let e := stdOrthonormalBasis ℝ E
  let j := fun i x => inner ℝ (e i) (J x)
  have hj (i) : ContDiff ℝ 1 (j i) := (innerSL ℝ (e i)).contDiff.comp hJ
  have hleft (i) : Integrable (fun x => fderiv ℝ (j i) x (e i) * η x) :=
    ((((hj i).continuous_fderiv one_ne_zero).clm_apply continuous_const).mul hη.continuous).integrable_of_hasCompactSupport hηK.mul_left
  have hright (i) : Integrable (fun x => j i x * fderiv ℝ η x (e i)) :=
    ((hj i).continuous.mul ((hη.continuous_fderiv one_ne_zero).clm_apply continuous_const)).integrable_of_hasCompactSupport (hηK.fderiv_apply ℝ (e i)).mul_left
  have hprod (i) : Integrable (fun x => j i x * η x) :=
    ((hj i).continuous.mul hη.continuous).integrable_of_hasCompactSupport hηK.mul_left
  have hibp (i) : (∫ x, fderiv ℝ (j i) x (e i) * η x) =
      -(∫ x, j i x * fderiv ℝ η x (e i)) := by
    have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (hleft i) (hright i)
      (hprod i) (fun x _ => (hj i).differentiable_one x)
      (fun x _ => hη.differentiable_one x)
    linarith
  have heq (x : E) : (∑ i, j i x * fderiv ℝ η x (e i)) = fderiv ℝ η x (J x) := by
    have h := congrArg (fderiv ℝ η x) (e.sum_repr' (J x))
    simpa only [map_sum, map_smul, smul_eq_mul] using h
  have hli : Integrable (fun x => fluxDivergence J x * η x) := by
    simpa only [fluxDivergence, Finset.sum_mul] using integrable_finsetSum _ (fun i _ => hleft i)
  have hri : Integrable (fun x => fderiv ℝ η x (J x)) := by
    simp_rw [← heq]
    exact integrable_finsetSum _ (fun i _ => hright i)
  refine ⟨hli, hri, ?_⟩
  calc
    _ = ∫ x, ∑ i, fderiv ℝ (j i) x (e i) * η x := by
      simp only [fluxDivergence, Finset.sum_mul, j, e]
    _ = ∑ i, ∫ x, fderiv ℝ (j i) x (e i) * η x :=
      integral_finsetSum _ (fun i _ => hleft i)
    _ = ∑ i, -(∫ x, j i x * fderiv ℝ η x (e i)) := Finset.sum_congr rfl (fun i _ => hibp i)
    _ = -(∫ x, ∑ i, j i x * fderiv ℝ η x (e i)) := by
      rw [integral_finsetSum _ (fun i _ => hright i), Finset.sum_neg_distrib]
    _ = _ := by simp_rw [heq]

/-- The pointwise density continuity equation implies the moving compact-test identity.
Only local joint continuity on the open time strip is required. -/
theorem hasDerivAt_density_test_integral
    (ρ ρt η ηt : ℝ → E → ℝ) (v : E → E) {a b t : ℝ} (ht : t ∈ Ioo a b)
    (hρ : ContinuousOn (Function.uncurry ρ) (Ioo a b ×ˢ (univ : Set E)))
    (hρt : ContinuousOn (Function.uncurry ρt) (Ioo a b ×ˢ (univ : Set E)))
    (hη : ContinuousOn (Function.uncurry η) (Ioo a b ×ˢ (univ : Set E)))
    (hηt : ContinuousOn (Function.uncurry ηt) (Ioo a b ×ˢ (univ : Set E)))
    (hdρ : ∀ s ∈ Ioo a b, ∀ x, HasDerivAt (fun r => ρ r x) (ρt s x) s)
    (hdη : ∀ s ∈ Ioo a b, ∀ x, HasDerivAt (fun r => η r x) (ηt s x) s)
    (hρsp : ContDiff ℝ 1 (ρ t)) (hv : ContDiff ℝ 1 v) (hηsp : ContDiff ℝ 1 (η t))
    (K : Set E) (hK : IsCompact K)
    (hzero : ∀ s ∈ Ioo a b, ∀ x ∉ K, η s x = 0)
    (hPDE : ∀ x, ρt t x + fluxDivergence (fun y => ρ t y • v y) x = 0) :
    HasDerivAt (fun s => ∫ x, ρ s x * η s x)
      (∫ x, ρ t x * (ηt t x + fderiv ℝ (η t) x (v x))) t := by
  have hd := hasDerivAt_integral_of_common_compact_support
    (fun s x => ρ s x * η s x) (fun s x => ρt s x * η s x + ρ s x * ηt s x) ht
    (hρ.mul hη) ((hρt.mul hη).add (hρ.mul hηt))
    (fun s hs x => (hdρ s hs x).mul (hdη s hs x)) K hK
    (fun s hs x hx => by rw [hzero s hs x hx, mul_zero])
  have hηK : HasCompactSupport (η t) := HasCompactSupport.intro hK (hzero t ht)
  have hηtK : HasCompactSupport (ηt t) := by
    apply HasCompactSupport.intro hK
    intro x hx
    have he : (fun r => η r x) =ᶠ[𝓝 t] fun _ => (0 : ℝ) := by
      filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
      exact hzero s hs x hx
    exact (hdη t ht x).unique ((hasDerivAt_const t (0 : ℝ)).congr_of_eventuallyEq he)
  have hcρt : Continuous (ρt t) := hρt.comp_continuous
    (continuous_const.prodMk continuous_id) (fun x => ⟨ht, mem_univ x⟩)
  have hcηt : Continuous (ηt t) := hηt.comp_continuous
    (continuous_const.prodMk continuous_id) (fun x => ⟨ht, mem_univ x⟩)
  have hi₁ : Integrable (fun x => ρt t x * η t x) :=
    (hcρt.mul hηsp.continuous).integrable_of_hasCompactSupport hηK.mul_left
  have hi₂ : Integrable (fun x => ρ t x * ηt t x) :=
    (hρsp.continuous.mul hcηt).integrable_of_hasCompactSupport hηtK.mul_left
  have hibp := fluxDivergence_compact_ibp (fun x => ρ t x • v x) (η t)
    (hρsp.smul hv) hηsp hηK
  have hi₃ : Integrable (fun x => ρ t x * fderiv ℝ (η t) x (v x)) := by
    simpa only [map_smul, smul_eq_mul] using hibp.2.1
  have he : (∫ x, ρt t x * η t x) = ∫ x, ρ t x * fderiv ℝ (η t) x (v x) := by
    calc
      _ = -(∫ x, fluxDivergence (fun y => ρ t y • v y) x * η t x) := by
        rw [← integral_neg]
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun x => by
          have h := hPDE x
          have hr : ρt t x = -fluxDivergence (fun y => ρ t y • v y) x := by linarith
          dsimp only
          rw [hr, neg_mul]
      _ = _ := by rw [hibp.2.2, neg_neg]; simp only [map_smul, smul_eq_mul]
  have hder : (∫ x, ρt t x * η t x + ρ t x * ηt t x) =
      ∫ x, ρ t x * (ηt t x + fderiv ℝ (η t) x (v x)) := by
    rw [integral_add hi₁ hi₂, he]
    simp_rw [mul_add]
    rw [integral_add hi₂ hi₃, add_comm]
  rw [hder] at hd
  exact hd

end AcceleratedLogConcave.Analysis.Poisson
