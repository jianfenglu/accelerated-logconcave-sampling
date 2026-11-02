import AcceleratedLogConcave.Kinetic.Reheating.GaussianPoincare
import AcceleratedLogConcave.Kinetic.Reheating.ProductAverage
import AcceleratedLogConcave.Kinetic.Reheating.HeatChannel

/-! Gaussian conditional Poincare for actual heat pullbacks. Classical compact
tests are extended through the genuine target weighted-gradient graph. -/
noncomputable section
open MeasureTheory ProbabilityTheory InnerProductSpace
open scoped RealInnerProductSpace ContDiff
namespace AcceleratedLogConcave.Kinetic.Reheating
open Analysis.WeightedGradient
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [MeasurableSpace E] [BorelSpace E] in
theorem gradient_translate_scale (φ : E → ℝ) (hφ : ContDiff ℝ 1 φ) (x e : E) (r : ℝ) :
    gradient (fun y => φ (x+r•y)) e = r • gradient φ (x+r•e) := by
  apply ext_inner_right ℝ
  intro v
  rw [inner_gradient_left, real_inner_smul_left, inner_gradient_left]
  have hd := ((hφ.differentiable_one (x+r•e)).hasFDerivAt).comp e
    (((hasFDerivAt_id (𝕜 := ℝ) e).const_smul r).const_add x)
  simpa only [Function.comp_def, Pi.smul_apply, id_eq,
    ContinuousLinearMap.comp_apply, smul_apply,
    ContinuousLinearMap.id_apply, map_smul, smul_eq_mul] using
    congrArg (fun L : E →L[ℝ] ℝ => L v) hd.fderiv

/-- Conditional Gaussian Poincare with the exact heat variance factor. -/
theorem gaussian_translated_compact_poincare (φ : E → ℝ) (hφ : ContDiff ℝ 1 φ)
    (hc : HasCompactSupport φ) (x : E) (t : ℝ) (ht : 0 ≤ t) :
    (∫ e, (φ (x+Real.sqrt t•e) - ∫ y, φ (x+Real.sqrt t•y) ∂stdGaussian E)^2 ∂stdGaussian E) ≤
      t * ∫ e, ‖gradient φ (x+Real.sqrt t•e)‖^2 ∂stdGaussian E := by
  have hgcont : Continuous (gradient φ) :=
    (toDual ℝ E).symm.continuous.comp (hφ.continuous_fderiv one_ne_zero)
  have hgcompact : HasCompactSupport (gradient φ) := by
    refine HasCompactSupport.of_support_subset_isCompact hc.isCompact ?_
    intro y hy
    by_contra hn
    exact hy (by simp [gradient, fderiv_of_notMem_tsupport ℝ hn])
  obtain ⟨C,hC⟩ := hc.exists_bound_of_continuous hφ.continuous
  obtain ⟨D,hD⟩ := hgcompact.exists_bound_of_continuous hgcont
  have hψ : ContDiff ℝ 1 (fun e => φ (x+Real.sqrt t•e)) :=
    hφ.comp (contDiff_const.add (contDiff_const.smul contDiff_id))
  have hp : MemLp (fun e => φ (x+Real.sqrt t•e)) 2 (stdGaussian E) :=
    MemLp.of_bound hψ.continuous.aestronglyMeasurable C (Filter.Eventually.of_forall fun e => hC _)
  have hq : MemLp (gradient (fun e => φ (x+Real.sqrt t•e))) 2 (stdGaussian E) := by
    have he : gradient (fun e => φ (x+Real.sqrt t•e)) =
        fun e => Real.sqrt t • gradient φ (x+Real.sqrt t•e) :=
      funext fun e => gradient_translate_scale φ hφ x e _
    rw [he]
    apply MemLp.of_bound (by fun_prop : Continuous (fun e =>
      Real.sqrt t • gradient φ (x+Real.sqrt t•e))).aestronglyMeasurable (Real.sqrt t*D)
    exact Filter.Eventually.of_forall fun e => by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
      exact mul_le_mul_of_nonneg_left (hD _) (Real.sqrt_nonneg _)
  have h := gaussian_c1_poincare _ hψ hp hq
  have he : (∫ e, ‖gradient (fun e => φ (x+Real.sqrt t•e)) e‖^2 ∂stdGaussian E) =
      t * ∫ e, ‖gradient φ (x+Real.sqrt t•e)‖^2 ∂stdGaussian E := by
    simp_rw [gradient_translate_scale φ hφ, norm_smul, mul_pow,
    Real.norm_eq_abs, sq_abs, Real.sq_sqrt ht]
    rw [integral_const_mul]
  rw [he] at h
  exact h

variable (μ : Measure E) [IsProbabilityMeasure μ]

/-- Actual scalar heat-observation pullback before adjoining momentum. -/
def heatScalarPullback (t : ℝ) : Lp ℝ 2 (heatedLaw μ t) →ₗᵢ[ℝ]
    Lp ℝ 2 (μ.prod (stdGaussian E)) :=
  Lp.compMeasurePreservingₗᵢ ℝ (fun z : E×E => z.1+Real.sqrt t•z.2)
    ((by fun_prop : Measurable (fun z : E×E => z.1+Real.sqrt t•z.2)).measurePreserving (μ.prod (stdGaussian E)))

/-- The same isometric pullback for the actual weak gradient. -/
def heatVectorPullback (t : ℝ) : Lp E 2 (heatedLaw μ t) →ₗᵢ[ℝ]
    Lp E 2 (μ.prod (stdGaussian E)) :=
  Lp.compMeasurePreservingₗᵢ ℝ (fun z : E×E => z.1+Real.sqrt t•z.2)
    ((by fun_prop : Measurable (fun z : E×E => z.1+Real.sqrt t•z.2)).measurePreserving (μ.prod (stdGaussian E)))

/-- Subtracting the genuine conditional Gaussian average of the heat pullback. -/
def heatCenteredPullback (t : ℝ) : Lp ℝ 2 (heatedLaw μ t) →L[ℝ]
    Lp ℝ 2 (μ.prod (stdGaussian E)) :=
  (heatScalarPullback μ t).toContinuousLinearMap -
    (productEmbedding μ (stdGaussian E)).toContinuousLinearMap.comp
      ((productAverage μ (stdGaussian E)).comp (heatScalarPullback μ t).toContinuousLinearMap)

theorem heatCenteredPullback_coe_of_ae (t : ℝ) (f : Lp ℝ 2 (heatedLaw μ t))
    (φ : E → ℝ) (hφ : f =ᵐ[heatedLaw μ t] φ) :
    heatCenteredPullback μ t f =ᵐ[μ.prod (stdGaussian E)] fun z =>
      φ (z.1+Real.sqrt t•z.2) - ∫ y, φ (z.1+Real.sqrt t•y) ∂stdGaussian E := by
  let hp : MeasurePreserving (fun z : E×E => z.1+Real.sqrt t•z.2)
      (μ.prod (stdGaussian E)) (heatedLaw μ t) :=
    (by fun_prop : Measurable (fun z : E×E => z.1+Real.sqrt t•z.2)).measurePreserving _
  have hB : heatScalarPullback μ t f =ᵐ[μ.prod (stdGaussian E)]
      fun z => φ (z.1+Real.sqrt t•z.2) :=
    (Lp.coeFn_compMeasurePreserving f hp).trans (hp.quasiMeasurePreserving.ae hφ)
  have hA := productAverage_coe μ (stdGaussian E) (heatScalarPullback μ t f)
  have hAE : productAverage μ (stdGaussian E) (heatScalarPullback μ t f) =ᵐ[μ]
      fun x => ∫ y, φ (x+Real.sqrt t•y) ∂stdGaussian E := by
    filter_upwards [hA, Measure.ae_ae_of_ae_prod hB] with x hx hy
    rw [hx, integral_congr_ae hy]
  have hI := Lp.coeFn_compMeasurePreserving
    (productAverage μ (stdGaussian E) (heatScalarPullback μ t f))
    (measurePreserving_fst (ν := stdGaussian E))
  filter_upwards [Lp.coeFn_sub (heatScalarPullback μ t f)
    (productEmbedding μ (stdGaussian E) (productAverage μ (stdGaussian E) (heatScalarPullback μ t f))),
    hB, hI, measurePreserving_fst.quasiMeasurePreserving.ae hAE] with z hz hBz hIz hAz
  change (heatScalarPullback μ t f - productEmbedding μ (stdGaussian E)
    (productAverage μ (stdGaussian E) (heatScalarPullback μ t f))) z = _ at hz
  change (productEmbedding μ (stdGaussian E)
    (productAverage μ (stdGaussian E) (heatScalarPullback μ t f))) z = _ at hIz
  change (productAverage μ (stdGaussian E) (heatScalarPullback μ t f)) z.1 = _ at hAz
  change (heatScalarPullback μ t f - productEmbedding μ (stdGaussian E)
    (productAverage μ (stdGaussian E) (heatScalarPullback μ t f))) z = _
  rw [hz]
  simp only [Pi.sub_apply, hBz, hIz, Function.comp_apply, hAz]

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E]
    [IsProbabilityMeasure μ] in
private theorem norm_sq_integral {Y : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
    (f : Lp Y 2 μ) : ‖f‖^2 = ∫ x, ‖f x‖^2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  simp only [real_inner_self_eq_norm_sq]

/-- The compact smooth graph satisfies the exact conditional displacement bound. -/
theorem heatCenteredPullback_compact_bound (t : ℝ) (ht : 0 ≤ t)
    (f : Lp ℝ 2 (heatedLaw μ t)) (G : Lp E 2 (heatedLaw μ t))
    (φ : E → ℝ) (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ)
    (hf : f =ᵐ[heatedLaw μ t] φ) (hG : G =ᵐ[heatedLaw μ t] gradient φ) :
    ‖heatCenteredPullback μ t f‖^2 ≤ t * ‖G‖^2 := by
  let L := heatCenteredPullback μ t f
  let H := heatVectorPullback μ t G
  let hp : MeasurePreserving (fun z : E×E => z.1+Real.sqrt t•z.2)
      (μ.prod (stdGaussian E)) (heatedLaw μ t) :=
    (by fun_prop : Measurable (fun z : E×E => z.1+Real.sqrt t•z.2)).measurePreserving _
  have hH : H =ᵐ[μ.prod (stdGaussian E)] fun z => gradient φ (z.1+Real.sqrt t•z.2) :=
    (Lp.coeFn_compMeasurePreserving G hp).trans (hp.quasiMeasurePreserving.ae hG)
  have hL := heatCenteredPullback_coe_of_ae μ t f φ hf
  have hLi : Integrable (fun z => ‖L z‖^2) (μ.prod (stdGaussian E)) :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable L)).mp (Lp.memLp L)
  have hHi : Integrable (fun z => ‖H z‖^2) (μ.prod (stdGaussian E)) :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable H)).mp (Lp.memLp H)
  have hpw : ∀ᵐ x ∂μ, (∫ e, ‖L (x,e)‖^2 ∂stdGaussian E) ≤
      t * ∫ e, ‖H (x,e)‖^2 ∂stdGaussian E := by
    filter_upwards [Measure.ae_ae_of_ae_prod hL, Measure.ae_ae_of_ae_prod hH] with x hx hy
    have hle : (∫ e, ‖L (x,e)‖^2 ∂stdGaussian E) =
        ∫ e, (φ (x+Real.sqrt t•e) - ∫ y, φ (x+Real.sqrt t•y) ∂stdGaussian E)^2 ∂stdGaussian E := by
      apply integral_congr_ae
      filter_upwards [hx] with e he
      change L (x,e) = _ at he
      rw [he, Real.norm_eq_abs, sq_abs]
    have hre : (∫ e, ‖H (x,e)‖^2 ∂stdGaussian E) =
        ∫ e, ‖gradient φ (x+Real.sqrt t•e)‖^2 ∂stdGaussian E := by
      apply integral_congr_ae
      filter_upwards [hy] with e he
      rw [he]
    rw [hle, hre]
    exact gaussian_translated_compact_poincare φ hφ hc x t ht
  have hi := integral_mono_ae hLi.integral_prod_left (hHi.integral_prod_left.const_mul t) hpw
  rw [integral_const_mul, ← integral_prod _ hLi, ← integral_prod _ hHi,
    ← norm_sq_integral, ← norm_sq_integral] at hi
  simpa only [H, (heatVectorPullback μ t).norm_map] using hi

private theorem graph_closure_norm_bound {H K F : Type*}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup K] [NormedSpace ℝ K]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (D : H →ₗ.[ℝ] K) (T : H →L[ℝ] F) (k : ℝ)
    (hb : ∀ p ∈ D.graph, ‖T p.1‖^2 ≤ k*‖p.2‖^2)
    {p : H×K} (hp : p ∈ D.graph.topologicalClosure) :
    ‖T p.1‖^2 ≤ k*‖p.2‖^2 := by
  have hc : IsClosed {p : H×K | ‖T p.1‖^2 ≤ k*‖p.2‖^2} :=
    isClosed_le ((T.continuous.comp continuous_fst).norm.pow 2)
      (continuous_const.mul (continuous_snd.norm.pow 2))
  exact hc.closure_subset_iff.mpr hb hp

/-- Gaussian conditional Poincare on the genuine target weak-gradient domain.
The domain membership is used through its proved compact smooth graph closure. -/
theorem heatCenteredPullback_closedGradient (t : ℝ) (ht : 0 ≤ t)
    (V : E → ℝ) (hV : ContDiff ℝ 1 V)
    (hI : Integrable (fun x => Real.exp (-V x)))
    (hμ : heatedLaw μ t = volume.tilted (fun x => -V x))
    (u : Sobolev (heatedLaw μ t) V hV hI hμ) :
    ‖heatCenteredPullback μ t (u : Lp ℝ 2 (heatedLaw μ t))‖^2 ≤
      t * ‖closedGradient (heatedLaw μ t) V hV hI hμ u‖^2 := by
  have hu := (closedGradient (heatedLaw μ t) V hV hI hμ).mem_graph u
  rw [closedGradient_graph_eq] at hu
  apply graph_closure_norm_bound (compactGradient (heatedLaw μ t) V hV hI hμ)
    (heatCenteredPullback μ t) t ?_ hu
  rintro ⟨f,G⟩ hfg
  obtain ⟨φ,hφ,hc,hf,hG⟩ := (mem_compactGradient_graph (heatedLaw μ t) V hV hI hμ f G).mp hfg
  exact heatCenteredPullback_compact_bound μ t ht f G φ (hφ.of_le (by norm_num)) hc hf hG

end AcceleratedLogConcave.Kinetic.Reheating
