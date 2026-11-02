import AcceleratedLogConcave.Conditional.Flow.WeightedDerivative
import AcceleratedLogConcave.Conditional.Flow.Continuity

/-! Actual observable-weighted weak continuity, with its full conditional
flux. The current decomposition and positive adjoint sign are independent
consequences, not assumptions of this equation. -/
noncomputable section
open Set Function Filter MeasureTheory ProbabilityTheory
open scoped Topology RealInnerProductSpace

namespace AcceleratedLogConcave.Conditional
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
local notation "E" => EuclideanSpace ℝ ι

theorem hasDerivAt_weightedInterpolation_test
    {F : E → ℝ} (hF : ContDiff ℝ 2 F) {ell : ℝ}
    (hlo : ∀ z a, 0 ≤ fderiv ℝ (fderiv ℝ F) z a a)
    (hup : ∀ z a, fderiv ℝ (fderiv ℝ F) z a a ≤ ell * ‖a‖ ^ 2)
    (x u : E) (r : ℝ) {a b ρ : ℝ} (ha : -1 < a) (hb : b < 1)
    (hρ : ρ ∈ Ioo a b) (ψ : ℝ × E → ℝ) (hψ : Continuous ψ)
    (hψd : ∀ p, p.1 ∈ Ioo a b → ContDiffAt ℝ 1 ψ p)
    (hψK : ∃ K : Set E, IsCompact K ∧ ∀ t y, y ∉ K → ψ (t, y) = 0) :
    HasDerivAt (fun s => ∫ y, inner ℝ u (conditionalMean F x r s y) * ψ (s, y)
      ∂interpolationLaw F x r s)
      (∫ y, ∫ z, inner ℝ u (primitiveObservable F x r z) *
        fderiv ℝ ψ (ρ, y) (1, (conditionalVariance ρ)⁻¹ • (z - ρ • y))
        ∂conditionalLaw F x r ρ y ∂interpolationLaw F x r ρ) ρ := by
  let := baseLaw_isProbabilityMeasure hF hlo x r
  let w : E → ℝ := fun z => inner ℝ u (primitiveObservable F x r z)
  have hw : Continuous w := (innerSL ℝ u).continuous.comp (continuous_primitiveObservable hF x r)
  have hB := contDiff_primitivePotential hF x r
  have hBlo := primitivePotential_hessian_nonneg hF hlo x r
  have hfg (t : ℝ) (ht : 0 < t) (c : E) :
      MemLp (primitiveObservable F x r) 2 (Gibbs.heatPosterior (primitivePotential F x r) t c) :=
    Gibbs.memLp_two_heatPosterior_of_affine_bound hB (m := 0) le_rfl ht
      (by simpa using hBlo) c (continuous_primitiveObservable hF x r)
      (‖gradient F 0‖ + |ell| * ‖x‖) (|ell| * |r|)
      (norm_primitiveObservable_le_affine hF hlo hup x r)
  have hwb : MemLp w 2 (baseLaw F x r) := (hfg 1 (by norm_num) 0).const_inner u
  have hzb : MemLp (fun z : E => z) 2 (baseLaw F x r) :=
    Gibbs.memLp_two_id_heatPosterior hB (m := 0) le_rfl (by norm_num)
      (by simpa using hBlo) 0
  have hW : Integrable (fun z => ‖w z‖) (baseLaw F x r) := (hwb.integrable (by norm_num)).norm
  have hWZ : Integrable (fun z : E => ‖w z‖ * ‖z‖) (baseLaw F x r) :=
    hwb.norm.integrable_mul hzb.norm
  have hN : Integrable (fun n : E => ‖n‖) (stdGaussian E) := IsGaussian.integrable_id.norm
  obtain ⟨K, hK, hzero⟩ := hψK
  obtain ⟨C₀, _, hC₀⟩ := compactTest_norm_bound (c := a) (d := b) hψ hK hzero
  have hwint (s : ℝ) (hs : s ∈ Icc a b) (y : E) :
      Integrable (primitiveObservable F x r) (conditionalLaw F x r s y) := by
    let := conditionalLaw_isProbabilityMeasure hF hlo x r (ha.trans_le hs.1) (hs.2.trans_lt hb) y
    have hmem : MemLp (primitiveObservable F x r) 2 (conditionalLaw F x r s y) :=
      hfg _ (conditionalVariance_pos (ha.trans_le hs.1) (hs.2.trans_lt hb)) _
    exact hmem.integrable (by norm_num)
  have hmean (s : ℝ) (hs : s ∈ Icc a b) (y : E) :
      (∫ z, w z ∂conditionalLaw F x r s y) = inner ℝ u (conditionalMean F x r s y) :=
    (innerSL ℝ u).integral_comp_comm (hwint s hs y)
  have hint (s : ℝ) (hs : s ∈ Icc a b) : Integrable
      (fun p : E × E => w p.1 * ψ (s, interpolationMap s p))
      ((baseLaw F x r).prod (stdGaussian E)) := by
    apply ((hW.comp_fst (stdGaussian E)).mul_const C₀).mono'
      ((hw.comp continuous_fst).mul
        (hψ.comp (continuous_const.prodMk (by unfold interpolationMap; fun_prop)))).aestronglyMeasurable
    exact Eventually.of_forall fun p => by
      change ‖w p.1 * ψ (s, interpolationMap s p)‖ ≤ _
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hC₀ s hs _) (norm_nonneg _)
  have hmap (s : ℝ) (hs : s ∈ Icc a b) :
      (∫ y, inner ℝ u (conditionalMean F x r s y) * ψ (s, y) ∂interpolationLaw F x r s) =
        ∫ p, w p.1 * ψ (s, interpolationMap s p)
          ∂(baseLaw F x r).prod (stdGaussian E) := by
    have h := conditional_disintegration_integral hF hlo x r s
      (conditionalVariance_pos (ha.trans_le hs.1) (hs.2.trans_lt hb))
      (fun q : E × E => w q.2 * ψ (s, q.1))
      (by apply Continuous.stronglyMeasurable; fun_prop) (hint s hs)
    simpa only [integral_mul_const, hmean s hs] using h
  let δ := min (ρ - a) (b - ρ) / 2
  have hδ : 0 < δ := div_pos (lt_min (sub_pos.mpr hρ.1) (sub_pos.mpr hρ.2)) (by norm_num)
  have hsub : Icc (ρ - δ) (ρ + δ) ⊆ Ioo a b := by
    intro s hs
    have h₁ := min_le_left (ρ - a) (b - ρ)
    have h₂ := min_le_right (ρ - a) (b - ρ)
    dsimp [δ] at hs
    constructor <;> linarith [hs.1, hs.2, hρ.1, hρ.2]
  have hv := conditionalVariance_pos (ha.trans hρ.1) (hρ.2.trans hb)
  obtain ⟨C, hC, hbound⟩ := compactTest_fderiv_bound hψd hsub hK hzero
  have hψon : ContDiffOn ℝ 1 ψ (Ioo a b ×ˢ (univ : Set E)) :=
    fun p hp => (hψd p hp.1).contDiffWithinAt
  have hDc : Continuous (fun y : E => fderiv ℝ ψ (ρ, y)) :=
    (hψon.continuousOn_fderiv_of_isOpen (isOpen_Ioo.prod isOpen_univ) le_rfl).comp_continuous
      (continuous_const.prodMk continuous_id) (fun y => ⟨hρ, mem_univ y⟩)
  have hlatent := hasDerivAt_weightedLatentInterpolation_integral (baseLaw F x r) (stdGaussian E)
    hw hW hWZ hN (ha.trans (hsub ⟨le_rfl, by linarith⟩).1)
    ((hsub ⟨by linarith, le_rfl⟩).2.trans hb)
    (by linarith : ρ - δ < ρ) (by linarith : ρ < ρ + δ)
    ψ hψ (fun s hs y => ((hψd (s, y) (hsub hs)).differentiableAt (by norm_num)).hasFDerivAt)
    hDc hC hbound (hint ρ ⟨hρ.1.le, hρ.2.le⟩)
  let g (q : E × E) := w q.2 * fderiv ℝ ψ (ρ, q.1)
    (1, (conditionalVariance ρ)⁻¹ • (q.2 - ρ • q.1))
  have hg : StronglyMeasurable g := by
    apply Continuous.stronglyMeasurable
    exact (hw.comp continuous_snd).mul
      ((hDc.comp continuous_fst).clm_apply (by fun_prop))
  have hgi : Integrable (fun p : E × E => g (interpolationMap ρ p, p.1))
      ((baseLaw F x r).prod (stdGaussian E)) := by
    simpa only [g, interpolationPathVelocity_eq hv] using hlatent.1
  have hBayes := conditional_disintegration_integral hF hlo x r ρ hv g hg hgi
  have heq : (∫ p, w p.1 * fderiv ℝ ψ (ρ, interpolationMap ρ p)
      (1, interpolationPathVelocity ρ p) ∂(baseLaw F x r).prod (stdGaussian E)) =
      ∫ y, ∫ z, w z * fderiv ℝ ψ (ρ, y)
        (1, (conditionalVariance ρ)⁻¹ • (z - ρ • y))
        ∂conditionalLaw F x r ρ y ∂interpolationLaw F x r ρ := by
    simpa only [g, interpolationPathVelocity_eq hv] using hBayes.symm
  rw [← heq]
  apply hlatent.2.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds hρ.1 hρ.2] with s hs
  exact hmap s ⟨hs.1.le, hs.2.le⟩

end AcceleratedLogConcave.Conditional
