import AcceleratedLogConcave.Kinetic.Reheating.HeatEvolution.Joint
import AcceleratedLogConcave.Kinetic.Reheating.HeatEvolution.Growth

/-! Actual material derivative of the classical heat quotient along the
reference probability flow. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace
open scoped Topology RealInnerProductSpace
namespace AcceleratedLogConcave.Kinetic.Reheating
open Analysis.Poisson AcceleratedLogConcave.HeatCalculus
variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι

theorem compactHeatNumerator_along_hasDerivAt {a b : ℝ}
    (F : ReferencePoissonFamily E a b) {f : E → ℝ}
    (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f) {t : ℝ} (ht : t ∈ Ioo a b)
    {z : ℝ → E} {z' : E} (hz : HasDerivAt z z' t) :
    HasDerivAt (fun s => compactHeatNumerator F f s (z s))
      ((1/2:ℝ)*compactTestLaplacian (compactHeatNumerator F f t) (z t) +
        fderiv ℝ (compactHeatNumerator F f t) (z t) z') t := by
  let h : E → ℝ := fun x => f x * F.density a x
  have h2 : ContDiff ℝ 2 h := hf.mul (reference_density_C2 F a ⟨le_rfl,F.ordered⟩)
  have hh : HasCompactSupport h := hc.mul_right
  apply hasDerivAt_along_of_partials ht
    (fun s hs x => compactHeatNumerator_classical_heat F hf hc s hs.1 x)
    (fun s _ x => compactTest_hasFDerivAt (compactHeatNumerator_C2 F hf hc s) x) _ _ hz
  · exact ((heatAverage_joint_laplacian_continuous h2 hh).comp
      ((continuous_fst.sub continuous_const).prodMk continuous_snd)).const_mul (1/2:ℝ)
        |>.continuousOn
  · exact ((heatAverage_joint_fderiv_continuous h2 hh).comp
      ((continuous_fst.sub continuous_const).prodMk continuous_snd)).continuousOn

theorem reference_density_along_hasDerivAt {a b : ℝ}
    (F : ReferencePoissonFamily E a b) {t : ℝ} (ht : t ∈ Ioo a b)
    (hscale : F.scale t = -(1/2:ℝ)) {z : ℝ → E} {z' : E} (hz : HasDerivAt z z' t) :
    HasDerivAt (fun s => F.density s (z s))
      ((1/2:ℝ)*compactTestLaplacian (F.density t) (z t) +
        fderiv ℝ (F.density t) (z t) z') t := by
  have hD : Continuous (fun p : ℝ × E => fderiv ℝ (F.potential p.1) p.2) := by
    have h := (toDual ℝ E).continuous.comp F.gradient_continuous
    convert h using 1
    apply funext
    intro p
    exact ((toDual ℝ E).apply_symm_apply (fderiv ℝ (F.potential p.1) p.2)).symm
  have hρ := F.density_continuous.mono (show Ioo a b ×ˢ (univ : Set E) ⊆
    Icc a b ×ˢ univ from fun p hp => ⟨Ioo_subset_Icc_self hp.1,hp.2⟩)
  have hd := hasDerivAt_along_of_partials ht F.density_hasDerivAt
    (fun s hs x => reference_density_hasFDerivAt F s (Ioo_subset_Icc_self hs) x)
    F.densityVelocity_continuous (hρ.neg.smul hD.continuousOn) hz
  have he := (F.density_hasDerivAt t ht (z t)).unique
    (reference_density_classical_heat F t ht hscale (z t))
  simpa only [he, (reference_density_hasFDerivAt F t (Ioo_subset_Icc_self ht) (z t)).fderiv]
    using hd

/-- The actual quotient along a heat-reference trajectory has material
derivative minus one half of its genuine weighted Laplacian. -/
theorem compactHeatQuotient_material_hasDerivAt {a b : ℝ}
    (F : ReferencePoissonFamily E a b) {f : E → ℝ}
    (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f) {t : ℝ} (ht : t ∈ Ioo a b)
    (hscale : F.scale t = -(1/2:ℝ)) {z : ℝ → E}
    (hz : HasDerivAt z ((1/2:ℝ) • gradient (F.potential t) (z t)) t) :
    HasDerivAt (fun s => compactHeatQuotient F f s (z s))
      (-(1/2:ℝ) * weightedHeatGenerator (F.potential t) (compactHeatQuotient F f t) (z t)) t := by
  have ht' := Ioo_subset_Icc_self ht
  have hp0 := (reference_density_pos F t ht' (z t)).ne'
  have hd := (compactHeatNumerator_along_hasDerivAt F hf hc ht hz).div
    (reference_density_along_hasDerivAt F ht hscale hz) hp0
  change HasDerivAt (fun s => compactHeatQuotient F f s (z s)) _ t at hd
  convert hd using 1
  have hl := compactTestLaplacian_mul (reference_density_C2 F t ht')
    (compactHeatQuotient_C2 F hf hc t ht') (z t)
  rw [← compactHeatNumerator_eq_density_mul F f t ht', reference_density_gradient F t ht',
    inner_smul_left, RCLike.conj_to_real] at hl
  have hn := congrFun (compactHeatNumerator_eq_density_mul F f t ht') (z t)
  have hg := compactHeatQuotient_fderiv F hf hc t ht' (z t)
  have hg' := congrArg (fun L : E →L[ℝ] ℝ => L (gradient (F.potential t) (z t))) hg
  simp only [add_apply, smul_apply, smul_eq_mul, ← inner_gradient_left] at hg'
  rw [← real_inner_comm (gradient (compactHeatQuotient F f t) (z t))
    (gradient (F.potential t) (z t))] at hg'
  have hnG : inner ℝ (gradient (compactHeatNumerator F f t) (z t))
      (gradient (F.potential t) (z t)) = F.density t (z t) *
        (inner ℝ (gradient (F.potential t) (z t)) (gradient (compactHeatQuotient F f t) (z t)) -
          compactHeatQuotient F f t (z t) *
            inner ℝ (gradient (F.potential t) (z t)) (gradient (F.potential t) (z t))) := by
    field_simp [hp0] at hg'
    nlinarith
  simp only [map_smul, smul_eq_mul, ← inner_gradient_left]
  rw [hl, hn, hnG, reference_density_gradient F t ht', inner_smul_left, RCLike.conj_to_real]
  unfold weightedHeatGenerator
  field_simp
  ring

end AcceleratedLogConcave.Kinetic.Reheating
