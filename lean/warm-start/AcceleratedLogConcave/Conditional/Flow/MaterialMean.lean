import AcceleratedLogConcave.Conditional.Flow.WeightedContinuity
import AcceleratedLogConcave.Conditional.Flow.JetCurrent
import AcceleratedLogConcave.Conditional.Flow.Regularity

/-! The actual material-mean identity in compact weak form. Ordinary
continuity tested with `M_i φ` is subtracted from observable-weighted
continuity tested with `φ`; their transport terms cancel. -/
noncomputable section
set_option maxHeartbeats 1600000
open Set Function Filter MeasureTheory ProbabilityTheory
open scoped Topology RealInnerProductSpace ContDiff

namespace AcceleratedLogConcave.Conditional
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Actual derivative along the probability velocity. -/
def conditionalMaterialMean (F : E → ℝ) (x : E) (r ρ : ℝ) (y : E) : E :=
  fderiv ℝ (fun p : ℝ × E => conditionalMean F x r p.1 p.2) (ρ, y)
    (1, probabilityVelocity F x r ρ y)

end AcceleratedLogConcave.Conditional

namespace AcceleratedLogConcave.Conditional
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
local notation "E" => EuclideanSpace ℝ ι

theorem integral_conditionalMaterialMean_mul_test
    {F : E → ℝ} (hF : ContDiff ℝ 2 F) {ell : ℝ}
    (hlo : ∀ z a, 0 ≤ fderiv ℝ (fderiv ℝ F) z a a)
    (hup : ∀ z a, fderiv ℝ (fderiv ℝ F) z a a ≤ ell * ‖a‖ ^ 2)
    (x u : E) {r : ℝ} (hr : r ≠ 0) {a b ρ : ℝ} (ha : -1 < a) (hb : b < 1)
    (hρ : ρ ∈ Ioo a b) (φ : E → ℝ) (hφ : ContDiff ℝ 1 φ) (hφK : HasCompactSupport φ) :
    (∫ y, inner ℝ u (conditionalMaterialMean F x r ρ y) * φ y ∂interpolationLaw F x r ρ) =
      ∫ y, fderiv ℝ φ y (firstScaledJetRow F x u r ρ y) ∂interpolationLaw F x r ρ := by
  let := interpolationLaw_isProbabilityMeasure hF hlo x r ρ
  have hab : a ≤ b := hρ.1.le.trans hρ.2.le
  have hρlo : -1 < ρ := ha.trans hρ.1
  have hρhi : ρ < 1 := hρ.2.trans hb
  let J (p : ℝ × E) := conditionalMean F x r p.1 p.2
  let m (y : E) := inner ℝ u (conditionalMean F x r ρ y)
  let v := probabilityVelocity F x r ρ
  let U := firstScaledJetRow F x u r ρ
  let Q (s : ℝ) := ∫ y, inner ℝ u (conditionalMean F x r s y) * φ y ∂interpolationLaw F x r s
  have hop : IsOpen {p : ℝ × E | -1 < p.1 ∧ p.1 < 1} :=
    (isOpen_lt continuous_const continuous_fst).inter (isOpen_lt continuous_fst continuous_const)
  have hJ : ContDiffOn ℝ 1 J {p | -1 < p.1 ∧ p.1 < 1} :=
    (contDiffOn_conditionalMean hF hlo hup x r).of_le (by norm_num)
  have hJa (p : ℝ × E) (hp : p.1 ∈ Ioo a b) : ContDiffAt ℝ 1 J p :=
    (hJ p ⟨ha.trans hp.1, hp.2.trans hb⟩).contDiffAt
      (hop.mem_nhds ⟨ha.trans hp.1, hp.2.trans hb⟩)
  have hj (y : E) : HasFDerivAt J (fderiv ℝ J (ρ, y)) (ρ, y) :=
    ((hJa (ρ, y) hρ).differentiableAt (by norm_num)).hasFDerivAt
  have hm : Continuous m := (innerSL ℝ u).continuous.comp
    (contDiff_one_conditionalMean hF hlo hup x r hρlo hρhi).continuous
  have hv : Continuous v := (continuous_const : Continuous (fun _ : E => (-r : ℝ))).smul
    (contDiff_one_conditionalMean hF hlo hup x r hρlo hρhi).continuous
  have hU : Continuous U := (contDiff_firstScaledJetRow hF hlo hup x u hr hρlo hρhi).continuous
  have hDJ : Continuous (fun y : E => fderiv ℝ J (ρ, y)) :=
    (hJ.continuousOn_fderiv_of_isOpen hop le_rfl).comp_continuous
      (continuous_const.prodMk continuous_id) (fun _ => ⟨hρlo, hρhi⟩)
  have hmaterial : Continuous (fun y : E => inner ℝ u (conditionalMaterialMean F x r ρ y)) :=
    (innerSL ℝ u).continuous.comp (hDJ.clm_apply (continuous_const.prodMk hv))
  have hfluxK (W : E → E) : HasCompactSupport (fun y => fderiv ℝ φ y (W y)) := by
    apply HasCompactSupport.intro hφK
    intro y hy
    rw [fderiv_of_notMem_tsupport ℝ hy]
    rfl
  have hfluxI (W : E → E) (hW : Continuous W) :
      Integrable (fun y => fderiv ℝ φ y (W y)) (interpolationLaw F x r ρ) :=
    ((hφ.continuous_fderiv one_ne_zero).clm_apply hW).integrable_of_hasCompactSupport (hfluxK W)
  have hi₁ : Integrable (fun y => inner ℝ u (conditionalMaterialMean F x r ρ y) * φ y)
      (interpolationLaw F x r ρ) :=
    (hmaterial.mul hφ.continuous).integrable_of_hasCompactSupport hφK.mul_left
  have hi₂ : Integrable (fun y => m y * fderiv ℝ φ y (v y)) (interpolationLaw F x r ρ) :=
    (hm.mul ((hφ.continuous_fderiv one_ne_zero).clm_apply hv)).integrable_of_hasCompactSupport
      (hfluxK v).mul_left
  have hi₃ := hfluxI U hU
  let ψ₀ (p : ℝ × E) := φ p.2
  have hdψ₀ (y : E) : fderiv ℝ ψ₀ (ρ, y) =
      (fderiv ℝ φ y).comp (ContinuousLinearMap.snd ℝ ℝ E) :=
    ((hφ.differentiable_one y).hasFDerivAt.comp (ρ, y)
      (ContinuousLinearMap.snd ℝ ℝ E).hasFDerivAt).fderiv
  have hwQ : HasDerivAt Q
      (∫ y, m y * fderiv ℝ φ y (v y) + fderiv ℝ φ y (U y) ∂interpolationLaw F x r ρ) ρ := by
    have hh := hasDerivAt_weightedInterpolation_test hF hlo hup x u r ha hb hρ ψ₀
      (hφ.continuous.comp continuous_snd)
      (fun p _ => hφ.contDiffAt.comp p contDiffAt_snd)
      ⟨tsupport φ, hφK, fun _ y hy => by
        change φ y = 0
        exact image_eq_zero_of_notMem_tsupport hy⟩
    convert hh using 1
    apply integral_congr_ae
    filter_upwards [] with y
    rw [integral_weighted_conditional_spaceTime_velocity hF hlo hup x u r hρlo hρhi y,
      hdψ₀ y]
    rfl
  let P (p : ℝ × E) := inner ℝ u
    (conditionalMean F x r (projIcc a b hab p.1) p.2) * φ p.2
  have hPeq (p : ℝ × E) (hp : p.1 ∈ Ioo a b) :
      P =ᶠ[𝓝 p] fun q => inner ℝ u (J q) * φ q.2 := by
    filter_upwards [(continuous_fst.tendsto p) (Ioo_mem_nhds hp.1 hp.2)] with q hq
    simp only [P, J, projIcc_of_mem hab ⟨hq.1.le, hq.2.le⟩]
  have hPc : Continuous P := by
    have hc := continuousOn_conditionalMean hF hlo hup x r ha hb
    have hp : Continuous (fun q : ℝ × E => ((projIcc a b hab q.1 : ℝ), q.2)) :=
      (continuous_subtype_val.comp ((continuous_projIcc (h := hab)).comp continuous_fst)).prodMk continuous_snd
    exact ((innerSL ℝ u).continuous.comp (hc.comp_continuous hp
      (fun q => ⟨(projIcc a b hab q.1).2, mem_univ q.2⟩))).mul
      (hφ.continuous.comp continuous_snd)
  have hP₁ (p : ℝ × E) (hp : p.1 ∈ Ioo a b) : ContDiffAt ℝ 1 P p :=
    (((innerSL ℝ u).contDiff.contDiffAt.comp p (hJa p hp)).mul
      (hφ.contDiffAt.comp p contDiffAt_snd)).congr_of_eventuallyEq (hPeq p hp)
  obtain ⟨_, hOrd⟩ := (hasWeakContinuityEquation_interpolation hF hlo hup x r ha hb)
    P hPc hP₁ ⟨tsupport φ, hφK, fun _ y hy => by
      dsimp [P]
      rw [image_eq_zero_of_notMem_tsupport hy, mul_zero]⟩
  have hDP (y : E) : fderiv ℝ P (ρ, y) (1, v y) =
      inner ℝ u (conditionalMaterialMean F x r ρ y) * φ y + m y * fderiv ℝ φ y (v y) := by
    have hh := (((innerSL ℝ u).hasFDerivAt.comp (ρ, y) (hj y)).mul
      ((hφ.differentiable_one y).hasFDerivAt.comp (ρ, y)
        (ContinuousLinearMap.snd ℝ ℝ E).hasFDerivAt)).congr_of_eventuallyEq (hPeq (ρ, y) hρ)
    rw [hh.fderiv]
    simp only [add_apply, smul_apply, smul_eq_mul, ContinuousLinearMap.comp_apply,
      innerSL_apply_apply]
    change m y * fderiv ℝ φ y (v y) + φ y * inner ℝ u (conditionalMaterialMean F x r ρ y) = _
    ring
  have hoQ : HasDerivAt Q
      (∫ y, inner ℝ u (conditionalMaterialMean F x r ρ y) * φ y +
        m y * fderiv ℝ φ y (v y) ∂interpolationLaw F x r ρ) ρ := by
    have hQeq : Q =ᶠ[𝓝 ρ] fun s => ∫ y, P (s, y) ∂interpolationLaw F x r s := by
      filter_upwards [Ioo_mem_nhds hρ.1 hρ.2] with s hs
      apply integral_congr_ae
      exact Eventually.of_forall fun y => by
        simp only [P, projIcc_of_mem hab ⟨hs.1.le, hs.2.le⟩]
    have hh := (hOrd ρ hρ).congr_of_eventuallyEq hQeq
    change HasDerivAt Q (∫ y, fderiv ℝ P (ρ, y) (1, v y) ∂interpolationLaw F x r ρ) ρ at hh
    simpa only [hDP] using hh
  have heq := hoQ.unique hwQ
  rw [integral_add hi₁ hi₂, integral_add hi₂ hi₃] at heq
  linarith

end AcceleratedLogConcave.Conditional
