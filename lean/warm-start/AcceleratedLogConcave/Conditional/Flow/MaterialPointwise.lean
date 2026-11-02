import AcceleratedLogConcave.Conditional.Flow.WeightedAdjoint
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import AcceleratedLogConcave.Conditional.Flow.MaterialMean
import AcceleratedLogConcave.Conditional.DensityRegularity

/-! # From the weak material identity to the positive pointwise adjoint -/
noncomputable section
namespace AcceleratedLogConcave.Conditional
open MeasureTheory InnerProductSpace Analysis.Poisson Kinetic
open scoped RealInnerProductSpace ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [MeasurableSpace E] [BorelSpace E] in
theorem continuous_weightedAdjoint {score U : E → E}
    (hs : Continuous score) (hU : ContDiff ℝ 1 U) : Continuous (weightedAdjoint score U) := by
  have hd : Continuous (fun y ↦ fluxDivergence U y) := by
    have heq : (fun y ↦ fluxDivergence U y) = fun y ↦
        ∑ i, inner ℝ (stdOrthonormalBasis ℝ E i)
          (fderiv ℝ U y (stdOrthonormalBasis ℝ E i)) := by
      funext y
      exact fluxDivergence_eq_sum_basis (stdOrthonormalBasis ℝ E) (hU.differentiable_one y)
    rw [heq]
    apply continuous_finsetSum
    intro i _
    exact continuous_const.inner ((hU.continuous_fderiv (by norm_num)).clm_apply continuous_const)
  exact hd.neg.add (hs.inner hU.continuous)

/-- A positive continuous density and smooth current upgrade the compact-test
material identity to a pointwise identity. This fixes the adjoint sign. -/
theorem material_eq_weightedAdjoint_of_weak
    {p material : E → ℝ} {score U : E → E}
    (hp : ContDiff ℝ 1 p) (hpos : ∀ y, 0 < p y)
    (hm : Continuous material) (hs : Continuous score) (hU : ContDiff ℝ 1 U)
    (hscore : ∀ y, HasFDerivAt p ((-p y) • innerSL ℝ (score y)) y)
    (hweak : ∀ φ : E → ℝ, ContDiff ℝ 1 φ → HasCompactSupport φ →
      (∫ y, p y * material y * φ y) = ∫ y, p y * fderiv ℝ φ y (U y)) :
    ∀ y, material y = weightedAdjoint score U y := by
  have ha := continuous_weightedAdjoint hs hU
  have hl := hp.continuous.mul hm
  have hr := hp.continuous.mul ha
  have hae : (fun y ↦ p y * material y) =ᵐ[volume]
      (fun y ↦ p y * weightedAdjoint score U y) := by
    apply ae_eq_of_integral_contDiff_smul_eq hl.locallyIntegrable hr.locallyIntegrable
    intro φ hφ hφK
    have h1 : ContDiff ℝ 1 φ := hφ.of_le (by simp)
    have hw := (hweak φ h1 hφK).trans
      (weightedAdjoint_compact_ibp p score U φ hp hU hscore h1 hφK).symm
    simpa only [smul_eq_mul, mul_comm (φ _), mul_assoc, Pi.mul_apply] using hw
  have heq := MeasureTheory.Measure.eq_of_ae_eq hae hl hr
  intro y
  exact mul_left_cancel₀ (hpos y).ne' (congrFun heq y)

section Actual
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
local notation "V" => EuclideanSpace ℝ ι

/-- The manuscript's pointwise material-mean identity, proved for the actual
conditional law and its actual velocity. The weighted adjoint has positive sign. -/
theorem conditionalMaterialMean_eq_weightedAdjoint {F : V → ℝ} (hF : ContDiff ℝ 2 F)
    {L : ℝ} (hlo : ∀ z a, 0 ≤ fderiv ℝ (fderiv ℝ F) z a a)
    (hup : ∀ z a, fderiv ℝ (fderiv ℝ F) z a a ≤ L * ‖a‖ ^ 2)
    (x u : V) {r : ℝ} (hr : r ≠ 0) {ρ : ℝ} (hρlo : -1 < ρ) (hρhi : ρ < 1) (y : V) :
    inner ℝ u (conditionalMaterialMean F x r ρ y) =
      weightedAdjoint (fun z ↦ z + (r * ρ) • conditionalMean F x r ρ z)
        (firstScaledJetRow F x u r ρ) y := by
  let p := interpolationDensity F x r ρ
  let m := fun z ↦ inner ℝ u (conditionalMaterialMean F x r ρ z)
  let score := fun z ↦ z + (r * ρ) • conditionalMean F x r ρ z
  let U := firstScaledJetRow F x u r ρ
  have hp : ContDiff ℝ 1 p := by
    have hh := (contDiffOn_interpolationDensity hF hlo x r).comp
      (contDiff_const.prodMk contDiff_id).contDiffOn
      (s := Set.univ) (fun _ _ ↦ ⟨hρlo, hρhi⟩)
    exact (contDiffOn_univ.mp hh).of_le (by simp)
  have hpos (z : V) : 0 < p z :=
    interpolationDensity_pos hF hlo x r ρ (conditionalVariance_pos hρlo hρhi) z
  have hmean := (contDiff_one_conditionalMean hF hlo hup x r hρlo hρhi).continuous
  have hs : Continuous score := by
    simpa only [score, Pi.add_def, Pi.smul_def, id_eq] using
      continuous_id.add (hmean.const_smul (r * ρ))
  have hU : ContDiff ℝ 1 U := contDiff_firstScaledJetRow hF hlo hup x u hr hρlo hρhi
  have hm : Continuous m := by
    let J := fun p : ℝ × V ↦ conditionalMean F x r p.1 p.2
    have hop : IsOpen {p : ℝ × V | -1 < p.1 ∧ p.1 < 1} :=
      (isOpen_lt continuous_const continuous_fst).inter (isOpen_lt continuous_fst continuous_const)
    have hJ : ContDiffOn ℝ 1 J {p | -1 < p.1 ∧ p.1 < 1} :=
      (contDiffOn_conditionalMean hF hlo hup x r).of_le (by simp)
    have hd : Continuous (fun z : V ↦ fderiv ℝ J (ρ, z)) :=
      (hJ.continuousOn_fderiv_of_isOpen hop le_rfl).comp_continuous
        (continuous_const.prodMk continuous_id) (fun _ ↦ ⟨hρlo, hρhi⟩)
    have hv : Continuous (probabilityVelocity F x r ρ) := by
      change Continuous (fun z : V ↦ -r • conditionalMean F x r ρ z)
      simpa only [Pi.smul_def] using hmean.const_smul (-r)
    exact (innerSL ℝ u).continuous.comp (hd.clm_apply (continuous_const.prodMk hv))
  have hconvert (g : V → ℝ) :
      (∫ z, g z ∂interpolationLaw F x r ρ) = ∫ z, p z * g z := by
    rw [interpolationLaw_eq_explicitDensity hF hlo x r ρ (conditionalVariance_pos hρlo hρhi)]
    simpa only [ENNReal.toReal_ofReal (hpos _).le, smul_eq_mul] using
      integral_withDensity_eq_integral_toReal_smul (hp.continuous.measurable.ennreal_ofReal)
        (Filter.Eventually.of_forall (fun _ ↦ ENNReal.ofReal_lt_top)) g
  apply material_eq_weightedAdjoint_of_weak hp hpos hm hs hU
    (fun z ↦ hasFDerivAt_interpolationDensity hF hlo hup x r hρlo hρhi z) ?_ y
  intro φ hφ hφK
  have hw := integral_conditionalMaterialMean_mul_test hF hlo hup x u hr
    (a := (ρ - 1) / 2) (b := (ρ + 1) / 2) (by linarith) (by linarith)
    (show ρ ∈ Set.Ioo ((ρ - 1) / 2) ((ρ + 1) / 2) from ⟨by linarith, by linarith⟩)
    φ hφ hφK
  rw [hconvert, hconvert] at hw
  simpa only [mul_assoc] using hw

end Actual

end AcceleratedLogConcave.Conditional
