import AcceleratedLogConcave.Numerics.CenterMeanSecondJetSource

/-! Original-data finite first source energy. The explicit scalar below depends
only on the physical scales and retains the square-root dimension rate. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set
open scoped ContDiff
namespace AcceleratedLogConcave.Numerics.CenterMeanSecondJetSource
open Conditional CenteringFlowLp
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
local notation "E" => EuclideanSpace ℝ ι
local notation "P" => Centering.Phase E

def sourceFirst (d : Data ι) (s : ℝ) (z : P) : E :=
  Centering.meanFirstJet (K d) (M d) s z.fst z.snd

def firstEnergyScale (d : Data ι) (s : ℝ) : ℝ :=
  |s⁻¹| * (d.r*d.ell) * (2*Real.exp 1*(d.r*d.ell))

omit [DecidableEq ι] in
theorem firstEnergyScale_nonneg (d : Data ι) (s : ℝ) : 0 ≤ firstEnergyScale d s := by
  have hr := d.hr
  have hell := d.hell
  unfold firstEnergyScale
  positivity

omit [DecidableEq ι] in
theorem continuous_sourceFirst (d : Data ι) (s : ℝ) : Continuous (sourceFirst d s) := by
  have hM := ((smooth_M d).fderiv_right (m := 0) (by simp)).continuous
  have hK := (Centering.sourceKernel_contDiff_one d.hF d.hell d.hlo d.hup
    d.x d.hr d.hb d.hb1 d.hsmall).continuous
  exact ((hM.comp (WithLp.prod_continuous_ofLp 2 E E).fst).clm_apply
    ((hK.comp (WithLp.prod_continuous_ofLp 2 E E).fst).clm_apply
      (WithLp.prod_continuous_ofLp 2 E E).snd)).const_smul (-s⁻¹ : ℝ)

omit [DecidableEq ι] in
theorem norm_sourceFirst_le (d : Data ι) (s : ℝ) (z : P) :
    ‖sourceFirst d s z‖ ≤ firstEnergyScale d s * ‖z.snd‖ := by
  have hM : ‖fderiv ℝ (M d) z.fst‖ ≤ d.r*d.ell :=
    norm_fderiv_le_of_lipschitz ℝ
      (lipschitzWith_conditionalMean d.hF d.hell d.hlo d.hup d.x d.hr
        (by linarith [d.hb]) d.hb1)
  have hK := norm_transportedSteinKernelTranspose_le d.hF d.hell d.hlo d.hup
    d.x d.hr d.hb d.hb1 d.hsmall z.fst
  change ‖(-s⁻¹) • (fderiv ℝ (M d) z.fst (K d z.fst z.snd))‖ ≤ _
  rw [norm_smul, Real.norm_eq_abs, abs_neg]
  calc
    _ ≤ |s⁻¹| * ((d.r*d.ell) * ‖K d z.fst z.snd‖) :=
      mul_le_mul_of_nonneg_left (((fderiv ℝ (M d) z.fst).le_opNorm _).trans
        (mul_le_mul_of_nonneg_right hM (norm_nonneg _))) (abs_nonneg _)
    _ ≤ |s⁻¹| * ((d.r*d.ell) * ((2*Real.exp 1*(d.r*d.ell))*‖z.snd‖)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
        (((K d z.fst).le_opNorm _).trans
          (mul_le_mul_of_nonneg_right hK (norm_nonneg _)))
        (mul_nonneg d.hr.le d.hell)) (abs_nonneg _)
    _ = _ := by unfold firstEnergyScale; ring

omit [DecidableEq ι] in
theorem sourceFirst_memLp (d : Data ι) (s : ℝ) :
    MemLp (sourceFirst d s) 2 (seedMeasure d) := by
  apply ((KernelFlowLp.momentum_memLp d).norm.const_mul (firstEnergyScale d s)).mono'
    (continuous_sourceFirst d s).aestronglyMeasurable
  exact Filter.Eventually.of_forall (norm_sourceFirst_le d s)

omit [DecidableEq ι] in
theorem integral_sourceFirst_norm_sq_le (d : Data ι) (s : ℝ) :
    (∫ z, ‖sourceFirst d s z‖^2 ∂seedMeasure d) ≤
      (firstEnergyScale d s)^2 * (Module.finrank ℝ E : ℝ) := by
  have hf := sourceFirst_memLp d s
  have hg := KernelFlowLp.momentum_memLp d
  have hi := (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mp hf
  have hj := ((memLp_two_iff_integrable_sq_norm hg.aestronglyMeasurable).mp hg).const_mul
    ((firstEnergyScale d s)^2)
  calc
    _ ≤ ∫ z : P, (firstEnergyScale d s)^2 * ‖z.snd‖^2 ∂seedMeasure d := by
      apply integral_mono_ae hi hj
      filter_upwards [] with z
      simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) (norm_sourceFirst_le d s z) 2
    _ = _ := by rw [integral_const_mul, KernelFlowLp.integral_momentum_norm_sq]

end AcceleratedLogConcave.Numerics.CenterMeanSecondJetSource
