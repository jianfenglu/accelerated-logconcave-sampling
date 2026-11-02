import AcceleratedLogConcave.Oracle.PrivateFinalGaussian
import AcceleratedLogConcave.Conditional.ProbabilityFlow
import AcceleratedLogConcave.Channels.GaussianForward

/-! Exact law of the literal conditional Gaussian-start sampling flow readout.
It starts from the private position Gaussian, not an original Gibbs-law state.
The executed approximation is joined to this reference by the retained coupling. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set
open scoped NNReal
namespace AcceleratedLogConcave.Oracle.PrivateSamplingReferenceLaw
open Numerics.AffineGraph Conditional
variable {d m : ℕ} (S : SamplingGeometry m)

/-- The source endpoint scaling turns its remaining conditional Gaussian
variance into exactly tau²/4. -/
theorem endpoint_noise_coefficient :
    (samplingEnd S.τ)⁻¹ * Real.sqrt (conditionalVariance (samplingEnd S.τ)) = S.τ/2 := by
  let rho := samplingEnd S.τ
  have hp : 0 < rho := S.samplingEnd_pos
  have ht : 0 < S.τ := S.R_pos.trans_le S.R_le_τ
  have hid : rho^2*(1+S.τ^2/4)=1 := by
    dsimp only [rho,samplingEnd]
    rw [inv_pow,Real.sq_sqrt (by positivity)]
    exact inv_mul_cancel₀ (by positivity)
  have hv := conditionalVariance_pos (by linarith : -1 < rho) S.samplingEnd_lt_one
  have hs := Real.sq_sqrt hv.le
  change rho⁻¹ * Real.sqrt (conditionalVariance rho) = S.τ/2
  apply (sq_eq_sq₀ (mul_nonneg (inv_nonneg.mpr hp.le) (Real.sqrt_nonneg _)) (by positivity)).mp
  rw [mul_pow,hs]
  unfold conditionalVariance
  field_simp
  nlinarith

variable {F : Point d → ℝ} (hF : ContDiff ℝ 2 F) {ell : ℝ}
  (hell : 0 ≤ ell) (hlo : ∀ z v, 0 ≤ fderiv ℝ (fderiv ℝ F) z v v)
  (hup : ∀ z v, fderiv ℝ (fderiv ℝ F) z v v ≤ ell*‖v‖^2)
  (x : Point d) {r : ℝ} (hr : 0 < r)

/-- Exact readout of the same private conditional flow as the source residual. -/
def readout (z : Point d) : Point d :=
  (samplingEnd S.τ)⁻¹ • convexProbabilityFlow hF hell hlo hup x hr
    S.samplingEnd_pos.le (by norm_num) S.samplingEnd_lt_one
    ⟨0,le_rfl,S.samplingEnd_pos.le⟩ z (samplingEnd S.τ)

include hF hlo in
theorem scaled_interpolation :
    (interpolationLaw F x r (samplingEnd S.τ)).map (fun y => (samplingEnd S.τ)⁻¹ • y) =
      Channels.forward (baseLaw F x r) ⟨S.τ^2/4,by positivity⟩ := by
  let : IsProbabilityMeasure (baseLaw F x r) := baseLaw_isProbabilityMeasure hF hlo x r
  have hi : Measurable (interpolationMap (samplingEnd S.τ) : Point d × Point d → Point d) := by
    unfold interpolationMap
    fun_prop
  rw [interpolationLaw,Measure.map_map (by fun_prop) hi]
  have he : (fun z : Point d × Point d =>
      (samplingEnd S.τ)⁻¹ • interpolationMap (samplingEnd S.τ) z) =
      (fun z => z.1 + (S.τ/2) • z.2) := by
    funext z
    simp only [interpolationMap,smul_add,smul_smul,
      inv_mul_cancel₀ (ne_of_gt S.samplingEnd_pos),one_smul,endpoint_noise_coefficient]
  change Measure.map (fun z : Point d × Point d =>
      (samplingEnd S.τ)⁻¹ • interpolationMap (samplingEnd S.τ) z) _ = _
  rw [he]
  have ht : Real.sqrt (S.τ^2/4) = S.τ/2 := by
    rw [Real.sqrt_div (sq_nonneg _),Real.sqrt_sq (S.R_pos.trans_le S.R_le_τ).le]
    norm_num
  have hnoise : Channels.noise (ι := Fin d) ⟨S.τ^2/4,by positivity⟩ =
      (stdGaussian (Point d)).map (fun z => (S.τ/2) • z) := by
    rw [Channels.noise_eq_scaled_stdGaussian]
    congr 1
    funext z
    congr 1
  have hprod : (baseLaw F x r).prod ((stdGaussian (Point d)).map (fun z => (S.τ/2) • z)) =
      ((baseLaw F x r).prod (stdGaussian (Point d))).map (Prod.map id (fun z => (S.τ/2) • z)) := by
    simpa only [Measure.map_id] using Measure.map_prod_map (baseLaw F x r)
      (stdGaussian (Point d)) measurable_id (measurable_const_smul (S.τ/2))
  unfold Channels.forward
  rw [hnoise,Measure.conv,hprod,Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

/-- Exact scaled endpoint law from the actual Gaussian-start flow. -/
theorem readout_preserving :
    MeasurePreserving (readout S hF hell hlo hup x hr) (stdGaussian (Point d))
      (Channels.forward (baseLaw F x r) ⟨S.τ^2/4,by positivity⟩) := by
  have hf := convexProbabilityFlow_measurePreserving_le hF hell hlo hup x hr
    S.samplingEnd_pos.le (by norm_num) S.samplingEnd_lt_one
  rw [interpolationLaw_zero hF hlo x r] at hf
  have hs : MeasurePreserving (fun y : Point d => (samplingEnd S.τ)⁻¹ • y)
      (interpolationLaw F x r (samplingEnd S.τ))
      ((interpolationLaw F x r (samplingEnd S.τ)).map (fun y => (samplingEnd S.τ)⁻¹ • y)) :=
    ⟨by fun_prop,rfl⟩
  rw [scaled_interpolation S hF hlo x] at hs
  exact hs.comp hf

/-- Adding a genuinely fresh Gaussian to the literal source readout composes
its heat variance. This is applied to the exact final residual aggregation. -/
theorem readout_add_noise_preserving (v : ℝ≥0) :
    MeasurePreserving (fun z : Point d × Point d =>
      readout S hF hell hlo hup x hr z.1 + Real.sqrt (v:ℝ) • z.2)
      ((stdGaussian (Point d)).prod (stdGaussian (Point d)))
      (Channels.forward (baseLaw F x r) (⟨S.τ^2/4,by positivity⟩+v)) := by
  let : IsProbabilityMeasure (baseLaw F x r) := baseLaw_isProbabilityMeasure hF hlo x r
  have hn : MeasurePreserving (fun z : Point d => Real.sqrt (v:ℝ) • z)
      (stdGaussian (Point d)) (Channels.noise v) :=
    ⟨by fun_prop,(Channels.noise_eq_scaled_stdGaussian v).symm⟩
  have hp := (readout_preserving S hF hell hlo hup x hr).prod hn
  have ha : MeasurePreserving (fun z : Point d × Point d => z.1+z.2)
      ((Channels.forward (baseLaw F x r) ⟨S.τ^2/4,by positivity⟩).prod (Channels.noise v))
      (Channels.forward (Channels.forward (baseLaw F x r) ⟨S.τ^2/4,by positivity⟩) v) :=
    ⟨by fun_prop,rfl⟩
  rw [Channels.forward_add] at ha
  exact ha.comp hp

/-- Exact pre-reserve reference law, variance 3 tau²/4 over the posterior
base law. The tau²/4 term comes from the actual endpoint scaling. -/
theorem pre_reference_preserving :
    MeasurePreserving (fun z : Point d × Point d =>
      readout S hF hell hlo hup x hr z.1 + (S.τ/Real.sqrt 2) • z.2)
      ((stdGaussian (Point d)).prod (stdGaussian (Point d)))
      (Channels.forward (baseLaw F x r) ⟨3*S.τ^2/4,by positivity⟩) := by
  have hp := readout_add_noise_preserving S hF hell hlo hup x hr ⟨S.τ^2/2,by positivity⟩
  have hv : (⟨S.τ^2/4,by positivity⟩ : ℝ≥0)+⟨S.τ^2/2,by positivity⟩ =
      ⟨3*S.τ^2/4,by positivity⟩ := by ext; dsimp; ring
  rw [hv] at hp
  convert hp using 1
  funext z
  congr 2
  symm
  exact (Real.sqrt_div (sq_nonneg S.τ) 2).trans
    (by rw [Real.sqrt_sq (S.R_pos.trans_le S.R_le_τ).le])

/-- The full reference uses a separate fresh reserve of size tau/2. Its law
is the base posterior convolved with variance tau², for private or public tau. -/
theorem reference_preserving :
    MeasurePreserving (fun z : (Point d × Point d) × Point d =>
      (readout S hF hell hlo hup x hr z.1.1 + (S.τ/Real.sqrt 2) • z.1.2) +
        (S.τ/2) • z.2)
      (((stdGaussian (Point d)).prod (stdGaussian (Point d))).prod (stdGaussian (Point d)))
      (Channels.forward (baseLaw F x r) ⟨S.τ^2,by positivity⟩) := by
  let : IsProbabilityMeasure (baseLaw F x r) := baseLaw_isProbabilityMeasure hF hlo x r
  have hn : MeasurePreserving (fun z : Point d => (S.τ/2) • z)
      (stdGaussian (Point d)) (Channels.noise ⟨S.τ^2/4,by positivity⟩) := by
    refine ⟨by fun_prop,?_⟩
    rw [Channels.noise_eq_scaled_stdGaussian]
    congr 1
    funext z
    congr 1
    change S.τ/2 = Real.sqrt (S.τ^2/4)
    rw [Real.sqrt_div (sq_nonneg S.τ), Real.sqrt_sq (S.R_pos.trans_le S.R_le_τ).le]
    norm_num
  have hp := (pre_reference_preserving S hF hell hlo hup x hr).prod hn
  have ha : MeasurePreserving (fun z : Point d × Point d => z.1+z.2)
      ((Channels.forward (baseLaw F x r) ⟨3*S.τ^2/4,by positivity⟩).prod
        (Channels.noise ⟨S.τ^2/4,by positivity⟩))
      (Channels.forward (Channels.forward (baseLaw F x r) ⟨3*S.τ^2/4,by positivity⟩)
        ⟨S.τ^2/4,by positivity⟩) := ⟨by fun_prop,rfl⟩
  rw [Channels.forward_add] at ha
  have hv : (⟨3*S.τ^2/4,by positivity⟩ : ℝ≥0)+⟨S.τ^2/4,by positivity⟩ =
      ⟨S.τ^2,by positivity⟩ := by ext; dsimp; ring
  rw [hv] at ha
  exact ha.comp hp

end AcceleratedLogConcave.Oracle.PrivateSamplingReferenceLaw
