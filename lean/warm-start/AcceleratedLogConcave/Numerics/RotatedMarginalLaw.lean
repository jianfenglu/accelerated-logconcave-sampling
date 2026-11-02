import AcceleratedLogConcave.Numerics.RotatedJointLaw
import AcceleratedLogConcave.Numerics.GaussianRowLaw
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 200000
namespace AcceleratedLogConcave.Numerics.MeanFlowLp
open Conditional AffineGraph AffineGraph.MeanGeometry
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ}
local notation "E" => EuclideanSpace ℝ ι

def rotationOfObservation (d : Data ι m) (k : d.G.Kernel) (z : ℝ) (b h s : E) : E :=
  let mid := (d.G.rho k/(1+(d.G.rho k)^2)) • (h+d.G.rho k • b)
  mid+Real.cos (z/d.G.rotationScale k) • (b-mid)+
    (d.G.rotationScale k*Real.sin (z/d.G.rotationScale k)) • s

omit [DecidableEq ι] in
theorem continuous_rotationOfObservation (d : Data ι m) (k : d.G.Kernel) (z : ℝ) :
    Continuous (fun p : (E × E) × E => rotationOfObservation d k z p.1.1 p.1.2 p.2) := by
  unfold rotationOfObservation
  fun_prop

theorem rotation_eq_observation (d : Data ι m) (j : Fin m) (k : d.G.Kernel) (z : ℝ)
    (ω : Seed d) : rotation d j k z ω =
      rotationOfObservation d k z (backward d j (d.G.rho k) ω)
        (observationFromNoise d k (backward d j (d.G.rho k) ω) (ω.2 j k))
        (score d (centerNode j) ω) := rfl

theorem lintegral_rotation_latent (d : Data ι m) (j : Fin m) (k : d.G.Kernel) (z : ℝ)
    (f : E → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ ω, f (rotation d j k z ω) ∂seedMeasure d) =
    ∫⁻ s, ∫⁻ u, ∫⁻ n₁, ∫⁻ n₂,
      f (rotationOfObservation d k z
        (d.G.rho k • u+Real.sqrt (d.G.variance k) • n₁)
        (u+Real.sqrt (d.G.variance k) • n₂) s)
      ∂stdGaussian E ∂stdGaussian E ∂baseLaw d.F d.x d.r ∂stdGaussian E :=
  lintegral_actual_observation d j k _
    (hf.comp (continuous_rotationOfObservation d k z).measurable)

omit [DecidableEq ι] in
theorem rotation_coefficients_sq (d : Data ι m) (k : d.G.Kernel) (z : ℝ) :
    ((d.G.rho k)^2+Real.cos (z/d.G.rotationScale k))^2/(1+(d.G.rho k)^2)^2 +
    (d.G.rho k*(1-Real.cos (z/d.G.rotationScale k)))^2/(1+(d.G.rho k)^2)^2 +
    (d.G.rotationScale k/Real.sqrt (d.G.variance k)*Real.sin (z/d.G.rotationScale k))^2 = 1 := by
  have hden : 1+(d.G.rho k)^2 ≠ 0 := ne_of_gt (by positivity)
  have hv := d.G.variance_pos k
  have hs := Real.sq_sqrt hv.le
  have hr := d.G.rotationScale_sq k
  have htrig := Real.sin_sq_add_cos_sq (z/d.G.rotationScale k)
  simp only [mul_pow,div_pow,hs,hr]
  field_simp [hden,hv.ne']
  nlinarith [htrig]

omit [DecidableEq ι] in
theorem rotation_latent_expansion (d : Data ι m) (k : d.G.Kernel) (z : ℝ) (u n₁ n₂ s : E) :
    rotationOfObservation d k z
      (d.G.rho k • u+Real.sqrt (d.G.variance k) • n₁)
      (u+Real.sqrt (d.G.variance k) • n₂) s =
    d.G.rho k • u+Real.sqrt (d.G.variance k) •
      ((((d.G.rho k)^2+Real.cos (z/d.G.rotationScale k))/(1+(d.G.rho k)^2)) • n₁+
      ((d.G.rho k*(1-Real.cos (z/d.G.rotationScale k)))/(1+(d.G.rho k)^2)) • n₂+
      (d.G.rotationScale k/Real.sqrt (d.G.variance k)*Real.sin (z/d.G.rotationScale k)) • s) := by
  have hden : 1+(d.G.rho k)^2 ≠ 0 := ne_of_gt (by positivity)
  have hv : Real.sqrt (d.G.variance k) ≠ 0 := (Real.sqrt_pos.mpr (d.G.variance_pos k)).ne'
  unfold rotationOfObservation
  simp only [smul_add,smul_sub,smul_smul]
  match_scalars <;> field_simp [hden,hv] <;> ring

/-- Actual rotated-seed marginal. The retained latent joint is established first;
only then is the independent Gaussian row reduced to a standard Gaussian. -/
theorem lintegral_rotation_marginal (d : Data ι m) (j : Fin m) (k : d.G.Kernel) (z : ℝ)
    (f : E → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ ω, f (rotation d j k z ω) ∂seedMeasure d) =
      ∫⁻ y, f y ∂interpolationLaw d.F d.x d.r (d.G.rho k) := by
  have := baseLaw_isProbabilityMeasure d.hF d.hlo d.x d.r
  let A := ((d.G.rho k)^2+Real.cos (z/d.G.rotationScale k))/(1+(d.G.rho k)^2)
  let B := (d.G.rho k*(1-Real.cos (z/d.G.rotationScale k)))/(1+(d.G.rho k)^2)
  let C := d.G.rotationScale k/Real.sqrt (d.G.variance k)*Real.sin (z/d.G.rotationScale k)
  have hrow : C^2+A^2+B^2=1 := by
    have hh := rotation_coefficients_sq d k z
    dsimp [A,B,C]
    simp only [div_pow] at *
    linarith
  rw [lintegral_rotation_latent d j k z f hf]
  simp_rw [rotation_latent_expansion]
  change (∫⁻ s, ∫⁻ u, ∫⁻ n₁, ∫⁻ n₂,
    f (d.G.rho k • u+Real.sqrt (d.G.variance k) • (A • n₁+B • n₂+C • s))
    ∂stdGaussian E ∂stdGaussian E ∂baseLaw d.F d.x d.r ∂stdGaussian E) = _
  have hm : Measurable (fun p : E × E => ∫⁻ n₁, ∫⁻ n₂,
      f (d.G.rho k • p.2+Real.sqrt (d.G.variance k) • (A • n₁+B • n₂+C • p.1))
      ∂stdGaussian E ∂stdGaussian E) := by
    apply Measurable.lintegral_prod_right
    apply Measurable.lintegral_prod_right
    exact hf.comp (by fun_prop)
  rw [lintegral_lintegral_swap hm.aemeasurable,
    interpolationLaw,lintegral_map hf (by unfold interpolationMap; fun_prop),
    lintegral_prod (fun p : E × E => f (interpolationMap (d.G.rho k) p))
      (hf.comp (by unfold interpolationMap; fun_prop)).aemeasurable]
  apply lintegral_congr
  intro u
  have hfu : Measurable (fun y : E => f (d.G.rho k • u+Real.sqrt (d.G.variance k) • y)) :=
    hf.comp (by fun_prop)
  have hh := (gaussianRow3_preserving C A B hrow).lintegral_comp hfu
  rw [lintegral_prod (fun p : (E × E) × E =>
      f (d.G.rho k • u+Real.sqrt (d.G.variance k) • (C • p.1.1+A • p.1.2+B • p.2)))
      (show AEMeasurable (fun p : (E × E) × E =>
        f (d.G.rho k • u+Real.sqrt (d.G.variance k) • (C • p.1.1+A • p.1.2+B • p.2))) _ from
        (hf.comp (by fun_prop)).aemeasurable)] at hh
  rw [lintegral_prod (fun p : E × E => ∫⁻ n₂,
      f (d.G.rho k • u+Real.sqrt (d.G.variance k) • (C • p.1+A • p.2+B • n₂)) ∂stdGaussian E)
      (show AEMeasurable (fun p : E × E => ∫⁻ n₂,
        f (d.G.rho k • u+Real.sqrt (d.G.variance k) • (C • p.1+A • p.2+B • n₂)) ∂stdGaussian E) _ from
        (show Measurable (fun p : (E × E) × E =>
          f (d.G.rho k • u+Real.sqrt (d.G.variance k) • (C • p.1.1+A • p.1.2+B • p.2))) from
          hf.comp (by fun_prop)).lintegral_prod_right.aemeasurable)] at hh
  simpa only [interpolationMap,conditionalVariance,MeanGeometry.variance,add_assoc,add_comm,add_left_comm] using hh

theorem rotation_preserving (d : Data ι m) (j : Fin m) (k : d.G.Kernel) (z : ℝ) :
    MeasurePreserving (rotation d j k z) (seedMeasure d)
      (interpolationLaw d.F d.x d.r (d.G.rho k)) := by
  let R : (E × E) × E → E := fun p => rotationOfObservation d k z p.1.1
    (observationFromNoise d k p.1.1 p.2) p.1.2
  have ho : Continuous (fun p : (E × E) × E => observationFromNoise d k p.1.1 p.2) :=
    (continuous_observationFromNoise d k).comp (continuous_fst.fst.prodMk continuous_snd)
  have hp : Continuous (fun p : (E × E) × E =>
      ((p.1.1, observationFromNoise d k p.1.1 p.2),p.1.2)) :=
    (continuous_fst.fst.prodMk ho).prodMk continuous_fst.snd
  have hR : Measurable R := ((continuous_rotationOfObservation d k z).comp hp).measurable
  have hm' := hR.comp (backward_score_noise_preserving d j k).measurable
  have he : rotation d j k z = R ∘ (fun ω : Seed d =>
      ((backward d j (d.G.rho k) ω,score d (centerNode j) ω),ω.2 j k)) := rfl
  have hm : Measurable (rotation d j k z) := he.symm ▸ hm'
  refine ⟨hm,?_⟩
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_map hf hm]
  exact lintegral_rotation_marginal d j k z f hf

theorem forward_preserving (d : Data ι m) (j : Fin m) (k : d.G.Kernel) (z t : ℝ) :
    MeasurePreserving (forward d j k z t) (seedMeasure d)
      (interpolationLaw d.F d.x d.r (SamplingFlowLp.sourceTime d.G.backwardEnd_pos.le t)) := by
  have ht := SamplingFlowLp.sourceTime_mem d.G.backwardEnd_pos.le t
  have hflow := TransportFlowLp.flow_preserving (transportData d) d.x
    ⟨d.G.rho k,(d.G.rho_mem k).1,(d.G.rho_mem k).2.le⟩ ht
  have he : TransportFlowLp.flow (transportData d) d.x
      ⟨d.G.rho k,(d.G.rho_mem k).1,(d.G.rho_mem k).2.le⟩
      (SamplingFlowLp.sourceTime d.G.backwardEnd_pos.le t) =
    TransportFlowLp.flow (transportData d) d.x
      ⟨d.G.rho k,(d.G.rho_mem k).1,(d.G.rho_mem k).2.le⟩ t := by
    funext p
    unfold TransportFlowLp.flow
    rw [SamplingFlowLp.sourceTime_eq d.G.backwardEnd_pos.le ht]
  rw [he] at hflow
  exact hflow.comp (rotation_preserving d j k z)

theorem lintegral_forwardMean_marginal (d : Data ι m) (j : Fin m) (k : d.G.Kernel) (z t : ℝ)
    (f : E → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ ω, f (forwardMean d j k z t ω) ∂seedMeasure d) =
    ∫⁻ y, f (Gibbs.primitiveMean d.F
      (d.x+(d.r*SamplingFlowLp.sourceTime d.G.backwardEnd_pos.le t) • y)
      (d.r*Real.sqrt (1-(SamplingFlowLp.sourceTime d.G.backwardEnd_pos.le t)^2)))
      ∂interpolationLaw d.F d.x d.r (SamplingFlowLp.sourceTime d.G.backwardEnd_pos.le t) := by
  let a := SamplingFlowLp.sourceTime d.G.backwardEnd_pos.le t
  have ha := SamplingFlowLp.sourceTime_mem d.G.backwardEnd_pos.le t
  have hq : 0 < d.r*Real.sqrt (1-a^2) := by
    apply mul_pos d.hr
    apply Real.sqrt_pos.mpr
    dsimp [a]
    nlinarith [ha.1,ha.2,d.G.backwardEnd_lt_one]
  have hmean : Continuous (fun y : E => Gibbs.primitiveMean d.F
      (d.x+(d.r*a) • y) (d.r*Real.sqrt (1-a^2))) :=
    (Gibbs.primitive_mean_lipschitz d.hF d.hell d.hlo d.hup hq).continuous.comp
      (continuous_const.add (continuous_id.const_smul (d.r*a)))
  exact (forward_preserving d j k z t).lintegral_comp (hf.comp hmean.measurable)

end AcceleratedLogConcave.Numerics.MeanFlowLp
