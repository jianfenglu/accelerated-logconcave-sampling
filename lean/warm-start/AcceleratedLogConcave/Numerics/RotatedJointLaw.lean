import AcceleratedLogConcave.Numerics.RotatedSeedLaw

noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace AcceleratedLogConcave.Numerics.TransportFlowLp
open Conditional
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
local notation "E" => EuclideanSpace ℝ ι

omit [DecidableEq ι] in
theorem flow_preserving (d : Data ι) (x : E) (s : Icc (0 : ℝ) d.b)
    {t : ℝ} (ht : t ∈ Icc 0 d.b) :
    MeasurePreserving (flow d x s t) (interpolationLaw d.F x d.r s)
      (interpolationLaw d.F x d.r t) := by
  have hm : Measurable (flow d x s t) := ((continuous_flow d x s).comp (continuous_const.prodMk continuous_id)).measurable
  refine ⟨hm, ?_⟩
  rw [← (SamplingCenterLp.path_preserving d x s.property).map_eq,
    Measure.map_map hm (SamplingCenterLp.path_preserving d x s.property).measurable]
  have he : (fun p => flow d x s t (SamplingCenterLp.path d x s p)) =
      SamplingCenterLp.path d x t := by
    funext p
    exact flow_cocycle d x ⟨0,le_rfl,d.hb⟩ s ⟨t,ht⟩ p
  change Measure.map (fun p => flow d x s t (SamplingCenterLp.path d x s p)) _ = _
  rw [he]
  exact (SamplingCenterLp.path_preserving d x ht).map_eq
end AcceleratedLogConcave.Numerics.TransportFlowLp

namespace AcceleratedLogConcave.Numerics.MeanFlowLp
open Conditional AffineGraph AffineGraph.MeanGeometry
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ}
local notation "E" => EuclideanSpace ℝ ι

omit [DecidableEq ι] in
/-- Exact standardized posterior conversion, including the original base potential. -/
theorem conditional_base_affine (d : Data ι m) (k : d.G.Kernel) (b : E) :
    Measure.map (fun q : E => d.G.rho k • b + Real.sqrt (d.G.variance k) • q)
      (baseLaw d.F (d.x+(d.r*d.G.rho k) • b) (d.r*Real.sqrt (d.G.variance k))) =
      conditionalLaw d.F d.x d.r (d.G.rho k) b := by
  have h := Gibbs.primitiveLaw_map_affine
    (F := primitivePotential d.F d.x d.r)
    (contDiff_primitivePotential d.hF d.x d.r).continuous.measurable
    (Real.sqrt_pos.mpr (d.G.variance_pos k)).ne' (d.G.rho k • b)
  rw [Real.sq_sqrt (d.G.variance_pos k).le] at h
  have he : Gibbs.primitiveLaw (primitivePotential d.F d.x d.r)
      (d.G.rho k • b) (Real.sqrt (d.G.variance k)) =
      baseLaw d.F (d.x+(d.r*d.G.rho k) • b) (d.r*Real.sqrt (d.G.variance k)) := by
    unfold Gibbs.primitiveLaw baseLaw primitivePotential
    congr 2
    funext q
    simp only [smul_add, smul_smul, add_assoc]
  rw [he] at h
  exact h

omit [DecidableEq ι] in
theorem conditionalEnd_variance_sqrt : Real.sqrt (conditionalVariance conditionalEnd) = conditionalEnd := by
  have hc : conditionalEnd^2 = (1:ℝ)/2 := by
    unfold conditionalEnd
    rw [div_pow,Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
    norm_num
  have hs := Real.sq_sqrt (show 0 ≤ conditionalVariance conditionalEnd by
    unfold conditionalVariance; rw [hc]; norm_num)
  have hp := conditionalEnd_pos
  have hnn := Real.sqrt_nonneg (conditionalVariance conditionalEnd)
  unfold conditionalVariance at *
  nlinarith

omit [DecidableEq ι] in
/-- The exact conditional-end observation kernel is posterior plus independent
Gaussian noise, not an independent second interpolation endpoint. -/
theorem conditional_observation_map (d : Data ι m) (k : d.G.Kernel) (b : E) :
    Measure.map (fun y : E => d.G.rho k • b +
      (Real.sqrt (d.G.variance k)/conditionalEnd) • y)
      (interpolationLaw d.F (d.x+(d.r*d.G.rho k) • b)
        (d.r*Real.sqrt (d.G.variance k)) conditionalEnd) =
    Measure.map (fun p : E × E => p.1+Real.sqrt (d.G.variance k) • p.2)
      ((conditionalLaw d.F d.x d.r (d.G.rho k) b).prod (stdGaussian E)) := by
  have := baseLaw_isProbabilityMeasure d.hF d.hlo
    (d.x+(d.r*d.G.rho k) • b) (d.r*Real.sqrt (d.G.variance k))
  rw [← conditional_base_affine d k b]
  conv_rhs => arg 2; arg 2; rw [← Measure.map_id (μ := stdGaussian E)]
  rw [Measure.map_prod_map _ _ (by fun_prop) measurable_id,
    Measure.map_map (by fun_prop) (by fun_prop), interpolationLaw,
    Measure.map_map (by fun_prop) (by unfold interpolationMap; fun_prop)]
  congr 1
  funext p
  dsimp [interpolationMap,Function.comp_def]
  rw [conditionalEnd_variance_sqrt]
  simp only [smul_add,smul_smul,div_mul_cancel₀ _ conditionalEnd_pos.ne']
  simp only [add_assoc]

/-- The retained (B,H) law is derived from the existing Bayes identity and
actual conditional endpoint. The two endpoints are never assumed independent. -/
theorem lintegral_observation_joint (d : Data ι m) (k : d.G.Kernel)
    (f : E × E → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ b, ∫⁻ y, f (b,d.G.rho k • b+(Real.sqrt (d.G.variance k)/conditionalEnd) • y)
      ∂interpolationLaw d.F (d.x+(d.r*d.G.rho k) • b)
        (d.r*Real.sqrt (d.G.variance k)) conditionalEnd
      ∂interpolationLaw d.F d.x d.r (d.G.rho k)) =
    ∫⁻ u, ∫⁻ n₁, ∫⁻ n₂,
      f (d.G.rho k • u+Real.sqrt (d.G.variance k) • n₁,
        u+Real.sqrt (d.G.variance k) • n₂)
      ∂stdGaussian E ∂stdGaussian E ∂baseLaw d.F d.x d.r := by
  let g : E × E → ℝ≥0∞ := fun p => ∫⁻ n, f (p.1,p.2+Real.sqrt (d.G.variance k) • n)
    ∂stdGaussian E
  have hg : Measurable g := by
    apply Measurable.lintegral_prod_right
    exact hf.comp (by fun_prop)
  have hb := conditional_disintegration_lintegral d.hF d.hlo d.x d.r (d.G.rho k)
    (d.G.variance_pos k) g hg
  refine Eq.trans ?_ hb
  apply lintegral_congr
  intro b
  have hfb : Measurable (fun h : E => f (b,h)) := hf.comp (measurable_const.prodMk measurable_id)
  rw [← lintegral_map hfb (show Measurable (fun y : E => d.G.rho k • b+
      (Real.sqrt (d.G.variance k)/conditionalEnd) • y) from by fun_prop),
    conditional_observation_map d k b, lintegral_map hfb (by fun_prop),
    lintegral_prod (fun p : E × E => f (b,p.1+Real.sqrt (d.G.variance k) • p.2))
      (show AEMeasurable (fun p : E × E => f (b,p.1+Real.sqrt (d.G.variance k) • p.2)) _ from
        (hfb.comp (by fun_prop)).aemeasurable)]

/-- Transported position and the actual centering score have the product law.
This independence is derived from phase preservation, not postulated. -/
theorem backward_score_preserving (d : Data ι m) (j : Fin m) (k : d.G.Kernel) :
    MeasurePreserving (fun w : Centering.Phase E =>
      (backward d j (d.G.rho k) (w,0), score d (centerNode j) (w,0)))
      (KernelFlowLp.seedMeasure (kernelData d))
      ((interpolationLaw d.F d.x d.r (d.G.rho k)).prod (stdGaussian E)) := by
  have := interpolationLaw_isProbabilityMeasure d.hF d.hlo d.x d.r (backwardEnd d.G.R)
  have hp := CenteringFlowLp.phase_preserving (kernelData d) (d.sigma/2)
    (half_pos d.hsigma) (centerNode j)
  have hpair : MeasurePreserving (WithLp.ofLp : Centering.Phase E → E × E)
      (KernelFlowLp.seedMeasure (kernelData d))
      ((interpolationLaw d.F d.x d.r (backwardEnd d.G.R)).prod (stdGaussian E)) := by
    refine ⟨(WithLp.prod_continuous_ofLp 2 E E).measurable, ?_⟩
    rw [KernelFlowLp.seedMeasure,Kinetic.coupledPhaseMeasure,
      Measure.map_map (by fun_prop) (by fun_prop)]
    exact Measure.map_id
  have ht := TransportFlowLp.flow_preserving (transportData d) d.x
    ⟨backwardEnd d.G.R,d.G.backwardEnd_pos.le,le_rfl⟩
    (t := d.G.rho k) ⟨(d.G.rho_mem k).1,(d.G.rho_mem k).2.le⟩
  change MeasurePreserving (TransportFlowLp.flow (transportData d) d.x _ (d.G.rho k))
    (interpolationLaw d.F d.x d.r (backwardEnd d.G.R))
    (interpolationLaw d.F d.x d.r (d.G.rho k)) at ht
  exact (ht.prod (MeasurePreserving.id (stdGaussian E))).comp (hpair.comp hp)

/-- The score/position product and one fresh conditional seed are retained together. -/
theorem backward_score_noise_preserving (d : Data ι m) (j : Fin m) (k : d.G.Kernel) :
    MeasurePreserving (fun ω : Seed d =>
      ((backward d j (d.G.rho k) ω, score d (centerNode j) ω),ω.2 j k))
      (seedMeasure d)
      (((interpolationLaw d.F d.x d.r (d.G.rho k)).prod (stdGaussian E)).prod (stdGaussian E)) := by
  have hn : MeasurePreserving (fun z : Fin m → d.G.Kernel → E => z j k)
      (Measure.pi fun _ : Fin m => Measure.pi fun _ : d.G.Kernel => stdGaussian E)
      (stdGaussian E) :=
    (measurePreserving_eval (fun _ : d.G.Kernel => stdGaussian E) k).comp
      (measurePreserving_eval (fun _ : Fin m => Measure.pi fun _ : d.G.Kernel => stdGaussian E) j)
  exact (backward_score_preserving d j k).prod hn

def observationFromNoise (d : Data ι m) (k : d.G.Kernel) (b n : E) : E :=
  d.G.rho k • b+(Real.sqrt (d.G.variance k)/conditionalEnd) •
    SamplingCenterLp.path (conditionalData d k) (d.x+(d.r*d.G.rho k) • b) conditionalEnd n

omit [DecidableEq ι] in
theorem continuous_observationFromNoise (d : Data ι m) (k : d.G.Kernel) :
    Continuous (fun p : E × E => observationFromNoise d k p.1 p.2) := by
  unfold observationFromNoise
  exact (continuous_fst.const_smul (d.G.rho k)).add
    (((SamplingCenterLp.continuous_path (conditionalData d k)).comp
      (continuous_const.prodMk ((continuous_const.add (continuous_fst.const_smul (d.r*d.G.rho k))).prodMk
        continuous_snd))).const_smul (Real.sqrt (d.G.variance k)/conditionalEnd))

/-- Full latent representation of the actual B, H and score, with fresh noises.
It follows from source transport, the exact endpoint and the existing Bayes theorem. -/
theorem lintegral_actual_observation (d : Data ι m) (j : Fin m) (k : d.G.Kernel)
    (f : (E × E) × E → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ ω, f ((backward d j (d.G.rho k) ω,
      observationFromNoise d k (backward d j (d.G.rho k) ω) (ω.2 j k)),
        score d (centerNode j) ω) ∂seedMeasure d) =
    ∫⁻ s, ∫⁻ u, ∫⁻ n₁, ∫⁻ n₂,
      f ((d.G.rho k • u+Real.sqrt (d.G.variance k) • n₁,
        u+Real.sqrt (d.G.variance k) • n₂),s)
      ∂stdGaussian E ∂stdGaussian E ∂baseLaw d.F d.x d.r ∂stdGaussian E := by
  have := interpolationLaw_isProbabilityMeasure d.hF d.hlo d.x d.r (d.G.rho k)
  let q : (E × E) × E → ℝ≥0∞ := fun p =>
    f ((p.1.1,observationFromNoise d k p.1.1 p.2),p.1.2)
  have hq : Measurable q := hf.comp
    ((measurable_fst.fst.prodMk ((continuous_observationFromNoise d k).measurable.comp
      (measurable_fst.fst.prodMk measurable_snd))).prodMk measurable_fst.snd)
  have hseed := (backward_score_noise_preserving d j k).lintegral_comp hq
  change (∫⁻ ω, q ((backward d j (d.G.rho k) ω,score d (centerNode j) ω),ω.2 j k)
    ∂seedMeasure d) = _
  rw [hseed,lintegral_prod q hq.aemeasurable,
    lintegral_prod (fun p : E × E => ∫⁻ n, q (p,n) ∂stdGaussian E)
      hq.lintegral_prod_right.aemeasurable,
    lintegral_lintegral_swap hq.lintegral_prod_right.aemeasurable]
  apply lintegral_congr
  intro s
  have hfs : Measurable (fun p : E × E => f (p,s)) :=
    hf.comp (measurable_id.prodMk measurable_const)
  refine Eq.trans ?_ (lintegral_observation_joint d k _ hfs)
  apply lintegral_congr
  intro b
  exact (SamplingCenterLp.path_preserving (conditionalData d k)
    (d.x+(d.r*d.G.rho k) • b) ⟨conditionalEnd_pos.le,le_rfl⟩).lintegral_comp
      (f := fun y => f ((b,d.G.rho k • b+(Real.sqrt (d.G.variance k)/conditionalEnd) • y),s))
      (hf.comp (by fun_prop))

end AcceleratedLogConcave.Numerics.MeanFlowLp
