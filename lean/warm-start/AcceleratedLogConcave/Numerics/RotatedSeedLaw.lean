import AcceleratedLogConcave.Numerics.ConditionalMeanLaw

noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace AcceleratedLogConcave.Numerics.MeanFlowLp
open Conditional AffineGraph AffineGraph.MeanGeometry
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ}
local notation "E" => EuclideanSpace ℝ ι

/-- Full initial-phase disintegration retains the score/position dependence.
Unlike a center-only test identity, this can be used for the actual rotation. -/
theorem lintegral_phase_conditional (d : Data ι m) (j : Fin m) (k : d.G.Kernel)
    {t : ℝ} (ht : t ∈ Icc 0 conditionalEnd)
    (f : Centering.Phase E × E → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ ω, f (ω.1, conditional d j k t ω) ∂seedMeasure d) =
      ∫⁻ w, ∫⁻ y, f (w,y)
        ∂interpolationLaw d.F (conditionalBaseCenter d j k w) (conditionalData d k).r t
        ∂KernelFlowLp.seedMeasure (kernelData d) := by
  have hX := (continuous_conditionalBaseCenter d j k).measurable
  have hpath : Measurable (fun ω : Seed d => conditional d j k t ω) := by
    simp only [conditional, conditionalCenter_eq_base]
    exact (SamplingCenterLp.continuous_path (conditionalData d k)).measurable.comp
      (f := fun ω : Seed d => (t,(conditionalBaseCenter d j k ω.1,ω.2 j k)))
      (measurable_const.prodMk ((hX.comp measurable_fst).prodMk
        (noise_projection_preserving d j k).measurable))
  change (∫⁻ ω, f (ω.1, conditional d j k t ω) ∂
    (KernelFlowLp.seedMeasure (kernelData d)).prod _) = _
  rw [lintegral_prod (fun ω : Seed d => f (ω.1, conditional d j k t ω))
    (show AEMeasurable (fun ω : Seed d => f (ω.1, conditional d j k t ω)) _ from
      (hf.comp (measurable_fst.prodMk hpath)).aemeasurable)]
  apply lintegral_congr
  intro w
  have hnoise : MeasurePreserving (fun z : Fin m → d.G.Kernel → E => z j k)
      (Measure.pi fun _ : Fin m => Measure.pi fun _ : d.G.Kernel => stdGaussian E)
      (stdGaussian E) :=
    (measurePreserving_eval (fun _ : d.G.Kernel => stdGaussian E) k).comp
      (measurePreserving_eval (fun _ : Fin m => Measure.pi fun _ : d.G.Kernel => stdGaussian E) j)
  have hflow := (SamplingCenterLp.path_preserving (conditionalData d k)
    (conditionalBaseCenter d j k w) ht).comp hnoise
  exact hflow.lintegral_comp (f := fun y => f (w,y))
    (hf.comp (measurable_const.prodMk measurable_id))

/-- The actual rotation with the conditional endpoint replaced by its integration variable.
The initial phase is retained, not resampled and not declared Gaussian. -/
def rotationFiber (d : Data ι m) (j : Fin m) (k : d.G.Kernel) (z : ℝ)
    (w : Centering.Phase E) (y : E) : E :=
  let B := backward d j (d.G.rho k) (w,0)
  let H := d.G.rho k • B + (Real.sqrt (d.G.variance k)/conditionalEnd) • y
  let mid := (d.G.rho k/(1+(d.G.rho k)^2)) • (H+d.G.rho k • B)
  mid+Real.cos (z/d.G.rotationScale k) • (B-mid)+
    (d.G.rotationScale k*Real.sin (z/d.G.rotationScale k)) • score d (centerNode j) (w,0)

theorem rotation_eq_fiber (d : Data ι m) (j : Fin m) (k : d.G.Kernel) (z : ℝ)
    (ω : Seed d) :
    rotation d j k z ω = rotationFiber d j k z ω.1 (conditional d j k conditionalEnd ω) := rfl

theorem continuous_rotationFiber (d : Data ι m) (j : Fin m) (k : d.G.Kernel) (z : ℝ) :
    Continuous (fun p : Centering.Phase E × E => rotationFiber d j k z p.1 p.2) := by
  have hp : Continuous (fun w : Centering.Phase E =>
      CenteringFlowLp.phase (kernelData d) (d.sigma/2) (half_pos d.hsigma) (centerNode j) w) :=
    (CenteringFlowLp.continuous_phase (kernelData d) (d.sigma/2) (half_pos d.hsigma)).comp
      (continuous_const.prodMk continuous_id)
  have hB : Continuous (fun w : Centering.Phase E => backward d j (d.G.rho k) (w,0)) := by
    exact (TransportFlowLp.continuous_flow (transportData d) d.x _).comp
      (continuous_const.prodMk ((WithLp.prod_continuous_ofLp 2 E E).fst.comp hp))
  have hS : Continuous (fun w : Centering.Phase E => score d (centerNode j) (w,0)) :=
    (WithLp.prod_continuous_ofLp 2 E E).snd.comp hp
  have hmid : Continuous (fun p : Centering.Phase E × E =>
      (d.G.rho k/(1+(d.G.rho k)^2)) •
        ((d.G.rho k • backward d j (d.G.rho k) (p.1,0) +
          (Real.sqrt (d.G.variance k)/conditionalEnd) • p.2) +
            d.G.rho k • backward d j (d.G.rho k) (p.1,0))) :=
    ((((hB.comp continuous_fst).const_smul (d.G.rho k)).add
      (continuous_snd.const_smul (Real.sqrt (d.G.variance k)/conditionalEnd))).add
      ((hB.comp continuous_fst).const_smul (d.G.rho k))).const_smul (d.G.rho k/(1+(d.G.rho k)^2))
  exact (hmid.add (((hB.comp continuous_fst).sub hmid).const_smul
    (Real.cos (z/d.G.rotationScale k)))).add
      ((hS.comp continuous_fst).const_smul (d.G.rotationScale k*Real.sin (z/d.G.rotationScale k)))

/-- Exact source-faithful test-integral reduction. This is not yet the assertion
that the rotated marginal equals the interpolation law: that needs the retained
Gaussian conditional identity, not independence of B and H. -/
theorem lintegral_rotation (d : Data ι m) (j : Fin m) (k : d.G.Kernel) (z : ℝ)
    (f : E → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ ω, f (rotation d j k z ω) ∂seedMeasure d) =
      ∫⁻ w, ∫⁻ y, f (rotationFiber d j k z w y)
        ∂interpolationLaw d.F (conditionalBaseCenter d j k w) (conditionalData d k).r conditionalEnd
        ∂KernelFlowLp.seedMeasure (kernelData d) := by
  simpa only [rotation_eq_fiber] using
    lintegral_phase_conditional d j k ⟨conditionalEnd_pos.le,le_rfl⟩
      (fun p => f (rotationFiber d j k z p.1 p.2))
      (hf.comp (continuous_rotationFiber d j k z).measurable)

/-- The same actual-seed reduction after deterministic forward transport.
No interpolation marginal equality is inserted as a hypothesis. -/
theorem lintegral_forward (d : Data ι m) (j : Fin m) (k : d.G.Kernel) (z t : ℝ)
    (f : E → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ ω, f (forward d j k z t ω) ∂seedMeasure d) =
      ∫⁻ w, ∫⁻ y, f (TransportFlowLp.flow (transportData d) d.x
        ⟨d.G.rho k,(d.G.rho_mem k).1,(d.G.rho_mem k).2.le⟩ t
        (rotationFiber d j k z w y))
        ∂interpolationLaw d.F (conditionalBaseCenter d j k w) (conditionalData d k).r conditionalEnd
        ∂KernelFlowLp.seedMeasure (kernelData d) := by
  exact lintegral_rotation d j k z
    (fun v => f (TransportFlowLp.flow (transportData d) d.x
      ⟨d.G.rho k,(d.G.rho_mem k).1,(d.G.rho_mem k).2.le⟩ t v))
    (hf.comp ((TransportFlowLp.continuous_flow (transportData d) d.x _).comp
      (continuous_const.prodMk continuous_id)).measurable)

/-- At zero angle the actual random rotated seed is exactly B, pointwise. -/
theorem rotation_zero_actual (d : Data ι m) (j : Fin m) (k : d.G.Kernel) (ω : Seed d) :
    rotation d j k 0 ω = backward d j (d.G.rho k) ω := by
  simp [rotation]

/-- Exact actual forward-mean test integral, retaining all joint conditioning.
This supplier proves no derivative or uniform jet estimate. -/
theorem lintegral_forwardMean (d : Data ι m) (j : Fin m) (k : d.G.Kernel) (z t : ℝ)
    (f : E → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ ω, f (forwardMean d j k z t ω) ∂seedMeasure d) =
      ∫⁻ w, ∫⁻ y, f (Gibbs.primitiveMean d.F
        (d.x + (d.r * SamplingFlowLp.sourceTime d.G.backwardEnd_pos.le t) •
          TransportFlowLp.flow (transportData d) d.x
            ⟨d.G.rho k,(d.G.rho_mem k).1,(d.G.rho_mem k).2.le⟩ t
            (rotationFiber d j k z w y))
        (d.r * Real.sqrt (1-(SamplingFlowLp.sourceTime d.G.backwardEnd_pos.le t)^2)))
        ∂interpolationLaw d.F (conditionalBaseCenter d j k w) (conditionalData d k).r conditionalEnd
        ∂KernelFlowLp.seedMeasure (kernelData d) := by
  let a := SamplingFlowLp.sourceTime d.G.backwardEnd_pos.le t
  have ha := SamplingFlowLp.sourceTime_mem d.G.backwardEnd_pos.le t
  have hq : 0 < d.r * Real.sqrt (1-a^2) := by
    apply mul_pos d.hr
    apply Real.sqrt_pos.mpr
    dsimp [a]
    nlinarith [ha.1,ha.2,d.G.backwardEnd_lt_one]
  have hmean : Continuous (fun v : E => Gibbs.primitiveMean d.F
      (d.x+(d.r*a) • v) (d.r*Real.sqrt (1-a^2))) :=
    (Gibbs.primitive_mean_lipschitz d.hF d.hell d.hlo d.hup hq).continuous.comp
      (continuous_const.add (continuous_id.const_smul (d.r*a)))
  exact lintegral_forward d j k z t _ (hf.comp hmean.measurable)

end AcceleratedLogConcave.Numerics.MeanFlowLp
