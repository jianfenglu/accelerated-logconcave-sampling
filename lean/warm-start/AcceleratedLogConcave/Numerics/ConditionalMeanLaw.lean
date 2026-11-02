import AcceleratedLogConcave.Numerics.MeanResidualBridge
import AcceleratedLogConcave.Conditional.Flow.Restriction

noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace AcceleratedLogConcave.Numerics.SamplingCenterLp
open Conditional
variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι

theorem path_preserving (d : Data ι) (x : E) {t : ℝ} (ht : t ∈ Icc 0 d.b) :
    MeasurePreserving (path d x t) (stdGaussian E) (interpolationLaw d.F x d.r t) := by
  classical
  have hsub : Icc 0 t ⊆ Icc 0 d.b := fun _ hu => ⟨hu.1, hu.2.trans ht.2⟩
  have he (p : E) :
      convexProbabilityFlowHomeomorph d.hF d.hell d.hlo d.hup x d.hr ht.1
        (by norm_num) (ht.2.trans_lt d.hb1) ⟨0, le_rfl, ht.1⟩ ⟨t, ht.1, le_rfl⟩ p = path d x t p := by
    rw [convexProbabilityFlowHomeomorph_apply]
    change _ = convexProbabilityFlow d.hF d.hell d.hlo d.hup x d.hr d.hb
      (by norm_num) d.hb1 ⟨0,le_rfl,d.hb⟩ p (SamplingFlowLp.sourceTime d.hb t)
    rw [SamplingFlowLp.sourceTime_eq d.hb ht]
    exact meanProbabilityFlow_eq_on_subinterval ht.1 d.hb hsub d.r
      (conditionalMean d.F x d.r)
      (continuousOn_conditionalMean d.hF d.hlo d.hup x d.r (by norm_num) (ht.2.trans_lt d.hb1))
      (continuousOn_conditionalMean d.hF d.hlo d.hup x d.r (by norm_num) d.hb1)
      (fun u hu => lipschitzWith_conditionalMean d.hF d.hell d.hlo d.hup x d.hr
        (by linarith [hu.1]) (hu.2.trans_lt (ht.2.trans_lt d.hb1)))
      (fun u hu => lipschitzWith_conditionalMean d.hF d.hell d.hlo d.hup x d.hr
        (by linarith [hu.1]) (hu.2.trans_lt d.hb1)) ⟨0,le_rfl,ht.1⟩ ⟨t,ht.1,le_rfl⟩ p
  have hp := convexProbabilityFlow_measurePreserving_le d.hF d.hell d.hlo d.hup x d.hr ht.1
    (by norm_num) (ht.2.trans_lt d.hb1)
  rw [interpolationLaw_zero d.hF d.hlo x d.r] at hp
  convert hp using 1
  exact (funext he).symm

end AcceleratedLogConcave.Numerics.SamplingCenterLp

namespace AcceleratedLogConcave.Numerics.MeanFlowLp
open Conditional AffineGraph AffineGraph.MeanGeometry
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ}
local notation "E" => EuclideanSpace ℝ ι

def conditionalBaseCenter (d : Data ι m) (j : Fin m) (k : d.G.Kernel)
    (w : Centering.Phase E) : E := conditionalCenter d j k (w,0)

theorem conditionalCenter_eq_base (d : Data ι m) (j : Fin m) (k : d.G.Kernel)
    (ω : Seed d) : conditionalCenter d j k ω = conditionalBaseCenter d j k ω.1 := rfl

theorem continuous_conditionalBaseCenter (d : Data ι m) (j : Fin m) (k : d.G.Kernel) :
    Continuous (conditionalBaseCenter d j k) := by
  unfold conditionalBaseCenter conditionalCenter backward position phase
  apply continuous_const.add
  change Continuous ((d.r * d.G.rho k) • (fun w : Centering.Phase E =>
    TransportFlowLp.flow (transportData d) d.x _ (d.G.rho k)
      (CenteringFlowLp.phase (kernelData d) (d.sigma/2) (half_pos d.hsigma) (centerNode j) w).fst))
  apply Continuous.const_smul
  exact (TransportFlowLp.continuous_flow (transportData d) d.x _).comp
    (continuous_const.prodMk ((WithLp.prod_continuous_ofLp 2 E E).fst.comp
      ((CenteringFlowLp.continuous_phase (kernelData d) (d.sigma/2) (half_pos d.hsigma)).comp
        (continuous_const.prodMk continuous_id))))

/-- Actual random-center disintegration. No conditional-law hypothesis or moments
are assumed. Test functions may be unbounded and nonnegative. -/
theorem lintegral_conditional (d : Data ι m) (j : Fin m) (k : d.G.Kernel)
    {t : ℝ} (ht : t ∈ Icc 0 conditionalEnd) (f : E × E → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ ω, f (conditionalCenter d j k ω, conditional d j k t ω) ∂seedMeasure d) =
      ∫⁻ w, ∫⁻ y, f (conditionalBaseCenter d j k w,y)
        ∂interpolationLaw d.F (conditionalBaseCenter d j k w) (conditionalData d k).r t
        ∂KernelFlowLp.seedMeasure (kernelData d) := by
  have hX := (continuous_conditionalBaseCenter d j k).measurable
  have hpath : Measurable (fun ω : Seed d => conditional d j k t ω) := by
    simp only [conditional, conditionalCenter_eq_base]
    exact (SamplingCenterLp.continuous_path (conditionalData d k)).measurable.comp
      (f := fun ω : Seed d => (t,(conditionalBaseCenter d j k ω.1,ω.2 j k)))
      (measurable_const.prodMk ((hX.comp measurable_fst).prodMk
        (noise_projection_preserving d j k).measurable))
  change (∫⁻ ω, f (conditionalBaseCenter d j k ω.1, conditional d j k t ω) ∂
    (KernelFlowLp.seedMeasure (kernelData d)).prod _) = _
  rw [lintegral_prod (fun ω : Seed d => f (conditionalBaseCenter d j k ω.1, conditional d j k t ω))
    (show AEMeasurable (fun ω : Seed d => f (conditionalBaseCenter d j k ω.1, conditional d j k t ω)) _ from
      (hf.comp ((hX.comp measurable_fst).prodMk hpath)).aemeasurable)]
  apply lintegral_congr
  intro w
  let X := conditionalBaseCenter d j k w
  have hnoise : MeasurePreserving (fun z : Fin m → d.G.Kernel → E => z j k)
      (Measure.pi fun _ : Fin m => Measure.pi fun _ : d.G.Kernel => stdGaussian E)
      (stdGaussian E) :=
    (measurePreserving_eval (fun _ : d.G.Kernel => stdGaussian E) k).comp
      (measurePreserving_eval (fun _ : Fin m => Measure.pi fun _ : d.G.Kernel => stdGaussian E) j)
  have hflow := (SamplingCenterLp.path_preserving (conditionalData d k) X ht).comp hnoise
  exact hflow.lintegral_comp (f := fun y => f (X,y)) (hf.comp (measurable_const.prodMk measurable_id))

/-- Center-uniform nonnegative bounds integrate against the actual seed law.
This is a transfer interface, not a supplied analytic expression bound. -/
theorem lintegral_conditional_le (d : Data ι m) (j : Fin m) (k : d.G.Kernel)
    {t : ℝ} (ht : t ∈ Icc 0 conditionalEnd) (f : E × E → ℝ≥0∞) (hf : Measurable f)
    (C : ℝ≥0∞)
    (hC : ∀ x, (∫⁻ y, f (x,y) ∂interpolationLaw d.F x (conditionalData d k).r t) ≤ C) :
    (∫⁻ ω, f (conditionalCenter d j k ω, conditional d j k t ω) ∂seedMeasure d) ≤ C := by
  rw [lintegral_conditional d j k ht f hf]
  calc
    _ ≤ ∫⁻ _w, C ∂KernelFlowLp.seedMeasure (kernelData d) := lintegral_mono (fun w => hC _)
    _ = C := by simp

end AcceleratedLogConcave.Numerics.MeanFlowLp

namespace AcceleratedLogConcave.Numerics.MeanFlowLp
open Conditional AffineGraph AffineGraph.MeanGeometry
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ}
local notation "E" => EuclideanSpace ℝ ι

/-- The primitive on the conditional fiber is the actual receiver, not the
centered reply. The radius is exactly `r * sqrt (variance rho)`. -/
theorem conditionalMean_eq_fiber (d : Data ι m) (j : Fin m) (k : d.G.Kernel)
    {t : ℝ} (ht : t ∈ Icc 0 conditionalEnd) (ω : Seed d) :
    conditionalMean d j k t ω =
      Conditional.conditionalMean d.F (conditionalCenter d j k ω)
        (conditionalData d k).r t (conditional d j k t ω) := by
  rw [AffineFlowIdentities.conditionalMean_eq_primitiveMean d.hF d.hell d.hlo d.hup
    _ (conditionalData d k).hr (by linarith [ht.1]) (ht.2.trans_lt conditionalEnd_lt_one)]
  simp only [conditionalMean, SamplingFlowLp.sourceTime_eq conditionalEnd_pos.le ht]

theorem lintegral_conditionalMean (d : Data ι m) (j : Fin m) (k : d.G.Kernel)
    {t : ℝ} (ht : t ∈ Icc 0 conditionalEnd) (g : E → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ ω, g (conditionalMean d j k t ω) ∂seedMeasure d) =
      ∫⁻ w, ∫⁻ y, g (Conditional.conditionalMean d.F (conditionalBaseCenter d j k w)
        (conditionalData d k).r t y)
        ∂interpolationLaw d.F (conditionalBaseCenter d j k w) (conditionalData d k).r t
        ∂KernelFlowLp.seedMeasure (kernelData d) := by
  have hlo : -1 < t := by linarith [ht.1]
  have hhi : t < 1 := ht.2.trans_lt conditionalEnd_lt_one
  have hr : 0 < (conditionalData d k).r * Real.sqrt (1-t^2) :=
    mul_pos (conditionalData d k).hr (Real.sqrt_pos.mpr (by nlinarith))
  have hm : Continuous (fun q : E × E => Conditional.conditionalMean d.F q.1
      (conditionalData d k).r t q.2) := by
    simp_rw [AffineFlowIdentities.conditionalMean_eq_primitiveMean d.hF d.hell d.hlo d.hup
      _ (conditionalData d k).hr hlo hhi]
    have hc : Continuous (fun q : E × E => q.1 + ((conditionalData d k).r*t) • q.2) := by fun_prop
    exact (Gibbs.primitive_mean_lipschitz d.hF d.hell d.hlo d.hup hr).continuous.comp hc
  simpa only [conditionalMean_eq_fiber d j k ht] using
    lintegral_conditional d j k ht
      (fun q => g (Conditional.conditionalMean d.F q.1 (conditionalData d k).r t q.2))
      (hg.comp hm.measurable)

end AcceleratedLogConcave.Numerics.MeanFlowLp
