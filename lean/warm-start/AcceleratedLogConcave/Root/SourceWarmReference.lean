import AcceleratedLogConcave.Root.SourceWarmSampler
import AcceleratedLogConcave.Kinetic.OriginalReferenceDimension
import AcceleratedLogConcave.Kinetic.OriginalReferenceBaseAlignment

/-! The accepted source reference phase at the same public schedule, with
its invariance and finite mixing bound supplied by the proved W12 contraction.
No local implementation error is assumed in this reference-only module. -/
noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option quotPrecheck false
open MeasureTheory ProbabilityTheory
namespace AcceleratedLogConcave.Root.SourceWarmReference
open Oracle Numerics Kinetic Kinetic.Reheating
variable (η Cw ε : ℝ) (D : ℕ) (hη : 0<η)
  (hD : SourceWarmSchedule.dimensionThreshold η Cw ε SourceWarmSampler.costCoefficient≤D)
  {κ : ℝ} (hκ : 1≤κ) {V : Point D→ℝ} (hV : ContDiff ℝ 2 V)
  (hlo : ∀ z v,κ⁻¹*‖v‖^2≤fderiv ℝ (fderiv ℝ V) z v v)
  (hup : ∀ z v,fderiv ℝ (fderiv ℝ V) z v v≤‖v‖^2)
local notation "P" => SourceWarmSchedule.schedule η Cw D
local notation "hk" => (show 0<κ from lt_of_lt_of_le (by norm_num) hκ)
local notation "hR" => SourceWarmSampler.radius_guard η Cw ε D hη hD
local notation "hc" => ((SourceWarmSchedule.scalar_guards η Cw D).2.1)
local notation "hsmall" => ((SourceWarmSchedule.scalar_guards η Cw D).2.2.1)
local notation "hK" => ((SourceWarmSchedule.scalar_guards η Cw D).1)
local notation "hC" => ((SourceWarmSchedule.scalar_guards η Cw D).2.2.2)
local notation "hy" => SourceWarmSampler.cubic_threshold η Cw ε D hη hD
local notation "hh" => (P).delta_pos
local notation "hhalf" => FinalMeanScheduledData.delta_half P hK hc hsmall hC hy
local notation "hm" => (show 0<(P).m from lt_of_lt_of_le (by norm_num) ((P).m_ge_two hc hsmall (by have := hC; linarith)))
local notation "M" => (CubicExecutableWorkShift.source P hR).M
local notation "hbig" => (show 2*(P).delta^2<2*(2*(P).delta^2) from by nlinarith [sq_pos_of_pos hh])
local notation "probG" => Gibbs.originalGibbs_probability_of_hessian_lower hV hk hlo
local notation "H" => originalHeatMixingFamily (R:=2*(2*(P).delta^2)) hV hk hh hbig hlo hup
local notation "Q" => OriginalReferenceMixing.referenceKernel hV hk hh hhalf hlo hup M hm (P).t ((P).t_pos hc) (P).K
local notation "Γ" => Real.sqrt ((κ+2*(P).delta^2)⁻¹)*(P).delta

def phase : Kernel (Point D×Point D) (Point D×Point D) := by
  letI := probG
  exact ReferencePhaseLaw.phaseKernel H (by have := hh; positivity) hbig (Real.sqrt 2*(P).delta) Γ Q
instance phase_markov : IsMarkovKernel (phase η Cw ε D hη hD hκ hV hlo hup) := by
  unfold phase
  infer_instance

theorem invariant : phase η Cw ε D hη hD hκ hV hlo hup ∘ₘ
    Schedule.Dyadic.phaseReference V (Schedule.Dyadic.sourceVariance (P).delta)=
      Schedule.Dyadic.phaseReference V (Schedule.Dyadic.sourceVariance (P).delta) := by
  let := probG
  rw [OriginalReferenceBaseAlignment.phaseReference_eq_source_clock_base hV hk hh hlo hup]
  exact ReferencePhaseLaw.phaseKernel_invariant H (by have := hh; positivity) hbig _ _ (by have := hh; positivity) Q
    (fun clock => OriginalReferenceMixing.referenceKernel_invariant hV hk hh hhalf hlo hup M hm
      (P).t ((P).t_pos hc) (P).K clock)
/-- Every accepted reference iterate is the literal homogeneous phase law. -/
theorem iterate_eq (ν : Measure (Point D×Point D)) (n : ℕ) :
    let := probG
    ReferencePhaseLaw.kernelIterateLaw H (by have := hh; positivity) hbig
      (Real.sqrt 2*(P).delta) Γ Q ν n=
    Probability.referenceLaw ν (fun _ => phase η Cw ε D hη hD hκ hV hlo hup) n := by
  let := probG
  induction n with
  | zero => rfl
  | succ n ih =>
    change ReferencePhaseLaw.phaseKernel H (by have := hh; positivity) hbig _ _ Q ∘ₘ
      ReferencePhaseLaw.kernelIterateLaw H (by have := hh; positivity) hbig _ _ Q ν n=_
    rw [ih]
    rfl

/-- All reference mixing hypotheses are discharged by the one public
threshold; the input may be an arbitrary joint warm position/momentum law. -/
theorem finite_mixing (hCw : 0≤Cw) (hε : 0<ε)
    (ν : Measure (Point D×Point D)) [IsProbabilityMeasure ν]
    (hw : Probability.L2Warm
      (Schedule.Dyadic.phaseReference V (Schedule.Dyadic.sourceVariance (P).delta)) ν ((D:ℝ)^Cw)) :
    letI := Schedule.Dyadic.phaseReference_isProbabilityMeasure
      (Gibbs.integrable_exp_neg_of_hessian_lower hV (inv_pos.mpr hk) hlo)
      (Schedule.Dyadic.sourceVariance (P).delta)
    Probability.totalVariationDistance
      (Probability.referenceLaw ν (fun _ => phase η Cw ε D hη hD hκ hV hlo hup)
        (SourceWarmSampler.phases η Cw ε D κ))
      (Schedule.Dyadic.phaseReference V (Schedule.Dyadic.sourceVariance (P).delta))≤ε/4 := by
  let := probG
  have hd : (1:ℝ)≤D := by exact_mod_cast (SourceWarmSchedule.dimension_components hD).1
  have hb : (D:ℝ)^Cw≤(D:ℝ)^(Cw+1) :=
    Real.rpow_le_rpow_of_exponent_le hd (by linarith)
  have hw' := hw.mono hb
  simp only [OriginalReferenceBaseAlignment.phaseReference_eq_source_clock_base hV hk hh hlo hup] at hw' ⊢
  have hp := source_dimension_mixing_parameters (SourceWarmSchedule.exponent_pos hη) hκ
    (SourceWarmSchedule.dimension_components hD).2.1
  rw [← SourceWarmSchedule.delta_eq hD] at hp
  have ht := OriginalReferencePhaseLaw.original_reference_warmTV_horizon
    hV hk hh hlo hup M hm (P).t ((P).t_pos hc) (P).K hκ hp.1 hp.2.2.2.2.2
    hp.2.1 hp.2.2.2.1 hp.2.2.2.2.1 ν ((D:ℝ)^(Cw+1)) (ε/4) hw'
    (Real.one_le_rpow hd (by linarith)) (by have := hh; positivity)
  have he := ReferencePhaseLaw.warmIterate_eq_kernelIterate H (by have := hh; positivity) hbig
    (Real.sqrt 2*(P).delta) Γ (by have := hh; positivity) Q
    (fun clock => OriginalReferenceMixing.referenceKernel_invariant hV hk hh hhalf hlo hup M hm
      (P).t ((P).t_pos hc) (P).K clock) hw' (SourceWarmSampler.phases η Cw ε D κ)
  have hie := iterate_eq η Cw ε D hη hD hκ hV hlo hup ν (SourceWarmSampler.phases η Cw ε D κ)
  simp only [SourceWarmSampler.phases] at he hie ⊢
  simpa only [he,hie] using ht
end AcceleratedLogConcave.Root.SourceWarmReference
