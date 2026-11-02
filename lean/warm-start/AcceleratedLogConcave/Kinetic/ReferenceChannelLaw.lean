import AcceleratedLogConcave.Kinetic.ReferenceChannel
import AcceleratedLogConcave.Probability.WarmCenteredDensity
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! A genuine output probability obtained by weighting an actual reference
coupling by the supplied input density. The construction uses its full input
law and does not assume coordinate independence. -/
noncomputable section
open MeasureTheory
set_option autoImplicit false
namespace AcceleratedLogConcave.Kinetic.ReferenceChannelLaw
open Analysis.Poisson
variable {X Ω : Type*} [MeasurableSpace X] [MeasurableSpace Ω]
  {μ ν : Measure X} {η : Measure Ω}
  [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [IsProbabilityMeasure η]
  {p q : Ω → X}

def weightedTape (ν : Measure X) (η : Measure Ω) (μ : Measure X) (p : Ω → X) : Measure Ω :=
  η.withDensity (fun ω => ν.rnDeriv μ (p ω))

def outputLaw (ν : Measure X) (η : Measure Ω) (μ : Measure X) (p q : Ω → X) : Measure X :=
  (weightedTape ν η μ p).map q

omit [IsProbabilityMeasure η] in
theorem weightedTape_probability (hp : MeasurePreserving p η μ) (hν : ν ≪ μ) :
    IsProbabilityMeasure (weightedTape ν η μ p) := by
  constructor
  rw [weightedTape, withDensity_apply _ MeasurableSet.univ]
  simp only [Measure.restrict_univ]
  rw [hp.lintegral_comp (Measure.measurable_rnDeriv ν μ), Measure.lintegral_rnDeriv hν]
  simp

omit [IsProbabilityMeasure η] in
theorem outputLaw_probability (hp : MeasurePreserving p η μ)
    (_hq : MeasurePreserving q η μ) (hν : ν ≪ μ) :
    IsProbabilityMeasure (outputLaw ν η μ p q) := by
  have := weightedTape_probability hp hν
  unfold outputLaw
  infer_instance

omit [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [IsProbabilityMeasure η] in
theorem outputLaw_absolutelyContinuous (hq : MeasurePreserving q η μ) :
    outputLaw ν η μ p q ≪ μ := by
  rw [← hq.map_eq]
  exact (withDensity_absolutelyContinuous η _).map hq.measurable

omit [IsProbabilityMeasure η] in
/-- The operator density paired against a measurable event is the actual
weighted tape event integral. -/
theorem density_setIntegral (hp : MeasurePreserving p η μ)
    (hq : MeasurePreserving q η μ) (f : Lp ℝ 2 μ)
    {s : Set X} (hs : MeasurableSet s) :
    ∫ x in s, ((referenceChannel hp hq).adjoint f) x ∂μ =
      ∫ ω, f (p ω) * s.indicator (fun _ => (1:ℝ)) (q ω) ∂η := by
  let g : Lp ℝ 2 μ := indicatorConstLp 2 hs (measure_ne_top μ s) (1:ℝ)
  have hpair := referenceChannel_pairing hq hp g f
  rw [← referenceChannel_adjoint hp hq] at hpair
  have hleft : inner ℝ g ((referenceChannel hp hq).adjoint f) =
      ∫ x in s, ((referenceChannel hp hq).adjoint f) x ∂μ := by
    rw [L2.inner_def, ← integral_indicator hs]
    apply integral_congr_ae
    filter_upwards [indicatorConstLp_coeFn (p := 2) (hs := hs) (hμs := measure_ne_top μ s) (c := (1:ℝ))] with x hx
    simp only [RCLike.inner_apply, conj_trivial]
    rw [mul_comm]
    change g x * ((referenceChannel hp hq).adjoint f) x = _
    rw [show g x = s.indicator (fun _ => (1:ℝ)) x from hx]
    by_cases hxmem : x ∈ s <;> simp [hxmem]
  rw [hleft] at hpair
  apply hpair.trans
  apply integral_congr_ae
  filter_upwards [hq.quasiMeasurePreserving.ae
    (indicatorConstLp_coeFn (p := 2) (hs := hs) (hμs := measure_ne_top μ s) (c := (1:ℝ)))] with ω hω
  rw [show g (q ω) = s.indicator (fun _ => (1:ℝ)) (q ω) from hω]
  ring


omit [IsProbabilityMeasure η] in
theorem output_event (hp : MeasurePreserving p η μ)
    (hq : MeasurePreserving q η μ) (hν : ν ≪ μ)
    {s : Set X} (hs : MeasurableSet s) :
    (outputLaw ν η μ p q).real s =
      ∫ ω, (ν.rnDeriv μ (p ω)).toReal * s.indicator (fun _ => (1:ℝ)) (q ω) ∂η := by
  have := weightedTape_probability hp hν
  have := outputLaw_probability hp hq hν
  have hi : Measurable (s.indicator (fun _ : X => (1:ℝ))) :=
    measurable_const.indicator hs
  calc
    _ = ∫ x, s.indicator (fun _ => (1:ℝ)) x ∂outputLaw ν η μ p q := by
      rw [integral_indicator hs]
      simp
    _ = ∫ ω, s.indicator (fun _ => (1:ℝ)) (q ω) ∂weightedTape ν η μ p := by
      exact integral_map hq.measurable.aemeasurable hi.aestronglyMeasurable
    _ = _ := by
      unfold weightedTape
      have he := integral_withDensity_eq_integral_toReal_smul
        (show Measurable (fun ω => ν.rnDeriv μ (p ω)) from
          (Measure.measurable_rnDeriv ν μ).comp hp.measurable)
        (hp.quasiMeasurePreserving.ae (Measure.rnDeriv_lt_top ν μ))
        (fun ω => s.indicator (fun _ => (1:ℝ)) (q ω))
      exact he


omit [IsProbabilityMeasure η] in
/-- The RN density of the genuine positive output measure is the L² density
adjoint, derived by measurable-event tests rather than postulated. -/
theorem output_rnDeriv (hp : MeasurePreserving p η μ)
    (hq : MeasurePreserving q η μ) {B : ℝ}
    (h : AcceleratedLogConcave.Probability.L2Warm μ ν B) :
    (fun x => ((outputLaw ν η μ p q).rnDeriv μ x).toReal) =ᵐ[μ]
      ((referenceChannel hp hq).adjoint
        (h.memLp.toLp (fun x => (ν.rnDeriv μ x).toReal)) : X → ℝ) := by
  have := outputLaw_probability hp hq h.absolutelyContinuous
  let f := h.memLp.toLp (fun x => (ν.rnDeriv μ x).toReal)
  let g := (referenceChannel hp hq).adjoint f
  apply Integrable.ae_eq_of_forall_setIntegral_eq _ _
    Measure.integrable_toReal_rnDeriv ((Lp.memLp g).integrable (by norm_num))
  intro s hs _
  rw [Measure.setIntegral_toReal_rnDeriv (outputLaw_absolutelyContinuous hq),
    density_setIntegral hp hq f hs, output_event hp hq h.absolutelyContinuous hs]
  apply integral_congr_ae
  filter_upwards [hp.quasiMeasurePreserving.ae h.memLp.coeFn_toLp] with ω hω
  rw [show f (p ω) = (ν.rnDeriv μ (p ω)).toReal from hω]


theorem density_eq_centered_add_one {B : ℝ}
    (h : AcceleratedLogConcave.Probability.L2Warm μ ν B) :
    h.memLp.toLp (fun x => (ν.rnDeriv μ x).toReal) =
      (h.centeredDensity : Lp ℝ 2 μ)+oneL2 μ := by
  apply Lp.ext
  filter_upwards [h.memLp.coeFn_toLp, h.centeredDensity_coe_ae,
    (memLp_const (1:ℝ) (μ := μ) (p := 2)).coeFn_toLp,
    Lp.coeFn_add (h.centeredDensity : Lp ℝ 2 μ) (oneL2 μ)] with x hf hc ho ha
  rw [hf, ha]
  change _ = (h.centeredDensity : Lp ℝ 2 μ) x+(oneL2 μ) x
  rw [hc, show (oneL2 μ) x=1 from ho]
  ring

/-- The exact centered density of the genuine output, as an a.e. identity. -/
theorem output_centered_rnDeriv (hp : MeasurePreserving p η μ)
    (hq : MeasurePreserving q η μ) {B : ℝ}
    (h : AcceleratedLogConcave.Probability.L2Warm μ ν B) :
    (fun x => ((outputLaw ν η μ p q).rnDeriv μ x).toReal-1) =ᵐ[μ]
      ((referenceChannel hp hq).adjoint (h.centeredDensity : Lp ℝ 2 μ) : X → ℝ) := by
  have he := output_rnDeriv hp hq h
  rw [density_eq_centered_add_one h, map_add, referenceChannel_adjoint,
    referenceChannel_one hq hp] at he
  rw [referenceChannel_adjoint]
  filter_upwards [he,
    Lp.coeFn_add (referenceChannel hq hp (h.centeredDensity : Lp ℝ 2 μ)) (oneL2 μ),
    (memLp_const (1:ℝ) (μ := μ) (p := 2)).coeFn_toLp] with x hx ha ho
  rw [hx, ha]
  change _+(oneL2 μ) x-1=_
  rw [show (oneL2 μ) x=1 from ho]
  ring

/-- Warmness of the output with its exact centered L² energy, rather than an
assumed probability or error certificate. -/
theorem output_warm (hp : MeasurePreserving p η μ)
    (hq : MeasurePreserving q η μ) {B : ℝ}
    (h : AcceleratedLogConcave.Probability.L2Warm μ ν B) :
    AcceleratedLogConcave.Probability.L2Warm μ (outputLaw ν η μ p q)
      (1+‖(referenceChannel hp hq).adjoint (h.centeredDensity : Lp ℝ 2 μ)‖^2) := by
  have := outputLaw_probability hp hq h.absolutelyContinuous
  have hRN := output_rnDeriv hp hq h
  have hmem := (Lp.memLp ((referenceChannel hp hq).adjoint
    (h.memLp.toLp (fun x => (ν.rnDeriv μ x).toReal)))).ae_eq hRN.symm
  have hsq := hmem.integrable_sq
  have hcenter := output_centered_rnDeriv hp hq h
  have hn : ∫ x, (((outputLaw ν η μ p q).rnDeriv μ x).toReal-1)^2 ∂μ =
      ‖(referenceChannel hp hq).adjoint (h.centeredDensity : Lp ℝ 2 μ)‖^2 := by
    calc
      _ = ∫ x, (((referenceChannel hp hq).adjoint (h.centeredDensity : Lp ℝ 2 μ)) x)^2 ∂μ := by
        apply integral_congr_ae
        filter_upwards [hcenter] with x hx
        rw [hx]
      _ = _ := by
        have he := real_inner_self_eq_norm_sq
          ((referenceChannel hp hq).adjoint (h.centeredDensity : Lp ℝ 2 μ))
        rw [L2.inner_def] at he
        simpa only [real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs] using he
  have hi := AcceleratedLogConcave.Probability.integral_centered_rnDeriv_sq μ
    (outputLaw ν η μ p q) (outputLaw_absolutelyContinuous hq) hsq
  refine ⟨outputLaw_absolutelyContinuous hq, hsq, ?_⟩
  linarith

/-- Total variation of the actual output is controlled by the adjoint's
centered-density norm, with the probability-event factor one half. -/
theorem output_totalVariation_le (hp : MeasurePreserving p η μ)
    (hq : MeasurePreserving q η μ) {B : ℝ}
    (h : AcceleratedLogConcave.Probability.L2Warm μ ν B) :
    have : IsProbabilityMeasure (outputLaw ν η μ p q) :=
      outputLaw_probability hp hq h.absolutelyContinuous
    AcceleratedLogConcave.Probability.totalVariationDistance (outputLaw ν η μ p q) μ ≤
      ‖(referenceChannel hp hq).adjoint (h.centeredDensity : Lp ℝ 2 μ)‖ / 2 := by
  have := outputLaw_probability hp hq h.absolutelyContinuous
  have ht := (output_warm hp hq h).totalVariationDistance_le
  simpa only [add_sub_cancel_left, Real.sqrt_sq (norm_nonneg _)] using ht

end AcceleratedLogConcave.Kinetic.ReferenceChannelLaw
