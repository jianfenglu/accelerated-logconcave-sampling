import AcceleratedLogConcave.Root.ClockChronologicalPast
import AcceleratedLogConcave.Root.ClockFinalAssemblyReadout

/-! The augmented Clock history retains its literal original split draw and
all initial raw assembly coordinates jointly with the complete source tape.
This support is derived from the constructed finite kernel on any source law. -/
noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option quotPrecheck false
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
namespace AcceleratedLogConcave.Root.ClockFinalAssemblySupport
open Oracle Oracle.TapeLowering Oracle.CanonicalTapeLaw Oracle.CanonicalTapeMeasurability
open ClockChronologicalCoupling ClockNoisyLayer
local instance canonicalTapeSpace {d c : ℕ} {Γ : Ctx} {τ : Ty} (p : Prog c Γ τ) :
    MeasurableSpace (Tape d p) := tapeSpace d p
variable (P : SourceSchedule) (hR : P.R≤1/2) (hc : 0<P.csch) (hsmall : P.csch<1/160)
  (clock : ClockLaw.Clock) (label : ℕ) {d : ℕ}
local notation "host" => Host P hR hc hsmall clock label
local notation "Sample" => History P d × Tape d host

def baseTape (z : Sample) : Base P d × Tape d host := (z.1.1,z.2)
theorem baseTape_measurable : Measurable (baseTape (d := d) P hR hc hsmall clock label) :=
  measurable_fst.fst.prodMk measurable_snd

/-- The original input together with the split draw and every raw assembly slot. -/
def sourceBase (z : Base P d × Tape d host) : Base P d :=
  let w := ClockRetainedFinalSplice.wholeTapeEquiv P hR hc hsmall clock d label z.2
  (z.1.1,(w.1,w.2.1))
theorem sourceBase_measurable : Measurable (sourceBase (d := d) P hR hc hsmall clock label) := by
  let : MeasurableSpace (ClockRetainedFinalSplice.MainFinalTapeData P hR hc hsmall clock d (P.K+4)) :=
    ClockRetainedWholeTapeLaw.mainFinalSpace P hR hc hsmall clock label
  have hw := (ClockRetainedWholeTapeLaw.wholeTapeMeasurableEquiv P hR hc hsmall clock label
    (d := d)).measurable.comp
      (measurable_snd : Measurable (Prod.snd : Base P d × Tape d host → _))
  exact measurable_fst.fst.prodMk (hw.fst.prodMk hw.snd.fst)

variable (hK : 10≤P.K) (hC : 8≤P.Csch) (hy : CubicScheduleThreshold.threshold P≤P.y)
  {V : Point d→ℝ} (hV : ContDiff ℝ 2 V)
  (hlo : ∀ z v,0≤fderiv ℝ (fderiv ℝ V) z v v)
  (hup : ∀ z v,fderiv ℝ (fderiv ℝ V) z v v≤‖v‖^2)
  (hyMean : MeanSourceScalarAbsorption.threshold P≤P.y)

/-- Full original source retention includes the initially recorded assembly,
not merely the smaller input/full-tape projection. -/
theorem kernel_baseTape (μ : Measure ((Point d × Point d) × Tape d host)) :
    (kernel P hR hc hsmall clock label hK hC hy hV hlo hup hyMean ∘ₘ μ).map
      (baseTape P hR hc hsmall clock label) =
    μ.map (fun z => ((prepare P hR hc hsmall clock label z).1.1,z.2)) := by
  have hp := ClockChronologicalPast.kernel_past P hR hc hsmall clock label hK hC hy hV hlo hup hyMean
    0 (Nat.zero_le _) μ
  have hp' := congrArg (fun ν => ν.map Prod.fst) hp
  rw [Measure.map_map measurable_fst (ClockChronologicalPast.past_measurable P hR hc hsmall clock label 0 (Nat.zero_le _)),
    Measure.map_map measurable_fst (ClockChronologicalPast.past_measurable P hR hc hsmall clock label 0 (Nat.zero_le _))] at hp'
  simp only [iteration,Measure.id_comp] at hp'
  change (kernel P hR hc hsmall clock label hK hC hy hV hlo hup hyMean ∘ₘ μ).map
    (baseTape P hR hc hsmall clock label) =
    (μ.map (prepare P hR hc hsmall clock label)).map (baseTape P hR hc hsmall clock label) at hp'
  rw [Measure.map_map (baseTape_measurable P hR hc hsmall clock label)
    (prepare_measurable P hR hc hsmall clock label)] at hp'
  exact hp'

/-- The actual constructed main kernel satisfies the full initial-assembly
support relation for every original source law. -/
theorem kernel_sourceBase_ae (μ : Measure ((Point d × Point d) × Tape d host)) :
    ∀ᵐ z ∂kernel P hR hc hsmall clock label hK hC hy hV hlo hup hyMean ∘ₘ μ,
      z.1.1 = sourceBase P hR hc hsmall clock label (baseTape P hR hc hsmall clock label z) := by
  let f := fun z : (Point d × Point d) × Tape d host =>
    ((prepare P hR hc hsmall clock label z).1.1,z.2)
  have hf : Measurable f := ((prepare_measurable P hR hc hsmall clock label).fst.fst).prodMk measurable_snd
  have he : MeasurableSet {z : Base P d × Tape d host |
      z.1=sourceBase P hR hc hsmall clock label z} :=
    measurableSet_eq_fun measurable_fst (sourceBase_measurable P hR hc hsmall clock label)
  have h : ∀ᵐ z ∂μ.map f,z.1=sourceBase P hR hc hsmall clock label z := by
    apply (ae_map_iff hf.aemeasurable he).2
    exact Filter.Eventually.of_forall fun z => rfl
  rw [← kernel_baseTape P hR hc hsmall clock label hK hC hy hV hlo hup hyMean μ] at h
  exact ae_of_ae_map (baseTape_measurable P hR hc hsmall clock label).aemeasurable h

end AcceleratedLogConcave.Root.ClockFinalAssemblySupport
