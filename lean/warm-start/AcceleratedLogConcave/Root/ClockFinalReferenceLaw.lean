import AcceleratedLogConcave.Root.ClockFinalJointLaw
import AcceleratedLogConcave.Root.ClockFinalCorrectionReadout

/-! Exact returned-reference Gaussian recombination for the actual completed
Clock kernel. The paired Pi/Pref law remains available separately; no assertion
makes actual child replies Gaussian. -/
noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option quotPrecheck false
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace AcceleratedLogConcave.Root.ClockFinalReferenceLaw
open Oracle Oracle.TapeLowering Oracle.NoisyLayer Oracle.CanonicalTapeLaw Oracle.CanonicalTapeMeasurability
open Oracle.TailOccurrenceCut Oracle.TailOccurrenceCut.TailCut Oracle.PrivateCausalLayer
open ClockNoisyLayer ClockChronologicalCoupling
local instance canonicalTapeSpace {d c : ℕ} {Γ : Ctx} {τ : Ty} (p : Prog c Γ τ) :
    MeasurableSpace (Tape d p) := tapeSpace d p
variable (P : SourceSchedule) (hR : P.R≤1/2) (hc : 0<P.csch) (hsmall : P.csch<1/160)
  (clock : ClockLaw.Clock) (label : ℕ) (hK : 10≤P.K) (hC : 8≤P.Csch)
  (hy : CubicScheduleThreshold.threshold P≤P.y)
  {d : ℕ} {V : Point d→ℝ} (hV : ContDiff ℝ 2 V)
  (hlo : ∀ z v,0≤fderiv ℝ (fderiv ℝ V) z v v)
  (hup : ∀ z v,fderiv ℝ (fderiv ℝ V) z v v≤‖v‖^2)
  (hyMean : MeanSourceScalarAbsorption.threshold P≤P.y)
local notation "host" => Host P hR hc hsmall clock label
local notation "L" => Probability.CanonicalNativeTapeLaw.primitiveLaws d
local notation "γ" => stdGaussian (Point d)
local notation "γZ" => Measure.pi (fun _ : Index P => stdGaussian (Point d))
local notation "pairs" => ClockFinalJointLaw.averagedPairs P hR hc hsmall clock label hK hC hy hV hlo hup hyMean
local notation "joint" => ClockFinalBatchCoupling.completedKernel P hR hc hsmall clock label hK hC hy hV hlo hup hyMean
local notation "retained" => ClockFinalJointLaw.retainedPairs (V := V) P hR hc hsmall clock label hK hC hy
local instance final_markov (i : Index P) : IsMarkovKernel
    (ClockMeanChildAccuracy.finalKernel P hK hc hsmall hC hyMean hV hlo hup clock i) :=
  ClockMeanChildAccuracy.final_markov P hK hc hsmall hC hyMean hV hlo hup clock i

/-- The Gaussian marginal is proved from the actual recursive retained
reference family and its invariant, with no lower accuracy premise. -/
theorem child_reference (i : Index P) (x : Point d) :
    (ClockMeanChildAccuracy.finalKernel P hK hc hsmall hC hyMean hV hlo hup clock i x).snd=γ :=
  FreshChildBatchCoupling.recursive_reference_marginal _ _ _ _ _ _ _ _ _ _ _ _
    ((ClockMeanChildAccuracy.finalLaw P hK hc hsmall hC hyMean hV hlo hup clock i).retained x)

/-- Project only returned references, retaining the full paired kernel separately. -/
def references (p : Index P → Point d × Point d) : Index P → Point d := fun i => (p i).2

theorem references_measurable : Measurable (references (d := d) P) :=
  Measurable.of_eval fun i => (measurable_pi_apply i).snd

theorem averagedPairs_reference : (pairs).map (references P)=Kernel.const _ γZ := by
  ext z : 1
  rw [Kernel.map_apply _ (references_measurable P),ClockFinalJointLaw.averagedPairs_apply]
  change (Measure.pi (fun i => (ClockMeanChildAccuracy.finalKernel P hK hc hsmall hC hyMean hV hlo hup clock i
    (ClockFinalBatchCoupling.center P clock hV hlo hup i z.1)).map (fun a => (a.1.1,a.2)))).map
      (fun p i => (p i).2)=γZ
  rw [Measure.pi_map_pi (fun _ => measurable_snd.aemeasurable)]
  congr 1
  funext i
  rw [Measure.map_map measurable_snd (measurable_fst.fst.prodMk measurable_snd)]
  exact child_reference P hc hsmall clock hK hC hV hlo hup hyMean i _

/-- Full coarse/reserve/returned-reference product on the same completed sample. -/
def referenceObservation (z : (History P d × Tape d host) × (Index P → Point d)) :
    ((Point d × Point d) × Point d) × (Index P → Point d) :=
  ((retained z).1,z.2)

include hV in
theorem referenceObservation_measurable : Measurable (referenceObservation (V := V) P hR hc hsmall clock label hK hC hy) :=
  (ClockFinalJointLaw.retainedPairs_measurable P hR hc hsmall clock label hK hC hy hV).fst.prodMk measurable_snd

theorem reference_observation_law (μX : Measure (Point d)) [IsProbabilityMeasure μX] :
    (joint ∘ₘ ((μX.prod γ).prod (tapeLaw L host))).map
      (referenceObservation (V := V) P hR hc hsmall clock label hK hC hy)=
      ((μX.prod γ).prod γ).prod γZ := by
  have h := congrArg (fun μ => μ.map (Prod.map id (references P)))
    (ClockFinalJointLaw.retained_pairs_law P hR hc hsmall clock label hK hC hy hV hlo hup hyMean μX)
  rw [Measure.map_map (measurable_id.prodMap (references_measurable P))
    (ClockFinalJointLaw.retainedPairs_measurable P hR hc hsmall clock label hK hC hy hV),
    ← Measure.compProd_map (references_measurable P),averagedPairs_reference,
    Measure.compProd_const] at h
  exact h

/-- The same source coefficients and their actual reserve coefficient. -/
def recombine (z : Point d × (Index P → Point d)) : Point d :=
  (∑ i,ClockRetainedFinalSplice.coefficient P clock i • z.2 i) +
    Conditional.GaussianAssembly.reserve (ClockRetainedFinalSplice.coefficient P clock) • z.1

theorem recombine_preserving : MeasurePreserving (recombine (d := d) P clock) ((γ).prod γZ) γ := by
  let D : RetainedLaw.Data (Fin d) (N P) :=
    { weight := ClockRetainedFinalSplice.weight P clock
      admissible := ClockRetainedFinalSplice.coefficient_admissible P clock
      child := fun _ => Kernel.id
      markov := fun _ => inferInstance
      invariant := fun _ => Measure.id_comp }
  exact RetainedLaw.recombine_preserving D

/-- Gaussian part of the reference correction. The mathematical mean row is
kept explicitly in ClockFinalCorrectionReadout.referenceOutput. -/
def gaussianCorrection (z : (History P d × Tape d host) × (Index P → Point d)) : Point d :=
  recombine P clock ((referenceObservation (V := V) P hR hc hsmall clock label hK hC hy z).1.2,z.2)

include hV in
theorem gaussianCorrection_measurable : Measurable (gaussianCorrection (V := V) P hR hc hsmall clock label hK hC hy) :=
  (recombine_preserving P clock).measurable.comp
    ((referenceObservation_measurable P hR hc hsmall clock label hK hC hy hV).fst.snd.prodMk measurable_snd)

/-- The actual reference has an independent standard Gaussian correction
jointly with the original source conditioning pair (xF,Y0). -/
theorem gaussian_correction_joint_law (μX : Measure (Point d)) [IsProbabilityMeasure μX] :
    (joint ∘ₘ ((μX.prod γ).prod (tapeLaw L host))).map
      (fun z => ((referenceObservation (V := V) P hR hc hsmall clock label hK hC hy z).1.1,
        gaussianCorrection (V := V) P hR hc hsmall clock label hK hC hy z))=(μX.prod γ).prod γ := by
  have hp : MeasurePreserving
      (referenceObservation (V := V) P hR hc hsmall clock label hK hC hy)
      (joint ∘ₘ ((μX.prod γ).prod (tapeLaw L host))) (((μX.prod γ).prod γ).prod γZ) :=
    ⟨referenceObservation_measurable P hR hc hsmall clock label hK hC hy hV,
      reference_observation_law P hR hc hsmall clock label hK hC hy hV hlo hup hyMean μX⟩
  have hr := ((MeasurePreserving.id (μX.prod γ)).prod (recombine_preserving P clock)).comp
    ((measurePreserving_prodAssoc (μX.prod γ) γ γZ).comp hp)
  exact hr.map_eq

end AcceleratedLogConcave.Root.ClockFinalReferenceLaw
