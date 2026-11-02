import AcceleratedLogConcave.Root.LocalRootLawWrapper
import AcceleratedLogConcave.Root.LocalRootLawReferenceLift
import AcceleratedLogConcave.Root.ClockBackwardKernel

/-!
The reference extension is now attached to the literal root execution sample.
The initial Gaussian split and the raw active-array seed are read from its
original tape. Full-tape packing, Gaussian split preservation, and exact parent
flow are the existing suppliers. Only exact child-reference draws are added.

The law construction is complete relative to `ConditionalLaw.Data`; producing
the prescribed nonterminal child family and an accurate coupling is separate.
In particular this construction does not assert that independent reference
draws are close to the executed child replies.
-/
noncomputable section
set_option autoImplicit false

namespace AcceleratedLogConcave.Root.LocalRootLawAssembly
open MeasureTheory ProbabilityTheory
open Oracle Oracle.CanonicalTapeLaw Oracle.CanonicalTapeMeasurability
open ClockNoisyLayer ClockRetainedFinalSplice ClockRetainedWholeTapeLaw
open LocalRootLawWrapper LocalRootLawReferenceLift
open Kinetic Analysis.Poisson

variable (P : SourceSchedule) (hR : P.R ≤ 1/2) (hc : 0 < P.csch)
  (hsmall : P.csch < 1/160) (clock : ClockLaw.Clock) {d : ℕ} (ell : ℕ)

local instance : MeasurableSpace (Tape d (code P hR hc hsmall clock ell)) :=
  tapeSpace d (code P hR hc hsmall clock ell)

/-- Same x, same split of (P,E0), same raw Z. No reference draw occurs here. -/
def initialHost (a : Sample P hR hc hsmall clock d ell) :
    Host (B := Point d × Point d) (d := d) (m := N P) :=
  (((a.1.1, ClockPublicSetup.splitValues a.1.2
      (initialE0 P hR hc hsmall clock ell a.2) 0),
    ClockPublicSetup.splitValues a.1.2
      (initialE0 P hR hc hsmall clock ell a.2) 1),
    assemblyZ P hR hc hsmall clock ell a.2)

theorem initialHost_measurable :
    Measurable (initialHost P hR hc hsmall clock ell (d := d)) := by
  let : MeasurableSpace (MainFinalTapeData P hR hc hsmall clock d (P.K+4)) :=
    mainFinalSpace P hR hc hsmall clock ell
  have he := (initialE0_measurable P hR hc hsmall clock ell (d := d)).comp
    (measurable_snd : Measurable (Prod.snd : Sample P hR hc hsmall clock d ell → _))
  have hz : Measurable (fun a : Sample P hR hc hsmall clock d ell =>
      assemblyZ P hR hc hsmall clock ell a.2) :=
    (wholeTapeMeasurableEquiv P hR hc hsmall clock ell).measurable.snd.fst.comp
      measurable_snd
  exact ((measurable_fst.fst.prodMk
    ((measurable_fst.snd.const_smul ClockPublicSetup.s).add
      (he.const_smul ClockPublicSetup.noise))).prodMk
    ((measurable_fst.snd.const_smul ClockPublicSetup.noise).add
      (he.const_smul (-ClockPublicSetup.s)))).prodMk hz

/-- Derive the host product law from the actual Gaussian/tape pushforward.
The input specialization here is μX × γ; the arbitrary-joint-input interpreter
law remains available in LocalRootLawWrapper and is not claimed to factor. -/
theorem initialHost_preserving (μX : Measure (Point d)) [IsProbabilityMeasure μX] :
    MeasurePreserving (initialHost P hR hc hsmall clock ell)
      (executionLaw P hR hc hsmall clock ell (μX.prod (stdGaussian (Point d))))
      (hostLaw (m := N P) (μX.prod (stdGaussian (Point d)))) := by
  let : MeasurableSpace (MainFinalTapeData P hR hc hsmall clock d (P.K+4)) :=
    mainFinalSpace P hR hc hsmall clock ell
  let γ := stdGaussian (Point d)
  let μZ := RetainedLaw.noiseLaw (ι := Fin d) (m := N P)
  let μmain := mainFinalLaw P hR hc hsmall clock ell (d := d)
  let ν := μX.prod γ
  let : IsProbabilityMeasure (tapeLaw (ClockPublicSetupTapeLaw.standardLaws d)
      (loop P hR hc hsmall clock ell)) :=
    tapeLaw_probability (ClockPublicSetupTapeLaw.standardLaws d) _
  let : IsProbabilityMeasure μmain := by
    unfold μmain mainFinalLaw
    infer_instance
  have hp : MeasurePreserving
      (Prod.map (id : Point d × Point d → Point d × Point d)
        (wholeTapeMeasurableEquiv P hR hc hsmall clock ell))
      (executionLaw P hR hc hsmall clock ell ν)
      (ν.prod (γ.prod (μZ.prod (μZ.prod μmain)))) :=
    ⟨measurable_id.prodMap
        (wholeTapeMeasurableEquiv P hR hc hsmall clock ell).measurable,
      ClockJointInputTapeLaw.jointInputAndWholeTapeLaw P hR hc hsmall clock ell ν⟩
  have hd : MeasurePreserving Prod.fst (μZ.prod (μZ.prod μmain)) μZ :=
    measurePreserving_fst
  have ha := (measurePreserving_prodAssoc ν γ μZ).symm MeasurableEquiv.prodAssoc
  have hs := (phaseSplit_measurePreserving μX ClockPublicSetup.s
    ClockPublicSetup.noise source_split_coefficients).prod (MeasurePreserving.id μZ)
  exact hs.comp (ha.comp
    (((MeasurePreserving.id ν).prod ((MeasurePreserving.id γ).prod hd)).comp hp))

variable (F : ReferencePoissonFamily (Point d) 0 (1/2)) (velocityScale : ℝ)

/-- The interpreter center is xF; the exact physical parent starts at sqrt(h) xF. -/
def physicalInitialHost (a : Sample P hR hc hsmall clock d ell) :
    Host (B := Point d × Point d) (d := d) (m := N P) :=
  let z := initialHost P hR hc hsmall clock ell a
  (((Real.sqrt P.delta • z.1.1.1,z.1.1.2),z.1.2),z.2)

theorem physicalInitialHost_measurable :
    Measurable (physicalInitialHost P hR hc hsmall clock ell (d := d)) := by
  have h := initialHost_measurable P hR hc hsmall clock ell (d := d)
  exact (((h.fst.fst.fst.const_smul (Real.sqrt P.delta)).prodMk h.fst.fst.snd).prodMk
    h.fst.snd).prodMk h.snd

/-- Exact physical reference trajectory; the old H0 and raw Z are untouched. -/
def exactHost : Sample P hR hc hsmall clock d ell →
    Host (B := Point d × Point d) (d := d) (m := N P) :=
  BackwardParentLaw.hostFlow F velocityScale clock ∘
    physicalInitialHost P hR hc hsmall clock ell

theorem exactHost_measurable :
    Measurable (exactHost P hR hc hsmall clock ell F velocityScale) :=
  (BackwardParentLaw.measurable_hostFlow F velocityScale clock).comp
    (physicalInitialHost_measurable P hR hc hsmall clock ell)

def terminalParentLaw (μX : Measure (Point d)) : Measure (Point d × Point d) :=
  ((μX.map (fun x => Real.sqrt P.delta • x)).prod (stdGaussian (Point d))).map
    (referenceCoupledPairFlow F velocityScale clock)

instance terminalParentLaw_probability (μX : Measure (Point d)) [IsProbabilityMeasure μX] :
    IsProbabilityMeasure (terminalParentLaw P clock F velocityScale μX) := by
  let : IsProbabilityMeasure (μX.map (fun x => Real.sqrt P.delta • x)) :=
    (Measure.isProbabilityMeasure_map_iff
      (measurable_id.const_smul (Real.sqrt P.delta)).aemeasurable).mpr inferInstance
  unfold terminalParentLaw
  exact (Measure.isProbabilityMeasure_map_iff
    (referenceCoupledPairFlow F velocityScale clock).measurable.aemeasurable).mpr inferInstance

theorem exactHost_preserving (μX : Measure (Point d)) [IsProbabilityMeasure μX] :
    MeasurePreserving (exactHost P hR hc hsmall clock ell F velocityScale)
      (executionLaw P hR hc hsmall clock ell (μX.prod (stdGaussian (Point d))))
      (hostLaw (m := N P) (terminalParentLaw P clock F velocityScale μX)) := by
  let : IsProbabilityMeasure (μX.map (fun x => Real.sqrt P.delta • x)) :=
    (Measure.isProbabilityMeasure_map_iff
      (measurable_id.const_smul (Real.sqrt P.delta)).aemeasurable).mpr inferInstance
  have hc₀ : MeasurePreserving (fun x : Point d => Real.sqrt P.delta • x)
      μX (μX.map (fun x => Real.sqrt P.delta • x)) :=
    ⟨by fun_prop, rfl⟩
  have hp := ((hc₀.prod (MeasurePreserving.id (stdGaussian (Point d)))).prod
    (MeasurePreserving.id (stdGaussian (Point d)))).prod
      (MeasurePreserving.id (RetainedLaw.noiseLaw (ι := Fin d) (m := N P)))
  exact (BackwardParentLaw.hostFlow_preserving_arbitrary F velocityScale clock _).comp
    (hp.comp (initialHost_preserving P hR hc hsmall clock ell μX))

/-- Pointwise recovery of the supplied entering P, not a fresh Gaussian P. -/
theorem entering_exactHost (a : Sample P hR hc hsmall clock d ell) :
    BackwardParentLaw.entering F velocityScale ClockPublicSetup.s ClockPublicSetup.noise
      clock (exactHost P hR hc hsmall clock ell F velocityScale a).1 = a.1.2 := by
  change BackwardParentLaw.entering F velocityScale ClockPublicSetup.s ClockPublicSetup.noise
    clock (referenceCoupledPairFlow F velocityScale clock
      (physicalInitialHost P hR hc hsmall clock ell a).1.1,
        (physicalInitialHost P hR hc hsmall clock ell a).1.2) = _
  rw [BackwardParentLaw.entering_forward]
  exact LocalRootLawWrapper.split_reconstruct _ _

variable (D : ConditionalLaw.Data (Point d × Point d) (Fin d) (N P))

/-- Explicit probability measure on (original input, entire original tape, references). -/
def couplingLaw (μX : Measure (Point d)) :
    Measure (Sample P hR hc hsmall clock d ell × (Index P → Point d)) :=
  liftLaw D (executionLaw P hR hc hsmall clock ell (μX.prod (stdGaussian (Point d))))
    (exactHost P hR hc hsmall clock ell F velocityScale)
    (exactHost_measurable P hR hc hsmall clock ell F velocityScale)

theorem couplingLaw_probability (μX : Measure (Point d)) [IsProbabilityMeasure μX] :
    IsProbabilityMeasure (couplingLaw P hR hc hsmall clock ell F velocityScale D μX) := by
  let := executionLaw_probability P hR hc hsmall clock ell
    (μX.prod (stdGaussian (Point d)))
  unfold couplingLaw
  infer_instance

theorem couplingLaw_original (μX : Measure (Point d)) [IsProbabilityMeasure μX] :
    (couplingLaw P hR hc hsmall clock ell F velocityScale D μX).map Prod.fst =
      executionLaw P hR hc hsmall clock ell (μX.prod (stdGaussian (Point d))) := by
  let := executionLaw_probability P hR hc hsmall clock ell
    (μX.prod (stdGaussian (Point d)))
  exact liftLaw_original _ _ _ _

/-- Actual center/entering-P/visible-output marginal under the constructed coupling. -/
theorem couplingLaw_actual (μX : Measure (Point d)) [IsProbabilityMeasure μX]
    (G : Point d → Point d) (hG : Measurable G) :
    (couplingLaw P hR hc hsmall clock ell F velocityScale D μX).map
      (fun z => (z.1.1, visible P hR hc hsmall clock ell G z.1)) =
      retainedLaw P hR hc hsmall clock ell G (μX.prod (stdGaussian (Point d))) := by
  exact extension_observable _ _
    (couplingLaw_original P hR hc hsmall clock ell F velocityScale D μX)
    (fun a => (a.1, visible P hR hc hsmall clock ell G a))
    (measurable_fst.prodMk (visible_measurable P hR hc hsmall clock ell G hG))

/-- Full microscopic reference joint, with the original H0 and exact parent retained. -/
theorem couplingLaw_reference (μX : Measure (Point d)) [IsProbabilityMeasure μX] :
    (couplingLaw P hR hc hsmall clock ell F velocityScale D μX).map
      (fun z => (exactHost P hR hc hsmall clock ell F velocityScale z.1,z.2)) =
      referenceLaw D (terminalParentLaw P clock F velocityScale μX) := by
  let := executionLaw_probability P hR hc hsmall clock ell
    (μX.prod (stdGaussian (Point d)))
  exact liftLaw_reference _ _ _ _ _
    (exactHost_preserving P hR hc hsmall clock ell F velocityScale μX).map_eq

def referenceOutput (z : Sample P hR hc hsmall clock d ell × (Index P → Point d)) : Point d :=
  ConditionalLaw.output D (exactHost P hR hc hsmall clock ell F velocityScale z.1,z.2)

theorem couplingLaw_retained_reference (μX : Measure (Point d)) [IsProbabilityMeasure μX] :
    (couplingLaw P hR hc hsmall clock ell F velocityScale D μX).map
      (fun z => ((exactHost P hR hc hsmall clock ell F velocityScale z.1).1,
        referenceOutput P hR hc hsmall clock ell F velocityScale D z)) =
      (terminalParentLaw P clock F velocityScale μX).prod (stdGaussian (Point d)) ⊗ₘ
        ConditionalLaw.rootKernel D := by
  let := executionLaw_probability P hR hc hsmall clock ell
    (μX.prod (stdGaussian (Point d)))
  exact liftLaw_retained_reference _ _ _ _ _
    (exactHost_preserving P hR hc hsmall clock ell F velocityScale μX).map_eq

theorem couplingLaw_parent_output (μX : Measure (Point d)) [IsProbabilityMeasure μX] :
    (couplingLaw P hR hc hsmall clock ell F velocityScale D μX).map
      (fun z => ((exactHost P hR hc hsmall clock ell F velocityScale z.1).1.1,
        referenceOutput P hR hc hsmall clock ell F velocityScale D z)) =
      (terminalParentLaw P clock F velocityScale μX).prod (stdGaussian (Point d)) := by
  let := executionLaw_probability P hR hc hsmall clock ell
    (μX.prod (stdGaussian (Point d)))
  exact liftLaw_parent_output _ _ _ _ _
    (exactHost_preserving P hR hc hsmall clock ell F velocityScale μX).map_eq

/-- Concrete source schedule/centers/scale adapter. `C` is the explicit open
lower-level prescribed child-kernel supplier; it is not a root coupling premise. -/
def sourceData (C : ClockBackwardKernel.Children (Fin d)
    (ClockSchedule.sourceCells P.delta) (ClockSchedule.sourceOrder P.K)) :
    ConditionalLaw.Data (Point d × Point d) (Fin d) (N P) :=
  ClockBackwardKernel.fixedData F (Real.sqrt (2*P.delta^2))
    (ClockSchedule.sourceCells P.delta) (ClockSchedule.sourceOrder P.K)
    (ClockSchedule.sourceCells_pos P.delta_pos) (ClockSchedule.sourceOrder_pos P.K)
    (Real.sqrt P.delta)⁻¹ C clock

theorem sourceData_weight (C : ClockBackwardKernel.Children (Fin d)
    (ClockSchedule.sourceCells P.delta) (ClockSchedule.sourceOrder P.K))
    (b : Point d × Point d) (i : Index P) :
    (sourceData P clock F C).weight b i = weight P clock i := rfl

/-- The adapter gives the existing source kernel itself, not just its invariant law. -/
theorem sourceData_rootKernel (C : ClockBackwardKernel.Children (Fin d)
    (ClockSchedule.sourceCells P.delta) (ClockSchedule.sourceOrder P.K))
    (b : Point d × Point d) (p : Point d) :
    ConditionalLaw.rootKernel (sourceData P clock F C) (b,p) =
      ClockBackwardKernel.sourceKernel F P.delta P.delta_pos P.K C (clock,(b,p)) :=
  (ClockBackwardKernel.kernel_section_apply F (Real.sqrt (2*P.delta^2))
    (ClockSchedule.sourceCells P.delta) (ClockSchedule.sourceOrder P.K)
    (ClockSchedule.sourceCells_pos P.delta_pos) (ClockSchedule.sourceOrder_pos P.K)
    (Real.sqrt P.delta)⁻¹ C clock b p).symm

/-- Source data uses the identical active inputs already computed by the root. -/
theorem sourceData_active (C : ClockBackwardKernel.Children (Fin d)
    (ClockSchedule.sourceCells P.delta) (ClockSchedule.sourceOrder P.K))
    (a : Sample P hR hc hsmall clock d ell) :
    ConditionalLaw.active (sourceData P clock F C)
      (exactHost P hR hc hsmall clock ell F (Real.sqrt (2*P.delta^2)) a) =
      activeValues P clock
        (ClockPublicSetup.splitValues a.1.2 (initialE0 P hR hc hsmall clock ell a.2) 1)
        (assemblyZ P hR hc hsmall clock ell a.2) := rfl

end AcceleratedLogConcave.Root.LocalRootLawAssembly
