import AcceleratedLogConcave.Root.ClockJointInputTapeLaw

/-!
The existing `ClockRetainedFinalSplice.code` returns the normalized dormant
correction. This file supplies its visible affine readout. It executes that
same code once, on the same full tape, and preserves the complete Result trace.
The new readout is an allowed finite affine computation; this file does not
claim that the old code itself already returns the visible momentum.

No accuracy premise, child-coupling premise, or new random draw is used.
-/
noncomputable section
set_option autoImplicit false

namespace AcceleratedLogConcave.Root.LocalRootLawWrapper
open MeasureTheory ProbabilityTheory
open Oracle Oracle.CanonicalTapeMeasurability Oracle.CanonicalTapeLaw
open ClockNoisyLayer ClockRetainedFinalSplice
open scoped BigOperators

variable (P : SourceSchedule) (hR : P.R ≤ 1/2) (hc : 0 < P.csch)
  (hsmall : P.csch < 1/160) (clock : ClockLaw.Clock)

abbrev Sample (d ell : ℕ) :=
  (Point d × Point d) × Tape d (code P hR hc hsmall clock ell)

variable {d : ℕ} (ell : ℕ)

local instance : MeasurableSpace (Tape d (code P hR hc hsmall clock ell)) :=
  tapeSpace d (code P hR hc hsmall clock ell)

/-- The already-drawn public E0; no replacement randomness. -/
def initialE0 (ω : Tape d (code P hR hc hsmall clock ell)) : Point d :=
  ω.2.2.1

/-- The already-drawn raw array used by the conditional active-input assembly. -/
def assemblyZ (ω : Tape d (code P hR hc hsmall clock ell)) : Index P → Point d :=
  fun i => (ω.2.2.2.2.2.1 i).1

/-- Literal interpreter Result, with its original supplied inputs and tape. -/
def hiddenRun (G : Point d → Point d) (a : Sample P hR hc hsmall clock d ell) :
    Result d .point :=
  run (code P hR hc hsmall clock ell) G
    ⟨table P hR hc hsmall clock, a.1.1, a.1.2⟩ Env.empty a.2

/-- Visible wrapper: P+n(Hhat-H0). Only the value is changed. -/
def visibleRun (G : Point d → Point d) (a : Sample P hR hc hsmall clock d ell) :
    Result d .point :=
  let result := hiddenRun P hR hc hsmall clock ell G a
  ⟨a.1.2 + ClockPublicSetup.noise •
      ((show Point d from result.value) -
        ClockPublicSetup.splitValues a.1.2
          (initialE0 P hR hc hsmall clock ell a.2) 1),
    result.trace⟩

def visible (G : Point d → Point d) (a : Sample P hR hc hsmall clock d ell) : Point d :=
  (visibleRun P hR hc hsmall clock ell G a).value

theorem visibleRun_trace (G : Point d → Point d)
    (a : Sample P hR hc hsmall clock d ell) :
    (visibleRun P hR hc hsmall clock ell G a).trace =
      (hiddenRun P hR hc hsmall clock ell G a).trace := rfl

/-- In particular every original-oracle query and Gaussian event is retained. -/
theorem visibleRun_counts (G : Point d → Point d)
    (a : Sample P hR hc hsmall clock d ell) :
    traceCounts (visibleRun P hR hc hsmall clock ell G a).trace =
      traceCounts (hiddenRun P hR hc hsmall clock ell G a).trace := rfl

theorem split_reconstruct (momentum E0 : Point d) :
    ClockPublicSetup.s • ClockPublicSetup.splitValues momentum E0 0 +
      ClockPublicSetup.noise • ClockPublicSetup.splitValues momentum E0 1 = momentum := by
  have h := congrArg Prod.fst
    (Kinetic.gaussianSplit_involutive ClockPublicSetup.s ClockPublicSetup.noise
      Kinetic.source_split_coefficients (momentum,E0))
  exact h

/-- The wrapper is also sY0+nHhat, with the same original split. -/
theorem visible_eq_affine (G : Point d → Point d)
    (a : Sample P hR hc hsmall clock d ell) :
    visible P hR hc hsmall clock ell G a =
      ClockPublicSetup.s • ClockPublicSetup.splitValues a.1.2
        (initialE0 P hR hc hsmall clock ell a.2) 0 +
      ClockPublicSetup.noise • (show Point d from (hiddenRun P hR hc hsmall clock ell G a).value) := by
  have h := split_reconstruct a.1.2 (initialE0 P hR hc hsmall clock ell a.2)
  dsimp only [visible, visibleRun]
  calc
    _ = (ClockPublicSetup.s • ClockPublicSetup.splitValues a.1.2
          (initialE0 P hR hc hsmall clock ell a.2) 0 +
        ClockPublicSetup.noise • ClockPublicSetup.splitValues a.1.2
          (initialE0 P hR hc hsmall clock ell a.2) 1) +
        ClockPublicSetup.noise •
          ((show Point d from (hiddenRun P hR hc hsmall clock ell G a).value) -
            ClockPublicSetup.splitValues a.1.2
              (initialE0 P hR hc hsmall clock ell a.2) 1) :=
      congrArg (fun p => p + ClockPublicSetup.noise •
        ((show Point d from (hiddenRun P hR hc hsmall clock ell G a).value) -
          ClockPublicSetup.splitValues a.1.2
            (initialE0 P hR hc hsmall clock ell a.2) 1)) h.symm
    _ = _ := by rw [smul_sub]; abel

/-- Actual final child values, obtained from the existing every-tape semantics.
The main layers, final auxiliary tapes, uniforms and residuals are unchanged. -/
def finalReplies (G : Point d → Point d)
    (a : Sample P hR hc hsmall clock d ell) : Index P → Point d :=
  let assemblyTape := a.2.2.2.2.2.2
  let initTape := assemblyTape.2.2
  let Z0 : Index P → Point d := fun i => (initTape.1 i).1
  let env : Env d (entryCtx P) := entryEnv P clock a.1.1 a.1.2
    (initialE0 P hR hc hsmall clock ell a.2)
    (assemblyZ P hR hc hsmall clock ell a.2) Z0
  fun i => Oracle.RetainedMeanFinalBatch.childPoint
    (finalChildren P hR hc hsmall clock ell G a.1.1 a.1.2 env initTape.2.2 i)

theorem hidden_eq_correction (G : Point d → Point d)
    (a : Sample P hR hc hsmall clock d ell) :
    (show Point d from (hiddenRun P hR hc hsmall clock ell G a).value) =
      ClockPublicSetup.splitValues a.1.2 (initialE0 P hR hc hsmall clock ell a.2) 1 +
      ∑ i, correctionWeight P clock i •
        (finalReplies P hR hc hsmall clock ell G a i - width P clock i •
          activeValues P clock
            (ClockPublicSetup.splitValues a.1.2 (initialE0 P hR hc hsmall clock ell a.2) 1)
            (assemblyZ P hR hc hsmall clock ell a.2) i) := by
  have h := congrArg (fun r : Result d .point => r.value)
    (run_code_every_tape P hR hc hsmall clock ell G a.1.1 a.1.2 a.2)
  exact h.trans (normalized_correction P clock
    (ClockPublicSetup.splitValues a.1.2 (initialE0 P hR hc hsmall clock ell a.2) 1)
    (assemblyZ P hR hc hsmall clock ell a.2)
    (finalReplies P hR hc hsmall clock ell G a)).symm

theorem visible_eq_correction (G : Point d → Point d)
    (a : Sample P hR hc hsmall clock d ell) :
    visible P hR hc hsmall clock ell G a = a.1.2 +
      ∑ i, (ClockPublicSetup.noise * correctionWeight P clock i) •
        (finalReplies P hR hc hsmall clock ell G a i - width P clock i •
          activeValues P clock
            (ClockPublicSetup.splitValues a.1.2 (initialE0 P hR hc hsmall clock ell a.2) 1)
            (assemblyZ P hR hc hsmall clock ell a.2) i) := by
  have h := congrArg (fun z : Point d => a.1.2 + ClockPublicSetup.noise •
    (z - ClockPublicSetup.splitValues a.1.2
      (initialE0 P hR hc hsmall clock ell a.2) 1))
    (hidden_eq_correction P hR hc hsmall clock ell G a)
  simpa only [visible, visibleRun, add_sub_cancel_left, Finset.smul_sum, smul_smul] using h

theorem visible_coefficient (i : Index P) :
    ClockPublicSetup.noise * correctionWeight P clock i =
      -(ClockPublicSetup.s * ClockCollocation.rF P.delta) * weight P clock i := by
  have hn : ClockPublicSetup.noise ≠ 0 := by
    unfold ClockPublicSetup.noise
    positivity
  have hr : ClockPublicSetup.s * ClockCollocation.rF P.delta ≠ 0 := by
    unfold ClockPublicSetup.s ClockCollocation.rF
    have := P.delta_pos
    positivity
  change ClockPublicSetup.noise *
      (-weight P clock i / (ClockPublicSetup.noise /
        (ClockPublicSetup.s * ClockCollocation.rF P.delta))) = _
  field_simp [hn, hr]

/-- Equation sroot-correction, for every actual input and every complete tape.
There is no division by the stopping clock. -/
theorem visible_eq_manuscript (G : Point d → Point d)
    (a : Sample P hR hc hsmall clock d ell) :
    visible P hR hc hsmall clock ell G a = a.1.2 +
      ∑ i, (-(ClockPublicSetup.s * ClockCollocation.rF P.delta) * weight P clock i) •
        (finalReplies P hR hc hsmall clock ell G a i - width P clock i •
          activeValues P clock
            (ClockPublicSetup.splitValues a.1.2 (initialE0 P hR hc hsmall clock ell a.2) 1)
            (assemblyZ P hR hc hsmall clock ell a.2) i) := by
  rw [visible_eq_correction]
  simp_rw [visible_coefficient]

theorem visible_zero_clock (G : Point d → Point d)
    (a : Sample P hR hc hsmall ⟨0, by norm_num⟩ d ell) :
    visible P hR hc hsmall ⟨0, by norm_num⟩ ell G a = a.1.2 := by
  rw [visible_eq_manuscript]
  have hw : ∀ i : Index P, weight P ⟨0, by norm_num⟩ i = 0 :=
    fun i => (ClockSchedule.zero_node_weight _ _ i).2
  simp only [hw, mul_zero, zero_smul, Finset.sum_const_zero, add_zero]

theorem initialE0_measurable :
    Measurable (initialE0 P hR hc hsmall clock ell (d := d)) :=
  (ClockRetainedTapeLaw.measurable_publicPrefix_toFun P hR hc hsmall clock ell).fst

theorem visible_measurable (G : Point d → Point d) (hG : Measurable G) :
    Measurable (visible P hR hc hsmall clock ell G) := by
  have hh := (ClockJointInputTapeLaw.retainedRun_measurable
    P hR hc hsmall clock ell G hG).snd
  have he := (initialE0_measurable P hR hc hsmall clock ell (d := d)).comp
    (measurable_snd : Measurable (Prod.snd : Sample P hR hc hsmall clock d ell → _))
  have hH : Measurable (fun a : Sample P hR hc hsmall clock d ell =>
      ClockPublicSetup.splitValues a.1.2 (initialE0 P hR hc hsmall clock ell a.2) 1) :=
    (measurable_fst.snd.const_smul ClockPublicSetup.noise).add
      (he.const_smul (-ClockPublicSetup.s))
  exact measurable_fst.snd.add ((hh.sub hH).const_smul ClockPublicSetup.noise)

/-- No independence between center and entering momentum is assumed. -/
def executionLaw (ν : Measure (Point d × Point d)) :
    Measure (Sample P hR hc hsmall clock d ell) :=
  ν.prod (tapeLaw (ClockPublicSetupTapeLaw.standardLaws d)
    (code P hR hc hsmall clock ell))

theorem executionLaw_probability (ν : Measure (Point d × Point d))
    [IsProbabilityMeasure ν] :
    IsProbabilityMeasure (executionLaw P hR hc hsmall clock ell ν) := by
  let := tapeLaw_probability (ClockPublicSetupTapeLaw.standardLaws d)
    (code P hR hc hsmall clock ell)
  unfold executionLaw
  infer_instance

def retainedLaw (G : Point d → Point d) (ν : Measure (Point d × Point d)) :
    Measure ((Point d × Point d) × Point d) :=
  (executionLaw P hR hc hsmall clock ell ν).map
    (fun a => (a.1, visible P hR hc hsmall clock ell G a))

theorem retainedLaw_probability (G : Point d → Point d) (hG : Measurable G)
    (ν : Measure (Point d × Point d)) [IsProbabilityMeasure ν] :
    IsProbabilityMeasure (retainedLaw P hR hc hsmall clock ell G ν) := by
  let := executionLaw_probability P hR hc hsmall clock ell ν
  exact (Measure.isProbabilityMeasure_map_iff
    (measurable_fst.prodMk (visible_measurable P hR hc hsmall clock ell G hG)).aemeasurable).mpr
      inferInstance

theorem retainedLaw_input (G : Point d → Point d) (hG : Measurable G)
    (ν : Measure (Point d × Point d)) [IsProbabilityMeasure ν] :
    (retainedLaw P hR hc hsmall clock ell G ν).map Prod.fst = ν := by
  let := tapeLaw_probability (ClockPublicSetupTapeLaw.standardLaws d)
    (code P hR hc hsmall clock ell)
  rw [retainedLaw, Measure.map_map measurable_fst
    (measurable_fst.prodMk (visible_measurable P hR hc hsmall clock ell G hG))]
  change (ν.prod (tapeLaw (ClockPublicSetupTapeLaw.standardLaws d)
    (code P hR hc hsmall clock ell))).map Prod.fst = ν
  simp

/-- Dimension zero needs no positive-dimension side condition. -/
theorem visible_dim_zero (G : Point 0 → Point 0)
    (a : Sample P hR hc hsmall clock 0 ell) :
    visible P hR hc hsmall clock ell G a = a.1.2 :=
  Subsingleton.elim _ _

end AcceleratedLogConcave.Root.LocalRootLawWrapper
