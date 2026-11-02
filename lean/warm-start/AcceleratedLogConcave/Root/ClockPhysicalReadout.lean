import AcceleratedLogConcave.Root.ClockRetainedTapeTransport

/-! Deterministic physical output of the literal retained root. The existing
root program returns the normalized latent H1; the prescribed source output
uses the original entering momentum and the same executed final child replies.
The adapter changes only the returned value and keeps the complete trace. -/
noncomputable section
set_option autoImplicit false
namespace AcceleratedLogConcave.Root.ClockPhysicalReadout
open Oracle Oracle.AffineLowering Oracle.NoisyLayer Oracle.TapeLowering
open Oracle.RetainedMeanFinalBatch
open ClockRetainedFinalSplice ClockNoisyLayer
open scoped BigOperators

variable (P : SourceSchedule) (hR : P.R ≤ 1/2) (hc : 0 < P.csch)
  (hsmall : P.csch < 1/160) (clock : ClockLaw.Clock)

/-- The literal source coefficient `c_i = -s r_F ω_i`. -/
def physicalCoefficient (i : Index P) : ℝ :=
  ClockPublicSetup.s * ClockCollocation.rF P.delta * coefficient P clock i

theorem physicalCoefficient_source (i : Index P) :
    physicalCoefficient P clock i =
      -(ClockPublicSetup.s * ClockCollocation.rF P.delta * weight P clock i) := by
  simp [physicalCoefficient, coefficient]

/-- Direct manuscript readout from every executed final conditional-gradient
correction `Q_i - σ_f P_i`. -/
def directW {d : ℕ} (momentum : Point d) (active Q : Index P → Point d) : Point d :=
  momentum + ∑ i, physicalCoefficient P clock i •
    (Q i - width P clock i • active i)

/-- Recover the physical output from the latent H1 and the retained entering
momentum and public E0 draw. -/
def physicalOutput {d : ℕ} (momentum E0 H1 : Point d) : Point d :=
  momentum + ClockPublicSetup.noise •
    (H1 - ClockPublicSetup.splitValues momentum E0 1)

/-- The final source width is exactly `n/(s r_F)`, uniformly in clock and slot. -/
theorem width_scale (i : Index P) :
    ClockPublicSetup.s * ClockCollocation.rF P.delta * width P clock i =
      ClockPublicSetup.noise := by
  have hr : Real.sqrt (2 * P.delta) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 (mul_pos (by norm_num) P.delta_pos))
  change (1 / 2 : ℝ) * Real.sqrt (2 * P.delta) *
    ((Real.sqrt 3 / 2) / ((1 / 2) * Real.sqrt (2 * P.delta))) = Real.sqrt 3 / 2
  field_simp

theorem physicalCoefficient_eq_noise_correction (i : Index P) :
    physicalCoefficient P clock i =
      ClockPublicSetup.noise * correctionWeight P clock i := by
  have hw := width_scale P clock i
  have hne : width P clock i ≠ 0 := ne_of_gt (width_pos P clock i)
  unfold physicalCoefficient correctionWeight
  rw [← hw]
  field_simp

theorem physicalOutput_eq_directW {d : ℕ} (momentum E0 : Point d)
    (active Q : Index P → Point d) :
    physicalOutput momentum E0
      (ClockPublicSetup.splitValues momentum E0 1 +
        ∑ i, correctionWeight P clock i •
          (Q i - width P clock i • active i)) =
      directW P clock momentum active Q := by
  unfold physicalOutput directW
  have hcancel : (ClockPublicSetup.splitValues momentum E0 1 +
      ∑ i, correctionWeight P clock i •
        (Q i - width P clock i • active i)) -
      ClockPublicSetup.splitValues momentum E0 1 =
      ∑ i, correctionWeight P clock i •
        (Q i - width P clock i • active i) := by abel
  rw [hcancel, Finset.smul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [smul_smul, ← physicalCoefficient_eq_noise_correction P clock i]

/-- Replacing the latent value by the physical value preserves every event. -/
def readoutResult {d : ℕ} (momentum E0 : Point d)
    (result : Result d .point) : Result d .point :=
  ⟨physicalOutput momentum E0 result.value, result.trace⟩

theorem readoutResult_trace {d : ℕ} (momentum E0 : Point d)
    (result : Result d .point) :
    (readoutResult momentum E0 result).trace = result.trace := rfl

/-- For every complete supplied tape, the readout of the existing root run is
the manuscript's direct finite sum over the very same executed final children.
No final child is rerun or replaced, including a zero-weight child. -/
theorem run_code_physical_value {d : ℕ} (ell : ℕ) (G : Point d → Point d)
    (xF momentum : Point d)
    (tape : Tape d (code P hR hc hsmall clock ell)) :
    let E0 : Point d := tape.2.2.1
    let assemblyTape := tape.2.2.2.2.2
    let Z : Index P → Point d := fun i => (assemblyTape.1 i).1
    let initTape := assemblyTape.2.2
    let Z0 : Index P → Point d := fun i => (initTape.1 i).1
    let finalTape := initTape.2.2
    let env : Env d (entryCtx P) := entryEnv P clock xF momentum E0 Z Z0
    let Q := fun i => childPoint
      (finalChildren P hR hc hsmall clock ell G xF momentum env finalTape i)
    (readoutResult momentum E0
      (run (code P hR hc hsmall clock ell) G
        ⟨table P hR hc hsmall clock, xF, momentum⟩ Env.empty tape)).value =
      directW P clock momentum
        (activeValues P clock (ClockPublicSetup.splitValues momentum E0 1) Z) Q := by
  have hr := run_code_every_tape P hR hc hsmall clock ell G xF momentum tape
  dsimp only at hr ⊢
  have hv := congrArg (fun result : Result d .point => result.value) hr
  change (run (code P hR hc hsmall clock ell) G
    ⟨table P hR hc hsmall clock, xF, momentum⟩ Env.empty tape).value = _ at hv
  change physicalOutput momentum tape.2.2.1
    (run (code P hR hc hsmall clock ell) G
      ⟨table P hR hc hsmall clock, xF, momentum⟩ Env.empty tape).value = _
  rw [hv]
  rw [← normalized_correction P clock
    (ClockPublicSetup.splitValues momentum tape.2.2.1 1)
    (fun i => (tape.2.2.2.2.2.1 i).1)
    (fun i => childPoint (finalChildren P hR hc hsmall clock ell G xF momentum
      (entryEnv P clock xF momentum tape.2.2.1
        (fun i => (tape.2.2.2.2.2.1 i).1)
        (fun i => (tape.2.2.2.2.2.2.2.1 i).1))
      tape.2.2.2.2.2.2.2.2.2 i))]
  exact physicalOutput_eq_directW P clock momentum tape.2.2.1 _ _

/-- The physical result uses the direct source sum while preserving the
complete original trace of that same run. -/
theorem run_code_physical_result {d : ℕ} (ell : ℕ) (G : Point d → Point d)
    (xF momentum : Point d)
    (tape : Tape d (code P hR hc hsmall clock ell)) :
    let E0 : Point d := tape.2.2.1
    let assemblyTape := tape.2.2.2.2.2
    let Z : Index P → Point d := fun i => (assemblyTape.1 i).1
    let initTape := assemblyTape.2.2
    let Z0 : Index P → Point d := fun i => (initTape.1 i).1
    let finalTape := initTape.2.2
    let env : Env d (entryCtx P) := entryEnv P clock xF momentum E0 Z Z0
    let Q := fun i => childPoint
      (finalChildren P hR hc hsmall clock ell G xF momentum env finalTape i)
    let source := run (code P hR hc hsmall clock ell) G
      ⟨table P hR hc hsmall clock, xF, momentum⟩ Env.empty tape
    readoutResult momentum E0 source =
      pointResult
        (directW P clock momentum
          (activeValues P clock (ClockPublicSetup.splitValues momentum E0 1) Z) Q)
        source.trace := by
  dsimp only
  have hv := run_code_physical_value P hR hc hsmall clock ell G xF momentum tape
  dsimp only at hv
  exact congrArg (fun v : Point d =>
    (⟨v, (run (code P hR hc hsmall clock ell) G
      ⟨table P hR hc hsmall clock, xF, momentum⟩ Env.empty tape).trace⟩ : Result d .point)) hv

/-- At the zero stopping clock, every final quadrature coefficient vanishes. -/
theorem physicalCoefficient_zero (i : Index P) :
    physicalCoefficient P ClockRetainedTapeTransport.anchorClock i = 0 := by
  simp [physicalCoefficient, coefficient, weight, ClockSchedule.weight,
    ClockRetainedTapeTransport.anchorClock]

theorem directW_zero {d : ℕ} (momentum : Point d)
    (active Q : Index P → Point d) :
    directW P ClockRetainedTapeTransport.anchorClock momentum active Q = momentum := by
  simp [directW, physicalCoefficient_zero P]

/-- The physical readout at zero clock returns the original entering
momentum for every complete tape, even though the latent output is H0. -/
theorem run_code_physical_zero {d : ℕ} (ell : ℕ) (G : Point d → Point d)
    (xF momentum : Point d)
    (tape : Tape d (code P hR hc hsmall ClockRetainedTapeTransport.anchorClock ell)) :
    (readoutResult momentum tape.2.2.1
      (run (code P hR hc hsmall ClockRetainedTapeTransport.anchorClock ell) G
        ⟨table P hR hc hsmall ClockRetainedTapeTransport.anchorClock, xF, momentum⟩
        Env.empty tape)).value = momentum := by
  have h := run_code_physical_value P hR hc hsmall
    ClockRetainedTapeTransport.anchorClock ell G xF momentum tape
  dsimp only at h
  exact h.trans (directW_zero P momentum _ _)

theorem run_code_physical_zero_result {d : ℕ} (ell : ℕ) (G : Point d → Point d)
    (xF momentum : Point d)
    (tape : Tape d (code P hR hc hsmall ClockRetainedTapeTransport.anchorClock ell)) :
    let source := run (code P hR hc hsmall ClockRetainedTapeTransport.anchorClock ell) G
      ⟨table P hR hc hsmall ClockRetainedTapeTransport.anchorClock, xF, momentum⟩
      Env.empty tape
    readoutResult momentum tape.2.2.1 source = pointResult momentum source.trace := by
  dsimp only
  exact congrArg (fun v : Point d =>
    (⟨v, (run (code P hR hc hsmall ClockRetainedTapeTransport.anchorClock ell) G
      ⟨table P hR hc hsmall ClockRetainedTapeTransport.anchorClock, xF, momentum⟩
      Env.empty tape).trace⟩ : Result d .point))
    (run_code_physical_zero P hR hc hsmall ell G xF momentum tape)

end AcceleratedLogConcave.Root.ClockPhysicalReadout
