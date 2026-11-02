import AcceleratedLogConcave.Root.ClockFinitePhaseKernel
import AcceleratedLogConcave.Root.ClockRetainedWork

/-! Exact execution transcript for the physical phase. The free uniform clock
and two final Gaussian draws add no gradient query; every root event is kept. -/
noncomputable section
set_option autoImplicit false
namespace AcceleratedLogConcave.Root.ClockFinitePhaseWork
open Oracle Oracle.TapeLowering Oracle.CubicScheduleThreshold
open ClockRetainedFinalSplice ClockRetainedTapeTransport ClockFinitePhaseKernel

variable (P : SourceSchedule) (hR : P.R ≤ 1/2) (hc : 0 < P.csch)
    (hsmall : P.csch < 1/160) {d : ℕ} (ell : ℕ)

def rootRun (G : Point d → Point d)
    (a : (Point d × Point d) × Draw P hR hc hsmall (d := d) ell) : Result d .point :=
  run (code P hR hc hsmall anchorClock ell) G
    ⟨anchorTable P hR hc hsmall (ClockUniformDraw.clockOfUniform a.2.1.1.1) ell,
      (normalizedInput P a.1).1,a.1.2⟩ Env.empty a.2.1.1.2

/-- Concrete returned phase and its full event transcript. -/
structure Execution (d : ℕ) where
  value : Point d × Point d
  trace : List (Event d)

def execute (Γ : ℝ) (G : Point d → Point d)
    (a : (Point d × Point d) × Draw P hR hc hsmall (d := d) ell) : Execution d :=
  ⟨output P hR hc hsmall ell Γ G a,
    (rootRun P hR hc hsmall ell G a).trace.take 1 ++ [Event.uniform []] ++
      (rootRun P hR hc hsmall ell G a).trace.drop 1 ++
      [Event.gaussian [], Event.gaussian []]⟩

/-- The clock draw is inserted after the root's first public E0 draw. -/
theorem rootRun_first_event (G : Point d → Point d)
    (a : (Point d × Point d) × Draw P hR hc hsmall (d := d) ell) :
    (rootRun P hR hc hsmall ell G a).trace.take 1 =
      [Event.gaussian (ClockPublicSetup.origin ell)] := rfl

/-- The two physical coordinate readouts have exactly the kernel's output. -/
theorem execute_value (Γ : ℝ) (G : Point d → Point d)
    (a : (Point d × Point d) × Draw P hR hc hsmall (d := d) ell) :
    (execute P hR hc hsmall ell Γ G a).value = output P hR hc hsmall ell Γ G a := rfl

theorem execute_queries (Γ : ℝ) (G : Point d → Point d)
    (a : (Point d × Point d) × Draw P hR hc hsmall (d := d) ell) :
    (traceCounts (execute P hR hc hsmall ell Γ G a).trace).queries =
      (traceCounts (rootRun P hR hc hsmall ell G a).trace).queries := by
  have h := congrArg (fun t : List (Event d) => (traceCounts t).queries)
    (List.take_append_drop 1 (rootRun P hR hc hsmall ell G a).trace)
  simpa [execute,traceCounts,shapeCounts,shapeCount,Event.erase] using h

/-- Same actual execution, with no exceptional tape or probabilistic restriction. -/
theorem execute_queries_le (hK : 10 ≤ P.K) (hC : 8 ≤ P.Csch)
    (hy : threshold P ≤ P.y) (Γ : ℝ) (G : Point d → Point d)
    (a : (Point d × Point d) × Draw P hR hc hsmall (d := d) ell) :
    ((traceCounts (execute P hR hc hsmall ell Γ G a).trace).queries : ℝ) ≤
      2*Real.exp (P.y/32) := by
  rw [execute_queries]
  exact ClockRetainedWork.executed_gradient_queries_le P hc hsmall anchorClock hK hC hy
    ell G _ a.2.1.1.2

/-- Boundary-clock regression for the full physical phase: position stays
fixed and only the declared momentum refresh remains, for every mixed tape. -/
theorem zero_clock_output (Γ : ℝ) (G : Point d → Point d) (x : Point d × Point d)
    (ω : Tape d (code P hR hc hsmall anchorClock ell)) (Gx Gp : Point d) :
    output P hR hc hsmall ell Γ G
      (x,(((⟨0,by constructor <;> norm_num⟩,ω),Gx),Gp)) =
      (x.1,Real.exp (-Γ) • x.2 + Real.sqrt (1-Real.exp (-2*Γ)) • Gp) := by
  dsimp only [output]
  rw [ClockPhysicalExecutionKernel.output_zero]
  simp [ClockUniformDraw.clockOfUniform,normalizedInput]

/-- Every execution of the same original-gradient phase whose law was
constructed above obeys the deterministic cap, including all root occurrences. -/
theorem original_gradient_queries_le (hK : 10 ≤ P.K) (hC : 8 ≤ P.Csch)
    (hy : threshold P ≤ P.y) (κ : ℝ) (V : Point d → ℝ)
    (a : (Point d × Point d) × Draw P hR hc hsmall (d := d) ell) :
    ((traceCounts (execute P hR hc hsmall ell (sourceGamma P κ) (gradient V) a).trace).queries : ℝ) ≤
      2*Real.exp (P.y/32) :=
  execute_queries_le P hR hc hsmall ell hK hC hy (sourceGamma P κ) (gradient V) a

end AcceleratedLogConcave.Root.ClockFinitePhaseWork
