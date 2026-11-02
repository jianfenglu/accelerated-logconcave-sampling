import AcceleratedLogConcave.Root.ClockFinalChildRms
import AcceleratedLogConcave.Root.FinalMeanStability

/-! The actual final reply and its source benchmark evaluate the same full
compiler-transformed seed, with the original stored Pi. Only the center moves.
The mathematical mean row is retained explicitly in every error. -/
noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option quotPrecheck false
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
namespace AcceleratedLogConcave.Root.ClockFinalEvaluator
open Oracle Oracle.AffineLowering Oracle.TapeLowering Oracle.NoisyLayer Oracle.FixedTapeStability
open Oracle.TailOccurrenceCut Oracle.TailOccurrenceCut.TailCut Oracle.PrivateCausalLayer
open ClockNoisyLayer ClockChronologicalCoupling
variable (P : SourceSchedule) (hR : P.R≤1/2) (hc : 0<P.csch) (hsmall : P.csch<1/160)
  (clock : ClockLaw.Clock) (label : ℕ) (hK : 10≤P.K) (hC : 8≤P.Csch)
  (hy : CubicScheduleThreshold.threshold P≤P.y) {d : ℕ}
local notation "host" => Host P hR hc hsmall clock label
local notation "cur" => terminalCursor P hR hc hsmall clock label
local notation "batch" => ClockFinalBatchCoupling.data P hR hc hsmall clock label hK hC hy
local notation "cut" => ClockFinalBatchCoupling.batchCut P hR hc hsmall clock label hK hC hy
local notation "Sample" => History P d × Tape d host

def input (z : Sample) : Inputs d (ClockRetainedFinalSplice.size P hR hc hsmall clock) :=
  ⟨ClockRetainedFinalSplice.table P hR hc hsmall clock,z.1.1.1.1,z.1.1.1.2⟩
def store (G : Point d→Point d) (z : Sample) : Env d (cur).ctx :=
  envAt G (input P hR hc hsmall clock label z) cut Env.empty (split cut z.2).1

def actualCenter (G : Point d→Point d) (i : Index P) (z : Sample) : Point d :=
  storedPoint (store P hR hc hsmall clock label hK hC hy G z) ((cur).old i)

def designated (G : Point d→Point d) (i : Index P) (z : Sample) : Point d :=
  storedPoint (store P hR hc hsmall clock label hK hC hy G z) ((batch).designated i)

/-- Literal auxiliary and residual inventories of the actual final occurrence. -/
def seed (i : Index P) (z : Sample) :=
  DesignatedChildAbsorbedLaw.tapeSeed ((batch).child i).program ((batch).child i).enumeration
    ((batch).slot i) ((batch).old i) ((batch).designated i) ((batch).auxiliary i)
    ((split cut z.2).2.1 i)

/-- Complete source tape and original Pi are fixed while the center varies. -/
def evaluator (G : Point d→Point d) (i : Index P) (z : Sample) (y : Point d) : Point d :=
  let s := seed P hR hc hsmall clock label hK hC hy i z
  (run ((batch).child i).program G
    ⟨((batch).child i).coefficient,y,designated P hR hc hsmall clock label hK hC hy G i z⟩ Env.empty
    (transformedSourceTape ((batch).child i).program ((batch).child i).enumeration
      (CovarianceSetup.childRoot ((batch).rho i) ((batch).radius i) ((batch).child i).shiftVector) s.1 s.2)).value

/-- Exact actual final reply, on every complete original source tape. -/
theorem finalReply_eq_evaluator (G : Point d→Point d) (i : Index P) (z : Sample) :
    ClockFinalCorrectionReadout.finalReply P hR hc hsmall clock label G z.1.1.1.1 z.1.1.1.2 z.2 i=
      evaluator P hR hc hsmall clock label hK hC hy G i z
        (actualCenter P hR hc hsmall clock label hK hC hy G i z) := by
  have h := ClockRetainedFinalSplice.run_finalChild P hR hc hsmall clock label i ((cur).old i)
      ((cur).saved (ClockRetainedFinalSplice.designatedRef P i)) G z.1.1.1.1 z.1.1.1.2
      (store P hR hc hsmall clock label hK hC hy G z) ((split cut z.2).2.1 i)
  have hv := congrArg (fun r : Result d .point => r.value) h
  exact hv

variable {V : Point d→ℝ} (hV : ContDiff ℝ 2 V)
  (hlo : ∀ z v,0≤fderiv ℝ (fderiv ℝ V) z v v)
  (hup : ∀ z v,fderiv ℝ (fderiv ℝ V) z v v≤‖v‖^2)

include hV hlo hup in
/-- Same original Pi and full transformed tape; only the center changes. -/
theorem evaluator_sub_le (i : Index P) (z : Sample) (x y : Point d) :
    ‖evaluator P hR hc hsmall clock label hK hC hy (gradient V) i z x-
      evaluator P hR hc hsmall clock label hK hC hy (gradient V) i z y‖≤2*P.delta*‖x-y‖ := by
  exact childStable_tape _ _ (gradient V) _
    (FinalMeanStability.final_mean_stable P hK hc hsmall hC hy hV hlo hup i clock)
    (designated P hR hc hsmall clock label hK hC hy (gradient V) i z) x y _

variable {m : ℝ} (hm : 0<m)
  (hstrong : ∀ z v,m*‖v‖^2≤fderiv ℝ (fderiv ℝ V) z v v)
local notation "Hlo" => OuterRootFlowIdentification.lower_nonneg hm hstrong

def benchmarkCenter (i : Index P) (z : Sample) : Point d :=
  ClockChronologicalCoupling.center P clock hV Hlo hup i z.1.1 + rhoC P • z.1.2.2 i

/-- The proved fullseed benchmark error is this exact evaluator at Phi+rho Z. -/
theorem benchmarkError_eq_evaluator (i : Index P) (z : Sample × (Index P→Point d)) :
    ClockFinalChildRms.benchmarkError P hR hc hsmall clock label hK hC hy hV hm hstrong hup i z=
      evaluator P hR hc hsmall clock label hK hC hy (gradient V) i z.1
        (benchmarkCenter P hR hc hsmall clock label hV hup hm hstrong i z.1) -
      ClockFinalChildRms.meanRow P clock hV hm hstrong hup i
        (ClockFinalObservationLaw.baseAssembly P clock z.1.1.1).1 -
      ClockRetainedFinalSplice.width P clock i • z.2 i := by
  simp only [ClockFinalChildRms.benchmarkError,ClockFinalChildRms.prefixError,
    DesignatedChildBatchBenchmarkError.sourceError,ClockFinalObservationLaw.observation,
    ClockFinalBatchCoupling.observation,split_afterBatch,batchParts_append]
  rw [sub_add_eq_sub_sub]
  rfl

/-- True-center final error, before controlling the main-loop center error. -/
def finalError (i : Index P) (z : Sample × (Index P→Point d)) : Point d :=
  ClockFinalCorrectionReadout.finalReply P hR hc hsmall clock label (gradient V)
    z.1.1.1.1.1 z.1.1.1.1.2 z.1.2 i -
    ClockFinalChildRms.meanRow P clock hV hm hstrong hup i
      (ClockFinalObservationLaw.baseAssembly P clock z.1.1.1).1 -
    ClockRetainedFinalSplice.width P clock i • z.2 i

private theorem error_norm_le (A B U Z : Point d) :
    ‖A-U-Z‖≤‖A-B‖+‖B-U-Z‖ := by
  have h := norm_add_le (A-B) (B-U-Z)
  have he : (A-B)+(B-U-Z)=A-U-Z := by module
  rw [he] at h
  exact h

/-- Deterministic actual final-child perturbation bound on the same seed. -/
theorem finalError_norm_le (i : Index P) (z : Sample × (Index P→Point d)) :
    ‖finalError P hR hc hsmall clock label hV hup hm hstrong i z‖≤
      2*P.delta*‖actualCenter P hR hc hsmall clock label hK hC hy (gradient V) i z.1-
        benchmarkCenter P hR hc hsmall clock label hV hup hm hstrong i z.1‖+
      ‖ClockFinalChildRms.benchmarkError P hR hc hsmall clock label hK hC hy hV hm hstrong hup i z‖ := by
  let A := ClockFinalCorrectionReadout.finalReply P hR hc hsmall clock label (gradient V)
    z.1.1.1.1.1 z.1.1.1.1.2 z.1.2 i
  let B := evaluator P hR hc hsmall clock label hK hC hy (gradient V) i z.1
    (benchmarkCenter P hR hc hsmall clock label hV hup hm hstrong i z.1)
  let U := ClockFinalChildRms.meanRow P clock hV hm hstrong hup i
    (ClockFinalObservationLaw.baseAssembly P clock z.1.1.1).1
  let Z := ClockRetainedFinalSplice.width P clock i • z.2 i
  have hbase := error_norm_le A B U Z
  have hactual := finalReply_eq_evaluator P hR hc hsmall clock label hK hC hy (gradient V) i z.1
  have he : ‖A-B‖=‖evaluator P hR hc hsmall clock label hK hC hy (gradient V) i z.1
      (actualCenter P hR hc hsmall clock label hK hC hy (gradient V) i z.1)-B‖ :=
    congrArg (fun q : Point d => ‖q-B‖) hactual
  have hmove := he.trans_le (evaluator_sub_le P hR hc hsmall clock label hK hC hy hV Hlo hup i z.1 _ _)
  have hb := benchmarkError_eq_evaluator P hR hc hsmall clock label hK hC hy hV hup hm hstrong i z
  have hbench : ‖B-U-Z‖=‖ClockFinalChildRms.benchmarkError P hR hc hsmall clock label hK hC hy hV hm hstrong hup i z‖ :=
    congrArg (fun q : Point d => ‖q‖) hb.symm
  exact hbase.trans (add_le_add hmove hbench.le)

end AcceleratedLogConcave.Root.ClockFinalEvaluator
