import AcceleratedLogConcave.Oracle.MeanExecutionSchedule
import AcceleratedLogConcave.Oracle.SourceMeanInputStability

/-! Literal mean-body execution to shared-layer numerical error propagation.
This file does not supply benchmark child accuracy, benchmark residual bounds,
reference marginals, recursive precision admissibility, D2, G2/J2, or local KL. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option quotPrecheck false
namespace AcceleratedLogConcave.Oracle.SourceMeanExecutionRms
open MeasureTheory
open Numerics.AffineGraph AffineLowering TapeLowering NoisyLayer RecursiveMeanProgram
open RecursiveMeanContinuation RetainedMeanFinalBatch SourceMeanExecutable CovarianceSetup
open Numerics
open scoped BigOperators NNReal

variable {m n a h d : ℕ}
variable (M : MeanGeometry m) (nodes : Fin n ≃ M.MeanNode)
    (anchors : Fin a ≃ M.Anchor) (r σ Ds δ t w : ℝ)
    (main : Fin n → ExecutableData) (final : Fin m → ExecutableData) (sampling : ExecutableData)

abbrev Ready (n m h : ℕ) := MeanExecutablePrefix.readyCtx n (m+1) h [.point,.point]

def finish {Δ : Ctx} (old _ : Fin n → Ref Δ .point) (saved : RefMap (Ready n m h) Δ) :=
  paidCorrection (fun i => (final i).size) (fun i => (final i).program)
    (fun i => (final i).enumeration) (finalSlot (a := a) main final sampling)
    (correctionSlot (a := a) main final sampling) (saved (MeanExecutablePrefix.saved .here))
    (fun i => old (nodes.symm (.center M i))) (fun i => saved (MeanExecutablePrefix.designated i))
    finalOrigin (finalAuxiliary final)

local notation "F" => finish (a := a) (h := h) M nodes main final sampling
local notation "c" => (fun i => (main i).size)
local notation "p" => (fun i => (main i).program)
local notation "e" => (fun i => (main i).enumeration)
local notation "slots" => (mainSlot (a := a) main final sampling)
local notation "tbl" => table M nodes anchors r σ Ds δ t w main final sampling
local notation "A" => (fun i j => M.matrix r σ (nodes i) (nodes j))
local notation "rho" => RecursiveMeanPublicTable.centerNoise r M.R Ds
local notation "R" => residualRoot A rho (rowBound (m := m) r σ δ t w)
local notation "T" => (fun i => childRoot rho (M.radius r (nodes i)) (main i).shiftVector)
local notation "coeff" => (fun i => (main i).coefficient)
local notation "dir" => (fun i => RefMap.shiftMany n (RefMap.shiftMany n (MeanExecutablePrefix.direct i)))
local notation "saved" => (fun q => RefMap.shiftMany n (RefMap.shiftMany n q))

/-- This is a theorem about the literal assembled table, not a supplied table match. -/
theorem main_table : tbl ∘ slots = layerTable c p A R T coeff := by
  funext j
  exact table_main M nodes anchors r σ Ds δ t w main final sampling j

/-- Initialization uses the draw in the same body tape, exactly once. -/
def initial (N : ℕ) (env : Env d (Ready n m h))
    (tape : Tape d (body (a := a) (h := h) M nodes main final sampling N)) (i : Fin n) : Point d :=
  storedPoint env (MeanExecutablePrefix.direct i) + rho • (show Point d from (tape.1 i).1)

def initialEnv (N : ℕ) (env : Env d (Ready n m h))
    (tape : Tape d (body (a := a) (h := h) M nodes main final sampling N)) :
    Env d (List.replicate n .point ++ (List.replicate n .point ++ Ready n m h)) :=
  Env.prepend (initial M nodes r Ds main final sampling N env tape)
    (Env.prepend (fun i => (show Point d from (tape.1 i).1)) env)

/-- Full main raw data, including the actual paid-final continuation tape. -/
def raw (N : ℕ) (tape : Tape d (body (a := a) (h := h) M nodes main final sampling N)) :=
  rawTapeEquiv c p slots e layerOrigin mainDesignated residualOrigin (mainAuxiliary main) F d N
    batchRef dir saved tape.2.2

/-- The pre-existing interpreter's stored final state, not a numerical certificate. -/
def state (N : ℕ) (G : Point d → Point d) (x P : Point d)
    (env : Env d (Ready n m h))
    (tape : Tape d (body (a := a) (h := h) M nodes main final sampling N)) :=
  finalState c p slots e layerOrigin mainDesignated residualOrigin (mainAuxiliary main) F
    G ⟨tbl,x,P⟩ N batchRef dir saved
    (initialEnv M nodes r Ds main final sampling N env tape) tape.2.2

/-- Every original retained value survives: in particular P and each designated P_i. -/
theorem state_saved (N : ℕ) (G : Point d → Point d) (x P : Point d)
    (env : Env d (Ready n m h))
    (tape : Tape d (body (a := a) (h := h) M nodes main final sampling N))
    (q : Ref (Ready n m h) .point) :
    let st := state M nodes anchors r σ Ds δ t w main final sampling N G x P env tape
    storedPoint st.env (st.saved q) = storedPoint env q := by
  dsimp only [state]
  rw [finalState_saved]
  simp only [initialEnv,MeanExecutablePrefix.stored_shiftMany]

/-- Source child evaluator on the exact complete body tape. -/
def evaluator {Ω : Type*} (N : ℕ) (G : Point d → Point d)
    (tape : Ω → Tape d (body (a := a) (h := h) M nodes main final sampling N))
    (U : Fin n → Ω → Point d) :=
  MeanExecutionSchedule.evaluator c p F e T coeff G N
    (fun ω => raw (a := a) (h := h) M nodes main final sampling N (tape ω)) U

def noise {Ω : Type*} (N : ℕ)
    (tape : Ω → Tape d (body (a := a) (h := h) M nodes main final sampling N)) :=
  MeanExecutionSchedule.residualNoise c p F N
    (fun ω => raw (a := a) (h := h) M nodes main final sampling N (tape ω))

def designatedNoise {Ω : Type*} (N : ℕ)
    (tape : Ω → Tape d (body (a := a) (h := h) M nodes main final sampling N)) :=
  MeanExecutionSchedule.designatedNoise c p F N
    (fun ω => raw (a := a) (h := h) M nodes main final sampling N (tape ω))

/-- No execution-to-numerical equality is assumed: stored nodes are derived from run. -/
theorem state_old_eq_iterate {Ω : Type*} (N : ℕ) (G : Point d → Point d) (x P : Ω → Point d)
    (env : Ω → Env d (Ready n m h))
    (tape : Ω → Tape d (body (a := a) (h := h) M nodes main final sampling N))
    (U : Fin n → Ω → Point d) :
    (fun i ω =>
      let st := state M nodes anchors r σ Ds δ t w main final sampling
        N G (x ω) (P ω) (env ω) (tape ω)
      storedPoint st.env (st.old i)) =
    SharedLayerRms.iterate (fun i ω => storedPoint (env ω) (MeanExecutablePrefix.direct i)) A R
      (evaluator M nodes r Ds main final sampling N G tape U)
      (noise M nodes main final sampling N tape)
      (fun i ω => initial M nodes r Ds main final sampling N (env ω) (tape ω) i) N := by
  unfold evaluator noise
  rw [← MeanExecutionSchedule.fold_eq_iterate]
  funext i ω
  have hs := MeanExecutionSchedule.finalState_raw_old c p F e T coeff G slots layerOrigin
    mainDesignated residualOrigin (mainAuxiliary main) A R ⟨tbl,x ω,P ω⟩
    (main_table M nodes anchors r σ Ds δ t w main final sampling)
    N batchRef dir saved (initialEnv M nodes r Ds main final sampling N (env ω) (tape ω))
    (raw M nodes main final sampling N (tape ω)) i
  simp only [raw] at hs
  rw [Equiv.symm_apply_apply] at hs
  simpa only [raw,initialEnv,MeanExecutablePrefix.stored_shiftMany,prepend_batchRef,state] using hs

/-- The literal body runs initialization, the same main tape, and the paid finish. -/
theorem body_value (N : ℕ) (G : Point d → Point d) (x P : Point d)
    (env : Env d (Ready n m h))
    (tape : Tape d (body (a := a) (h := h) M nodes main final sampling N)) :
    let st := state M nodes anchors r σ Ds δ t w main final sampling N G x P env tape
    childPoint (run (body (a := a) (h := h) M nodes main final sampling N) G ⟨tbl,x,P⟩ env tape) =
      childPoint (run (F st.old st.direct st.saved) G ⟨tbl,x,P⟩ st.env st.tape) := by
  dsimp only [body,NonterminalMeanBlock.code] at tape ⊢
  rw [run_initialize]
  have h := run_iterateThen_value c p slots e layerOrigin mainDesignated residualOrigin
    (mainAuxiliary main) F G ⟨tbl,x,P⟩ N batchRef dir saved
    (initialEnv M nodes r Ds main final sampling N env tape) tape.2.2
  simp only [childPoint,state,initialEnv] at h ⊢
  simp only [finish,table_rho] at h ⊢
  exact h

/-- Extract the actual final child source tape. It depends on the complete body
sample, and is reused unchanged when the child is evaluated at the benchmark. -/
def finalTape (N : ℕ) (G : Point d → Point d) (x P : Point d)
    (env : Env d (Ready n m h))
    (tape : Tape d (body (a := a) (h := h) M nodes main final sampling N)) (i : Fin m) :
    Tape d (final i).program :=
  let st := state M nodes anchors r σ Ds δ t w main final sampling N G x P env tape
  let restored := restoreTape (finalSlot (a := a) main final sampling i)
    (compileWith (final i).program (final i).enumeration (finalAuxiliary final i))
    (fun q => nomatch q) (st.old (nodes.symm (.center M i)))
    (st.saved (MeanExecutablePrefix.designated i)) (st.tape.1 i)
  let v := unpackCompiledTape (final i).program (final i).enumeration (finalAuxiliary final i) restored
  transformedSourceTape (final i).program (final i).enumeration
    (childRoot rho (r*M.R) (final i).shiftVector) v.1 v.2

def finalEvaluator (N : ℕ) (G : Point d → Point d) (x P : Point d)
    (env : Env d (Ready n m h))
    (tape : Tape d (body (a := a) (h := h) M nodes main final sampling N)) (i : Fin m)
    (z : Point d) : Point d :=
  childPoint (run (final i).program G
    ⟨(final i).coefficient,z,storedPoint env (MeanExecutablePrefix.designated i)⟩ Env.empty
    (finalTape M nodes anchors r σ Ds δ t w main final sampling N G x P env tape i))

/-- Exact final correction: original P and designated blocks, no resampling. -/
theorem body_paid_final (N : ℕ) (G : Point d → Point d) (x P : Point d)
    (env : Env d (Ready n m h))
    (tape : Tape d (body (a := a) (h := h) M nodes main final sampling N)) :
    let st := state M nodes anchors r σ Ds δ t w main final sampling N G x P env tape
    childPoint (run (body (a := a) (h := h) M nodes main final sampling N) G ⟨tbl,x,P⟩ env tape) =
      σ • storedPoint env (MeanExecutablePrefix.saved .here) +
        ∑ i, Numerics.GaussLegendre.weight m i •
          (finalEvaluator M nodes anchors r σ Ds δ t w main final sampling N G x P env tape i
            (storedPoint st.env (st.old (nodes.symm (.center M i)))) -
              RecursiveMeanPublicTable.finalWidth M.R σ •
                storedPoint env (MeanExecutablePrefix.designated i)) := by
  rw [body_value]
  dsimp only
  let st := state M nodes anchors r σ Ds δ t w main final sampling N G x P env tape
  have hc : tbl ∘ correctionSlot (a := a) main final sampling =
      RetainedMeanCorrection.table σ (Numerics.GaussLegendre.weight m)
        (fun _ => RecursiveMeanPublicTable.finalWidth M.R σ) :=
    funext fun j => table_correction M nodes anchors r σ Ds δ t w main final sampling j
  dsimp only [finish]
  rw [run_paidCorrection _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hc]
  dsimp only [childPoint,pointResult]
  rw [state_saved]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  have hf : tbl ∘ finalSlot (a := a) main final sampling i =
      matrixTable (childRoot rho (r*M.R) (final i).shiftVector) (final i).coefficient :=
    funext fun j => table_final M nodes anchors r σ Ds δ t w main final sampling i j
  rw [run_designatedChild _ _ _ _ _ _ _ _ _ _ _ hf]
  simp only [childPoint,state_saved,finalEvaluator,finalTape]
  congr 8

end AcceleratedLogConcave.Oracle.SourceMeanExecutionRms
