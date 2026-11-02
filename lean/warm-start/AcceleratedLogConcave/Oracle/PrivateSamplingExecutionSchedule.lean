import AcceleratedLogConcave.Oracle.PrivateSamplingFirstBandOutput
import AcceleratedLogConcave.Oracle.MeanExecutionSchedule

/-! The literal PRIVATE initialization and finite loop, read from its complete
execution tape. This is an operational join, not an accuracy certificate.
No replacement algorithm, independent copy, or supplied state equation is used. -/
noncomputable section
namespace AcceleratedLogConcave.Oracle.PrivateSamplingExecutionSchedule
open Numerics Numerics.AffineGraph AffineLowering TapeLowering NoisyLayer
open RecursiveMeanProgram RecursiveMeanContinuation PrivateSamplingProgram
open SourceExecutableTables CovarianceSetup
open scoped BigOperators
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

variable {m n d : ℕ} (S : SamplingGeometry m) (e : Fin n ≃ S.Node)
  (r Ds : ℝ) (main final : Fin n → ExecutableData) (N : ℕ)

abbrev Entry (n : ℕ) := replyCtx n [.point,.scalar,.point,.point]
local notation "cfg" => samplingConfig main final N
local notation "c" => (fun i : Fin n => ExecutableData.size (main i))
local notation "p" => (fun i : Fin n => ExecutableData.program (main i))
local notation "en" => (fun i : Fin n => ExecutableData.enumeration (main i))
local notation "A" => samplingMatrix S e r
local notation "rho" => samplingNoise S r Ds
local notation "C" => residualRoot A rho (r^2)
local notation "T" => (fun i : Fin n => childRoot rho (S.radius r (e i)) (ExecutableData.shiftVector (main i)))
local notation "coeff" => (fun i : Fin n => ExecutableData.coefficient (main i))
local notation "tbl" => samplingTable S e r Ds main final
local notation "dir" => (fun i : Fin n => RefMap.shiftMany n (RefMap.shiftMany n (batchRef i)))
local notation "saved" => (fun q => RefMap.shiftMany n (RefMap.shiftMany n q))

def finisher {Δ : Ctx} (old _ : Fin n → Ref Δ .point)
    (keep : RefMap (Entry n) Δ) :=
  PrivateSamplingProgram.finish cfg old (keep (RefMap.shiftMany n .here))
local notation "F" => finisher main final N

/-- The table identity is derived from the public source constructor. -/
theorem main_table : tbl ∘ (cfg).mainSlots = layerTable c p A C T coeff := by
  funext j
  exact samplingTable_main S e r Ds main final j

/-- The actual setup coefficient, not an assumed direct-array identification. -/
theorem direct_weight (i : Fin n) :
    tbl ((cfg).directWeight i) = r*S.mesh.location m (e i) := by
  change tbl (scalarSlot main final (Fin.castAdd _ i)) = _
  simp [samplingScalarTable]

theorem initial_noise : tbl (cfg).noise = rho := by
  change tbl (scalarSlot main final (Fin.natAdd _ (Fin.natAdd _ (0 : Fin 4)))) = _
  simp [samplingScalarTable]

abbrev FullTape := Tape d (SamplingExecutable.build S e r Ds main final N).program
abbrev inp (x P : Point d) : Inputs d (samplingSize main final) := ⟨tbl,x,P⟩

def bodyTape (ω : FullTape (d := d) S e r Ds main final N) := ω.2.2.2.2.2

def entry (x P : Point d) (ω : FullTape (d := d) S e r Ds main final N) : Env d (Entry n) :=
  setupEnv cfg (inp S e r Ds main final x P) (show Point d from ω.2.1)

def initial (x : Point d) (ω : FullTape (d := d) S e r Ds main final N) (i : Fin n) : Point d :=
  x + (r*S.mesh.location m (e i)) • (show Point d from ω.2.1) +
    rho • (show Point d from ((bodyTape S e r Ds main final N ω).1 i).1)

def initialEnv (x P : Point d) (ω : FullTape (d := d) S e r Ds main final N) :
    Env d (replyCtx n (replyCtx n (Entry n))) :=
  Env.prepend (initial S e r Ds main final N x ω)
    (Env.prepend (fun i => (show Point d from ((bodyTape S e r Ds main final N ω).1 i).1))
      (entry S e r Ds main final N x P ω))

def raw (ω : FullTape (d := d) S e r Ds main final N) :=
  rawTapeEquiv c p (cfg).mainSlots en (cfg).layerOrigin (cfg).mainDesignated (cfg).mainResidual
    (cfg).mainAuxiliary F d N batchRef dir saved (bodyTape S e r Ds main final N ω).2.2

/-- The same raw schedule, including the unexecuted fresh-final tail. -/
def evaluator (G : Point d → Point d)
    (U : Fin n → FullTape (d := d) S e r Ds main final N → Point d) :=
  MeanExecutionSchedule.evaluator c p F en T coeff G N (raw S e r Ds main final N) U

def residualNoise :=
  MeanExecutionSchedule.residualNoise c p F N (raw (d := d) S e r Ds main final N)

def designatedNoise :=
  MeanExecutionSchedule.designatedNoise c p F N (raw (d := d) S e r Ds main final N)

/-- Actual stored state equals the public numerical iterate on this very tape.
No numerical-accuracy, marginal-law or equality premise is retained. -/
theorem state_old_eq_iterate (G : Point d → Point d) (x P : Point d)
    (U : Fin n → FullTape (d := d) S e r Ds main final N → Point d) :
    (fun i ω =>
      let st := PrivateSamplingTapeProjections.state cfg G (inp S e r Ds main final x P) ω
      storedPoint st.env (st.old i)) =
    SharedLayerRms.iterate
      (fun i ω => x + (r*S.mesh.location m (e i)) • (show Point d from ω.2.1)) A C
      (evaluator S e r Ds main final N G U)
      (residualNoise S e r Ds main final N)
      (fun i ω => initial S e r Ds main final N x ω i) N := by
  dsimp only [evaluator,residualNoise]
  refine Eq.trans ?_ (MeanExecutionSchedule.fold_eq_iterate c p F en T coeff G A C N
    (raw S e r Ds main final N)
    (fun i ω => x + (r*S.mesh.location m (e i)) • (show Point d from ω.2.1))
    (fun i ω => initial S e r Ds main final N x ω i) U)
  funext i ω
  have hentry (j : Fin n) : storedPoint (entry S e r Ds main final N x P ω) (batchRef j) =
      x + (r*S.mesh.location m (e j)) • (show Point d from ω.2.1) := by
    exact (setupEnv_direct cfg (inp S e r Ds main final x P)
      (show Point d from ω.2.1) j).trans
      (congrArg (fun z : ℝ => x + z • (show Point d from ω.2.1))
        (direct_weight S e r Ds main final N j))
  have hdir (j : Fin n) :
      storedPoint (initialEnv S e r Ds main final N x P ω) (dir j) =
        x + (r*S.mesh.location m (e j)) • (show Point d from ω.2.1) := by
    exact ((prepend_shiftMany _ _ (RefMap.shiftMany n (batchRef j))).trans
      (prepend_shiftMany _ _ (batchRef j))).trans (hentry j)
  have hi (j : Fin n) :
      storedPoint (initialEnv S e r Ds main final N x P ω) (batchRef j) =
        initial S e r Ds main final N x ω j := prepend_batchRef _ _ j
  have hs := MeanExecutionSchedule.finalState_raw_old c p F en T coeff G (cfg).mainSlots
    (cfg).layerOrigin (cfg).mainDesignated (cfg).mainResidual (cfg).mainAuxiliary A C
    (inp S e r Ds main final x P) (main_table S e r Ds main final N)
    N batchRef dir saved (initialEnv S e r Ds main final N x P ω)
    (raw S e r Ds main final N ω) i
  have ht := congrArg (fun tail =>
    let st := finalState c p (cfg).mainSlots en (cfg).layerOrigin (cfg).mainDesignated (cfg).mainResidual
      (cfg).mainAuxiliary F G (inp S e r Ds main final x P) N batchRef dir saved
      (initialEnv S e r Ds main final N x P ω) tail
    storedPoint st.env (st.old i))
    ((rawTapeEquiv c p (cfg).mainSlots en (cfg).layerOrigin (cfg).mainDesignated (cfg).mainResidual
      (cfg).mainAuxiliary F d N batchRef dir saved).symm_apply_apply
        (bodyTape S e r Ds main final N ω).2.2)
  have he : (fun j => storedPoint (entry S e r Ds main final N x P ω) (batchRef j) +
      (inp S e r Ds main final x P).coefficient (cfg).noise •
        (show Point d from ((bodyTape S e r Ds main final N ω).1 j).1)) =
        initial S e r Ds main final N x ω := by
    funext j
    exact congrArg₂ (fun (v : Point d) (a : ℝ) =>
      v + a • (show Point d from ((bodyTape S e r Ds main final N ω).1 j).1))
      (hentry j) (initial_noise S e r Ds main final N)
  have hfold := ht.symm.trans hs
  simp only [hdir, hi] at hfold
  exact (congrArg (fun init : Fin n → Point d =>
    let st := finalState c p (cfg).mainSlots en (cfg).layerOrigin
      (cfg).mainDesignated (cfg).mainResidual (cfg).mainAuxiliary F G
      (inp S e r Ds main final x P) N batchRef dir saved
      (Env.prepend init
        (Env.prepend
          (fun j => (show Point d from ((bodyTape S e r Ds main final N ω).1 j).1))
          (entry S e r Ds main final N x P ω)))
      (bodyTape S e r Ds main final N ω).2.2
    storedPoint st.env (st.old i)) he).trans hfold

/-- The initialization's actual Gaussian cancels against the shared benchmark.
Only a path difference remains; there is no absolute-state moment premise. -/
theorem initial_sub_reference (x : Point d)
    (Y : Fin n → FullTape (d := d) S e r Ds main final N → Point d)
    (ω : FullTape (d := d) S e r Ds main final N) (i : Fin n) :
    initial S e r Ds main final N x ω i -
      (x + (r*S.mesh.location m (e i)) • Y i ω +
        rho • (show Point d from ((bodyTape S e r Ds main final N ω).1 i).1)) =
      (r*S.mesh.location m (e i)) • ((show Point d from ω.2.1) - Y i ω) := by
  simp only [initial, smul_sub]
  abel

end AcceleratedLogConcave.Oracle.PrivateSamplingExecutionSchedule
