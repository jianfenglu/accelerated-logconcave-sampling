import AcceleratedLogConcave.Oracle.PrivateSamplingExecutionSchedule
import AcceleratedLogConcave.Oracle.PrefixCursor

/-! Concrete entering-state readout for the original full private tape.
Reconstructed locally; the compact receiving checkpoint omits its pinned wrapper. -/
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

local notation "F" => finisher main final N

def enteringState (G : Point d → Point d) (x P : Point d) (k : ℕ)
    (ω : FullTape (d := d) S e r Ds main final N) :=
  prefixCursor c p (cfg).mainSlots en (cfg).layerOrigin (cfg).mainDesignated
    (cfg).mainResidual (cfg).mainAuxiliary F G (inp S e r Ds main final x P)
    N k batchRef dir saved
    (Env.prepend
      (fun j => storedPoint (entry S e r Ds main final N x P ω) (batchRef j) +
        (inp S e r Ds main final x P).coefficient (cfg).noise •
          (show Point d from ((bodyTape S e r Ds main final N ω).1 j).1))
      (Env.prepend (fun j => (show Point d from ((bodyTape S e r Ds main final N ω).1 j).1))
        (entry S e r Ds main final N x P ω)))
    (bodyTape S e r Ds main final N ω).2.2

def actualCenterAt (G : Point d → Point d) (x P : Point d) (k : ℕ) (i : Fin n)
    (ω : FullTape (d := d) S e r Ds main final N) : Point d :=
  let st := enteringState S e r Ds main final N G x P k ω
  storedPoint st.env (st.old i)

theorem enteringCenter_eq_iterate (G : Point d → Point d) (x P : Point d)
    (U : Fin n → FullTape (d := d) S e r Ds main final N → Point d)
    (k : ℕ) (hk : k ≤ N) :
    actualCenterAt S e r Ds main final N G x P k =
    SharedLayerRms.iterate
      (fun i ω => x + (r*S.mesh.location m (e i)) • (show Point d from ω.2.1)) A C
      (evaluator S e r Ds main final N G U)
      (residualNoise S e r Ds main final N)
      (fun i ω => initial S e r Ds main final N x ω i) k := by
  dsimp only [evaluator,residualNoise]
  refine Eq.trans ?_ (MeanExecutionSchedule.prefixFold_eq_iterate c p F en T coeff G A C N k hk
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
  have hs := MeanExecutionSchedule.prefixCursor_raw_old c p F en T coeff G (cfg).mainSlots
    (cfg).layerOrigin (cfg).mainDesignated (cfg).mainResidual (cfg).mainAuxiliary A C
    (inp S e r Ds main final x P) (main_table S e r Ds main final N)
    N k hk batchRef dir saved (initialEnv S e r Ds main final N x P ω)
    (raw S e r Ds main final N ω) i
  have ht := congrArg (fun tail =>
    let st := prefixCursor c p (cfg).mainSlots en (cfg).layerOrigin (cfg).mainDesignated (cfg).mainResidual
      (cfg).mainAuxiliary F G (inp S e r Ds main final x P) N k batchRef dir saved
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
    let st := prefixCursor c p (cfg).mainSlots en (cfg).layerOrigin
      (cfg).mainDesignated (cfg).mainResidual (cfg).mainAuxiliary F G
      (inp S e r Ds main final x P) N k batchRef dir saved
      (Env.prepend init
        (Env.prepend
          (fun j => (show Point d from ((bodyTape S e r Ds main final N ω).1 j).1))
          (entry S e r Ds main final N x P ω)))
      (bodyTape S e r Ds main final N ω).2.2
    storedPoint st.env (st.old i)) he).trans hfold

end AcceleratedLogConcave.Oracle.PrivateSamplingExecutionSchedule
