import AcceleratedLogConcave.Oracle.CubicExecutableWorkShift
import AcceleratedLogConcave.Numerics.SourceScheduleFeasibility

/-! Actual prescribed-mesh cardinalities and every-tape work, at explicit
scalar geometry and work thresholds. The source occurrence count includes the
extra kernel origin and the private sampling prefix. -/
noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace AcceleratedLogConcave.Numerics.SourceWorkResolution
open AcceleratedLogConcave.Oracle
open AcceleratedLogConcave.Oracle.ScalarSchedulePayment
open AcceleratedLogConcave.Oracle.CubicExecutableWorkShift
open AcceleratedLogConcave.Oracle.ExecutableWorkCardinality
open AcceleratedLogConcave.Oracle.RecursiveExecutable
open AcceleratedLogConcave.Oracle.TapeLowering
open AcceleratedLogConcave.Numerics.AffineGraph
open AcceleratedLogConcave.Oracle.ChildAbsorption
open AcceleratedLogConcave.Oracle.CovarianceSetup

def schedule (K : ℕ) (c C y : ℝ) : Oracle.SourceSchedule := ⟨K,c,C,y⟩

theorem schedule_t (K : ℕ) (c C y : ℝ) :
    (schedule K c C y).t = SourceSchedule.t K c := rfl

theorem schedule_nP (K : ℕ) (c C y : ℝ) :
    (schedule K c C y).NP = SourceSchedule.nP K C := rfl

theorem schedule_H (K : ℕ) (c C y : ℝ) :
    (schedule K c C y).H = SourceSchedule.H K c C := rfl

theorem schedule_T (K : ℕ) (c C y : ℝ) :
    (schedule K c C y).T = SourceSchedule.T K c C := by
  unfold schedule Oracle.SourceSchedule.T Oracle.SourceSchedule.gammaM
    Oracle.SourceSchedule.D0 Oracle.SourceSchedule.NP Oracle.SourceSchedule.H
    Oracle.SourceSchedule.A Oracle.SourceSchedule.t
    SourceSchedule.T SourceSchedule.d0 SourceSchedule.nP SourceSchedule.H SourceSchedule.t
    RecursiveExecutable.sourceLayers
  ring

theorem schedule_w (K : ℕ) (c C y : ℝ) :
    (schedule K c C y).w = SourceSchedule.w K c C := by
  change c / (schedule K c C y).T = c / SourceSchedule.T K c C
  rw [schedule_T]

theorem schedule_m (K : ℕ) (c C y : ℝ) :
    (schedule K c C y).m = SourceSchedule.m K c C := by
  unfold Oracle.SourceSchedule.m SourceSchedule.m
    Root.RecursiveRadiusFamily.meanOrder
  rw [schedule_w]
  rfl

theorem schedule_delta (K : ℕ) (c C y : ℝ) :
    (schedule K c C y).delta = SourceSchedule.δ y := rfl

theorem radiusGuard (P : Oracle.SourceSchedule) (hc : 0 < P.csch)
    (hsmall : P.csch < 1/160) (hC : 1 ≤ P.Csch)
    (hy : 0 ≤ P.y) (hgeom : Ygeom P ≤ P.y) : P.R ≤ 1/2 :=
  (geometry_caps P hc hsmall hC hy hgeom).2.2.1.trans
    (geometry_caps P hc hsmall hC hy hgeom).2.2.2

/-- The literal mean and private-node counts are bounded by a polynomial in
the order and resolution, times the exact prescribed inverse-mesh factor. -/
theorem actual_counts (P : Oracle.SourceSchedule) (hc : 0 < P.csch)
    (hsmall : P.csch < 1/160) (hC : 1 ≤ P.Csch)
    (hy : 0 ≤ P.y) (hgeom : Ygeom P ≤ P.y) :
    let hR := radiusGuard P hc hsmall hC hy hgeom
    (n P hR:ℝ) ≤ 1280*(P.m:ℝ)^4*(1+P.t*P.y)^2*
      Real.exp (2*P.w*P.y) ∧
    (ns P hR:ℝ) ≤ 1280*(P.m:ℝ)^4*(1+P.t*P.y)^2*
      Real.exp (2*P.w*P.y) := by
  exact ScalarSchedulePayment.actual_counts P _ hc hsmall hC hy hgeom

/-- The common base is made from the actual mean and private counts; the
scalar work threshold absorbs its full padded support height. -/
theorem tier_work (P : Oracle.SourceSchedule) (hc : 0 < P.csch)
    (hsmall : P.csch < 1/160) (hC : 1 ≤ P.Csch)
    (hy : 0 ≤ P.y) (hgeom : Ygeom P ≤ P.y)
    (hwork : Ywork P ≤ P.y) :
    let hR := radiusGuard P hc hsmall hC hy hgeom
    D P hR ≤ a P*(1+P.y)^2*Real.exp (2*P.w*P.y) ∧
    (D P hR)^(G P) ≤ Real.exp (P.y/64) := by
  exact ⟨actual_D_upper P _ hc hsmall hC hy hgeom,
    actual_D_work P _ hc hsmall hC hy hwork hgeom⟩

/-- For every oracle, input, and tape, the actual recursive executable's
query-plus-Gaussian work is paid by the source schedule. The branching base
uses both literal mesh inventories, including the private prefix. -/
theorem executed_work {d : ℕ} (P : Oracle.SourceSchedule)
    (hc : 0 < P.csch) (hsmall : P.csch < 1/160)
    (hC : 1 ≤ P.Csch) (hy : 0 ≤ P.y)
    (hgeom : Ygeom P ≤ P.y) (hwork : Ywork P ≤ P.y)
    (scale r σ q : ℝ) (hqK : q ≤ (P.K:ℝ))
    (oracle : Point d → Point d)
    (input : Inputs d (CubicExecutableWorkShift.data P
      (radiusGuard P hc hsmall hC hy hgeom) hc hsmall scale r σ q).size)
    (tape : Tape d (CubicExecutableWorkShift.data P
      (radiusGuard P hc hsmall hC hy hgeom) hc hsmall scale r σ q).program) :
    let hR := radiusGuard P hc hsmall hC hy hgeom
    let counts := traceCounts (run (CubicExecutableWorkShift.data P hR hc hsmall
      scale r σ q).program oracle input Env.empty tape).trace
    ((counts.queries+counts.gaussianBlocks:ℕ):ℝ) ≤
      (D P hR)^(G P) ∧
    ((counts.queries+counts.gaussianBlocks:ℕ):ℝ) ≤ Real.exp (P.y/64) := by
  let hR := radiusGuard P hc hsmall hC hy hgeom
  let C := CubicExecutableWorkShift.source P hR
  have hn := RecursiveExecutable.executed_full_work_mean_le C.M C.nodes
    (CubicExecutableWorkShift.anchors P hR) (CubicExecutableWorkShift.seeds P hR)
    C.Ds C.δ C.t C.w C.layers (P.t_pos hc)
    (CubicExecutableWorkShift.step_quarter P hc hsmall) C.mesh C.snodes
    scale r σ q oracle input tape
  have hrank := Precision.precisionRank_mono (P.t_pos hc) hqK
  have hcap := rho_add_one_le_G P hc hC
  have hpow := absorb_leading_two (CubicExecutableWorkShift.D_ge_two P hR)
    (CubicExecutableWorkShift.branching_le_D P hR)
    (show Precision.precisionRank P.t q+1 ≤ G P by
      change Precision.precisionRank P.t (P.K:ℝ)+1 ≤ G P at hcap
      omega)
  have hworkR :
      ((traceCounts (run (CubicExecutableWorkShift.data P hR hc hsmall
        scale r σ q).program oracle input Env.empty tape).trace).queries+
        (traceCounts (run (CubicExecutableWorkShift.data P hR hc hsmall
        scale r σ q).program oracle input Env.empty tape).trace).gaussianBlocks:ℕ)
      ≤ 2*RecursiveExecutable.fullBranching P.NP (n P hR) (ns P hR) P.m
        (CubicExecutableWorkShift.seedCount P hR)^Precision.precisionRank P.t q := hn
  have hfinal :
      (((traceCounts (run (CubicExecutableWorkShift.data P hR hc hsmall
        scale r σ q).program oracle input Env.empty tape).trace).queries+
        (traceCounts (run (CubicExecutableWorkShift.data P hR hc hsmall
        scale r σ q).program oracle input Env.empty tape).trace).gaussianBlocks:ℕ):ℝ)
      ≤ (D P hR)^(G P) := by
    have hcast :
        (((traceCounts (run (CubicExecutableWorkShift.data P hR hc hsmall
          scale r σ q).program oracle input Env.empty tape).trace).queries+
          (traceCounts (run (CubicExecutableWorkShift.data P hR hc hsmall
          scale r σ q).program oracle input Env.empty tape).trace).gaussianBlocks:ℕ):ℝ)
        ≤ ((2*RecursiveExecutable.fullBranching P.NP (n P hR) (ns P hR) P.m
          (CubicExecutableWorkShift.seedCount P hR)^Precision.precisionRank P.t q:ℕ):ℝ) :=
      by exact_mod_cast hworkR
    exact hcast.trans hpow
  exact ⟨hfinal, hfinal.trans (tier_work P hc hsmall hC hy hgeom hwork).2⟩

end AcceleratedLogConcave.Numerics.SourceWorkResolution
