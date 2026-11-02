import AcceleratedLogConcave.Oracle.MeanOriginalBounds
import AcceleratedLogConcave.Oracle.MeanMainErrorTransport
import AcceleratedLogConcave.Oracle.SourceMeanRetainedBodyRms

/-! Finite RMS propagation for the executed mean body. The benchmark width
is the actual main-child width, separately from the parent output scale.
The interpreter, complete body tape, paid final children and original Pi
corrections remain literal. Lower-child quantitative inputs are differences. -/
noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
namespace AcceleratedLogConcave.Oracle.MeanCompletedRms
section Main
open MeasureTheory Numerics SourceMeanExecutionRms
open Numerics.AffineGraph AffineLowering TapeLowering NoisyLayer
open RetainedMeanFinalBatch SourceMeanExecutable CovarianceSetup FixedTapeStability
open scoped BigOperators NNReal

variable {m n a h d : ℕ}
variable (M : MeanGeometry m) (nodes : Fin n ≃ M.MeanNode)
    (anchors : Fin a ≃ M.Anchor) (r σ Ds δ t w : ℝ)
    (main : Fin n → ExecutableData) (final : Fin m → ExecutableData) (sampling : ExecutableData)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (N : ℕ) (G : Point d → Point d) (x P : Ω → Point d)
    (env : Ω → Env d (Ready n m h))
    (tape : Ω → Tape d (body (a := a) (h := h) M nodes main final sampling N))
    (xStar U nu0 : Fin n → Ω → Point d)
    (Gref : ℕ → Fin n → Ω → Point d)
local notation "A" => (fun i j => M.matrix r σ (nodes i) (nodes j))
local notation "rho" => RecursiveMeanPublicTable.centerNoise r M.R Ds
local notation "Cmat" => residualRoot A rho (rowBound (m := m) r σ δ t w)
local notation "b" => (fun i ω => storedPoint (env ω) (MeanExecutablePrefix.direct i))
local notation "init" => (fun i ω => initial M nodes r Ds main final sampling N (env ω) (tape ω) i)
local notation "eval" => evaluator M nodes r Ds main final sampling N G tape U
local notation "Z" => noise M nodes main final sampling N tape
local notation "Pmain" => SourceMeanRetainedRms.finiteReference N Gref
local notation "X" => SharedLayerRms.iterate b A Cmat eval Z init
local notation "childWidth" => CovarianceSetup.sigma n rho (rowBound (m := m) r σ δ t w)
local notation "Y" => SharedLayerRms.benchmark xStar A Cmat childWidth Pmain Z nu0
local notation "err" => (fun k i ω => X k i ω - Y k i ω)
local notation "H" => SharedLayerRms.childError eval Y U childWidth Pmain
local notation "res" => SharedLayerRms.residual b A U xStar
local notation "actual" => (fun i ω =>
  let st := state M nodes anchors r σ Ds δ t w main final sampling
    N G (x ω) (P ω) (env ω) (tape ω)
  storedPoint st.env (st.old i) - Y N i ω)

/-- Stored interpreter nodes obey the numerical recurrence bound. Neither the
benchmark child RMS estimates nor the benchmark residual estimate is proved here.
No probability, Gaussian law, independence, or absolute moment is required. -/
theorem retained_main_error_bound (κ : ℝ≥0) (aRow Rres : ℝ)
    (ha : 0 ≤ aRow) (hR : 0 ≤ Rres) (ε : ℕ → Fin n → ℝ)
    (hrow : ∀ i, ∑ j, |A i j| ≤ aRow)
    (hstable : ∀ i, ChildStable (main i).program (main i).coefficient G κ)
    (hmeas : ∀ k, k < N → ∀ i, AEStronglyMeasurable
      (fun ω => eval k i ω (X k i ω) - eval k i ω (Y k i ω)) μ)
    (hinit : ∀ i, MemLp (fun ω => init i ω - (xStar i ω + nu0 i ω)) 2 μ)
    (hres : ∀ i, MemLp (res i) 2 μ)
    (hresBound : ∀ i, ‖(hres i).toLp (res i)‖ ≤ Rres)
    (hchild : ∀ k, k < N → ∀ i, MemLp (H k i) 2 μ)
    (hchildBound : ∀ k (hk : k < N) i, ‖(hchild k hk i).toLp (H k i)‖ ≤ ε k i) :
    ∃ hactual : ∀ i, MemLp (actual i) 2 μ,
      Collocation.rawNodeErrorNorm μ actual hactual ≤
        ((κ : ℝ)*aRow)^N * Collocation.rawNodeErrorNorm μ
          (fun i ω => init i ω - (xStar i ω + nu0 i ω)) hinit +
        Collocation.forcingSum ((κ : ℝ)*aRow)
          (fun k => Rres + SharedLayerRms.childRowBudget A (finiteBudget N ε) k) N := by
  have hn (k : ℕ) (hk : ¬ k < N) (ω : Ω) :
      MeanExecutionSchedule.inputAt (fun i => (main i).size) (fun i => (main i).program)
        (finish (a := a) (h := h) M nodes main final sampling) N
        (raw M nodes main final sampling N (tape ω)) k = none :=
    MeanExecutionSchedule.inputAt_none _ _ _ N _ k (Nat.le_of_not_gt hk)
  have hm : ∀ k i, AEStronglyMeasurable
      (fun ω => eval k i ω (X k i ω) - eval k i ω (Y k i ω)) μ := by
    intro k i
    by_cases hk : k < N
    · exact hmeas k hk i
    · simpa only [evaluator,MeanExecutionSchedule.evaluator,hn k hk,sub_self] using
        (aestronglyMeasurable_const : AEStronglyMeasurable (fun _ : Ω => (0 : Point d)) μ)
  have hzero (k : ℕ) (hk : ¬ k < N) (i : Fin n) : H k i = (fun _ => 0) := by
    funext ω
    simp only [SharedLayerRms.childError,evaluator,MeanExecutionSchedule.evaluator,
      hn k hk,SourceMeanRetainedRms.finiteReference,ite_eq_right hk,sub_self,smul_zero]
  have hc : ∀ k i, MemLp (H k i) 2 μ := by
    intro k i
    by_cases hk : k < N
    · exact hchild k hk i
    · rw [hzero k hk i]
      exact MemLp.zero
  have hcb : ∀ k i, ‖(hc k i).toLp (H k i)‖ ≤ finiteBudget N ε k i := by
    intro k i
    by_cases hk : k < N
    · simpa [finiteBudget, hk] using hchildBound k hk i
    · simp [finiteBudget, hk, hzero k hk i]
  obtain ⟨herr,hbound⟩ := SharedLayerRms.iterate_error_bound b xStar U init nu0 A Cmat eval
    Pmain Z childWidth μ κ aRow Rres ha hR (finiteBudget N ε) hrow
    (MeanExecutionSchedule.evaluator_lipschitz _ _ _ _ _ _ _ N _ U κ hstable) hm hinit
    hres hresBound hc hcb
  have he : actual = err N := by
    have hs := state_old_eq_iterate M nodes anchors r σ Ds δ t w main final sampling N G x P env tape U
    funext i ω
    exact congrArg (fun z => z - Y N i ω) (congrFun (congrFun hs i) ω)
  have hactual : ∀ i, MemLp (actual i) 2 μ := by rw [he]; exact herr N
  have heLp : (fun i => (hactual i).toLp (actual i)) =
      (fun i => (herr N i).toLp (err N i)) := by
    funext i
    apply Lp.ext
    filter_upwards [(hactual i).coeFn_toLp,(herr N i).coeFn_toLp] with ω ha hb
    rw [ha,hb]
    exact congrFun (congrFun he i) ω
  refine ⟨hactual,?_⟩
  change ‖fun i => (hactual i).toLp (actual i)‖ ≤ _
  rw [heLp]
  exact hbound N


end Main
section Body
open MeasureTheory Numerics SourceMeanExecutionRms
open Numerics.AffineGraph AffineLowering TapeLowering NoisyLayer
open RetainedMeanFinalBatch SourceMeanExecutable CovarianceSetup FixedTapeStability
open scoped BigOperators NNReal

variable {m n a h d : ℕ}
variable (M : MeanGeometry m) (nodes : Fin n ≃ M.MeanNode)
    (anchors : Fin a ≃ M.Anchor) (r σ Ds δ t w : ℝ)
    (main : Fin n → ExecutableData) (final : Fin m → ExecutableData) (sampling : ExecutableData)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (N : ℕ) (G : Point d → Point d) (x P : Ω → Point d)
    (env : Ω → Env d (Ready n m h))
    (tape : Ω → Tape d (body (a := a) (h := h) M nodes main final sampling N))
    (xStar U nu0 : Fin n → Ω → Point d)
    (Gref : ℕ → Fin n → Ω → Point d) (Pref : Fin m → Ω → Point d)
local notation "A" => (fun i j => M.matrix r σ (nodes i) (nodes j))
local notation "rho" => RecursiveMeanPublicTable.centerNoise r M.R Ds
local notation "Cmat" => residualRoot A rho (rowBound (m := m) r σ δ t w)
local notation "b" => (fun i ω => storedPoint (env ω) (MeanExecutablePrefix.direct i))
local notation "init" => (fun i ω => initial M nodes r Ds main final sampling N (env ω) (tape ω) i)
local notation "eval" => evaluator M nodes r Ds main final sampling N G tape U
local notation "Z" => noise M nodes main final sampling N tape
local notation "Pmain" => SourceMeanRetainedRms.finiteReference N Gref
local notation "X" => SharedLayerRms.iterate b A Cmat eval Z init
local notation "childWidth" => CovarianceSetup.sigma n rho (rowBound (m := m) r σ δ t w)
local notation "Y" => SharedLayerRms.benchmark xStar A Cmat childWidth Pmain Z nu0
local notation "H" => SharedLayerRms.childError eval Y U childWidth Pmain
local notation "res" => SharedLayerRms.residual b A U xStar
local notation "XE" => (fun i ω =>
  let st := state M nodes anchors r σ Ds δ t w main final sampling
    N G (x ω) (P ω) (env ω) (tape ω)
  storedPoint st.env (st.old i))
local notation "FE" => (fun i ω => finalEvaluator M nodes anchors r σ Ds δ t w main final sampling
  N G (x ω) (P ω) (env ω) (tape ω) i)
local notation "active" => (fun i => nodes.symm (.center M i))
local notation "Pi" => (fun i ω => storedPoint (env ω) (MeanExecutablePrefix.designated i))
local notation "P0" => (fun ω => storedPoint (env ω) (MeanExecutablePrefix.saved .here))
local notation "wf" => Numerics.GaussLegendre.weight m
local notation "width" => RecursiveMeanPublicTable.finalWidth M.R σ
local notation "out" => (fun ω => RetainedMeanFinalBatch.childPoint (run
  (body (a := a) (h := h) M nodes main final sampling N) G
  ⟨table M nodes anchors r σ Ds δ t w main final sampling,x ω,P ω⟩ (env ω) (tape ω)))

/-- End-to-end finite bound for the real body. Benchmark data live on the same
arbitrary measure space as the entire execution tape; no marginal/law premises
are silently added. Each final child remains a paid actual source execution. -/
theorem retained_body_error_bound (κ κf : ℝ≥0) (aRow Rres : ℝ)
    (ha : 0 ≤ aRow) (hR : 0 ≤ Rres) (ε : ℕ → Fin n → ℝ)
    (hrow : ∀ i, ∑ j, |A i j| ≤ aRow)
    (hstable : ∀ i, ChildStable (main i).program (main i).coefficient G κ)
    (hmeas : ∀ k, k < N → ∀ i, AEStronglyMeasurable
      (fun ω => eval k i ω (X k i ω) - eval k i ω (Y k i ω)) μ)
    (hinit : ∀ i, MemLp (fun ω => init i ω - (xStar i ω + nu0 i ω)) 2 μ)
    (hres : ∀ i, MemLp (res i) 2 μ)
    (hresBound : ∀ i, ‖(hres i).toLp (res i)‖ ≤ Rres)
    (hchild : ∀ k, k < N → ∀ i, MemLp (H k i) 2 μ)
    (hchildBound : ∀ k (hk : k < N) i, ‖(hchild k hk i).toLp (H k i)‖ ≤ ε k i)
    (UF : Fin m → Ω → Point d) (εf : Fin m → ℝ)
    (hfinalStable : ∀ i, ChildStable (final i).program (final i).coefficient G κf)
    (hfinalMeas : ∀ i, AEStronglyMeasurable
      (fun ω => FE i ω (XE (active i) ω) - FE i ω (Y N (active i) ω)) μ)
    (hfinalChild : ∀ i, MemLp
      (fun ω => FE i ω (Y N (active i) ω) - width • Pref i ω - UF i ω) 2 μ)
    (hfinalBound : ∀ i, ‖(hfinalChild i).toLp
      (fun ω => FE i ω (Y N (active i) ω) - width • Pref i ω - UF i ω)‖ ≤ εf i) :
    let D := ((κ : ℝ)*aRow)^N * Collocation.rawNodeErrorNorm μ
      (fun i ω => init i ω - (xStar i ω + nu0 i ω)) hinit +
      Collocation.forcingSum ((κ : ℝ)*aRow)
        (fun k => Rres + SharedLayerRms.childRowBudget A (finiteBudget N ε) k) N
    let outputError := fun ω => out ω - (σ • P0 ω + ∑ i, wf i • (UF i ω + width • (Pref i ω - Pi i ω)))
    ∃ hout : MemLp outputError 2 μ,
      ‖hout.toLp outputError‖ ≤ (∑ i, |wf i|) * ((κf : ℝ)*D) + ∑ i, |wf i| *εf i := by
  dsimp only
  let D := ((κ : ℝ)*aRow)^N * Collocation.rawNodeErrorNorm μ
    (fun i ω => init i ω - (xStar i ω + nu0 i ω)) hinit +
    Collocation.forcingSum ((κ : ℝ)*aRow)
      (fun k => Rres + SharedLayerRms.childRowBudget A (finiteBudget N ε) k) N
  obtain ⟨herr,hB⟩ := retained_main_error_bound M nodes anchors r σ Ds δ t w main final sampling μ
    N G x P env tape xStar U nu0 Gref κ aRow Rres ha hR ε hrow hstable hmeas hinit
    hres hresBound hchild hchildBound
  have hD (j : Fin n) : ‖(herr j).toLp (fun ω => XE j ω - Y N j ω)‖ ≤ D :=
    (norm_le_pi_norm (fun i => (herr i).toLp (fun ω => XE i ω - Y N i ω)) j).trans hB
  have hf (i : Fin m) (ω : Ω) : LipschitzWith κf (FE i ω) := by
    apply LipschitzWith.of_dist_le_mul
    intro u v
    simp only [dist_eq_norm]
    exact childStable_tape (final i).program (final i).coefficient G κf (hfinalStable i)
      (Pi i ω) u v (finalTape M nodes anchors r σ Ds δ t w main final sampling
        N G (x ω) (P ω) (env ω) (tape ω) i)
  let UFpaid := fun i ω => UF i ω + width • (Pref i ω - Pi i ω)
  have hechild (i : Fin m) :
      (fun ω => FE i ω (Y N (active i) ω) - width • Pi i ω - UFpaid i ω) =
      (fun ω => FE i ω (Y N (active i) ω) - width • Pref i ω - UF i ω) := by
    funext ω
    dsimp only [UFpaid]
    rw [smul_sub]
    abel
  have hpaidChild (i : Fin m) : MemLp
      (fun ω => FE i ω (Y N (active i) ω) - width • Pi i ω - UFpaid i ω) 2 μ := by
    rw [hechild]
    exact hfinalChild i
  have hpaidBudget (i : Fin m) : ‖(hpaidChild i).toLp
      (fun ω => FE i ω (Y N (active i) ω) - width • Pi i ω - UFpaid i ω)‖ ≤ εf i := by
    simpa only [hechild] using hfinalBound i
  obtain ⟨hpaid,hpaidBound⟩ := MeanPaidFinalRms.paid_error_bound μ σ wf (fun _ => width)
    P0 Pi UFpaid XE (Y N) active FE κf D εf hf herr hD hfinalMeas hpaidChild hpaidBudget
  have he : (fun ω => out ω - (σ • P0 ω + ∑ i, wf i • (UF i ω + width • (Pref i ω - Pi i ω)))) =
      (fun ω => (σ • P0 ω + ∑ i, wf i • (FE i ω (XE (active i) ω) - width • Pi i ω)) -
        (σ • P0 ω + ∑ i, wf i • (UF i ω + width • (Pref i ω - Pi i ω)))) := by
    funext ω
    exact congrArg (fun z => z - (σ • P0 ω + ∑ i, wf i • (UF i ω + width • (Pref i ω - Pi i ω))))
      (body_paid_final M nodes anchors r σ Ds δ t w main final sampling
        N G (x ω) (P ω) (env ω) (tape ω))
  rw [he]
  exact ⟨hpaid,hpaidBound⟩


end Body

section OriginalSource
open MeasureTheory Numerics Numerics.MeanFlowLp Numerics.MeanResidualBridge Numerics.MeanCollocationLp
open Numerics.AffineGraph AffineLowering TapeLowering NoisyLayer SourceMeanExecutable
open scoped BigOperators NNReal
open FixedTapeStability
variable {D m n a h : ℕ} (d : MeanFlowLp.Data (Fin D) m)
  (nodes : Fin n ≃ d.G.MeanNode) (anchors : Fin a ≃ d.G.Anchor)
  (seeds : Fin h ≃ Fin m × d.G.Kernel) (Ds δ t w : ℝ)
  (main : Fin n → ExecutableData) (final : Fin m → ExecutableData) (sampling : ExecutableData)
  {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
  (P U V : Ω → Point D) (raw : Ω → Fin (m+1) → Point D) (Z : Ω → Fin h → Point D)

/-- The reference seed uses the same literal assembly and flow draws; only
its private position is the returned lower reference, scaled by actual b*. -/
def sourceSeed (ω : Ω) : Seed d :=
  (WithLp.toLp 2 (backwardEnd d.G.R • V ω,
    SourceMeanShift.splitValues d.G nodes anchors d.r d.sigma Ds δ t w main final sampling (P ω) (raw ω) 0),
      fun j k => Z ω (seeds.symm (j,k)))

/-- Exact source cache, with the actual private return U. -/
def actualCache (ω : Ω) : Env D (SourceMeanExecutionRms.Ready n m h) :=
  SourceMeanShift.cache d.G nodes anchors seeds d.r d.sigma Ds δ t w main final sampling
    d.x (P ω) (U ω) (raw ω) (Z ω)

def anchorError (ω : Ω) : Point D := backwardEnd d.G.R • (U ω-V ω)

local notation "seed" => sourceSeed d nodes anchors seeds Ds δ t w main final sampling P V raw Z
local notation "env" => actualCache d nodes anchors seeds Ds δ t w main final sampling P U raw Z
local notation "anchor" => anchorError d U V

omit [MeasurableSpace Ω] in
/-- The direct-vector difference contains the actual private anchor error,
with its literal position coefficient, and no independent replacement tape. -/
theorem direct_displacement (i : Fin n) (ω : Ω) :
    storedPoint (env ω) (MeanExecutablePrefix.direct i)-
      (MeanCollocationLp.rawGraph d (seed ω)).direct (nodes i) =
        (d.r*d.G.positionCoeff (nodes i)) • anchor ω := by
  dsimp only [actualCache]
  rw [SourceMeanShift.cache_direct]
  change d.G.direct d.r d.sigma d.x (backwardEnd d.G.R • U ω) _ _ (nodes i)-
    d.G.direct d.r d.sigma d.x (backwardEnd d.G.R • V ω) _ _ (nodes i)=_
  simp only [sourceSeed,WithLp.toLp_snd]
  rw [SourceMeanStability.direct_sub,sub_self,zero_add]
  simp only [anchorError,smul_smul,mul_assoc]

/-- Original mean-flow regularity and its moment budget transfer along the
actual source-seed projection. No target accuracy is a transport input. -/
theorem initializer_on_source
    (hp : MeasurePreserving seed μ (seedMeasure d))
    (h₀ : ℝ) (hmesh : MeshConditions d h₀) (hhalf : contraction d h₀≤1/2) (i : Fin n) :
    ∃ hi : MemLp (fun ω => MeanOriginalBounds.initializerError d (nodes i) (seed ω)) 2 μ,
      ‖hi.toLp _‖≤ MeanOriginalBounds.initializerBudget d h₀ := by
  let h := MeanOriginalBounds.initializer_memLp d (nodes i)
  refine ⟨h.comp_measurePreserving hp,?_⟩
  change ‖(h.comp_measurePreserving hp).toLp (MeanOriginalBounds.initializerError d (nodes i) ∘ seed)‖≤_
  change ‖Lp.compMeasurePreserving seed hp (h.toLp _)‖≤_
  rw [Lp.norm_compMeasurePreserving]
  exact MeanOriginalBounds.initializer_norm_le d h₀ hmesh hhalf (nodes i)

 theorem residual_on_source
    (hp : MeasurePreserving seed μ (seedMeasure d))
    (h₀ : ℝ) (hmesh : MeshConditions d h₀) (i : Fin n) :
    ∃ hi : MemLp (fun ω => rawResidual d (nodes i) (seed ω)) 2 μ,
      ‖hi.toLp _‖≤MeanOriginalBounds.residualBudget d h₀ := by
  let h := MeanOriginalBounds.residual_memLp d (nodes i)
  refine ⟨h.comp_measurePreserving hp,?_⟩
  change ‖(h.comp_measurePreserving hp).toLp (rawResidual d (nodes i) ∘ seed)‖≤_
  change ‖Lp.compMeasurePreserving seed hp (h.toLp _)‖≤_
  rw [Lp.norm_compMeasurePreserving]
  exact MeanOriginalBounds.residual_norm_le d h₀ hmesh (nodes i)

 theorem quadrature_on_source
    (hp : MeasurePreserving seed μ (seedMeasure d)) (hm : 2≤m) :
    ∃ hi : MemLp (fun ω => MeanOriginalBounds.quadratureError d (seed ω)) 2 μ,
      ‖hi.toLp _‖≤MeanOriginalBounds.quadratureBudget d := by
  let h := MeanOriginalBounds.quadrature_memLp d
  refine ⟨h.comp_measurePreserving hp,?_⟩
  change ‖(h.comp_measurePreserving hp).toLp (MeanOriginalBounds.quadratureError d ∘ seed)‖≤_
  change ‖Lp.compMeasurePreserving seed hp (h.toLp _)‖≤_
  rw [Lp.norm_compMeasurePreserving]
  exact MeanOriginalBounds.quadrature_norm_le d hm

/-- Actual initialized-center error after cancellation of the same initial
draw; this is a difference only. -/
def directError (i : Fin n) (ω : Ω) : Point D :=
  storedPoint (env ω) (MeanExecutablePrefix.direct i)-rawReference d (nodes i) (seed ω)

 omit [MeasurableSpace Ω] in
theorem directError_eq (i : Fin n) (ω : Ω) :
    directError d nodes anchors seeds Ds δ t w main final sampling P U V raw Z i ω =
      (d.r*d.G.positionCoeff (nodes i)) • anchor ω+
        MeanOriginalBounds.initializerError d (nodes i) (seed ω) := by
  dsimp only [directError,MeanOriginalBounds.initializerError,rawIterate,FiniteGraph.iterate]
  simp only [Nat.rec_zero]
  rw [← direct_displacement d nodes anchors seeds Ds δ t w main final sampling P U V raw Z i ω]
  abel

 theorem direct_error_bound
    (hp : MeasurePreserving seed μ (seedMeasure d))
    (h₀ : ℝ) (hmesh : MeshConditions d h₀) (hhalf : contraction d h₀≤1/2)
    (hpsi : d.G.psi≤d.G.R^4) (Eprivate : ℝ)
    (hanchor : MemLp anchor 2 μ) (hanchorBound : ‖hanchor.toLp anchor‖≤Eprivate) (i : Fin n) :
    ∃ hi : MemLp (directError d nodes anchors seeds Ds δ t w main final sampling P U V raw Z i) 2 μ,
      ‖hi.toLp _‖≤d.r*backwardEnd d.G.R*Eprivate+MeanOriginalBounds.initializerBudget d h₀ := by
  obtain ⟨hi,hiB⟩ := initializer_on_source d nodes anchors seeds Ds δ t w main final sampling μ P V raw Z hp h₀ hmesh hhalf i
  let hd := hanchor.const_smul (d.r*d.G.positionCoeff (nodes i))
  have he : directError d nodes anchors seeds Ds δ t w main final sampling P U V raw Z i =
      (fun ω => (d.r*d.G.positionCoeff (nodes i)) • anchor ω+
        MeanOriginalBounds.initializerError d (nodes i) (seed ω)) :=
    funext (directError_eq d nodes anchors seeds Ds δ t w main final sampling P U V raw Z i)
  rw [he]
  refine ⟨hd.add hi,?_⟩
  have hc := d.G.positionCoeff_mem hpsi (nodes i)
  have hco : 0≤d.r*d.G.positionCoeff (nodes i) := mul_nonneg d.hr.le hc.1
  have hcoB : d.r*d.G.positionCoeff (nodes i)≤d.r*backwardEnd d.G.R :=
    mul_le_mul_of_nonneg_left hc.2 d.hr.le
  have hEB : 0≤Eprivate := (norm_nonneg _).trans hanchorBound
  have hdB : ‖hd.toLp (fun ω => (d.r*d.G.positionCoeff (nodes i)) • anchor ω)‖≤d.r*backwardEnd d.G.R*Eprivate := by
    change ‖(d.r*d.G.positionCoeff (nodes i)) • hanchor.toLp anchor‖≤_
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hco]
    exact (mul_le_mul_of_nonneg_left hanchorBound hco).trans (mul_le_mul_of_nonneg_right hcoB hEB)
  change ‖(hd.add hi).toLp ((fun ω => (d.r*d.G.positionCoeff (nodes i)) • anchor ω)+
    (fun ω => MeanOriginalBounds.initializerError d (nodes i) (seed ω)))‖≤_
  change ‖hd.toLp _+hi.toLp _‖≤_
  exact (norm_add_le _ _).trans (add_le_add hdB hiB)

omit [MeasurableSpace Ω] in
/-- The actual noisy initialization uses this same initial body occurrence;
the benchmark carries precisely the same occurrence. -/
theorem initial_error_eq (N : ℕ)
    (tape : Ω → Tape D (SourceMeanExecutable.body (a := a) (h := h) d.G nodes main final sampling N))
    (i : Fin n) (ω : Ω) :
    SourceMeanExecutionRms.initial d.G nodes d.r Ds main final sampling N (env ω) (tape ω) i-
      (rawReference d (nodes i) (seed ω)+RecursiveMeanPublicTable.centerNoise d.r d.G.R Ds •
        (show Point D from ((tape ω).1 i).1)) =
      directError d nodes anchors seeds Ds δ t w main final sampling P U V raw Z i ω := by
  dsimp only [SourceMeanExecutionRms.initial,directError]
  abel

/-- The actual affine residual has the original source row defect plus only
the genuine private direct displacement. -/
def sourceResidual (i : Fin n) (ω : Ω) : Point D :=
  SharedLayerRms.residual
    (fun i ω => storedPoint (env ω) (MeanExecutablePrefix.direct i))
    (fun i j => d.G.matrix d.r d.sigma (nodes i) (nodes j))
    (fun i ω => Gibbs.primitiveMean d.F (rawReference d (nodes i) (seed ω)) (d.G.radius d.r (nodes i)))
    (fun i ω => rawReference d (nodes i) (seed ω)) i ω

 omit [MeasurableSpace Ω] in
theorem sourceResidual_eq (i : Fin n) (ω : Ω) :
    sourceResidual d nodes anchors seeds Ds δ t w main final sampling P U V raw Z i ω =
      (d.r*d.G.positionCoeff (nodes i)) • anchor ω+rawResidual d (nodes i) (seed ω) := by
  dsimp only [sourceResidual,SharedLayerRms.residual,rawResidual,FiniteGraph.step,
    FiniteGraph.updateFromReplies,FiniteGraph.collect,FiniteGraph.requests,MeanGeometry.graph]
  rw [← direct_displacement d nodes anchors seeds Ds δ t w main final sampling P U V raw Z i ω]
  rw [← Equiv.sum_comp nodes]
  dsimp only [MeanCollocationLp.rawGraph,MeanGeometry.graph]
  abel

 theorem source_residual_bound
    (hp : MeasurePreserving seed μ (seedMeasure d))
    (h₀ : ℝ) (hmesh : MeshConditions d h₀) (hpsi : d.G.psi≤d.G.R^4) (Eprivate : ℝ)
    (hanchor : MemLp anchor 2 μ) (hanchorBound : ‖hanchor.toLp anchor‖≤Eprivate) (i : Fin n) :
    ∃ hi : MemLp (sourceResidual d nodes anchors seeds Ds δ t w main final sampling P U V raw Z i) 2 μ,
      ‖hi.toLp _‖≤d.r*backwardEnd d.G.R*Eprivate+MeanOriginalBounds.residualBudget d h₀ := by
  obtain ⟨hi,hiB⟩ := residual_on_source d nodes anchors seeds Ds δ t w main final sampling μ P V raw Z hp h₀ hmesh i
  let hd := hanchor.const_smul (d.r*d.G.positionCoeff (nodes i))
  have he : sourceResidual d nodes anchors seeds Ds δ t w main final sampling P U V raw Z i =
      (fun ω => (d.r*d.G.positionCoeff (nodes i)) • anchor ω+rawResidual d (nodes i) (seed ω)) :=
    funext (sourceResidual_eq d nodes anchors seeds Ds δ t w main final sampling P U V raw Z i)
  rw [he]
  refine ⟨hd.add hi,?_⟩
  have hc := d.G.positionCoeff_mem hpsi (nodes i)
  have hco : 0≤d.r*d.G.positionCoeff (nodes i) := mul_nonneg d.hr.le hc.1
  have hcoB : d.r*d.G.positionCoeff (nodes i)≤d.r*backwardEnd d.G.R :=
    mul_le_mul_of_nonneg_left hc.2 d.hr.le
  have hEB : 0≤Eprivate := (norm_nonneg _).trans hanchorBound
  have hdB : ‖hd.toLp (fun ω => (d.r*d.G.positionCoeff (nodes i)) • anchor ω)‖≤d.r*backwardEnd d.G.R*Eprivate := by
    change ‖(d.r*d.G.positionCoeff (nodes i)) • hanchor.toLp anchor‖≤_
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hco]
    exact (mul_le_mul_of_nonneg_left hanchorBound hco).trans (mul_le_mul_of_nonneg_right hcoB hEB)
  change ‖(hd.add hi).toLp ((fun ω => (d.r*d.G.positionCoeff (nodes i)) • anchor ω)+
    (fun ω => rawResidual d (nodes i) (seed ω)))‖≤_
  change ‖hd.toLp _+hi.toLp _‖≤_
  exact (norm_add_le _ _).trans (add_le_add hdB hiB)

/-- The source scalar recurrence, with both original-data and genuinely
lower private-anchor payments exposed in physical units. -/
def sourceMainBudget (h₀ : ℝ) (N : ℕ) (κ : ℝ≥0) (aRow Eprivate : ℝ)
    (ε : ℕ → Fin n → ℝ) : ℝ :=
  ((κ:ℝ)*aRow)^N*(d.r*backwardEnd d.G.R*Eprivate+MeanOriginalBounds.initializerBudget d h₀)+
    Collocation.forcingSum ((κ:ℝ)*aRow)
      (fun k => d.r*backwardEnd d.G.R*Eprivate+MeanOriginalBounds.residualBudget d h₀+
        SharedLayerRms.childRowBudget (fun i j => d.G.matrix d.r d.sigma (nodes i) (nodes j))
          (SourceMeanExecutionRms.finiteBudget N ε) k) N

variable (N : ℕ) (G : Point D → Point D)
  (tape : Ω → Tape D (SourceMeanExecutable.body (a := a) (h := h) d.G nodes main final sampling N))
  (Gref : ℕ → Fin n → Ω → Point D)
local notation "Amat" => (fun i j => d.G.matrix d.r d.sigma (nodes i) (nodes j))
local notation "rho" => RecursiveMeanPublicTable.centerNoise d.r d.G.R Ds
local notation "Cmat" => CovarianceSetup.residualRoot Amat rho (SourceMeanExecutable.rowBound (m := m) d.r d.sigma δ t w)
local notation "childWidth" => CovarianceSetup.sigma n rho (SourceMeanExecutable.rowBound (m := m) d.r d.sigma δ t w)
local notation "Phi" => (fun i ω => rawReference d (nodes i) (seed ω))
local notation "reply" => (fun i ω => Gibbs.primitiveMean d.F (Phi i ω) (d.G.radius d.r (nodes i)))
local notation "nu0" => (fun i ω => rho • (show Point D from ((tape ω).1 i).1))
local notation "direct" => (fun i ω => storedPoint (env ω) (MeanExecutablePrefix.direct i))
local notation "initial" => (fun i ω => SourceMeanExecutionRms.initial d.G nodes d.r Ds main final sampling N (env ω) (tape ω) i)
local notation "eval" => SourceMeanExecutionRms.evaluator d.G nodes d.r Ds main final sampling N G tape reply
local notation "noise" => SourceMeanExecutionRms.noise d.G nodes main final sampling N tape
local notation "Pmain" => SourceMeanRetainedRms.finiteReference N Gref
local notation "X" => SharedLayerRms.iterate direct Amat Cmat eval noise initial
local notation "Y" => SharedLayerRms.benchmark Phi Amat Cmat childWidth Pmain noise nu0
local notation "childErr" => SharedLayerRms.childError eval Y reply childWidth Pmain
local notation "actualNodes" => (fun i ω =>
  let st := SourceMeanExecutionRms.state d.G nodes anchors d.r d.sigma Ds δ t w main final sampling N G d.x (P ω) (env ω) (tape ω)
  storedPoint st.env (st.old i)-Y N i ω)

/-- The finite executed main body with original-data initializer/residual
suppliers. Its only quantitative difference inputs are genuinely lower
private and main-child errors, on the same source space. -/
theorem source_main_error_bound
    (hp : MeasurePreserving seed μ (seedMeasure d))
    (h₀ : ℝ) (hmesh : MeshConditions d h₀) (hhalf : contraction d h₀≤1/2)
    (hpsi : d.G.psi≤d.G.R^4) (κ : ℝ≥0) (aRow : ℝ) (ha : 0≤aRow)
    (Eprivate : ℝ) (hanchor : MemLp anchor 2 μ) (hanchorBound : ‖hanchor.toLp anchor‖≤Eprivate)
    (ε : ℕ → Fin n → ℝ) (hrow : ∀ i,∑ j,|Amat i j|≤aRow)
    (hstable : ∀ i,ChildStable (main i).program (main i).coefficient G κ)
    (hmeas : ∀ k,k<N → ∀ i,AEStronglyMeasurable (fun ω => eval k i ω (X k i ω)-eval k i ω (Y k i ω)) μ)
    (hchild : ∀ k,k<N → ∀ i,MemLp (childErr k i) 2 μ)
    (hchildBound : ∀ k (hk : k<N) i,‖(hchild k hk i).toLp _‖≤ε k i) :
    ∃ herr : ∀ i,MemLp (actualNodes i) 2 μ,
      Collocation.rawNodeErrorNorm μ actualNodes herr≤sourceMainBudget d nodes h₀ N κ aRow Eprivate ε := by
  have he (i : Fin n) : (fun ω => initial i ω-(Phi i ω+nu0 i ω)) =
      directError d nodes anchors seeds Ds δ t w main final sampling P U V raw Z i := by
    funext ω
    exact initial_error_eq d nodes anchors seeds Ds δ t w main final sampling P U V raw Z N tape i ω
  have hIB (i : Fin n) := direct_error_bound d nodes anchors seeds Ds δ t w main final sampling μ P U V raw Z hp h₀ hmesh hhalf hpsi Eprivate hanchor hanchorBound i
  let hi : ∀ i,MemLp (fun ω => initial i ω-(Phi i ω+nu0 i ω)) 2 μ := fun i =>
    (he i).symm ▸ (hIB i).choose
  have hIB' (i : Fin n) : ‖(hi i).toLp _‖≤d.r*backwardEnd d.G.R*Eprivate+MeanOriginalBounds.initializerBudget d h₀ := by
    simpa only [he i] using (hIB i).choose_spec
  have hRB (i : Fin n) := source_residual_bound d nodes anchors seeds Ds δ t w main final sampling μ P U V raw Z hp h₀ hmesh hpsi Eprivate hanchor hanchorBound i
  let hr : ∀ i,MemLp (SharedLayerRms.residual direct Amat reply Phi i) 2 μ := fun i => (hRB i).choose
  have hRB' (i : Fin n) : ‖(hr i).toLp _‖≤d.r*backwardEnd d.G.R*Eprivate+MeanOriginalBounds.residualBudget d h₀ := (hRB i).choose_spec
  have hE0 : 0≤Eprivate := (norm_nonneg _).trans hanchorBound
  have hR0 : 0≤d.r*backwardEnd d.G.R*Eprivate+MeanOriginalBounds.residualBudget d h₀ :=
    add_nonneg (mul_nonneg (mul_nonneg d.hr.le d.G.backwardEnd_pos.le) hE0) (MeanOriginalBounds.residualBudget_nonneg d h₀)
  obtain ⟨herr,hB⟩ := retained_main_error_bound d.G nodes anchors d.r d.sigma Ds δ t w main final sampling μ N G
    (fun _ => d.x) P env tape Phi reply nu0 Gref κ aRow _ ha hR0 ε hrow hstable hmeas hi hr hRB' hchild hchildBound
  refine ⟨herr,hB.trans ?_⟩
  unfold sourceMainBudget
  apply add_le_add _ le_rfl
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg (mul_nonneg κ.coe_nonneg ha) N)
  exact (pi_norm_le_iff_of_nonneg (add_nonneg (mul_nonneg (mul_nonneg d.hr.le d.G.backwardEnd_pos.le) hE0)
    (MeanOriginalBounds.initializerBudget_nonneg d h₀ hmesh hhalf))).2 hIB'

variable (Pref : Fin m → Ω → Point D)
local notation "XE" => (fun i ω =>
  let st := SourceMeanExecutionRms.state d.G nodes anchors d.r d.sigma Ds δ t w main final sampling N G d.x (P ω) (env ω) (tape ω)
  storedPoint st.env (st.old i))
local notation "FE" => (fun i ω => SourceMeanExecutionRms.finalEvaluator d.G nodes anchors d.r d.sigma Ds δ t w main final sampling N G d.x (P ω) (env ω) (tape ω) i)
local notation "active" => (fun i => nodes.symm (.center d.G i))
local notation "Pi" => (fun i ω => storedPoint (env ω) (MeanExecutablePrefix.designated i))
local notation "wf" => Numerics.GaussLegendre.weight m
local notation "width" => RecursiveMeanPublicTable.finalWidth d.G.R d.sigma
local notation "UF" => (fun i ω => reply (active i) ω)
local notation "out" => (fun ω => RetainedMeanFinalBatch.childPoint (run
  (SourceMeanExecutable.body (a := a) (h := h) d.G nodes main final sampling N) G
    ⟨SourceMeanExecutable.table d.G nodes anchors d.r d.sigma Ds δ t w main final sampling,d.x,P ω⟩ (env ω) (tape ω)))
local notation "paidTarget" => (fun ω => d.sigma • P ω+∑ i,wf i • (UF i ω+width • (Pref i ω-Pi i ω)))

/-- The same final correction is added to the original analytic endpoint.
It retains original P and all original designated Pi values literally. -/
def referenceReadout (ω : Ω) : Point D :=
  rawTerminalTarget d (seed ω)+
    (d.sigma • P ω-(d.sigma/2) • (seed ω).1.snd+
      ∑ i,wf i • (width • (Pref i ω-Pi i ω)))

omit [MeasurableSpace Ω] in
/-- The numerical target and analytic reference differ by exactly the full
original center quadrature defect; no Gaussian or accuracy premise is used. -/
theorem paid_target_sub_reference (ω : Ω) :
    paidTarget ω-referenceReadout d nodes anchors seeds Ds δ t w main final sampling P U V raw Z Pref ω =
      MeanOriginalBounds.quadratureError d (seed ω) := by
  dsimp only [referenceReadout,MeanOriginalBounds.quadratureError,MeanOriginalBounds.referenceOutput,
    MeanGeometry.meanOutput,FiniteGraph.collect,FiniteGraph.requests,MeanCollocationLp.rawGraph,MeanGeometry.graph]
  simp only [Equiv.apply_symm_apply,smul_add,Finset.sum_add_distrib]
  abel

/-- Full paid final-body error, with original initializer and row defects
already supplied rather than assumed. -/
theorem source_body_error_bound
    (hp : MeasurePreserving seed μ (seedMeasure d))
    (h₀ : ℝ) (hmesh : MeshConditions d h₀) (hhalf : contraction d h₀≤1/2)
    (hpsi : d.G.psi≤d.G.R^4) (κ κf : ℝ≥0) (aRow : ℝ) (ha : 0≤aRow)
    (Eprivate : ℝ) (hanchor : MemLp anchor 2 μ) (hanchorBound : ‖hanchor.toLp anchor‖≤Eprivate)
    (ε : ℕ → Fin n → ℝ) (hrow : ∀ i,∑ j,|Amat i j|≤aRow)
    (hstable : ∀ i,ChildStable (main i).program (main i).coefficient G κ)
    (hmeas : ∀ k,k<N → ∀ i,AEStronglyMeasurable (fun ω => eval k i ω (X k i ω)-eval k i ω (Y k i ω)) μ)
    (hchild : ∀ k,k<N → ∀ i,MemLp (childErr k i) 2 μ)
    (hchildBound : ∀ k (hk : k<N) i,‖(hchild k hk i).toLp _‖≤ε k i)
    (εf : Fin m → ℝ)
    (hfinalStable : ∀ i,ChildStable (final i).program (final i).coefficient G κf)
    (hfinalMeas : ∀ i,AEStronglyMeasurable (fun ω => FE i ω (XE (active i) ω)-FE i ω (Y N (active i) ω)) μ)
    (hfinalChild : ∀ i,MemLp (fun ω => FE i ω (Y N (active i) ω)-width • Pref i ω-UF i ω) 2 μ)
    (hfinalBound : ∀ i,‖(hfinalChild i).toLp _‖≤εf i) :
    ∃ hout : MemLp (fun ω => out ω-paidTarget ω) 2 μ,
      ‖hout.toLp _‖≤(∑ i,|wf i|)*((κf:ℝ)*sourceMainBudget d nodes h₀ N κ aRow Eprivate ε)+∑ i,|wf i| *εf i := by
  obtain ⟨herr,hB⟩ := source_main_error_bound d nodes anchors seeds Ds δ t w main final sampling μ P U V raw Z N G tape Gref
    hp h₀ hmesh hhalf hpsi κ aRow ha Eprivate hanchor hanchorBound ε hrow hstable hmeas hchild hchildBound
  have hD (j : Fin n) : ‖(herr j).toLp (fun ω => XE j ω-Y N j ω)‖≤sourceMainBudget d nodes h₀ N κ aRow Eprivate ε :=
    (norm_le_pi_norm (fun i => (herr i).toLp (fun ω => XE i ω-Y N i ω)) j).trans hB
  have hf (i : Fin m) (ω : Ω) : LipschitzWith κf (FE i ω) := by
    apply LipschitzWith.of_dist_le_mul
    intro u v
    simp only [dist_eq_norm]
    exact childStable_tape (final i).program (final i).coefficient G κf (hfinalStable i)
      (Pi i ω) u v (SourceMeanExecutionRms.finalTape d.G nodes anchors d.r d.sigma Ds δ t w main final sampling N G d.x (P ω) (env ω) (tape ω) i)
  let UFpaid := fun i ω => UF i ω+width • (Pref i ω-Pi i ω)
  have hechild (i : Fin m) : (fun ω => FE i ω (Y N (active i) ω)-width • Pi i ω-UFpaid i ω)=
      (fun ω => FE i ω (Y N (active i) ω)-width • Pref i ω-UF i ω) := by
    funext ω
    dsimp only [UFpaid]
    rw [smul_sub]
    abel
  have hpaidChild (i : Fin m) : MemLp (fun ω => FE i ω (Y N (active i) ω)-width • Pi i ω-UFpaid i ω) 2 μ := by
    rw [hechild]
    exact hfinalChild i
  have hpaidBound (i : Fin m) : ‖(hpaidChild i).toLp _‖≤εf i := by simpa only [hechild] using hfinalBound i
  obtain ⟨hpaid,hpaidB⟩ := MeanPaidFinalRms.paid_error_bound μ d.sigma wf (fun _ => width)
    P Pi UFpaid XE (Y N) active FE κf _ εf hf herr hD hfinalMeas hpaidChild hpaidBound
  have he : (fun ω => out ω-paidTarget ω)=
      (fun ω => (d.sigma • P ω+∑ i,wf i • (FE i ω (XE (active i) ω)-width • Pi i ω))-paidTarget ω) := by
    funext ω
    apply congrArg (fun y => y-paidTarget ω)
    have h := SourceMeanExecutionRms.body_paid_final d.G nodes anchors d.r d.sigma Ds δ t w main final sampling N G d.x (P ω) (env ω) (tape ω)
    dsimp only at h
    dsimp only [actualCache] at h
    rw [SourceMeanShift.cache_retained] at h
    exact h
  rw [he]
  exact ⟨hpaid,hpaidB⟩

/-- End-to-end source body difference to its explicit retained reference,
including the original-data center quadrature payment. -/
theorem source_output_error_bound
    (hp : MeasurePreserving seed μ (seedMeasure d))
    (h₀ : ℝ) (hmesh : MeshConditions d h₀) (hhalf : contraction d h₀≤1/2)
    (hpsi : d.G.psi≤d.G.R^4) (κ κf : ℝ≥0) (aRow : ℝ) (ha : 0≤aRow)
    (Eprivate : ℝ) (hanchor : MemLp anchor 2 μ) (hanchorBound : ‖hanchor.toLp anchor‖≤Eprivate)
    (ε : ℕ → Fin n → ℝ) (hrow : ∀ i,∑ j,|Amat i j|≤aRow)
    (hstable : ∀ i,ChildStable (main i).program (main i).coefficient G κ)
    (hmeas : ∀ k,k<N → ∀ i,AEStronglyMeasurable (fun ω => eval k i ω (X k i ω)-eval k i ω (Y k i ω)) μ)
    (hchild : ∀ k,k<N → ∀ i,MemLp (childErr k i) 2 μ)
    (hchildBound : ∀ k (hk : k<N) i,‖(hchild k hk i).toLp _‖≤ε k i)
    (εf : Fin m → ℝ)
    (hfinalStable : ∀ i,ChildStable (final i).program (final i).coefficient G κf)
    (hfinalMeas : ∀ i,AEStronglyMeasurable (fun ω => FE i ω (XE (active i) ω)-FE i ω (Y N (active i) ω)) μ)
    (hfinalChild : ∀ i,MemLp (fun ω => FE i ω (Y N (active i) ω)-width • Pref i ω-UF i ω) 2 μ)
    (hfinalBound : ∀ i,‖(hfinalChild i).toLp _‖≤εf i) :
    ∃ hout : MemLp (fun ω => out ω-referenceReadout d nodes anchors seeds Ds δ t w main final sampling P U V raw Z Pref ω) 2 μ,
      ‖hout.toLp _‖≤(∑ i,|wf i|)*((κf:ℝ)*sourceMainBudget d nodes h₀ N κ aRow Eprivate ε)+∑ i,|wf i| *εf i+
        MeanOriginalBounds.quadratureBudget d := by
  obtain ⟨hb,hbB⟩ := source_body_error_bound d nodes anchors seeds Ds δ t w main final sampling μ P U V raw Z N G tape Gref Pref
    hp h₀ hmesh hhalf hpsi κ κf aRow ha Eprivate hanchor hanchorBound ε hrow hstable hmeas hchild hchildBound
    εf hfinalStable hfinalMeas hfinalChild hfinalBound
  obtain ⟨hq,hqB⟩ := quadrature_on_source d nodes anchors seeds Ds δ t w main final sampling μ P V raw Z hp hmesh.order
  have he : (fun ω => out ω-referenceReadout d nodes anchors seeds Ds δ t w main final sampling P U V raw Z Pref ω)=
      (fun ω => out ω-paidTarget ω)+(fun ω => MeanOriginalBounds.quadratureError d (seed ω)) := by
    funext ω
    simp only [Pi.add_apply]
    rw [← paid_target_sub_reference d nodes anchors seeds Ds δ t w main final sampling P U V raw Z Pref ω]
    exact (sub_add_sub_cancel _ _ _).symm
  rw [he]
  refine ⟨hb.add hq,?_⟩
  change ‖hb.toLp _+hq.toLp _‖≤_
  exact (norm_add_le _ _).trans (add_le_add hbB hqB)

end OriginalSource
end AcceleratedLogConcave.Oracle.MeanCompletedRms
