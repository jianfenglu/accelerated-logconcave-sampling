import AcceleratedLogConcave.Oracle.SourceMeanExecutionRms

/-! Conditional RMS accuracy of the literal finite main body.
All benchmark error and graph-residual premises are exposed, not manufactured
from fixed-tape stability. L2 hypotheses concern differences only. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option quotPrecheck false
namespace AcceleratedLogConcave.Oracle.SourceMeanExecutionRms
open MeasureTheory Numerics
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
local notation "A" => (fun i j => M.matrix r σ (nodes i) (nodes j))
local notation "rho" => RecursiveMeanPublicTable.centerNoise r M.R Ds
local notation "Cmat" => residualRoot A rho (rowBound (m := m) r σ δ t w)
local notation "b" => (fun i ω => storedPoint (env ω) (MeanExecutablePrefix.direct i))
local notation "init" => (fun i ω => initial M nodes r Ds main final sampling N (env ω) (tape ω) i)
local notation "eval" => evaluator M nodes r Ds main final sampling N G tape U
local notation "Z" => noise M nodes main final sampling N tape
local notation "Pmain" => designatedNoise M nodes main final sampling N tape
local notation "X" => SharedLayerRms.iterate b A Cmat eval Z init
local notation "Y" => SharedLayerRms.benchmark xStar A Cmat σ Pmain Z nu0
local notation "err" => (fun k i ω => X k i ω - Y k i ω)
local notation "H" => SharedLayerRms.childError eval Y U σ Pmain
local notation "res" => SharedLayerRms.residual b A U xStar
local notation "actual" => (fun i ω =>
  let st := state M nodes anchors r σ Ds δ t w main final sampling
    N G (x ω) (P ω) (env ω) (tape ω)
  storedPoint st.env (st.old i) - Y N i ω)

/-- The finite budget is extended by zero only outside the actual execution. -/
def finiteBudget (N : ℕ) (ε : ℕ → Fin n → ℝ) (k : ℕ) (i : Fin n) : ℝ :=
  if k < N then ε k i else 0

/-- Stored interpreter nodes obey the numerical recurrence bound. Neither the
benchmark child RMS estimates nor the benchmark residual estimate is proved here.
No probability, Gaussian law, independence, or absolute moment is required. -/
theorem main_error_bound (κ : ℝ≥0) (aRow Rres : ℝ)
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
      designatedNoise,MeanExecutionSchedule.designatedNoise,hn k hk,sub_self,smul_zero]
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
    Pmain Z σ μ κ aRow Rres ha hR (finiteBudget N ε) hrow
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

end AcceleratedLogConcave.Oracle.SourceMeanExecutionRms
