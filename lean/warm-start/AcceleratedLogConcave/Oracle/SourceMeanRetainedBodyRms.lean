import AcceleratedLogConcave.Oracle.SourceMeanRetainedRms
import AcceleratedLogConcave.Oracle.MeanPaidFinalRms

/-! Actual paid-final body propagation with retained child reference outputs.
The literal correction still subtracts original designated inputs. The target
therefore retains each reference-minus-designated correction explicitly.
This consumes lower-child error bounds, not a current-parent accuracy premise. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option quotPrecheck false
namespace AcceleratedLogConcave.Oracle.SourceMeanRetainedRms
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
local notation "Pmain" => finiteReference N Gref
local notation "X" => SharedLayerRms.iterate b A Cmat eval Z init
local notation "Y" => SharedLayerRms.benchmark xStar A Cmat σ Pmain Z nu0
local notation "H" => SharedLayerRms.childError eval Y U σ Pmain
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
local notation "out" => (fun ω => childPoint (run
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

end AcceleratedLogConcave.Oracle.SourceMeanRetainedRms
