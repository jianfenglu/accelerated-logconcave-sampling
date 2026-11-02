import AcceleratedLogConcave.Oracle.SourceMeanBodyError
import AcceleratedLogConcave.Oracle.SourceMeanPrivateAnchorStability

/-! The finite-body RMS estimate on the literal complete source build.
The incoming cache is constructed from the actual private call, assembly draws,
flow draws and unchanged body tail. No private accuracy or retained law is assumed. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option quotPrecheck false
namespace AcceleratedLogConcave.Oracle.SourceMeanBuildRms
open MeasureTheory Numerics
open Numerics.AffineGraph AffineLowering TapeLowering NoisyLayer
open RetainedMeanFinalBatch SourceMeanExecutable CovarianceSetup FixedTapeStability
open SourceMeanExecutionRms
open scoped BigOperators NNReal

variable {m n a h d : ℕ}
variable (M : MeanGeometry m) (nodes : Fin n ≃ M.MeanNode)
    (anchors : Fin a ≃ M.Anchor) (seeds : Fin h ≃ Fin m × M.Kernel)
    (r σ Ds δ t w : ℝ)
    (main : Fin n → ExecutableData) (final : Fin m → ExecutableData) (sampling : ExecutableData)
    (N : ℕ) (privateShift : GaussianSlot sampling.program → ℝ)
local notation "prog" => (build M nodes anchors seeds r σ Ds δ t w main final sampling N privateShift).program
local notation "tbl" => table M nodes anchors r σ Ds δ t w main final sampling

/-- Execute the actual embedded private child on its own slice of this same tape. -/
def privateResult (G : Point d → Point d) (x P : Point d) (τ : Tape d prog) : Point d :=
  childPoint (run (sampling.program.embed
    (prefixSlot (a := a) main final sampling ∘ PrefixPublicTable.privateSlot)
    (.there .here) .here) G ⟨tbl,x,P⟩ (SourceMeanShift.inputEnv x P) (τ.2.2.1 0))

/-- This is the actual prefix store, including the direct terms and retained inputs. -/
def actualEnv (G : Point d → Point d) (x P : Point d) (τ : Tape d prog) :
    Env d (Ready n m h) :=
  SourceMeanShift.cache M nodes anchors seeds r σ Ds δ t w main final sampling x P
    (privateResult M nodes anchors seeds r σ Ds δ t w main final sampling N privateShift G x P τ)
    (fun i => (τ.2.2.2.2.1 i).1) (fun i => (τ.2.2.2.2.2.2.1 i).1)

/-- No coordinates are regenerated: this is the complete body tail. -/
def actualTape (τ : Tape d prog) : Tape d (body (a := a) (h := h) M nodes main final sampling N) :=
  τ.2.2.2.2.2.2.2.2

theorem actualEnv_retained (G : Point d → Point d) (x P : Point d) (τ : Tape d prog) :
    storedPoint (actualEnv M nodes anchors seeds r σ Ds δ t w main final sampling N privateShift G x P τ)
      (MeanExecutablePrefix.saved .here) = P := by
  exact SourceMeanShift.cache_retained _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

/-- Full-build value equality only; the full program and its paid trace are unchanged. -/
theorem build_value (G : Point d → Point d) (x P : Point d) (τ : Tape d prog) :
    childPoint (run prog G ⟨tbl,x,P⟩ Env.empty τ) =
      childPoint (run (body (a := a) (h := h) M nodes main final sampling N) G ⟨tbl,x,P⟩
        (actualEnv M nodes anchors seeds r σ Ds δ t w main final sampling N privateShift G x P τ)
        (actualTape M nodes anchors seeds r σ Ds δ t w main final sampling N privateShift τ)) := by
  exact SourceMeanPrivateAnchorStability.build_eq_output M nodes anchors seeds r σ Ds δ t w
    main final sampling N privateShift G x P τ

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (G : Point d → Point d) (x P : Ω → Point d)
    (xStar U nu0 : Fin n → Ω → Point d)
set_option backward.isDefEq.respectTransparency true in
/-- All benchmark premises concern this actual prefix and unchanged body tape. -/
theorem build_error_bound (fullTape : Ω → Tape d prog) :
    let env : Ω → Env d (Ready n m h) := fun ω => actualEnv M nodes anchors seeds r σ Ds δ t w main final sampling N privateShift G (x ω) (P ω) (fullTape ω)
    let tape : Ω → Tape d (body (a := a) (h := h) M nodes main final sampling N) := fun ω => actualTape M nodes anchors seeds r σ Ds δ t w main final sampling N privateShift (fullTape ω)
    let A := (fun i j => M.matrix r σ (nodes i) (nodes j))
    let rho := RecursiveMeanPublicTable.centerNoise r M.R Ds
    let Cmat := residualRoot A rho (rowBound (m := m) r σ δ t w)
    let b := (fun i ω => storedPoint (env ω) (MeanExecutablePrefix.direct i))
    let init := (fun i ω => initial M nodes r Ds main final sampling N (env ω) (tape ω) i)
    let eval := evaluator M nodes r Ds main final sampling N G tape U
    let Z := noise M nodes main final sampling N tape
    let Pmain := designatedNoise M nodes main final sampling N tape
    let X := SharedLayerRms.iterate b A Cmat eval Z init
    let Y := SharedLayerRms.benchmark xStar A Cmat σ Pmain Z nu0
    let H := SharedLayerRms.childError eval Y U σ Pmain
    let res := SharedLayerRms.residual b A U xStar
    let XE := (fun i ω =>
      let st := state M nodes anchors r σ Ds δ t w main final sampling
        N G (x ω) (P ω) (env ω) (tape ω)
      storedPoint st.env (st.old i))
    let FE := (fun i ω => finalEvaluator M nodes anchors r σ Ds δ t w main final sampling
      N G (x ω) (P ω) (env ω) (tape ω) i)
    let active := (fun i => nodes.symm (.center M i))
    let Pi := (fun i ω => storedPoint (env ω) (MeanExecutablePrefix.designated i))
    let _P0 := (fun ω => storedPoint (env ω) (MeanExecutablePrefix.saved .here))
    let wf := Numerics.GaussLegendre.weight m
    let width := RecursiveMeanPublicTable.finalWidth M.R σ
    let out := (fun ω => childPoint (run prog G ⟨tbl,x ω,P ω⟩ Env.empty (fullTape ω)))
    ∀ (κ κf : ℝ≥0) (aRow Rres : ℝ)
    (_ha : 0 ≤ aRow) (_hR : 0 ≤ Rres) (ε : ℕ → Fin n → ℝ)
    (_hrow : ∀ i, ∑ j, |A i j| ≤ aRow)
    (_hstable : ∀ i, ChildStable (main i).program (main i).coefficient G κ)
    (_hmeas : ∀ k, k < N → ∀ i, AEStronglyMeasurable
      (fun ω => eval k i ω (X k i ω) - eval k i ω (Y k i ω)) μ)
    (hinit : ∀ i, MemLp (fun ω => init i ω - (xStar i ω + nu0 i ω)) 2 μ)
    (hres : ∀ i, MemLp (res i) 2 μ)
    (_hresBound : ∀ i, ‖(hres i).toLp (res i)‖ ≤ Rres)
    (hchild : ∀ k, k < N → ∀ i, MemLp (H k i) 2 μ)
    (_hchildBound : ∀ k (hk : k < N) i, ‖(hchild k hk i).toLp (H k i)‖ ≤ ε k i)
    (UF : Fin m → Ω → Point d) (εf : Fin m → ℝ)
    (_hfinalStable : ∀ i, ChildStable (final i).program (final i).coefficient G κf)
    (_hfinalMeas : ∀ i, AEStronglyMeasurable
      (fun ω => FE i ω (XE (active i) ω) - FE i ω (Y N (active i) ω)) μ)
    (hfinalChild : ∀ i, MemLp
      (fun ω => FE i ω (Y N (active i) ω) - width • Pi i ω - UF i ω) 2 μ)
    (_hfinalBound : ∀ i, ‖(hfinalChild i).toLp _‖ ≤ εf i),
    let D := ((κ : ℝ)*aRow)^N * Collocation.rawNodeErrorNorm μ
      (fun i ω => init i ω - (xStar i ω + nu0 i ω)) hinit +
      Collocation.forcingSum ((κ : ℝ)*aRow)
        (fun k => Rres + SharedLayerRms.childRowBudget A (finiteBudget N ε) k) N
    let outputError := fun ω => out ω - (σ • P ω + ∑ i, wf i • UF i ω)
    ∃ hout : MemLp outputError 2 μ,
      ‖hout.toLp outputError‖ ≤ (∑ i, |wf i|) * ((κf : ℝ)*D) + ∑ i, |wf i| *εf i := by
  intro env tape A rho Cmat b init eval Z Pmain X Y H res XE FE active Pi P0 wf width out κ κf aRow Rres ha hR ε hrow hstable hmeas hinit hres hresBound hchild hchildBound UF εf hfinalStable hfinalMeas hfinalChild hfinalBound
  have hb := SourceMeanExecutionRms.body_error_bound M nodes anchors r σ Ds δ t w
    main final sampling μ N G x P env tape xStar U nu0 κ κf aRow Rres ha hR ε
    hrow hstable hmeas hinit hres hresBound hchild hchildBound UF εf
    hfinalStable hfinalMeas hfinalChild hfinalBound
  have he : (fun ω => out ω - (σ • P ω + ∑ i, wf i • UF i ω)) =
      (fun ω => childPoint (run (body (a := a) (h := h) M nodes main final sampling N)
        G ⟨tbl,x ω,P ω⟩ (env ω) (tape ω)) - (σ • P0 ω + ∑ i, wf i • UF i ω)) := by
    funext ω
    exact congrArg₂ (fun u v : Point d => u - v)
      (build_value M nodes anchors seeds r σ Ds δ t w main final sampling N privateShift G (x ω) (P ω) (fullTape ω))
      (congrArg (fun z : Point d => σ • z + ∑ i, wf i • UF i ω)
        (actualEnv_retained M nodes anchors seeds r σ Ds δ t w main final sampling N privateShift G (x ω) (P ω) (fullTape ω))).symm
  rw [he]
  exact hb

end AcceleratedLogConcave.Oracle.SourceMeanBuildRms
