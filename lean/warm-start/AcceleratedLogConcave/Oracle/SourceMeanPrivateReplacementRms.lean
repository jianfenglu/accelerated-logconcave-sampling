import AcceleratedLogConcave.Oracle.SourceMeanBuildRms

/-! Replace only the private anchor in the cache constructed by the literal full
build. Both executions retain the same external center, original momentum,
assembly draws, flow draws, and complete body tape. All finite-body accuracy
premises below concern the replacement cache. No reference law, independence,
individual-output moment, or nonterminal D2 statement is supplied. -/
noncomputable section
set_option quotPrecheck false
namespace AcceleratedLogConcave.Oracle.SourceMeanPrivateReplacementRms
open MeasureTheory Numerics
open Numerics.AffineGraph AffineLowering TapeLowering NoisyLayer
open RetainedMeanFinalBatch SourceMeanExecutable CovarianceSetup FixedTapeStability
open SourceMeanExecutionRms
open scoped BigOperators NNReal

section Domination
variable {Ω E F : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedAddCommGroup F]

/-- Difference-only domination followed by the L2 triangle inequality. -/
theorem replacement_error_bound (μ : Measure Ω) (actual replacement target : Ω → E)
    (privateDifference : Ω → F) (C B : ℝ)
    (hmeas : AEStronglyMeasurable (fun ω => actual ω - replacement ω) μ)
    (hprivate : MemLp privateDifference 2 μ)
    (hpoint : ∀ ω, ‖actual ω - replacement ω‖ ≤ C * ‖privateDifference ω‖)
    (hbody : MemLp (fun ω => replacement ω - target ω) 2 μ)
    (hbodyBound : ‖hbody.toLp (fun ω => replacement ω - target ω)‖ ≤ B) :
    ∃ hout : MemLp (fun ω => actual ω - target ω) 2 μ,
      ‖hout.toLp (fun ω => actual ω - target ω)‖ ≤
        C * ‖hprivate.toLp privateDifference‖ + B := by
  have hdiff : MemLp (fun ω => actual ω - replacement ω) 2 μ :=
    hprivate.of_le_mul hmeas (Filter.Eventually.of_forall hpoint)
  have hdiffBound : ‖hdiff.toLp (fun ω => actual ω - replacement ω)‖ ≤
      C * ‖hprivate.toLp privateDifference‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [hdiff.coeFn_toLp,hprivate.coeFn_toLp] with ω hd hp
    rw [hd,hp]
    exact hpoint ω
  have hout : MemLp (fun ω => actual ω - target ω) 2 μ :=
    (hdiff.add hbody).ae_eq (Filter.Eventually.of_forall fun ω => by
      change (actual ω - replacement ω) + (replacement ω - target ω) = actual ω - target ω
      abel)
  have hid : hout.toLp (fun ω => actual ω - target ω) =
      hdiff.toLp (fun ω => actual ω - replacement ω) +
        hbody.toLp (fun ω => replacement ω - target ω) := by
    apply Lp.ext
    filter_upwards [hout.coeFn_toLp,hdiff.coeFn_toLp,hbody.coeFn_toLp,
      Lp.coeFn_add (hdiff.toLp _) (hbody.toLp _)] with ω ho hd hb ha
    rw [ho,ha]
    simp only [_root_.Pi.add_apply,hd,hb]
    abel
  refine ⟨hout,?_⟩
  rw [hid]
  exact (norm_add_le _ _).trans (add_le_add hdiffBound hbodyBound)
end Domination

variable {m n a h d : ℕ}
variable (M : MeanGeometry m) (nodes : Fin n ≃ M.MeanNode)
    (anchors : Fin a ≃ M.Anchor) (seeds : Fin h ≃ Fin m × M.Kernel)
    (r σ Ds δ t w : ℝ)
    (main : Fin n → ExecutableData) (final : Fin m → ExecutableData) (sampling : ExecutableData)
    (N : ℕ) (privateShift : GaussianSlot sampling.program → ℝ)
local notation "prog" => (build M nodes anchors seeds r σ Ds δ t w main final sampling N privateShift).program
local notation "tbl" => table M nodes anchors r σ Ds δ t w main final sampling

/-- Only the anchor changes; every other cache coordinate is from the same full tape. -/
def replacementEnv (x P V : Point d) (τ : Tape d prog) : Env d (Ready n m h) :=
  SourceMeanShift.cache M nodes anchors seeds r σ Ds δ t w main final sampling x P V
    (fun i => (τ.2.2.2.2.1 i).1) (fun i => (τ.2.2.2.2.2.2.1 i).1)

theorem replacementEnv_retained (x P V : Point d) (τ : Tape d prog) :
    storedPoint (replacementEnv M nodes anchors seeds r σ Ds δ t w main final sampling N privateShift x P V τ)
      (MeanExecutablePrefix.saved .here) = P := by
  exact SourceMeanShift.cache_retained _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

/-- Literal full-build replacement under an arbitrary fixed complete tape. -/
theorem build_replacement_sub_le (G : Point d → Point d) (κ A : ℝ)
    (hm : 0 < m) (hr : 0 ≤ r) (hκ : 0 ≤ κ) (hA : 0 ≤ A)
    (hpsi : M.psi ≤ M.R^4)
    (hmain : ∀ i, ChildStable (main i).program (main i).coefficient G κ)
    (hfinal : ∀ i, ChildStable (final i).program (final i).coefficient G κ)
    (hrow : ∀ i : M.MeanNode, ∑ j, |M.matrix r σ i j| ≤ A)
    (x P V : Point d) (τ : Tape d prog) :
    ‖childPoint (run prog G ⟨tbl,x,P⟩ Env.empty τ) -
      childPoint (run (body (a := a) (h := h) M nodes main final sampling N) G ⟨tbl,x,P⟩
        (replacementEnv M nodes anchors seeds r σ Ds δ t w main final sampling N privateShift x P V τ)
        (SourceMeanBuildRms.actualTape M nodes anchors seeds r σ Ds δ t w main final sampling N privateShift τ))‖ ≤
      SourceMeanPrivateAnchorStability.coefficient M r N κ A *
        ‖SourceMeanBuildRms.privateResult M nodes anchors seeds r σ Ds δ t w main final sampling
          N privateShift G x P τ - V‖ := by
  rw [SourceMeanPrivateAnchorStability.build_eq_output]
  exact SourceMeanPrivateAnchorStability.output_sub_le M nodes anchors seeds r σ Ds δ t w
    main final sampling N G κ A hm hr hκ hA hpsi hmain hfinal hrow x P
    (SourceMeanBuildRms.privateResult M nodes anchors seeds r σ Ds δ t w main final sampling
      N privateShift G x P τ) V
    (fun i => (τ.2.2.2.2.1 i).1) (fun i => (τ.2.2.2.2.2.2.1 i).1)
    (SourceMeanBuildRms.actualTape M nodes anchors seeds r σ Ds δ t w main final sampling N privateShift τ)

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (G : Point d → Point d) (x P V : Ω → Point d)
    (xStar U nu0 : Fin n → Ω → Point d)
set_option backward.isDefEq.respectTransparency true in
/-- The actual full build is bounded by private-anchor propagation plus the
explicit finite-body estimate at the replacement cache. No body accuracy is
assumed as a whole, and only the private difference needs an L2 moment. -/
theorem build_error_bound (fullTape : Ω → Tape d prog) :
    let env : Ω → Env d (Ready n m h) := fun ω =>
      replacementEnv M nodes anchors seeds r σ Ds δ t w main final sampling N privateShift
        (x ω) (P ω) (V ω) (fullTape ω)
    let tape : Ω → Tape d (body (a := a) (h := h) M nodes main final sampling N) := fun ω =>
      SourceMeanBuildRms.actualTape M nodes anchors seeds r σ Ds δ t w main final sampling
        N privateShift (fullTape ω)
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
    let replacement := (fun ω => childPoint (run (body (a := a) (h := h) M nodes main final sampling N)
      G ⟨tbl,x ω,P ω⟩ (env ω) (tape ω)))
    let privateDifference := (fun ω => SourceMeanBuildRms.privateResult M nodes anchors seeds
      r σ Ds δ t w main final sampling N privateShift G (x ω) (P ω) (fullTape ω) - V ω)
    ∀ (κ κf : ℝ≥0) (aRow Rres : ℝ)
    (_hm : 0 < m) (_hr : 0 ≤ r) (_hpsi : M.psi ≤ M.R^4)
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
    (_hfinalBound : ∀ i, ‖(hfinalChild i).toLp _‖ ≤ εf i)
    (_hprivateMeas : AEStronglyMeasurable (fun ω => out ω - replacement ω) μ)
    (hprivate : MemLp privateDifference 2 μ),
    let κprivate := max (κ : ℝ) (κf : ℝ)
    let Cprivate := SourceMeanPrivateAnchorStability.coefficient M r N κprivate aRow
    let D := ((κ : ℝ)*aRow)^N * Collocation.rawNodeErrorNorm μ
      (fun i ω => init i ω - (xStar i ω + nu0 i ω)) hinit +
      Collocation.forcingSum ((κ : ℝ)*aRow)
        (fun k => Rres + SharedLayerRms.childRowBudget A (finiteBudget N ε) k) N
    let outputError := fun ω => out ω - (σ • P ω + ∑ i, wf i • UF i ω)
    ∃ hout : MemLp outputError 2 μ,
      ‖hout.toLp outputError‖ ≤ Cprivate * ‖hprivate.toLp privateDifference‖ +
        ((∑ i, |wf i|) * ((κf : ℝ)*D) + ∑ i, |wf i| *εf i) := by
  intro env tape A rho Cmat b init eval Z Pmain X Y H res XE FE active Pi P0 wf width
    out replacement privateDifference κ κf aRow Rres hm hr hpsi ha hR ε hrow hstable hmeas
    hinit hres hresBound hchild hchildBound UF εf hfinalStable hfinalMeas hfinalChild
    hfinalBound hprivateMeas hprivate κprivate Cprivate D outputError
  obtain ⟨hbody,hbodyBound⟩ := SourceMeanExecutionRms.body_error_bound M nodes anchors r σ Ds δ t w
    main final sampling μ N G x P env tape xStar U nu0 κ κf aRow Rres ha hR ε
    hrow hstable hmeas hinit hres hresBound hchild hchildBound UF εf
    hfinalStable hfinalMeas hfinalChild hfinalBound
  have hretained : P0 = P := by
    funext ω
    exact replacementEnv_retained M nodes anchors seeds r σ Ds δ t w main final sampling
      N privateShift (x ω) (P ω) (V ω) (fullTape ω)
  have hmainPrivate : ∀ i, ChildStable (main i).program (main i).coefficient G κprivate := by
    intro i p u v z rest
    exact (hstable i p u v z rest).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  have hfinalPrivate : ∀ i, ChildStable (final i).program (final i).coefficient G κprivate := by
    intro i p u v z rest
    exact (hfinalStable i p u v z rest).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _))
  have hrowPrivate (i : M.MeanNode) : ∑ j, |M.matrix r σ i j| ≤ aRow := by
    have hi := hrow (nodes.symm i)
    change ∑ j, |M.matrix r σ (nodes (nodes.symm i)) (nodes j)| ≤ aRow at hi
    calc
      _ = ∑ j, |M.matrix r σ i (nodes j)| := (nodes.sum_comp _).symm
      _ ≤ aRow := by simpa only [Equiv.apply_symm_apply] using hi
  have hpoint (ω : Ω) : ‖out ω - replacement ω‖ ≤ Cprivate * ‖privateDifference ω‖ := by
    exact build_replacement_sub_le M nodes anchors seeds r σ Ds δ t w main final sampling
      N privateShift G κprivate aRow hm hr (le_trans κ.coe_nonneg (le_max_left _ _)) ha hpsi
      hmainPrivate hfinalPrivate hrowPrivate (x ω) (P ω) (V ω) (fullTape ω)
  have he : (fun ω => replacement ω - (σ • P0 ω + ∑ i, wf i • UF i ω)) =
      (fun ω => replacement ω - (σ • P ω + ∑ i, wf i • UF i ω)) := by
    rw [hretained]
  have hb : ∃ hb : MemLp (fun ω => replacement ω - (σ • P ω + ∑ i, wf i • UF i ω)) 2 μ,
      ‖hb.toLp _‖ ≤ (∑ i, |wf i|) * ((κf : ℝ)*D) + ∑ i, |wf i| *εf i := by
    rw [← he]
    exact ⟨hbody,hbodyBound⟩
  obtain ⟨hb,hbBound⟩ := hb
  exact replacement_error_bound μ out replacement (fun ω => σ • P ω + ∑ i, wf i • UF i ω)
    privateDifference Cprivate ((∑ i, |wf i|) * ((κf : ℝ)*D) + ∑ i, |wf i| *εf i)
    hprivateMeas hprivate hpoint hb hbBound

end AcceleratedLogConcave.Oracle.SourceMeanPrivateReplacementRms
