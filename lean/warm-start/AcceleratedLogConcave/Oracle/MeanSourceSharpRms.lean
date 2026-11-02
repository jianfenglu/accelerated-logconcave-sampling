import AcceleratedLogConcave.Oracle.MeanCompletedRms
import AcceleratedLogConcave.Oracle.MeanSharpOriginalBounds

/-! Intrinsic initializer payment in the actual finite mean program.
Reuses the proved finite RMS recurrence and literal final correction. The
initializer is the same source error with its sharper physical displacement
bound, required to preserve the parent-width dependence in recursion. -/
noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
namespace AcceleratedLogConcave.Oracle.MeanSourceSharpRms
open MeanCompletedRms
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

local notation "seed" => sourceSeed d nodes anchors seeds Ds δ t w main final sampling P V raw Z
local notation "env" => actualCache d nodes anchors seeds Ds δ t w main final sampling P U raw Z
local notation "anchor" => anchorError d U V


theorem initializer_on_source
    (hp : MeasurePreserving seed μ (seedMeasure d))
    (i : Fin n) :
    ∃ hi : MemLp (fun ω => MeanOriginalBounds.initializerError d (nodes i) (seed ω)) 2 μ,
      ‖hi.toLp _‖≤ MeanSharpOriginalBounds.initializerBudget d := by
  let h := MeanOriginalBounds.initializer_memLp d (nodes i)
  refine ⟨h.comp_measurePreserving hp,?_⟩
  change ‖(h.comp_measurePreserving hp).toLp (MeanOriginalBounds.initializerError d (nodes i) ∘ seed)‖≤_
  change ‖Lp.compMeasurePreserving seed hp (h.toLp _)‖≤_
  rw [Lp.norm_compMeasurePreserving]
  exact MeanSharpOriginalBounds.initializer_norm_le d (nodes i)

 theorem direct_error_bound
    (hp : MeasurePreserving seed μ (seedMeasure d))
    (hpsi : d.G.psi≤d.G.R^4) (Eprivate : ℝ)
    (hanchor : MemLp anchor 2 μ) (hanchorBound : ‖hanchor.toLp anchor‖≤Eprivate) (i : Fin n) :
    ∃ hi : MemLp (directError d nodes anchors seeds Ds δ t w main final sampling P U V raw Z i) 2 μ,
      ‖hi.toLp _‖≤d.r*backwardEnd d.G.R*Eprivate+MeanSharpOriginalBounds.initializerBudget d := by
  obtain ⟨hi,hiB⟩ := initializer_on_source d nodes anchors seeds Ds δ t w main final sampling μ P V raw Z hp i
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


/-- The source scalar recurrence, with both original-data and genuinely
lower private-anchor payments exposed in physical units. -/
def sourceMainBudget (h₀ : ℝ) (N : ℕ) (κ : ℝ≥0) (aRow Eprivate : ℝ)
    (ε : ℕ → Fin n → ℝ) : ℝ :=
  ((κ:ℝ)*aRow)^N*(d.r*backwardEnd d.G.R*Eprivate+MeanSharpOriginalBounds.initializerBudget d)+
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
    (h₀ : ℝ) (hmesh : MeshConditions d h₀)
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
  have hIB (i : Fin n) := direct_error_bound d nodes anchors seeds Ds δ t w main final sampling μ P U V raw Z hp hpsi Eprivate hanchor hanchorBound i
  let hi : ∀ i,MemLp (fun ω => initial i ω-(Phi i ω+nu0 i ω)) 2 μ := fun i =>
    (he i).symm ▸ (hIB i).choose
  have hIB' (i : Fin n) : ‖(hi i).toLp _‖≤d.r*backwardEnd d.G.R*Eprivate+MeanSharpOriginalBounds.initializerBudget d := by
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
    (MeanSharpOriginalBounds.initializerBudget_nonneg d))).2 hIB'

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

/-- Full paid final-body error, with original initializer and row defects
already supplied rather than assumed. -/
theorem source_body_error_bound
    (hp : MeasurePreserving seed μ (seedMeasure d))
    (h₀ : ℝ) (hmesh : MeshConditions d h₀)
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
    hp h₀ hmesh hpsi κ aRow ha Eprivate hanchor hanchorBound ε hrow hstable hmeas hchild hchildBound
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
    (h₀ : ℝ) (hmesh : MeshConditions d h₀)
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
    hp h₀ hmesh hpsi κ κf aRow ha Eprivate hanchor hanchorBound ε hrow hstable hmeas hchild hchildBound
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
end AcceleratedLogConcave.Oracle.MeanSourceSharpRms
