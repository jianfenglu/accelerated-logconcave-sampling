import AcceleratedLogConcave.Oracle.MeanChronologicalFinalAlignment
import AcceleratedLogConcave.Oracle.MeanChronologicalSupport

/-! Joint Gaussian comparison laws of the actual finite mean-main coupling.
The static coarse host retains incoming correlations and the original parent.
Only the complete unread tape is a fresh product factor. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace AcceleratedLogConcave.Oracle.MeanChronologicalFinalLaws
open Numerics Numerics.AffineGraph AffineLowering TapeLowering NoisyLayer
open RecursiveMeanProgram RecursiveMeanContinuation SourceMeanLayer SourceMeanExecutable
open TailOccurrenceCut TailCut CanonicalTapeLaw CanonicalTapeMeasurability
open PrivateCausalLayer PrivateCausalAdvance MeanChronologicalCoupling MeanChronologicalLaws MeanChronologicalFinalAlignment
local instance canonicalTapeSpace {d c : ℕ} {Γ : Ctx} {τ : Ty} (p : Prog c Γ τ) :
    MeasurableSpace (Tape d p) := tapeSpace d p
variable {m n a h d : ℕ} (M : MeanGeometry m) (nodes : Fin n ≃ M.MeanNode)
  (anchors : Fin a ≃ M.Anchor) (seeds : Fin h ≃ Fin m × M.Kernel)
  (main : Fin n → ExecutableData) (final : Fin m → ExecutableData) (sampling : ExecutableData) (N : ℕ)
  (r Ds : ℝ) (hr : 0<r) (hDs : 0<Ds)
  (hmass : ∀ i,CovarianceSetup.shiftSq (main i).shiftVector≤Ds^2)
  {A : Type*} [MeasurableSpace A]
  (L : PrimitiveLaws d) (hL : L.pointDraw=stdGaussian (Point d))
  (x P referencePosition : A → Point d) (hx : Measurable x) (hP : Measurable P)
  (hreference : Measurable referencePosition)
  {F : Point d → ℝ} (hF : ContDiff ℝ 2 F) {ell : ℝ} (hell : 0≤ell)
  (hlo : ∀ z v,0≤fderiv ℝ (fderiv ℝ F) z v v)
  (hup : ∀ z v,fderiv ℝ (fderiv ℝ F) z v v≤ell*‖v‖^2)
  (σ : ℝ) (hσ : 0<σ) (hsmall : r^2*ell≤1/2) (δ t w : ℝ)
local instance : MeasurableSpace
    (Prefix d (MeanMainBatchCoupling.bodyCut M nodes anchors seeds main final sampling N)) := prefixSpace d _


variable (Jall : ∀ (k : ℕ) (hk : k<N),FreshChildBatchCoupling.Lower L
  (data M nodes anchors seeds main final sampling N r Ds hr hDs hmass (stage M nodes anchors seeds main final sampling N k hk.le).1 (stage_positive M nodes anchors seeds main final sampling N k hk)))

/-- The constructed finite kernel reaches the exact canonical designated
paid-final cut used by the retained final conditional. -/
theorem kernel_finalBatch_laws
    (hfinalMass : ∀ i,CovarianceSetup.shiftSq (final i).shiftVector≤Ds^2)
    (ha : 0<rowBound (m := m) r σ δ t w)
    (hA : ∀ i,∑ j,|M.matrix r σ (nodes i) (nodes j)|≤rowBound (m := m) r σ δ t w)
    (ρ : Measure (A × Tape d (Host M nodes anchors seeds main final sampling N))) [IsProbabilityMeasure ρ]
    (μ : Measure (A × Prefix d (MeanMainBatchCoupling.bodyCut M nodes anchors seeds main final sampling N))) [IsProbabilityMeasure μ]
    (hsplit : ρ.map (CausalTailHistory.unpack (MeanMainBatchCoupling.bodyCut M nodes anchors seeds main final sampling N))=
      μ.prod (tapeLaw L (body (a := a) (h := h) M nodes main final sampling N))) :
    let cut := MeanFinalBatchCoupling.batchCut M nodes anchors seeds main final sampling N r Ds hr hDs hfinalMass
    let : MeasurableSpace (Prefix d cut) := prefixSpace d _
    ∃ (ν : Measure (History (d := d) M nodes anchors seeds main final sampling N A × Prefix d cut)),IsProbabilityMeasure ν ∧
      (kernel M nodes anchors seeds main final sampling N r Ds hr hDs hmass L hL x P referencePosition hx hP hreference hF hell hlo hup σ hσ hsmall δ t w Jall ∘ₘ ρ).map (CausalTailHistory.unpack cut)=
        ν.prod (tapeLaw L (.batch finalOrigin
          (DesignatedChildBatchCoupling.program (MeanFinalBatchCoupling.data M nodes anchors seeds main final sampling N r Ds hr hDs hfinalMass))
          (MeanFinalBatchCoupling.suffix M nodes anchors seeds main final sampling N))) ∧
      ν.map (fun z => (z.1.1,z.1.2.2))=μ.prod (Measure.pi fun _ : Fin n => stdGaussian (Point d)) := by
  let law : FinishFocus (SourceMeanExecutionRms.finish (a := a) (h := h) M nodes main final sampling)
      (Host M nodes anchors seeds main final sampling N) → Prop := fun f =>
    let : MeasurableSpace (Prefix d f.cut) := prefixSpace d _
    ∃ (ν : Measure (History (d := d) M nodes anchors seeds main final sampling N A × Prefix d f.cut)),IsProbabilityMeasure ν ∧
      (kernel M nodes anchors seeds main final sampling N r Ds hr hDs hmass L hL x P referencePosition hx hP hreference hF hell hlo hup σ hσ hsmall δ t w Jall ∘ₘ ρ).map (CausalTailHistory.unpack f.cut)=
        ν.prod (tapeLaw L (SourceMeanExecutionRms.finish (a := a) (h := h) M nodes main final sampling f.old f.direct f.saved)) ∧
      ν.map (fun z => (z.1.1,z.1.2.2))=μ.prod (Measure.pi fun _ : Fin n => stdGaussian (Point d))
  have h : law (terminalFocus M nodes anchors seeds main final sampling N) :=
    MeanChronologicalFinish.kernel_terminalCut_laws M nodes anchors seeds main final sampling N r Ds hr hDs hmass L hL x P referencePosition hx hP hreference hF hell hlo hup σ hσ hsmall δ t w Jall ha hA ρ μ hsplit
  rw [terminalFocus_eq] at h
  exact h

end AcceleratedLogConcave.Oracle.MeanChronologicalFinalLaws
