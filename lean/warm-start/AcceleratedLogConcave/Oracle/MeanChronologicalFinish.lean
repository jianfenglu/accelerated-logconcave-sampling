import AcceleratedLogConcave.Oracle.MeanChronologicalLaws

/-! Laws at the literal paid-final continuation reached by the constructed
finite mean kernel, with the complete incoming coarse host and source tape. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace AcceleratedLogConcave.Oracle.MeanChronologicalFinish
open Numerics Numerics.AffineGraph AffineLowering TapeLowering NoisyLayer
open RecursiveMeanProgram RecursiveMeanContinuation SourceMeanLayer SourceMeanExecutable
open TailOccurrenceCut TailCut CanonicalTapeLaw CanonicalTapeMeasurability
open PrivateCausalLayer PrivateCausalAdvance MeanChronologicalCoupling MeanChronologicalLaws
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


def zeroCut (s : Cursor M nodes anchors seeds main final sampling N) (hz : s.remaining=0) :
    TailCut (SourceMeanExecutionRms.finish (a := a) (h := h) M nodes main final sampling s.old s.direct s.saved)
      (Host M nodes anchors seeds main final sampling N) := by
  have h := s.cut
  rw [hz] at h
  exact h

theorem zero_cursor_laws (s : Cursor M nodes anchors seeds main final sampling N) (hz : s.remaining=0)
    (ρ : Measure (History (d := d) M nodes anchors seeds main final sampling N A × Tape d (Host M nodes anchors seeds main final sampling N)))
    (ν : Measure (Coarse (d := d) M nodes anchors seeds main final sampling N A)) :
    let : MeasurableSpace (Prefix d s.cut) := prefixSpace d _
    let : MeasurableSpace (Prefix d (zeroCut M nodes anchors seeds main final sampling N s hz)) := prefixSpace d _
    (∃ (μ : Measure (History (d := d) M nodes anchors seeds main final sampling N A × Prefix d s.cut)),IsProbabilityMeasure μ ∧
      ρ.map (CausalTailHistory.unpack s.cut)=μ.prod (tapeLaw L (Loop M nodes main final sampling s.remaining s.old s.direct s.saved)) ∧
      μ.map (fun z => (z.1.1,z.1.2.2))=ν.prod (Measure.pi fun _ : Fin n => stdGaussian (Point d))) →
    ∃ (μ : Measure (History (d := d) M nodes anchors seeds main final sampling N A × Prefix d (zeroCut M nodes anchors seeds main final sampling N s hz))),IsProbabilityMeasure μ ∧
      ρ.map (CausalTailHistory.unpack (zeroCut M nodes anchors seeds main final sampling N s hz))=μ.prod
        (tapeLaw L (SourceMeanExecutionRms.finish (a := a) (h := h) M nodes main final sampling s.old s.direct s.saved)) ∧
      μ.map (fun z => (z.1.1,z.1.2.2))=ν.prod (Measure.pi fun _ : Fin n => stdGaussian (Point d)) := by
  cases s with
  | mk remaining ctx old direct saved cut =>
    cases remaining with
    | zero => exact fun h => h
    | succ remaining => exact False.elim (Nat.succ_ne_zero remaining hz)

variable (Jall : ∀ (k : ℕ) (hk : k<N),FreshChildBatchCoupling.Lower L
  (data M nodes anchors seeds main final sampling N r Ds hr hDs hmass (stage M nodes anchors seeds main final sampling N k hk.le).1 (stage_positive M nodes anchors seeds main final sampling N k hk)))

/-- Exact laws at the actual reached paid-final continuation, ready for the
retained designated final batch. The whole static incoming host remains. -/
theorem kernel_terminalCut_laws
    (ha : 0<rowBound (m := m) r σ δ t w)
    (hA : ∀ i,∑ j,|M.matrix r σ (nodes i) (nodes j)|≤rowBound (m := m) r σ δ t w)
    (ρ : Measure (A × Tape d (Host M nodes anchors seeds main final sampling N))) [IsProbabilityMeasure ρ]
    (μ : Measure (A × Prefix d (MeanMainBatchCoupling.bodyCut M nodes anchors seeds main final sampling N))) [IsProbabilityMeasure μ]
    (hsplit : ρ.map (CausalTailHistory.unpack (MeanMainBatchCoupling.bodyCut M nodes anchors seeds main final sampling N))=
      μ.prod (tapeLaw L (body (a := a) (h := h) M nodes main final sampling N))) :
    let s := terminalCursor M nodes anchors seeds main final sampling N
    let cut := terminalCut M nodes anchors seeds main final sampling N
    let : MeasurableSpace (Prefix d cut) := prefixSpace d _
    ∃ (ν : Measure (History (d := d) M nodes anchors seeds main final sampling N A × Prefix d cut)),IsProbabilityMeasure ν ∧
      (kernel M nodes anchors seeds main final sampling N r Ds hr hDs hmass L hL x P referencePosition hx hP hreference hF hell hlo hup σ hσ hsmall δ t w Jall ∘ₘ ρ).map (CausalTailHistory.unpack cut)=
        ν.prod (tapeLaw L (SourceMeanExecutionRms.finish (a := a) (h := h) M nodes main final sampling s.old s.direct s.saved)) ∧
      ν.map (fun z => (z.1.1,z.1.2.2))=μ.prod (Measure.pi fun _ : Fin n => stdGaussian (Point d)) :=
  zero_cursor_laws M nodes anchors seeds main final sampling N L (terminalCursor M nodes anchors seeds main final sampling N) (terminal_remaining M nodes anchors seeds main final sampling N) _ μ
    (kernel_terminal_laws M nodes anchors seeds main final sampling N r Ds hr hDs hmass L hL x P referencePosition hx hP hreference hF hell hlo hup σ hσ hsmall δ t w Jall ha hA ρ μ hsplit)

end AcceleratedLogConcave.Oracle.MeanChronologicalFinish
