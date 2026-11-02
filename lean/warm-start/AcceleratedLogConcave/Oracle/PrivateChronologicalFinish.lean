import AcceleratedLogConcave.Oracle.PrivateChronologicalLaws

/-! The actual terminal chronology laws at the literal paid-finish cut.
Only dependent target transport is performed; the cut and original tape are
the ones reached by the constructed finite execution. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
namespace AcceleratedLogConcave.Oracle.PrivateChronologicalFinish
open Numerics.AffineGraph AffineLowering TapeLowering SourceExecutableTables
open TailOccurrenceCut TailCut CanonicalTapeLaw CanonicalTapeMeasurability
open PrivateChronologicalCoupling PrivateChronologicalLaws

local instance canonicalTapeSpace {d c : ℕ} {Γ : Ctx} {τ : Ty} (p : Prog c Γ τ) :
    MeasurableSpace (Tape d p) := tapeSpace d p

variable {m n d : ℕ} (S : SamplingGeometry m) (e : Fin n ≃ S.Node)
  (r Ds : ℝ) (main final : Fin n → ExecutableData) (N : ℕ)

def zeroCut (s : Cursor S e r Ds main final N) (hz : s.remaining=0) :
    TailCut (PrivateSamplingExecutionSchedule.finisher main final N s.old s.direct s.saved)
      (Host S e r Ds main final N) := by
  have h := s.cut
  rw [hz] at h
  exact h

theorem zero_cursor_laws (L : PrimitiveLaws d)
    (s : Cursor S e r Ds main final N) (hz : s.remaining=0)
    (ρ : Measure (History d N n × Tape d (Host S e r Ds main final N)))
    (ν : Measure ((Point d × Point d) × Point d)) :
    let : MeasurableSpace (Prefix d s.cut) := prefixSpace d _
    let : MeasurableSpace (Prefix d (zeroCut S e r Ds main final N s hz)) := prefixSpace d _
    (∃ (μ : Measure (History d N n × Prefix d s.cut)), IsProbabilityMeasure μ ∧
      ρ.map (CausalTailHistory.unpack s.cut) =
        μ.prod (tapeLaw L (Loop main final N s.remaining s.old s.direct s.saved)) ∧
      μ.map (fun z => (z.1.1,z.1.2.2)) =
        ν.prod (Measure.pi fun _ : Fin n => stdGaussian (Point d))) →
    ∃ (μ : Measure (History d N n × Prefix d (zeroCut S e r Ds main final N s hz))),
      IsProbabilityMeasure μ ∧
      ρ.map (CausalTailHistory.unpack (zeroCut S e r Ds main final N s hz)) =
        μ.prod (tapeLaw L (PrivateSamplingExecutionSchedule.finisher main final N s.old s.direct s.saved)) ∧
      μ.map (fun z => (z.1.1,z.1.2.2)) =
        ν.prod (Measure.pi fun _ : Fin n => stdGaussian (Point d)) := by
  cases s with
  | mk remaining ctx old direct saved cut =>
    cases remaining with
    | zero => exact fun h => h
    | succ remaining => exact False.elim (Nat.succ_ne_zero remaining hz)

variable (hr : 0 < r) (hDs : 0 < Ds)
  (hmass : ∀ i, CovarianceSetup.shiftSq (main i).shiftVector ≤ Ds^2)
  (L : PrimitiveLaws d) (hL : L.pointDraw = stdGaussian (Point d))
  {F : Point d → ℝ} (hF : ContDiff ℝ 2 F) {ell : ℝ} (hell : 0 ≤ ell)
  (hlo : ∀ z v, 0 ≤ fderiv ℝ (fderiv ℝ F) z v v)
  (hup : ∀ z v, fderiv ℝ (fderiv ℝ F) z v v ≤ ell*‖v‖^2)
  (J : ∀ (k : ℕ) (hk : k<N), FreshChildBatchCoupling.Lower L
    (PrivateChronologicalCoupling.data S e r Ds main final N hr hDs hmass
      (stage S e r Ds main final N k hk.le).1
      (stage_positive S e r Ds main final N k hk)))

/-- Literal paid-finish cut laws of the constructed terminal kernel, including
the original parent P in the coarse product and retaining the full source. -/
theorem kernel_terminalCut_laws (hm : 0<m) (x : Point d) :
    let s := terminalCursor S e r Ds main final N
    let cut := terminalCut S e r Ds main final N
    let : MeasurableSpace (Prefix d cut) := prefixSpace d _
    ∃ (μ : Measure (History d N n × Prefix d cut)), IsProbabilityMeasure μ ∧
      (kernel S e r Ds main final N hr hDs hmass L hL hF hell hlo hup J x).map
        (CausalTailHistory.unpack cut) =
          μ.prod (tapeLaw L (PrivateSamplingExecutionSchedule.finisher main final N s.old s.direct s.saved)) ∧
      μ.map (fun z => (z.1.1,z.1.2.2)) =
        (coarseLaw x).prod (Measure.pi fun _ : Fin n => stdGaussian (Point d)) := by
  exact zero_cursor_laws S e r Ds main final N L (terminalCursor S e r Ds main final N)
    (terminal_remaining S e r Ds main final N) _ (coarseLaw x)
    (kernel_terminal_laws S e r Ds main final N hr hDs hmass L hL hF hell hlo hup J hm x)

theorem kernel_terminalFocus_laws (hm : 0<m) (x : Point d) :
    let f := terminalFocus S e r Ds main final N
    let : MeasurableSpace (Prefix d f.cut) := prefixSpace d _
    ∃ (μ : Measure (History d N n × Prefix d f.cut)), IsProbabilityMeasure μ ∧
      (kernel S e r Ds main final N hr hDs hmass L hL hF hell hlo hup J x).map
        (CausalTailHistory.unpack f.cut) =
          μ.prod (tapeLaw L (PrivateSamplingExecutionSchedule.finisher main final N f.old f.direct f.saved)) ∧
      μ.map (fun z => (z.1.1,z.1.2.2)) =
        (coarseLaw x).prod (Measure.pi fun _ : Fin n => stdGaussian (Point d)) :=
  kernel_terminalCut_laws S e r Ds main final N hr hDs hmass L hL hF hell hlo hup J hm x
end AcceleratedLogConcave.Oracle.PrivateChronologicalFinish
