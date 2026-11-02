import AcceleratedLogConcave.Root.LocalRootLawQuantitative
import AcceleratedLogConcave.Root.OuterRootFlowIdentification

/-! Source-only literal old-Y/initial-E0 tape alignment. No marginal equality
is used to manufacture a path coupling. -/
noncomputable section
set_option autoImplicit false
namespace AcceleratedLogConcave.Root.OuterRootExactTapePath
open MeasureTheory ProbabilityTheory Oracle Oracle.CanonicalTapeMeasurability
open ClockNoisyLayer ClockRetainedFinalSplice LocalRootLawWrapper LocalRootLawReferenceLift
open OuterRootFlowIdentification OuterRootPhysicalPath
variable (P : SourceSchedule) (hR : P.R ≤ 1/2) (hc : 0 < P.csch)
  (hsmall : P.csch < 1/160) (clock : ClockLaw.Clock) {d : ℕ} (ell : ℕ)
local instance : MeasurableSpace (Tape d (code P hR hc hsmall clock ell)) :=
  tapeSpace d (code P hR hc hsmall clock ell)

variable {V : Point d → ℝ} (hV : ContDiff ℝ 2 V) {m : ℝ} (hm : 0 < m)
  (hh : 0 < P.delta)
  (hlo : ∀ z v, m*‖v‖^2 ≤ fderiv ℝ (fderiv ℝ V) z v v)
  (hup : ∀ z v, fderiv ℝ (fderiv ℝ V) z v v ≤ ‖v‖^2)

/-- The exact parent in the quantitative receiver is the conditional path
started from this execution's xF and this execution's split Gaussian Y0. -/
theorem exactParentY_eq_rawY (a : Sample P hR hc hsmall clock d ell) :
    LocalRootLawQuantitative.exactParentY P hR hc hsmall clock ell
      (OuterRootFlowIdentification.family hV hm hh hlo hup) a =
    rawY hV hh (lower_nonneg hm hlo) hup a.1.1
      (LocalRootLawQuantitative.oldY P hR hc hsmall clock ell a) clock := by
  have H := conditional_eq_reference_trajectory hV hm hh hlo hup a.1.1
    (LocalRootLawQuantitative.oldY P hR hc hsmall clock ell a) clock.property
  have H2 := congrArg Prod.snd H
  exact H2.symm

/-- The interpreter center law is the literal inverse-scaled physical heat law. -/
def centerLaw : Measure (Point d) :=
  ((OuterRootFlowIdentification.family hV hm hh hlo hup).law 0).map
    (fun x => (Real.sqrt P.delta)⁻¹ • x)

theorem centerLaw_physical_map :
    (centerLaw P hV hm hh hlo hup).map (fun x => Real.sqrt P.delta • x) =
      (OuterRootFlowIdentification.family hV hm hh hlo hup).law 0 := by
  have hs : Real.sqrt P.delta ≠ 0 := (Real.sqrt_pos.2 hh).ne'
  rw [centerLaw,Measure.map_map (by fun_prop) (by fun_prop)]
  have he : (fun x : Point d => Real.sqrt P.delta • ((Real.sqrt P.delta)⁻¹ • x)) = id := by
    funext x
    simp only [smul_smul,mul_inv_cancel₀ hs,one_smul,id_eq]
  simp only [Function.comp_def] at *
  rw [he,Measure.map_id]

/-- The common physical seed is read from the literal tape, not redrawn.
Its product law follows from the existing whole-tape split theorem. -/
theorem physicalSeed_preserving :
    MeasurePreserving
      (fun a : Sample P hR hc hsmall clock d ell =>
        (Real.sqrt P.delta • a.1.1,LocalRootLawQuantitative.oldY P hR hc hsmall clock ell a))
      (executionLaw P hR hc hsmall clock ell
        ((centerLaw P hV hm hh hlo hup).prod (stdGaussian (Point d))))
      (((OuterRootFlowIdentification.family hV hm hh hlo hup).law 0).prod
        (stdGaussian (Point d))) := by
  let mu := centerLaw P hV hm hh hlo hup
  let : IsProbabilityMeasure mu := by unfold mu centerLaw; infer_instance
  have hhost := LocalRootLawAssembly.initialHost_preserving P hR hc hsmall clock ell mu
  have hp : MeasurePreserving
      (fun a : Sample P hR hc hsmall clock d ell =>
        (a.1.1,LocalRootLawQuantitative.oldY P hR hc hsmall clock ell a))
      (executionLaw P hR hc hsmall clock ell (mu.prod (stdGaussian (Point d))))
      (mu.prod (stdGaussian (Point d))) :=
    measurePreserving_fst.comp (measurePreserving_fst.comp hhost)
  have hx : MeasurePreserving (fun x : Point d => Real.sqrt P.delta • x) mu
      ((OuterRootFlowIdentification.family hV hm hh hlo hup).law 0) :=
    ⟨by fun_prop,centerLaw_physical_map P hV hm hh hlo hup⟩
  exact (hx.prod (MeasurePreserving.id (stdGaussian (Point d)))).comp hp

end AcceleratedLogConcave.Root.OuterRootExactTapePath
