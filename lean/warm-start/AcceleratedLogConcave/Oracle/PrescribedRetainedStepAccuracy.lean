import AcceleratedLogConcave.Oracle.PrescribedRetainedQuantitativeInduction
import AcceleratedLogConcave.Oracle.MeanStandaloneLowerErrorBound
import AcceleratedLogConcave.Oracle.MeanCompletedSourcePayments
import AcceleratedLogConcave.Oracle.PrescribedFourChildGuards
import AcceleratedLogConcave.Oracle.PrescribedRetainedCoreEquation

/-! Actual nonterminal quantitative step for the exact retained core.
Every accuracy input below concerns a strictly lower actual child call. -/
noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace AcceleratedLogConcave.Oracle.PrescribedRetainedStepAccuracy
open Numerics Numerics.AffineGraph CubicExecutableWorkShift RecursiveCall
open RecursiveRetainedAccuracy PrescribedRetainedQuantitativeInduction
variable (P : SourceSchedule) (hK : 10≤P.K) (hc : 0<P.csch) (hcsmall : P.csch<1/160)
  (hC : 8≤P.Csch) (hy : PrivateSourceScalarAbsorption.threshold P≤P.y)
  {d : ℕ} (ell r0 σ0 : ℝ) (hell : 0≤ell) (hr0 : 0<r0) (hσ0 : 0<σ0)
  (hrootRadius : ell*r0^2≤P.delta)
  {V : Point d → ℝ} (scale : ℝ) (hV : ContDiff ℝ 2 V)
  (hlo : ∀ z v,0≤fderiv ℝ (fderiv ℝ (scaledPotential V scale)) z v v)
  (hup : ∀ z v,fderiv ℝ (fderiv ℝ (scaledPotential V scale)) z v v≤ell*‖v‖^2)

/-- The quantitative IH is exactly the complete physical lower-fibre bound
consumed by the actual source RMS producer. -/
theorem call_fiber {p : State} {depth cost : ℕ}
    (hp : Path (source P (PrescribedRetainedCoupling.radiusGuard P hK hc hcsmall hC hy))
      (PrescribedRecursiveStability.root P r0 σ0) p depth cost)
    (hacc : AccurateCall P hK hc hcsmall hC hy ell r0 σ0 hell hr0 hσ0 hrootRadius scale hV hlo hup hp) :
    MeanStandaloneLowerErrorBound.Fiber (F := scaledPotential V scale) (gradient V)
      (data P (PrescribedRetainedCoupling.radiusGuard P hK hc hcsmall hC hy) hc hcsmall scale p.radius p.width p.precision)
      (reachableLaw P hK hc hcsmall hC hy ell r0 σ0 hell hr0 hσ0 hrootRadius scale hV hlo hup hp).joint
      p.radius p.width (4*p.width*P.delta^p.precision) := by
  intro y
  obtain ⟨hmem,hbound⟩ := hacc y
  refine ⟨hmem,?_⟩
  dsimp only [RecursiveRetainedAccuracy.error,PrescribedRetainedAccuracy.parameters,
    MeanCompletedReference.parentTheta,Conditional.SourceParameters.radius,
    Conditional.SourceParameters.width] at hbound
  simpa only [mul_assoc] using hbound

variable {p : State} {depth cost : ℕ}
  (hp : Path (source P (PrescribedRetainedCoupling.radiusGuard P hK hc hcsmall hC hy)) (PrescribedRecursiveStability.root P r0 σ0) p depth cost) (hq : 1/2<p.precision)

/-- Exact lower IH at the literal main source occurrence, with its complete
standalone seed and the exact lower joint used by the active core step. -/
theorem main_fiber (i : Fin (ScalarSchedulePayment.n P (PrescribedRetainedCoupling.radiusGuard P hK hc hcsmall hC hy)))
    (hacc : AccurateCall P hK hc hcsmall hC hy ell r0 σ0 hell hr0 hσ0 hrootRadius scale hV hlo hup (PrescribedRetainedChildPaths.main_path (d := d) P hK hc hcsmall hC hy ell r0 σ0 hell hr0 hσ0 hrootRadius hp hq i)) :
    MeanStandaloneLowerErrorBound.Fiber (F := scaledPotential V scale) (gradient V)
      (MeanMainBatchCoupling.recursiveMain (source P (PrescribedRetainedCoupling.radiusGuard P hK hc hcsmall hC hy)).M (source P (PrescribedRetainedCoupling.radiusGuard P hK hc hcsmall hC hy)).nodes (anchors P (PrescribedRetainedCoupling.radiusGuard P hK hc hcsmall hC hy)) (seeds P (PrescribedRetainedCoupling.radiusGuard P hK hc hcsmall hC hy)) (source P (PrescribedRetainedCoupling.radiusGuard P hK hc hcsmall hC hy)).mesh (source P (PrescribedRetainedCoupling.radiusGuard P hK hc hcsmall hC hy)).snodes P.Ds P.delta P.t P.w P.NP (P.t_pos hc) (step_quarter P hc hcsmall) scale p.radius p.width p.precision i)
      (PrescribedRetainedCoreEquation.mainLaws P hK hc hcsmall hC hy ell r0 σ0 hell hr0 hσ0 hrootRadius scale hV hlo hup hp hq i).joint
      ((source P (PrescribedRetainedCoupling.radiusGuard P hK hc hcsmall hC hy)).M.radius p.radius ((source P (PrescribedRetainedCoupling.radiusGuard P hK hc hcsmall hC hy)).nodes i)) (RecursiveMeanPublicTable.mainWidth (ScalarSchedulePayment.n P (PrescribedRetainedCoupling.radiusGuard P hK hc hcsmall hC hy)) p.radius (source P (PrescribedRetainedCoupling.radiusGuard P hK hc hcsmall hC hy)).M.R P.Ds (SourceMeanExecutable.rowBound (m := P.m) p.radius p.width P.delta P.t P.w)) (4*(RecursiveMeanPublicTable.mainWidth (ScalarSchedulePayment.n P (PrescribedRetainedCoupling.radiusGuard P hK hc hcsmall hC hy)) p.radius (source P (PrescribedRetainedCoupling.radiusGuard P hK hc hcsmall hC hy)).M.R P.Ds (SourceMeanExecutable.rowBound (m := P.m) p.radius p.width P.delta P.t P.w))*P.delta^(p.precision-1/4)) := by
  exact call_fiber P hK hc hcsmall hC hy ell r0 σ0 hell hr0 hσ0 hrootRadius scale hV hlo hup (PrescribedRetainedChildPaths.main_path (d := d) P hK hc hcsmall hC hy ell r0 σ0 hell hr0 hσ0 hrootRadius hp hq i) hacc

/-- Exact lower IH at the literal final source occurrence, with its complete
standalone seed and the exact lower joint used by the active core step. -/
theorem final_fiber (i : Fin P.m)
    (hacc : AccurateCall P hK hc hcsmall hC hy ell r0 σ0 hell hr0 hσ0 hrootRadius scale hV hlo hup (PrescribedRetainedChildPaths.final_path (d := d) P hK hc hcsmall hC hy ell r0 σ0 hell hr0 hσ0 hrootRadius hp hq i)) :
    MeanStandaloneLowerErrorBound.Fiber (F := scaledPotential V scale) (gradient V)
      (MeanMainBatchCoupling.recursiveFinal (source P (PrescribedRetainedCoupling.radiusGuard P hK hc hcsmall hC hy)).M (source P (PrescribedRetainedCoupling.radiusGuard P hK hc hcsmall hC hy)).nodes (anchors P (PrescribedRetainedCoupling.radiusGuard P hK hc hcsmall hC hy)) (seeds P (PrescribedRetainedCoupling.radiusGuard P hK hc hcsmall hC hy)) (source P (PrescribedRetainedCoupling.radiusGuard P hK hc hcsmall hC hy)).mesh (source P (PrescribedRetainedCoupling.radiusGuard P hK hc hcsmall hC hy)).snodes P.Ds P.delta P.t P.w P.NP (P.t_pos hc) (step_quarter P hc hcsmall) scale p.radius p.width p.precision i)
      (PrescribedRetainedCoreEquation.finalLaws P hK hc hcsmall hC hy ell r0 σ0 hell hr0 hσ0 hrootRadius scale hV hlo hup hp hq i).joint
      (p.radius*(source P (PrescribedRetainedCoupling.radiusGuard P hK hc hcsmall hC hy)).M.R) (RecursiveMeanPublicTable.finalWidth (source P (PrescribedRetainedCoupling.radiusGuard P hK hc hcsmall hC hy)).M.R p.width) (4*(RecursiveMeanPublicTable.finalWidth (source P (PrescribedRetainedCoupling.radiusGuard P hK hc hcsmall hC hy)).M.R p.width)*P.delta^(p.precision-P.t)) := by
  exact call_fiber P hK hc hcsmall hC hy ell r0 σ0 hell hr0 hσ0 hrootRadius scale hV hlo hup (PrescribedRetainedChildPaths.final_path (d := d) P hK hc hcsmall hC hy ell r0 σ0 hell hr0 hσ0 hrootRadius hp hq i) hacc

/-- Exact lower IH at the literal privateMain source occurrence, with its complete
standalone seed and the exact lower joint used by the active core step. -/
theorem privateMain_fiber (i : Fin (ScalarSchedulePayment.ns P (PrescribedRetainedCoupling.radiusGuard P hK hc hcsmall hC hy)))
    (hacc : AccurateCall P hK hc hcsmall hC hy ell r0 σ0 hell hr0 hσ0 hrootRadius scale hV hlo hup (PrescribedRetainedChildPaths.privateMain_path (d := d) P hK hc hcsmall hC hy ell r0 σ0 hell hr0 hσ0 hrootRadius hp hq i)) :
    MeanStandaloneLowerErrorBound.Fiber (F := scaledPotential V scale) (gradient V)
      (PrivateRecursiveBatchBudget.main (source P (PrescribedRetainedCoupling.radiusGuard P hK hc hcsmall hC hy)).M (source P (PrescribedRetainedCoupling.radiusGuard P hK hc hcsmall hC hy)).nodes (anchors P (PrescribedRetainedCoupling.radiusGuard P hK hc hcsmall hC hy)) (seeds P (PrescribedRetainedCoupling.radiusGuard P hK hc hcsmall hC hy)) (source P (PrescribedRetainedCoupling.radiusGuard P hK hc hcsmall hC hy)).mesh (source P (PrescribedRetainedCoupling.radiusGuard P hK hc hcsmall hC hy)).snodes P.Ds P.delta P.t P.w P.NP (P.t_pos hc) (step_quarter P hc hcsmall) scale p.radius p.precision i)
      (PrescribedRetainedCoreEquation.privateMainLaws P hK hc hcsmall hC hy ell r0 σ0 hell hr0 hσ0 hrootRadius scale hV hlo hup hp hq i).joint
      ((source P (PrescribedRetainedCoupling.radiusGuard P hK hc hcsmall hC hy)).S.radius p.radius ((source P (PrescribedRetainedCoupling.radiusGuard P hK hc hcsmall hC hy)).snodes i)) (RecursiveMeanPublicTable.mainWidth (ScalarSchedulePayment.ns P (PrescribedRetainedCoupling.radiusGuard P hK hc hcsmall hC hy)) p.radius (source P (PrescribedRetainedCoupling.radiusGuard P hK hc hcsmall hC hy)).S.R P.Ds (p.radius^2)) (4*(RecursiveMeanPublicTable.mainWidth (ScalarSchedulePayment.ns P (PrescribedRetainedCoupling.radiusGuard P hK hc hcsmall hC hy)) p.radius (source P (PrescribedRetainedCoupling.radiusGuard P hK hc hcsmall hC hy)).S.R P.Ds (p.radius^2))*P.delta^(p.precision-1/4)) := by
  exact call_fiber P hK hc hcsmall hC hy ell r0 σ0 hell hr0 hσ0 hrootRadius scale hV hlo hup (PrescribedRetainedChildPaths.privateMain_path (d := d) P hK hc hcsmall hC hy ell r0 σ0 hell hr0 hσ0 hrootRadius hp hq i) hacc

/-- Exact lower IH at the literal privateFinal source occurrence, with its complete
standalone seed and the exact lower joint used by the active core step. -/
theorem privateFinal_fiber (i : Fin (ScalarSchedulePayment.ns P (PrescribedRetainedCoupling.radiusGuard P hK hc hcsmall hC hy)))
    (hacc : AccurateCall P hK hc hcsmall hC hy ell r0 σ0 hell hr0 hσ0 hrootRadius scale hV hlo hup (PrescribedRetainedChildPaths.privateFinal_path (d := d) P hK hc hcsmall hC hy ell r0 σ0 hell hr0 hσ0 hrootRadius hp hq i)) :
    MeanStandaloneLowerErrorBound.Fiber (F := scaledPotential V scale) (gradient V)
      (PrivateRecursiveBatchBudget.final (source P (PrescribedRetainedCoupling.radiusGuard P hK hc hcsmall hC hy)).M (source P (PrescribedRetainedCoupling.radiusGuard P hK hc hcsmall hC hy)).nodes (anchors P (PrescribedRetainedCoupling.radiusGuard P hK hc hcsmall hC hy)) (seeds P (PrescribedRetainedCoupling.radiusGuard P hK hc hcsmall hC hy)) (source P (PrescribedRetainedCoupling.radiusGuard P hK hc hcsmall hC hy)).mesh (source P (PrescribedRetainedCoupling.radiusGuard P hK hc hcsmall hC hy)).snodes P.Ds P.delta P.t P.w P.NP (P.t_pos hc) (step_quarter P hc hcsmall) scale p.radius p.precision i)
      (PrescribedRetainedCoreEquation.privateFinalLaws P hK hc hcsmall hC hy ell r0 σ0 hell hr0 hσ0 hrootRadius scale hV hlo hup hp hq i).joint
      ((source P (PrescribedRetainedCoupling.radiusGuard P hK hc hcsmall hC hy)).S.radius p.radius ((source P (PrescribedRetainedCoupling.radiusGuard P hK hc hcsmall hC hy)).snodes i)) (SourceExecutableTables.samplingFinalWidth (source P (PrescribedRetainedCoupling.radiusGuard P hK hc hcsmall hC hy)).S p.radius) (4*(SourceExecutableTables.samplingFinalWidth (source P (PrescribedRetainedCoupling.radiusGuard P hK hc hcsmall hC hy)).S p.radius)*P.delta^(p.precision-1/4)) := by
  exact call_fiber P hK hc hcsmall hC hy ell r0 σ0 hell hr0 hσ0 hrootRadius scale hV hlo hup (PrescribedRetainedChildPaths.privateFinal_path (d := d) P hK hc hcsmall hC hy ell r0 σ0 hell hr0 hσ0 hrootRadius hp hq i) hacc

end AcceleratedLogConcave.Oracle.PrescribedRetainedStepAccuracy
