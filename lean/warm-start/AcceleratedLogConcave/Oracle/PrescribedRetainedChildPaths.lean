import AcceleratedLogConcave.Oracle.PrescribedRetainedAccuracy

/-! Exact reachable physical parameters of the four lower joints used by
RecursiveRetainedCoupling.core. Main occurrence indices remain literal; a
first-layer occurrence witnesses reachability of their shared scalar law. -/
noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
namespace AcceleratedLogConcave.Oracle.PrescribedRetainedChildPaths
open Numerics Numerics.AffineGraph CubicExecutableWorkShift RecursiveCall
variable (P : SourceSchedule) (hK : 10≤P.K) (hc : 0<P.csch) (hcsmall : P.csch<1/160)
  (hC : 8≤P.Csch) (hy : PrivateSourceScalarAbsorption.threshold P≤P.y)
  {d : ℕ} (ell r0 σ0 : ℝ) (hell : 0≤ell) (hr0 : 0<r0) (hσ0 : 0<σ0)
  (hrootRadius : ell*r0^2≤P.delta)

/-- Only physical scalar parameters and precision determine the call node. -/
def endpoint {ell : ℝ} (a : Conditional.SourceParameters (Point d) ell) (q : ℝ) : State :=
  ⟨a.radius,a.width,q⟩

variable {p : State} {depth cost : ℕ}
  (hp : RecursiveCall.Path (source P (PrescribedRetainedCoupling.radiusGuard P hK hc hcsmall hC hy)) (PrescribedRecursiveStability.root P r0 σ0) p depth cost)

/-- The exact main-call parameter object passed by core to its lower joint. -/
def mainTheta (i : Fin (ScalarSchedulePayment.n P (PrescribedRetainedCoupling.radiusGuard P hK hc hcsmall hC hy))) :=
  MeanMainBatchCoupling.mainParameters (source P (PrescribedRetainedCoupling.radiusGuard P hK hc hcsmall hC hy)).M (source P (PrescribedRetainedCoupling.radiusGuard P hK hc hcsmall hC hy)).nodes (PrescribedRetainedAccuracy.parameters (d := d) P hK hc hcsmall hC hy ell r0 σ0 hell hr0 hσ0 hrootRadius (p := p) (depth := depth) (cost := cost) hp).radius (PrescribedRetainedAccuracy.parameters (d := d) P hK hc hcsmall hC hy ell r0 σ0 hell hr0 hσ0 hrootRadius (p := p) (depth := depth) (cost := cost) hp).width P.Ds P.delta P.t P.w ell
    (PrescribedRetainedAccuracy.parameters (d := d) P hK hc hcsmall hC hy ell r0 σ0 hell hr0 hσ0 hrootRadius (p := p) (depth := depth) (cost := cost) hp).radius_pos (PrescribedRetainedAccuracy.parameters (d := d) P hK hc hcsmall hC hy ell r0 σ0 hell hr0 hσ0 hrootRadius (p := p) (depth := depth) (cost := cost) hp).width_pos P.Ds_pos P.delta_pos hell (PrescribedRetainedAccuracy.parameters (d := d) P hK hc hcsmall hC hy ell r0 σ0 hell hr0 hσ0 hrootRadius (p := p) (depth := depth) (cost := cost) hp).small i (0 : Point d)

/-- The exact active-final parameter object passed by core. -/
def finalTheta :=
  MeanMainBatchCoupling.finalParameters (source P (PrescribedRetainedCoupling.radiusGuard P hK hc hcsmall hC hy)).M (PrescribedRetainedAccuracy.parameters (d := d) P hK hc hcsmall hC hy ell r0 σ0 hell hr0 hσ0 hrootRadius (p := p) (depth := depth) (cost := cost) hp).radius (PrescribedRetainedAccuracy.parameters (d := d) P hK hc hcsmall hC hy ell r0 σ0 hell hr0 hσ0 hrootRadius (p := p) (depth := depth) (cost := cost) hp).width ell
    (PrescribedRetainedAccuracy.parameters (d := d) P hK hc hcsmall hC hy ell r0 σ0 hell hr0 hσ0 hrootRadius (p := p) (depth := depth) (cost := cost) hp).radius_pos (PrescribedRetainedAccuracy.parameters (d := d) P hK hc hcsmall hC hy ell r0 σ0 hell hr0 hσ0 hrootRadius (p := p) (depth := depth) (cost := cost) hp).width_pos hell (PrescribedRetainedAccuracy.parameters (d := d) P hK hc hcsmall hC hy ell r0 σ0 hell hr0 hσ0 hrootRadius (p := p) (depth := depth) (cost := cost) hp).small (0 : Point d)

/-- The exact private main-call parameter object passed by core. -/
def privateMainTheta (i : Fin (ScalarSchedulePayment.ns P (PrescribedRetainedCoupling.radiusGuard P hK hc hcsmall hC hy))) :=
  PrivateRecursiveBatchBudget.mainParameters (source P (PrescribedRetainedCoupling.radiusGuard P hK hc hcsmall hC hy)).S (source P (PrescribedRetainedCoupling.radiusGuard P hK hc hcsmall hC hy)).snodes (PrescribedRetainedAccuracy.parameters (d := d) P hK hc hcsmall hC hy ell r0 σ0 hell hr0 hσ0 hrootRadius (p := p) (depth := depth) (cost := cost) hp).radius P.Ds ell
    (by have h := P.m_ge_two hc hcsmall (by linarith : 1≤P.Csch); omega)
    (PrescribedRetainedAccuracy.parameters (d := d) P hK hc hcsmall hC hy ell r0 σ0 hell hr0 hσ0 hrootRadius (p := p) (depth := depth) (cost := cost) hp).radius_pos P.Ds_pos hell (PrescribedRetainedAccuracy.parameters (d := d) P hK hc hcsmall hC hy ell r0 σ0 hell hr0 hσ0 hrootRadius (p := p) (depth := depth) (cost := cost) hp).small i (0 : Point d)

/-- The exact private final-call parameter object passed by core. -/
def privateFinalTheta (i : Fin (ScalarSchedulePayment.ns P (PrescribedRetainedCoupling.radiusGuard P hK hc hcsmall hC hy))) :=
  PrivateRecursiveBatchBudget.finalParameters (source P (PrescribedRetainedCoupling.radiusGuard P hK hc hcsmall hC hy)).S (source P (PrescribedRetainedCoupling.radiusGuard P hK hc hcsmall hC hy)).snodes (PrescribedRetainedAccuracy.parameters (d := d) P hK hc hcsmall hC hy ell r0 σ0 hell hr0 hσ0 hrootRadius (p := p) (depth := depth) (cost := cost) hp).radius ell
    (PrescribedRetainedAccuracy.parameters (d := d) P hK hc hcsmall hC hy ell r0 σ0 hell hr0 hσ0 hrootRadius (p := p) (depth := depth) (cost := cost) hp).radius_pos hell (PrescribedRetainedAccuracy.parameters (d := d) P hK hc hcsmall hC hy ell r0 σ0 hell hr0 hσ0 hrootRadius (p := p) (depth := depth) (cost := cost) hp).small i (0 : Point d)

/-- Main lower-joint reachability follows from an actual first-layer call. -/
theorem main_path (hq : 1/2<p.precision)
    (i : Fin (ScalarSchedulePayment.n P (PrescribedRetainedCoupling.radiusGuard P hK hc hcsmall hC hy))) :
    RecursiveCall.Path (source P (PrescribedRetainedCoupling.radiusGuard P hK hc hcsmall hC hy)) (PrescribedRecursiveStability.root P r0 σ0)
      (endpoint (mainTheta (d := d) P hK hc hcsmall hC hy ell r0 σ0 hell hr0 hσ0 hrootRadius hp i) (p.precision-1/4))
      (depth+1) (cost+1) :=
  hp.snoc (Occurrence.meanMain ⟨0,P.NP_pos (by linarith)⟩ i) ⟨hq,rfl⟩

/-- Final lower-joint reachability uses the actual q−t edge. -/
theorem final_path (hq : 1/2<p.precision) (i : Fin P.m) :
    RecursiveCall.Path (source P (PrescribedRetainedCoupling.radiusGuard P hK hc hcsmall hC hy)) (PrescribedRecursiveStability.root P r0 σ0)
      (endpoint (finalTheta (d := d) P hK hc hcsmall hC hy ell r0 σ0 hell hr0 hσ0 hrootRadius hp) (p.precision-P.t))
      (depth+1) (cost+0) :=
  hp.snoc (Occurrence.activeFinal i) ⟨hq,rfl⟩

/-- Private main lower joints are reached by the actual private first layer. -/
theorem privateMain_path (hq : 1/2<p.precision)
    (i : Fin (ScalarSchedulePayment.ns P (PrescribedRetainedCoupling.radiusGuard P hK hc hcsmall hC hy))) :
    RecursiveCall.Path (source P (PrescribedRetainedCoupling.radiusGuard P hK hc hcsmall hC hy)) (PrescribedRecursiveStability.root P r0 σ0)
      (endpoint (privateMainTheta (d := d) P hK hc hcsmall hC hy ell r0 σ0 hell hr0 hσ0 hrootRadius hp i) (p.precision-1/4))
      (depth+1) (cost+1) :=
  hp.snoc (Occurrence.samplingMain ⟨0,P.NP_pos (by linarith)⟩ i) ⟨hq,rfl⟩

/-- Private final lower joints remain actual calls independently of loop count. -/
theorem privateFinal_path (hq : 1/2<p.precision)
    (i : Fin (ScalarSchedulePayment.ns P (PrescribedRetainedCoupling.radiusGuard P hK hc hcsmall hC hy))) :
    RecursiveCall.Path (source P (PrescribedRetainedCoupling.radiusGuard P hK hc hcsmall hC hy)) (PrescribedRecursiveStability.root P r0 σ0)
      (endpoint (privateFinalTheta (d := d) P hK hc hcsmall hC hy ell r0 σ0 hell hr0 hσ0 hrootRadius hp i) (p.precision-1/4))
      (depth+1) (cost+1) :=
  hp.snoc (Occurrence.samplingFinal i) ⟨hq,rfl⟩


/-- The canonical reached parameter object is the exact lower object used by core. -/
theorem main_parameters_eq (hq : 1/2<p.precision) (i : Fin (ScalarSchedulePayment.n P (PrescribedRetainedCoupling.radiusGuard P hK hc hcsmall hC hy))) :
    PrescribedRetainedAccuracy.parameters (d := d) P hK hc hcsmall hC hy ell r0 σ0 hell hr0 hσ0 hrootRadius (main_path (d := d) P hK hc hcsmall hC hy ell r0 σ0 hell hr0 hσ0 hrootRadius hp hq i) = mainTheta (d := d) P hK hc hcsmall hC hy ell r0 σ0 hell hr0 hσ0 hrootRadius hp i := by
  apply Subtype.ext
  rfl

/-- The canonical reached parameter object is the exact lower object used by core. -/
theorem final_parameters_eq (hq : 1/2<p.precision) (i : Fin P.m) :
    PrescribedRetainedAccuracy.parameters (d := d) P hK hc hcsmall hC hy ell r0 σ0 hell hr0 hσ0 hrootRadius (final_path (d := d) P hK hc hcsmall hC hy ell r0 σ0 hell hr0 hσ0 hrootRadius hp hq i) = finalTheta (d := d) P hK hc hcsmall hC hy ell r0 σ0 hell hr0 hσ0 hrootRadius hp := by
  apply Subtype.ext
  rfl

/-- The canonical reached parameter object is the exact lower object used by core. -/
theorem privateMain_parameters_eq (hq : 1/2<p.precision) (i : Fin (ScalarSchedulePayment.ns P (PrescribedRetainedCoupling.radiusGuard P hK hc hcsmall hC hy))) :
    PrescribedRetainedAccuracy.parameters (d := d) P hK hc hcsmall hC hy ell r0 σ0 hell hr0 hσ0 hrootRadius (privateMain_path (d := d) P hK hc hcsmall hC hy ell r0 σ0 hell hr0 hσ0 hrootRadius hp hq i) = privateMainTheta (d := d) P hK hc hcsmall hC hy ell r0 σ0 hell hr0 hσ0 hrootRadius hp i := by
  apply Subtype.ext
  rfl

/-- The canonical reached parameter object is the exact lower object used by core. -/
theorem privateFinal_parameters_eq (hq : 1/2<p.precision) (i : Fin (ScalarSchedulePayment.ns P (PrescribedRetainedCoupling.radiusGuard P hK hc hcsmall hC hy))) :
    PrescribedRetainedAccuracy.parameters (d := d) P hK hc hcsmall hC hy ell r0 σ0 hell hr0 hσ0 hrootRadius (privateFinal_path (d := d) P hK hc hcsmall hC hy ell r0 σ0 hell hr0 hσ0 hrootRadius hp hq i) = privateFinalTheta (d := d) P hK hc hcsmall hC hy ell r0 σ0 hell hr0 hσ0 hrootRadius hp i := by
  apply Subtype.ext
  rfl

end AcceleratedLogConcave.Oracle.PrescribedRetainedChildPaths
