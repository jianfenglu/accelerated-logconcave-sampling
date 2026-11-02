import AcceleratedLogConcave.Root.ClockFinalReconstruction
import AcceleratedLogConcave.Root.RecursiveRadiusFamily

/-! Exact prescribed physical-radius recursive reference kernels in every
actual final retained pair. Precision, radius, width and public mean geometry
are the source ones; no merely Gaussian replacement is used. -/
noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option quotPrecheck false
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
namespace AcceleratedLogConcave.Root.ClockFinalReferenceChildren
open Oracle Oracle.CubicExecutableWorkShift Oracle.TapeLowering
open ClockNoisyLayer ClockBackwardKernel RecursiveRadiusFamily
local instance canonicalTapeSpace {d c : ℕ} {Γ : Ctx} {τ : Ty} (p : Prog c Γ τ) :
    MeasurableSpace (Tape d p) := CanonicalTapeMeasurability.tapeSpace d p
variable (P : SourceSchedule) (hR : P.R≤1/2) (hc : 0<P.csch) (hsmall : P.csch<1/160)
  (hK : 10≤P.K) (hC : 8≤P.Csch) (hy : CubicScheduleThreshold.threshold P≤P.y)
  {d : ℕ} {V : Point d→ℝ} (hV : ContDiff ℝ 2 V)
  (hlo : ∀ z v,0≤fderiv ℝ (fderiv ℝ V) z v v)
  (hup : ∀ z v,fderiv ℝ (fderiv ℝ V) z v v≤‖v‖^2)
local notation "hhalf" => FinalMeanScheduledData.delta_half P hK hc hsmall hC hy
local notation "Gmean" => (source P hR).M
include hc hsmall hC in
private theorem order_pos : 0<P.m := by
  have h := P.m_ge_two hc hsmall (by linarith : 1≤P.Csch)
  omega

/-- The already prescribed source physical-radius family at integer K. -/
def children : RadiusChildren (Fin d) P.delta P.K :=
  physicalRadiusChildren P.delta_pos hhalf hV hlo hup Gmean (order_pos P hc hsmall hC)
    P.t (P.t_pos hc) P.K

variable (clock : ClockLaw.Clock)
/-- Forward source centers on the same original conditional root path. -/
def forwardChild (i : Index P) : Kernel ((Point d × Point d) × Point d) (Point d) :=
  ((children P hR hc hsmall hK hC hy hV hlo hup).kernel i).comap
    (fun z => ((radiusParameter P.delta P.delta_pos P.K i clock,
      ClockFinalBatchCoupling.center P clock hV hlo hup i z.1),z.2))
    ((measurable_const.prodMk ((ClockFinalBatchCoupling.center_measurable P clock hV hlo hup i).comp measurable_fst)).prodMk measurable_snd)
instance forwardChild_markov (i : Index P) : IsMarkovKernel
    (forwardChild P hR hc hsmall hK hC hy hV hlo hup clock i) := by
  let _ : IsMarkovKernel ((children P hR hc hsmall hK hC hy hV hlo hup).kernel i) :=
    (children P hR hc hsmall hK hC hy hV hlo hup).markov i
  unfold forwardChild
  infer_instance

theorem forwardChild_invariant (i : Index P) (c : Point d × Point d) :
    (forwardChild P hR hc hsmall hK hC hy hV hlo hup clock i).comap
      (fun p => (c,p)) measurable_prodMk_left ∘ₘ stdGaussian (Point d)=stdGaussian (Point d) := by
  exact (children P hR hc hsmall hK hC hy hV hlo hup).invariant i
    (radiusParameter P.delta P.delta_pos P.K i clock) (ClockFinalBatchCoupling.center P clock hV hlo hup i c)

variable (hyMean : MeanSourceScalarAbsorption.threshold P≤P.y)
/-- Complete Pi/Pref identity at the literal source radius, distinct final
width, integer precision K and unchanged public geometry. -/
theorem final_retained (i : Index P) (c : Point d × Point d) :
    (ClockMeanChildAccuracy.finalKernel P hK hc hsmall hC hyMean hV hlo hup clock i
      (ClockFinalBatchCoupling.center P clock hV hlo hup i c)).map (fun z => (z.1.1,z.2))=
    (stdGaussian (Point d)) ⊗ₘ
      (forwardChild P hR hc hsmall hK hC hy hV hlo hup clock i).comap
        (fun p => (c,p)) measurable_prodMk_left := by
  exact (ClockMeanChildAccuracy.finalLaw P hK hc hsmall hC hyMean hV hlo hup clock i).retained _

/-- The finite paired kernel is the prescribed product of source-reference
transitions, retaining Pi jointly with Pref at each actual child. -/
theorem averagedPairs_apply (label : ℕ) (c : (Point d × Point d) × Point d) :
    ClockFinalJointLaw.averagedPairs P hR hc hsmall clock label hK hC hy hV hlo hup hyMean c=
      Measure.pi (fun i => (stdGaussian (Point d)) ⊗ₘ
        (forwardChild P hR hc hsmall hK hC hy hV hlo hup clock i).comap
          (fun p => (c.1,p)) measurable_prodMk_left) := by
  rw [ClockFinalJointLaw.averagedPairs_apply]
  congr 1
  funext i
  exact final_retained P hR hc hsmall hK hC hy hV hlo hup clock hyMean i c.1

end AcceleratedLogConcave.Root.ClockFinalReferenceChildren
