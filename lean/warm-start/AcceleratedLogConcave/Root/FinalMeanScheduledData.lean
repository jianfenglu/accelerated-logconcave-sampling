import AcceleratedLogConcave.Root.FinalMeanInitialCertificate
import AcceleratedLogConcave.Oracle.CubicExecutableWorkShift

/-! Literal final-slot data at the source physical resolution h=exp(-y)=delta.
The outer clock inventory is distinct from the internal mean order. No program
or law equivalence is assumed: the executable is the existing constructor. -/
noncomputable section
set_option autoImplicit false
namespace AcceleratedLogConcave.Root.FinalMeanScheduledData
open Oracle Oracle.CubicExecutableWorkShift Oracle.ScalarSchedulePayment Oracle.CubicScheduleThreshold
open ClockBackwardKernel RecursiveRadiusFamily
open scoped NNReal
variable (P : SourceSchedule)

abbrev Slot := Fin (ClockSchedule.sourceCells P.delta * ClockSchedule.sourceOrder P.K)

def state (i : Slot P) (clock : ClockLaw.Clock) : Oracle.RecursiveCall.State :=
  FinalMeanInitialCertificate.finalMeanState P.delta P.delta_pos P.K i clock

def scale : ℝ := Real.sqrt P.delta
def oracleConstant : ℝ≥0 := ⟨P.delta, P.delta_pos.le⟩

theorem physical_resolution : P.delta = Real.exp (-P.y) := rfl

theorem state_parameters (i : Slot P) (clock : ClockLaw.Clock) :
    (state P i clock).radius = sourceRadius P.delta P.delta_pos P.K i clock ∧
    (state P i clock).width = Real.sqrt 3/Real.sqrt (2*P.delta) ∧
    (state P i clock).precision = (P.K:ℝ) :=
  ⟨rfl, sourceWidth_eq _, rfl⟩

theorem scale_sq : (scale P)^2 = P.delta := Real.sq_sqrt P.delta_pos.le

theorem physical_variance (i : Slot P) (clock : ClockLaw.Clock) :
    P.delta*(state P i clock).radius^2 =
      2*P.delta^2*(1-(ClockSchedule.node (ClockSchedule.sourceCells P.delta)
        (ClockSchedule.sourceOrder P.K) (ClockSchedule.sourceCells_pos P.delta_pos) clock i:ℝ)^2) := by
  let u := ClockSchedule.node (ClockSchedule.sourceCells P.delta) (ClockSchedule.sourceOrder P.K)
    (ClockSchedule.sourceCells_pos P.delta_pos) clock i
  have hu : 0 ≤ 1-(u:ℝ)^2 := by nlinarith [u.2.1,u.2.2]
  change P.delta*(Real.sqrt (2*P.delta)*Real.sqrt (1-(u:ℝ)^2))^2 = _
  rw [mul_pow, Real.sq_sqrt (mul_nonneg (by norm_num) P.delta_pos.le), Real.sq_sqrt hu]
  ring

def finalData (hR : P.R ≤ 1/2) (hc : 0 < P.csch) (hsmall : P.csch < 1/160)
    (i : Slot P) (clock : ClockLaw.Clock) : ExecutableData :=
  data P hR hc hsmall (scale P) (state P i clock).radius (state P i clock).width (state P i clock).precision

theorem finalData_literal (hR : P.R ≤ 1/2) (hc : 0 < P.csch) (hsmall : P.csch < 1/160)
    (i : Slot P) (clock : ClockLaw.Clock) :
    finalData P hR hc hsmall i clock = data P hR hc hsmall (Real.sqrt P.delta)
      (sourceRadius P.delta P.delta_pos P.K i clock) (sourceWidth P.delta) (P.K:ℝ) := rfl

theorem geometry_exact (hR : P.R ≤ 1/2) :
    let C := source P hR
    C.M.R = C.δ^C.t ∧ C.M.psi = C.δ^(4*C.t) ∧
    C.M.backward = Numerics.AffineGraph.actualKernelInterval C.M.R (C.δ^C.w)
      C.M.R_pos C.M.R_le_half (Real.rpow_pos_of_pos P.delta_pos C.w) := by
  refine ⟨rfl, ?_, rfl⟩
  change P.R^4 = P.delta^(4*P.t)
  exact P.psi_eq_R_pow.symm

theorem root_positive (i : Slot P) (clock : ClockLaw.Clock) :
    0 < (state P i clock).radius ∧ 0 < (state P i clock).width :=
  ⟨radius_pos P.delta_pos (radiusParameter P.delta P.delta_pos P.K i clock), sourceWidth_pos P.delta_pos⟩

section Scheduled
variable (hK : 10 ≤ P.K) (hc : 0 < P.csch) (hsmall : P.csch < 1/160)
  (hC : 8 ≤ P.Csch) (hy : threshold P ≤ P.y)
local notation "hR" => CubicSchedulePayments.radius_guard P hK hc hsmall hC hy

include hK hc hsmall hC hy in
theorem delta_half : P.delta ≤ 1/2 := by
  have hg := (CubicSchedulePayments.actual_scalar_payments P hK hc hsmall hC hy).2.2.2.2.2.1
  exact (hg.2.1.trans hg.2.2.1).trans hg.2.2.2

theorem initial_size (i : Slot P) (clock : ClockLaw.Clock) :
    Oracle.RecursiveSize.SizeBound (oracleConstant P) (source P hR).δ 1 1
      (state P i clock).radius (state P i clock).width :=
  FinalMeanInitialCertificate.finalSlot_sizeBound P.delta_pos (delta_half P hK hc hsmall hC hy) P.K i clock

theorem final_work {d : ℕ} (i : Slot P) (clock : ClockLaw.Clock) (oracle : Point d → Point d)
    (input : Inputs d (finalData P hR hc hsmall i clock).size)
    (tape : Tape d (finalData P hR hc hsmall i clock).program) :
    let E := finalData P hR hc hsmall i clock
    let counts := traceCounts (run E.program oracle input Env.empty tape).trace
    ((counts.queries+counts.gaussianBlocks:ℕ):ℝ) ≤ Real.exp (P.y/64) :=
  (executed_work P hK hc hsmall hC hy (scale P) (state P i clock).radius (state P i clock).width
    (P.K:ℝ) le_rfl oracle input tape).2

theorem final_queryShift_and_mass (i : Slot P) (clock : ClockLaw.Clock) :
    let E := finalData P hR hc hsmall i clock
    ChildAbsorption.QueryShift E.program E.enumeration E.coefficient (state P i clock).radius E.shiftVector ∧
      CovarianceSetup.shiftSq E.shiftVector ≤ P.Ds^2 := by
  have hs := queryShift_and_mass P hK hc hsmall hC hy (scale P) (state P i clock).radius
    (state P i clock).width (P.K:ℝ) (root_positive P i clock).1 le_rfl
  exact ⟨hs.1, hs.2.2⟩
end Scheduled

section OriginalOracle
variable {d : ℕ} {V : Point d → ℝ} (hV : ContDiff ℝ 2 V)
  (hlo : ∀ z a, 0 ≤ fderiv ℝ (fderiv ℝ V) z a a)
  (hup : ∀ z a, fderiv ℝ (fderiv ℝ V) z a a ≤ ‖a‖^2)

include hV hlo hup in
theorem normalized_gradient : LipschitzWith (oracleConstant P)
    (fun z => scale P • gradient V (scale P • z)) :=
  FinalMeanInitialCertificate.normalized_gradient_lipschitz hV hlo hup P.delta_pos.le

include hV in
theorem normalized_gradient_eq (z : Point d) :
    gradient (physicalPotential V P.delta) z = scale P • gradient V (scale P • z) :=
  PhysicalPosteriorScaling.physicalPotential_gradient hV P.delta z
end OriginalOracle
end AcceleratedLogConcave.Root.FinalMeanScheduledData
