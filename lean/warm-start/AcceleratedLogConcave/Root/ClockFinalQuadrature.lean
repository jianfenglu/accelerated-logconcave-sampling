import AcceleratedLogConcave.Root.ClockMainPrimitiveResidual
import AcceleratedLogConcave.Root.OuterRootSeedDefectLp
import AcceleratedLogConcave.Root.ClockPhysicalReadout

/-! Final physical quadrature defect on the actual original split seed.
The score row uses precisely the true Clock centers and source widths. -/
noncomputable section
set_option autoImplicit false
set_option Elab.async false
open MeasureTheory
open scoped BigOperators
namespace AcceleratedLogConcave.Root.ClockFinalQuadrature
open Oracle ClockChronologicalCoupling OuterRootFlowIdentification ClockCenterMoment
open OuterRootSeedDefectLp OuterRootStrongJetLp
variable (P : SourceSchedule) {d : ℕ} {V : Point d → ℝ} (hV : ContDiff ℝ 2 V)
  {m : ℝ} (hm : 0<m)
  (hlo : ∀ z v,m*‖v‖^2≤fderiv ℝ (fderiv ℝ V) z v v)
  (hup : ∀ z v,fderiv ℝ (fderiv ℝ V) z v v≤‖v‖^2)
  (clock : ClockLaw.Clock)
local notation "F" => family hV hm P.delta_pos hlo hup
local notation "data" => OuterRootOriginalData.data hV P.delta_pos (lower_nonneg hm hlo) hup
local notation "c" => (Real.sqrt P.delta)⁻¹

def defect (b : Base P d) : Point d :=
  seedDefect data c (ClockSchedule.sourceCells P.delta) (ClockSchedule.sourceOrder P.K)
    clock ClockPublicSetup.s (physicalSeed P b)

theorem defect_memLp : MemLp (defect P hV hm hlo hup clock) 2 (baseLaw P hV hm hlo hup) :=
  (seedDefect_memLp F data c _ _ clock ClockPublicSetup.s).comp_measurePreserving
    (physicalSeed_preserving P hV hm hlo hup)

theorem defect_eq_primitive_row (b : Base P d) :
    defect P hV hm hlo hup clock b =
      ClockPublicSetup.s • ClockPublicSetup.splitValues b.1.2 b.2.1 0 +
      (∑ i : ClockNoisyLayer.Index P, (ClockPublicSetup.noise *
        ClockRetainedFinalSplice.correctionWeight P clock i) •
        Gibbs.primitiveMean (OuterRootOriginalData.potential V P.delta)
          (center P clock hV (lower_nonneg hm hlo) hup i b) (ClockNoisyLayer.radius P clock i)) -
      ClockPublicSetup.s • OuterRootPhysicalPath.rawY hV P.delta_pos (lower_nonneg hm hlo) hup
        b.1.1 (ClockPublicSetup.splitValues b.1.2 b.2.1 0) clock := by
  have hinput : c • (physicalSeed P b).1=b.1.1 := by
    simp only [physicalSeed,smul_smul,inv_mul_cancel₀ (Real.sqrt_pos.mpr P.delta_pos).ne',one_smul]
  have hj (i : ClockNoisyLayer.Index P) := OuterRootLiteralScore.jet_one_eq_score
    hV P.delta_pos (lower_nonneg hm hlo) hup b.1.1 (physicalSeed P b).2
      ⟨(ClockCollocation.u_mem P.delta_pos P.K clock i).1,
        (ClockCollocation.u_mem P.delta_pos P.K clock i).2.trans clock.2.2⟩
  have hz : OuterRootPhysicalPath.rawY hV P.delta_pos (lower_nonneg hm hlo) hup b.1.1
      (physicalSeed P b).2 0 = (physicalSeed P b).2 := by
    unfold OuterRootPhysicalPath.rawY
    exact Conditional.convexProbabilityFlow_initial _ _ _ _ _ _ _ _ _ _ _
  rw [defect,seedDefect,OuterRootMainResidual.seedJet_zero_eq_rawY hV hm P.delta_pos hlo hup _ (by norm_num),
    OuterRootMainResidual.seedJet_zero_eq_rawY hV hm P.delta_pos hlo hup _ clock.property,hinput,hz]
  congr 1
  rw [Finset.smul_sum]
  apply congrArg (fun z => ClockPublicSetup.s • (physicalSeed P b).2 + z)
  apply Finset.sum_congr rfl
  intro i _
  change ClockPublicSetup.s • (ClockRetainedFinalSplice.weight P clock i •
    (Numerics.ConditionalSmoothing.jet data 1 (ClockCollocation.u P.delta P.K clock i)
      (c • (physicalSeed P b).1,(physicalSeed P b).2)).2) = _
  rw [hinput,hj]
  change ClockPublicSetup.s • (ClockRetainedFinalSplice.weight P clock i •
    ((-Real.sqrt (2*P.delta)) • OuterRootLiteralScore.score hV P.delta_pos (lower_nonneg hm hlo) hup
      b.1.1 (ClockPublicSetup.splitValues b.1.2 b.2.1 0) (ClockCollocation.u P.delta P.K clock i))) = _
  rw [ClockMainPrimitiveResidual.score_eq_primitiveMean P hV hm hlo hup clock]
  rw [← ClockPhysicalReadout.physicalCoefficient_eq_noise_correction,ClockPhysicalReadout.physicalCoefficient_source]
  simp only [smul_smul,ClockCollocation.rF]
  congr 1
  ring

theorem defect_energy (hsmall : P.delta≤1/2) :
    (∫ b, ‖defect P hV hm hlo hup clock b‖^2 ∂baseLaw P hV hm hlo hup) ≤
      (ClockPublicSetup.s * ClockQuadraturePower.orderConstant P.K * Real.sqrt (d:ℝ) * P.delta^(P.K+6))^2 := by
  have hp := physicalSeed_preserving P hV hm hlo hup
  obtain ⟨hi,he⟩ := seedDefect_energy F data c (ClockSchedule.sourceCells P.delta)
    (ClockSchedule.sourceOrder P.K) clock ClockPublicSetup.s
  have hmeas := hi.aestronglyMeasurable
  rw [← hp.map_eq] at hmeas
  have heq := integral_map hp.measurable.aemeasurable hmeas
  rw [hp.map_eq] at heq
  change (∫ b,‖seedDefect data c _ _ clock ClockPublicSetup.s (physicalSeed P b)‖^2 ∂baseLaw P hV hm hlo hup)≤_
  rw [← heq,he]
  have hb := ClockQuadraturePower.source_endpoint_error hV hm P.delta_pos hlo hup hsmall P.K clock
  simp only [Fintype.card_fin] at hb
  have hs := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (mul_nonneg
    (ClockQuadraturePower.orderConstant_nonneg P.K) (Real.sqrt_nonneg _)) (pow_nonneg P.delta_pos.le _))).mpr hb
  calc
    _ ≤ ClockPublicSetup.s^2*(ClockQuadraturePower.orderConstant P.K*Real.sqrt (d:ℝ)*P.delta^(P.K+6))^2 :=
      mul_le_mul_of_nonneg_left hs (sq_nonneg _)
    _ = _ := by ring

theorem defect_norm_le (hsmall : P.delta≤1/2) :
    ‖(defect_memLp P hV hm hlo hup clock).toLp (defect P hV hm hlo hup clock)‖ ≤
      ClockPublicSetup.s * ClockQuadraturePower.orderConstant P.K * Real.sqrt (d:ℝ) * P.delta^(P.K+6) := by
  have hb := defect_energy P hV hm hlo hup clock hsmall
  rw [← Analysis.DominatedLp.norm_sq_toLp (defect_memLp P hV hm hlo hup clock)] at hb
  apply (sq_le_sq₀ (norm_nonneg _) ?_).mp hb
  exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num [ClockPublicSetup.s])
    (ClockQuadraturePower.orderConstant_nonneg P.K)) (Real.sqrt_nonneg _)) (pow_nonneg P.delta_pos.le _)
end AcceleratedLogConcave.Root.ClockFinalQuadrature
