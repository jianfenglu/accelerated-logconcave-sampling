import AcceleratedLogConcave.Root.OuterRootLiteralScore
import AcceleratedLogConcave.Root.OuterRootCenterMoment
import AcceleratedLogConcave.Root.ClockInitialComparison
import AcceleratedLogConcave.Root.OuterRootExactTapePath

/-! Original-data moment supplier at the actual Clock child benchmark centers,
retaining the original entering momentum, split draw and raw assembly host. -/
noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
namespace AcceleratedLogConcave.Root.ClockCenterMoment
open Oracle ClockChronologicalCoupling OuterRootFlowIdentification
variable (P : SourceSchedule) {d : ℕ} {V : Point d → ℝ} (hV : ContDiff ℝ 2 V)
  {m : ℝ} (hm : 0<m)
  (hlo : ∀ z v,m*‖v‖^2≤fderiv ℝ (fderiv ℝ V) z v v)
  (hup : ∀ z v,fderiv ℝ (fderiv ℝ V) z v v≤‖v‖^2)
local notation "F" => family hV hm P.delta_pos hlo hup
local notation "μX" => OuterRootExactTapePath.centerLaw P hV hm P.delta_pos hlo hup

/-- Actual stationary input/split/raw-assembly product from initialization. -/
def baseLaw : Measure (Base P d) :=
  ((μX).prod (stdGaussian (Point d))).prod ((stdGaussian (Point d)).prod
    (Measure.pi fun _ : ClockNoisyLayer.Index P => stdGaussian (Point d)))

instance baseLaw_probability : IsProbabilityMeasure (baseLaw P hV hm hlo hup) := by
  unfold baseLaw OuterRootExactTapePath.centerLaw
  infer_instance

def physicalSeed (b : Base P d) : Point d × Point d :=
  (Real.sqrt P.delta • b.1.1,ClockPublicSetup.splitValues b.1.2 b.2.1 0)

theorem physicalSeed_preserving : MeasurePreserving (physicalSeed (d := d) P)
    (baseLaw P hV hm hlo hup) (OuterRootStrongJetLp.seedMeasure F) := by
  let γ := stdGaussian (Point d)
  let γn := Measure.pi fun _ : ClockNoisyLayer.Index P => γ
  let : IsProbabilityMeasure μX := by unfold OuterRootExactTapePath.centerLaw; infer_instance
  have ha := (measurePreserving_prodAssoc ((μX).prod γ) γ γn).symm
  have hd := (measurePreserving_fst (μ := ((μX).prod γ).prod γ) (ν := γn)).comp ha
  have hs := (measurePreserving_fst (μ := (μX).prod γ) (ν := γ)).comp
    (Kinetic.phaseSplit_measurePreserving μX ClockPublicSetup.s ClockPublicSetup.noise Kinetic.source_split_coefficients)
  have hx : MeasurePreserving (fun x : Point d => Real.sqrt P.delta • x) μX ((F).law 0) :=
    ⟨by fun_prop,OuterRootExactTapePath.centerLaw_physical_map P hV hm P.delta_pos hlo hup⟩
  exact ((hx.prod (MeasurePreserving.id γ)).comp (hs.comp hd))

/-- Exact source-clock center equality after the actual orthogonal split. -/
theorem center_eq (clock : ClockLaw.Clock) (i : ClockNoisyLayer.Index P) (b : Base P d) :
    ClockChronologicalCoupling.center P clock hV (lower_nonneg hm hlo) hup i b =
      OuterRootCenterMoment.center hV hm P.delta_pos hlo hup
        ⟨ClockCollocation.u P.delta P.K clock i,
          (ClockCollocation.u_mem P.delta_pos P.K clock i).1,
          (ClockCollocation.u_mem P.delta_pos P.K clock i).2.trans clock.2.2⟩
        (physicalSeed P b) := by
  rw [ClockChronologicalCoupling.center_eq_source,
    OuterRootLiteralScore.path_eq_rawY hV P.delta_pos (lower_nonneg hm hlo) hup _ _
      ⟨(ClockCollocation.u_mem P.delta_pos P.K clock i).1,
        (ClockCollocation.u_mem P.delta_pos P.K clock i).2.trans clock.2.2⟩]
  simp only [OuterRootCenterMoment.center,physicalSeed,smul_smul,
    inv_mul_cancel₀ (Real.sqrt_pos.mpr P.delta_pos).ne',one_smul,ClockCollocation.rF]

/-- The exact benchmark center required by every actual Clock child has its
primitive-scale square bounded by 10d, with no supplied moment hypothesis. -/
theorem center_scale_square (hdelta : P.delta≤1/2) (clock : ClockLaw.Clock)
    (i : ClockNoisyLayer.Index P) :
    Integrable (fun b => (Gibbs.primitiveScale (scaledPotential V (Real.sqrt P.delta))
      (ClockChronologicalCoupling.center P clock hV (lower_nonneg hm hlo) hup i b))^2)
      (baseLaw P hV hm hlo hup) ∧
    (∫ b,(Gibbs.primitiveScale (scaledPotential V (Real.sqrt P.delta))
      (ClockChronologicalCoupling.center P clock hV (lower_nonneg hm hlo) hup i b))^2
      ∂baseLaw P hV hm hlo hup)≤10*(d:ℝ) := by
  let u : Set.Icc (0:ℝ) (1/2) := ⟨ClockCollocation.u P.delta P.K clock i,
    (ClockCollocation.u_mem P.delta_pos P.K clock i).1,
    (ClockCollocation.u_mem P.delta_pos P.K clock i).2.trans clock.2.2⟩
  obtain ⟨hi,hb⟩ := OuterRootCenterMoment.center_scale_square hV hm P.delta_pos hlo hup hdelta u
  have hp := physicalSeed_preserving P hV hm hlo hup
  have he : (fun b => (Gibbs.primitiveScale (scaledPotential V (Real.sqrt P.delta))
      (ClockChronologicalCoupling.center P clock hV (lower_nonneg hm hlo) hup i b))^2) =
      (fun p => (Gibbs.primitiveScale (scaledPotential V (Real.sqrt P.delta))
        (OuterRootCenterMoment.center hV hm P.delta_pos hlo hup u p))^2) ∘ physicalSeed P := by
    funext b
    rw [center_eq]
    rfl
  rw [he]
  refine ⟨hp.integrable_comp_of_integrable hi,?_⟩
  have hmeas := hi.aestronglyMeasurable
  rw [← hp.map_eq] at hmeas
  have heq := integral_map hp.measurable.aemeasurable hmeas
  rw [hp.map_eq] at heq
  exact heq.symm.trans_le hb

end AcceleratedLogConcave.Root.ClockCenterMoment
