import AcceleratedLogConcave.Root.ClockCenterMoment
import AcceleratedLogConcave.Channels.TerminalHeatBias

/-! Initial source graph error at the actual original Gaussian-start centers.
Both endpoint momentum moments follow from the actual probability flow. -/
noncomputable section
set_option autoImplicit false
set_option Elab.async false
open MeasureTheory ProbabilityTheory
namespace AcceleratedLogConcave.Root.ClockMainInitialEnergy
open Oracle ClockChronologicalCoupling OuterRootFlowIdentification ClockCenterMoment
variable (P : SourceSchedule) {d : ℕ} {V : Point d → ℝ} (hV : ContDiff ℝ 2 V)
  {m : ℝ} (hm : 0<m)
  (hlo : ∀ z v,m*‖v‖^2≤fderiv ℝ (fderiv ℝ V) z v v)
  (hup : ∀ z v,fderiv ℝ (fderiv ℝ V) z v v≤‖v‖^2)
  (clock : ClockLaw.Clock) (i : ClockNoisyLayer.Index P)
local notation "F" => family hV hm P.delta_pos hlo hup
local notation "μB" => baseLaw P hV hm hlo hup
local notation "u" => ClockCollocation.u P.delta P.K clock i
local notation "E" => Point d

def initialError (b : Base P d) : E :=
  ClockNoisyLayer.b P clock b.1.1 (ClockPublicSetup.splitValues b.1.2 b.2.1 0) i -
    ClockChronologicalCoupling.center P clock hV (lower_nonneg hm hlo) hup i b

def initialMomentum (b : Base P d) : E := (physicalSeed P b).2

def flowMomentum (b : Base P d) : E :=
  (Kinetic.referenceCoupledPairFlow F (Real.sqrt (2*P.delta^2))
    ⟨u,(ClockCollocation.u_mem P.delta_pos P.K clock i).1,
      (ClockCollocation.u_mem P.delta_pos P.K clock i).2.trans clock.2.2⟩ (physicalSeed P b)).2

theorem initialMomentum_preserving : MeasurePreserving (initialMomentum (d := d) P)
    μB (stdGaussian E) :=
  (measurePreserving_snd (μ := (F).law 0) (ν := stdGaussian E)).comp
    (physicalSeed_preserving P hV hm hlo hup)

theorem flowMomentum_preserving : MeasurePreserving (flowMomentum P hV hm hlo hup clock i)
    μB (stdGaussian E) := by
  let t : Set.Icc (0:ℝ) (1/2) := ⟨u,(ClockCollocation.u_mem P.delta_pos P.K clock i).1,
    (ClockCollocation.u_mem P.delta_pos P.K clock i).2.trans clock.2.2⟩
  exact (measurePreserving_snd (μ := (F).law t) (ν := stdGaussian E)).comp
    ((Kinetic.referenceCoupledPairFlow_measurePreserving F (Real.sqrt (2*P.delta^2)) t).comp
      (physicalSeed_preserving P hV hm hlo hup))

theorem initialError_eq (b : Base P d) :
    initialError P hV hm hlo hup clock i b =
      (ClockCollocation.rF P.delta*u) •
        (initialMomentum P b-flowMomentum P hV hm hlo hup clock i b) := by
  have ht : u∈Set.Icc (0:ℝ) (1/2) :=
    ⟨(ClockCollocation.u_mem P.delta_pos P.K clock i).1,
      (ClockCollocation.u_mem P.delta_pos P.K clock i).2.trans clock.2.2⟩
  have he := congrArg Prod.snd (conditional_eq_reference_trajectory hV hm P.delta_pos hlo hup
    b.1.1 (initialMomentum P b) ht)
  change OuterRootPhysicalPath.rawY hV P.delta_pos (lower_nonneg hm hlo) hup
    b.1.1 (initialMomentum P b) u=flowMomentum P hV hm hlo hup clock i b at he
  rw [initialError,ClockCenterMoment.center_eq P hV hm hlo hup]
  simp only [OuterRootCenterMoment.center,physicalSeed,smul_smul,
    inv_mul_cancel₀ (Real.sqrt_pos.mpr P.delta_pos).ne',one_smul]
  change ClockNoisyLayer.b P clock b.1.1 (initialMomentum P b) i -
    (b.1.1+(ClockCollocation.rF P.delta*u) •
      OuterRootPhysicalPath.rawY hV P.delta_pos (lower_nonneg hm hlo) hup b.1.1 (initialMomentum P b) u)=_
  rw [he]
  simp only [ClockNoisyLayer.b,ClockCollocation.graph]
  module

private theorem gaussian_norm_square {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω}
    (f : Ω → E) (hp : MeasurePreserving f ν (stdGaussian E)) :
    Integrable (fun z => ‖f z‖^2) ν ∧ (∫ z,‖f z‖^2 ∂ν)=(d:ℝ) := by
  have hi := (IsGaussian.memLp_two_id (μ := stdGaussian E)).norm.integrable_sq
  refine ⟨hp.integrable_comp_of_integrable hi,?_⟩
  have hmeas := hi.aestronglyMeasurable
  rw [← hp.map_eq] at hmeas
  have he := integral_map hp.measurable.aemeasurable hmeas
  rw [hp.map_eq] at he
  have hgauss : (∫ z : Point d,‖z‖^2 ∂stdGaussian (Point d))=(d:ℝ) := by
    simpa using (show (∫ z : Point d,‖z‖^2 ∂stdGaussian (Point d)) =
      (Module.finrank ℝ (Point d):ℝ) from Channels.TerminalHeatBiasAux.integral_norm_sq_stdGaussian)
  exact he.symm.trans hgauss

/-- Every actual initialized row has an explicit square-energy payment. -/
theorem initialError_energy :
    Integrable (fun b => ‖initialError P hV hm hlo hup clock i b‖^2) μB ∧
    (∫ b,‖initialError P hV hm hlo hup clock i b‖^2 ∂μB)≤
      (ClockCollocation.rF P.delta)^2*(d:ℝ) := by
  let f := initialMomentum (d := d) P
  let g := flowMomentum P hV hm hlo hup clock i
  have hf := initialMomentum_preserving P hV hm hlo hup
  have hg := flowMomentum_preserving P hV hm hlo hup clock i
  have hmf := (IsGaussian.memLp_two_id (μ := stdGaussian E)).comp_measurePreserving hf
  have hmg := (IsGaussian.memLp_two_id (μ := stdGaussian E)).comp_measurePreserving hg
  have he : initialError P hV hm hlo hup clock i = (ClockCollocation.rF P.delta*u) • (f-g) :=
    funext (initialError_eq P hV hm hlo hup clock i)
  have hmerr : MemLp (initialError P hV hm hlo hup clock i) 2 μB := by
    rw [he]
    exact (hmf.sub hmg).const_smul _
  obtain ⟨hfi,hfe⟩ := gaussian_norm_square f hf
  obtain ⟨hgi,hge⟩ := gaussian_norm_square g hg
  have hsub (b : Base P d) : ‖f b-g b‖^2≤2*‖f b‖^2+2*‖g b‖^2 := by
    have hn := norm_sub_le (f b) (g b)
    nlinarith [sq_nonneg (‖f b‖-‖g b‖),norm_nonneg (f b-g b),norm_nonneg (f b),norm_nonneg (g b)]
  have hi := (hmf.sub hmg).norm.integrable_sq
  have hb := integral_mono hi ((hfi.const_mul 2).add (hgi.const_mul 2)) hsub
  change (∫ b,‖f b-g b‖^2 ∂μB) ≤ ∫ b,2*‖f b‖^2+2*‖g b‖^2 ∂μB at hb
  rw [integral_add (hfi.const_mul 2) (hgi.const_mul 2),integral_const_mul,integral_const_mul,hfe,hge] at hb
  refine ⟨hmerr.norm.integrable_sq,?_⟩
  simp_rw [initialError_eq,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs]
  rw [integral_const_mul]
  have hu := ClockCollocation.u_mem P.delta_pos P.K clock i
  have hu2 : u^2≤1/4 := by nlinarith [hu.1,hu.2,clock.2.2]
  calc
    _ ≤ (ClockCollocation.rF P.delta*u)^2*(4*(d:ℝ)) :=
      mul_le_mul_of_nonneg_left (by linarith : (∫ b,‖f b-g b‖^2 ∂μB)≤4*(d:ℝ)) (sq_nonneg _)
    _ ≤ _ := by nlinarith [mul_nonneg (sq_nonneg (ClockCollocation.rF P.delta)) (mul_nonneg (by nlinarith : 0≤1-4*u^2) (Nat.cast_nonneg d : (0:ℝ)≤d))]

theorem initialError_memLp : MemLp (initialError P hV hm hlo hup clock i) 2 μB := by
  have hf := (IsGaussian.memLp_two_id (μ := stdGaussian (Point d))).comp_measurePreserving
    (initialMomentum_preserving P hV hm hlo hup)
  have hg := (IsGaussian.memLp_two_id (μ := stdGaussian (Point d))).comp_measurePreserving
    (flowMomentum_preserving P hV hm hlo hup clock i)
  have he : initialError P hV hm hlo hup clock i =
      (ClockCollocation.rF P.delta*u) • (initialMomentum P-flowMomentum P hV hm hlo hup clock i) :=
    funext (initialError_eq P hV hm hlo hup clock i)
  rw [he]
  exact (hf.sub hg).const_smul _

theorem initialError_norm_le :
    ‖(initialError_memLp P hV hm hlo hup clock i).toLp (initialError P hV hm hlo hup clock i)‖≤
      ClockCollocation.rF P.delta*Real.sqrt (d:ℝ) := by
  have hb := (initialError_energy P hV hm hlo hup clock i).2
  rw [← Analysis.DominatedLp.norm_sq_toLp (initialError_memLp P hV hm hlo hup clock i)] at hb
  have hnon : 0≤ClockCollocation.rF P.delta*Real.sqrt (d:ℝ) := by
    exact mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hs : (ClockCollocation.rF P.delta*Real.sqrt (d:ℝ))^2=
      (ClockCollocation.rF P.delta)^2*(d:ℝ) := by
    rw [mul_pow,Real.sq_sqrt (Nat.cast_nonneg d)]
  rw [← hs] at hb
  exact (sq_le_sq₀ (norm_nonneg _) hnon).mp hb
end AcceleratedLogConcave.Root.ClockMainInitialEnergy
