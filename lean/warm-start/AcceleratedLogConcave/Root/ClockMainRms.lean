import AcceleratedLogConcave.Root.ClockMainRmsData
import AcceleratedLogConcave.Root.ClockMainLoopChildRms
import AcceleratedLogConcave.Root.ClockFinalAssemblySupport
import AcceleratedLogConcave.Root.ClockMainPrimitiveResidual
import AcceleratedLogConcave.Root.ClockMainEnergyPayments

/-! Closed finite RMS bound for the actual retained Clock main-loop kernel.
Every probabilistic and numerical payment is derived from original data. -/
noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
namespace AcceleratedLogConcave.Root.ClockMainRms
open Oracle Oracle.AffineLowering Oracle.NoisyLayer Oracle.TapeLowering Oracle.CanonicalTapeLaw Oracle.CanonicalTapeMeasurability
open ClockChronologicalCoupling ClockNoisyLayer Numerics ClockMainRmsData
local instance canonicalTapeSpace {d c : ℕ} {Γ : Ctx} {τ : Ty} (p : Prog c Γ τ) :
    MeasurableSpace (Tape d p) := tapeSpace d p
variable (P : SourceSchedule) (hR : P.R≤1/2) (hc : 0<P.csch) (hsmall : P.csch<1/160)
  (clock : ClockLaw.Clock) (label : ℕ) (hK : 10≤P.K) (hC : 8≤P.Csch)
  (hy : CubicScheduleThreshold.threshold P≤P.y)
  {d : ℕ} {V : Point d→ℝ} (hV : ContDiff ℝ 2 V) {m : ℝ} (hm : 0<m)
  (hlo : ∀ z v,m*‖v‖^2≤fderiv ℝ (fderiv ℝ V) z v v)
  (hup : ∀ z v,fderiv ℝ (fderiv ℝ V) z v v≤‖v‖^2)
  (hyMean : MeanSourceScalarAbsorption.threshold P≤P.y)
local notation "Hlo" => OuterRootFlowIdentification.lower_nonneg hm hlo
local notation "host" => Host P hR hc hsmall clock label
local notation "X" => Sample (d := d) P hR hc hsmall clock label
local notation "sigma" => CovarianceSetup.sigma (N P) (rhoC P) (a P)
local notation "target" => ClockMainRmsData.target P hR hc hsmall clock label hV Hlo hup
local notation "reply" => ClockMainRmsData.reply P hR hc hsmall clock label hV Hlo hup
local notation "direct" => ClockMainRmsData.direct (d := d) P hR hc hsmall clock label
local notation "initial" => ClockMainRmsData.initial (d := d) P hR hc hsmall clock label
local notation "nu0" => ClockMainRmsData.initialNoise (d := d) P hR hc hsmall clock label
local notation "eval" => ClockMainRmsData.evaluator P hR hc hsmall clock label hV Hlo hup
local notation "refs" => ClockMainRmsData.reference (d := d) P hR hc hsmall clock label
local notation "noise" => ClockMainRmsData.noise (d := d) P hR hc hsmall clock label
local notation "Y" => ClockMainRmsData.benchmark P hR hc hsmall clock label hV Hlo hup
local notation "err" => ClockMainRmsData.error P hR hc hsmall clock label hV Hlo hup

def inputLaw : Measure (Point d×Point d) :=
  (OuterRootExactTapePath.centerLaw P hV hm P.delta_pos hlo hup).prod (stdGaussian (Point d))
instance inputLaw_probability : IsProbabilityMeasure (inputLaw P hV hm hlo hup) := by
  unfold inputLaw OuterRootExactTapePath.centerLaw
  infer_instance

def sourceLaw := (inputLaw P hV hm hlo hup).prod
  (tapeLaw (Probability.CanonicalNativeTapeLaw.primitiveLaws d) host)

def law : Measure X := kernel P hR hc hsmall clock label hK hC hy hV Hlo hup hyMean ∘ₘ
  sourceLaw P hR hc hsmall clock label hV hm hlo hup
local notation "lawM" => law P hR hc hsmall clock label hK hC hy hV hm hlo hup hyMean

/-- Full augmented Base has its genuine original-data law on the actual kernel. -/
theorem base_preserving : MeasurePreserving (fun z : X => z.1.1) lawM (ClockCenterMoment.baseLaw P hV hm hlo hup) := by
  have hp : MeasurePreserving (ClockChronologicalLaws.comparison P hR hc hsmall clock label) lawM
      ((ClockCenterMoment.baseLaw P hV hm hlo hup).prod (Measure.pi fun _ : Index P => stdGaussian (Point d))) := by
    refine ⟨ClockChronologicalLaws.comparison_measurable P hR hc hsmall clock label,?_⟩
    exact ClockChronologicalLaws.kernel_comparison_law P hR hc hsmall clock label hK hC hy hV Hlo hup hyMean
      (inputLaw P hV hm hlo hup)
  exact (measurePreserving_fst (μ := ClockCenterMoment.baseLaw P hV hm hlo hup)
    (ν := Measure.pi fun _ : Index P => stdGaussian (Point d))).comp hp

/-- The actual direct graph uses the initially retained split occurrence. -/
theorem direct_eq_base_ae : ∀ᵐ z ∂lawM, ∀ i,
    direct i z = b P clock z.1.1.1.1 (ClockPublicSetup.splitValues z.1.1.1.2 z.1.1.2.1 0) i := by
  filter_upwards [ClockFinalAssemblySupport.kernel_sourceBase_ae P hR hc hsmall clock label hK hC hy hV Hlo hup hyMean
    (sourceLaw P hR hc hsmall clock label hV hm hlo hup)] with z hz
  have he := congrArg (fun v : Base P d => v.2.1) hz
  change z.1.1.2.1 = (ClockMainStateReadout.coordinates P hR hc hsmall clock label z.2).1 at he
  intro i
  dsimp only [ClockMainRmsData.direct,ClockMainStateReadout.direct]
  rw [← he]

private theorem pullback_bound {Ω B E : Type*} [MeasurableSpace Ω] [MeasurableSpace B]
    [NormedAddCommGroup E] [NormedSpace ℝ E] {μa : Measure Ω} {ν : Measure B}
    (f : Ω→B) (hp : MeasurePreserving f μa ν) (g : B→E) (hg : MemLp g 2 ν)
    (actual : Ω→E) (hae : actual =ᵐ[μa] g∘f) (R : ℝ) (hb : ‖hg.toLp g‖≤R) :
    ∃ h : MemLp actual 2 μa, ‖h.toLp actual‖≤R := by
  have ht := hg.comp_measurePreserving hp
  have ha := ht.ae_eq hae.symm
  refine ⟨ha,?_⟩
  rw [MemLp.toLp_congr ha ht hae,← Lp.toLp_compMeasurePreserving hg hp,Lp.norm_compMeasurePreserving]
  exact hb

/-- The initial error is paid on the SAME retained main-loop law. -/
theorem initial_bound (i : Index P) :
    ∃ h : MemLp (fun z : X => initial i z - (target i z+nu0 i z)) 2 lawM,
      ‖h.toLp (fun z : X => initial i z - (target i z+nu0 i z))‖≤ClockCollocation.rF P.delta*Real.sqrt (d:ℝ) := by
  apply pullback_bound (fun z : X => z.1.1) (base_preserving P hR hc hsmall clock label hK hC hy hV hm hlo hup hyMean)
    (ClockMainInitialEnergy.initialError P hV hm hlo hup clock i)
    (ClockMainInitialEnergy.initialError_memLp P hV hm hlo hup clock i)
  · filter_upwards [direct_eq_base_ae P hR hc hsmall clock label hK hC hy hV hm hlo hup hyMean] with z hz
    change (direct i z+nu0 i z)-(target i z+nu0 i z) = _
    rw [show (direct i z+nu0 i z)-(target i z+nu0 i z)=direct i z-target i z by abel,hz i]
    rfl
  · exact ClockMainInitialEnergy.initialError_norm_le P hV hm hlo hup clock i

/-- The actual row residual is the proved original-data quadrature defect. -/
theorem residual_bound (i : Index P) :
    ∃ h : MemLp (SharedLayerRms.residual direct (A P clock) reply target i) 2 lawM,
      ‖h.toLp (SharedLayerRms.residual direct (A P clock) reply target i)‖≤
      (ClockCollocation.rF P.delta/2)*ClockQuadraturePower.orderConstant P.K*Real.sqrt (d:ℝ)*P.delta^(P.K+6) := by
  apply pullback_bound (fun z : X => z.1.1) (base_preserving P hR hc hsmall clock label hK hC hy hV hm hlo hup hyMean)
    (ClockMainResidualEnergy.residual P hV hm hlo hup clock i)
    (ClockMainEnergyPayments.residual_memLp P hV hm hlo hup clock i)
  · filter_upwards [direct_eq_base_ae P hR hc hsmall clock label hK hC hy hV hm hlo hup hyMean] with z hz
    dsimp only [SharedLayerRms.residual,Function.comp_apply]
    rw [hz i,ClockMainPrimitiveResidual.residual_eq_primitive_graph]
    rfl
  · exact ClockMainEnergyPayments.residual_norm_le P hV hm hlo hup clock i (FinalMeanScheduledData.delta_half P hK hc hsmall hC hy)

/-- Exact finite child payment; it vanishes outside actual execution. -/
def childBudget (k : ℕ) (_i : Index P) : ℝ :=
  if k<P.K+4 then Real.sqrt ((4*sigma*P.delta^(P.K:ℝ))^2*(10*(d:ℝ))) else 0

/-- No current-call accuracy or moment assumption occurs in the finite RMS bound. -/
theorem iterate_error_bound :
    ∃ herr : ∀ k i, MemLp (err k i) 2 lawM,
      ∀ n, Collocation.rawNodeErrorNorm lawM (err n) (herr n) ≤
        ((2*P.delta)*a P)^n * Collocation.rawNodeErrorNorm lawM (err 0) (herr 0) +
          Collocation.forcingSum ((2*P.delta)*a P)
            (fun k => (ClockCollocation.rF P.delta/2)*ClockQuadraturePower.orderConstant P.K*Real.sqrt (d:ℝ)*P.delta^(P.K+6) +
              SharedLayerRms.childRowBudget (A P clock) (childBudget (d := d) P) k) n := by
  classical
  let resBudget := (ClockCollocation.rF P.delta/2)*ClockQuadraturePower.orderConstant P.K*Real.sqrt (d:ℝ)*P.delta^(P.K+6)
  have hinit : ∀ i, MemLp (fun z : X => initial i z-(target i z+nu0 i z)) 2 lawM :=
    fun i => (initial_bound P hR hc hsmall clock label hK hC hy hV hm hlo hup hyMean i).choose
  have hres : ∀ i, MemLp (SharedLayerRms.residual direct (A P clock) reply target i) 2 lawM :=
    fun i => (residual_bound P hR hc hsmall clock label hK hC hy hV hm hlo hup hyMean i).choose
  have hresBound i : ‖(hres i).toLp (SharedLayerRms.residual direct (A P clock) reply target i)‖≤resBudget :=
    (residual_bound P hR hc hsmall clock label hK hC hy hV hm hlo hup hyMean i).choose_spec
  have hchild : ∀ k i, MemLp (SharedLayerRms.childError eval Y reply sigma refs k i) 2 lawM := by
    intro k i
    by_cases hk : k<P.K+4
    · have hb := (ClockMainLoopChildRms.loop_child_error_bound P hR hc hsmall clock label hK hC hy hV hm hlo hup hyMean k hk i).choose
      have he : SharedLayerRms.childError eval Y reply sigma refs k i =
          ClockMainErrorHistory.stageError P hR hc hsmall clock label hV Hlo hup k hk i :=
        funext fun z => childError_eq P hR hc hsmall clock label hV Hlo hup k hk i z
      rwa [he]
    · have he : SharedLayerRms.childError eval Y reply sigma refs k i = 0 :=
        funext fun z => childError_after P hR hc hsmall clock label hV Hlo hup k (by omega) i z
      rw [he]
      exact MemLp.zero
  have hchildBound k i : ‖(hchild k i).toLp (SharedLayerRms.childError eval Y reply sigma refs k i)‖≤childBudget (d := d) P k i := by
    by_cases hk : k<P.K+4
    · obtain ⟨hmem,_,hb⟩ := ClockMainLoopChildRms.loop_child_error_bound P hR hc hsmall clock label hK hC hy hV hm hlo hup hyMean k hk i
      have he : SharedLayerRms.childError eval Y reply sigma refs k i =
          ClockMainErrorHistory.stageError P hR hc hsmall clock label hV Hlo hup k hk i :=
        funext fun z => childError_eq P hR hc hsmall clock label hV Hlo hup k hk i z
      simpa only [childBudget,ite_eq_left hk,he] using hb
    · have he : SharedLayerRms.childError eval Y reply sigma refs k i = 0 :=
        funext fun z => childError_after P hR hc hsmall clock label hV Hlo hup k (by omega) i z
      simp only [childBudget,ite_eq_right hk,he,MemLp.toLp_zero,norm_zero,le_refl]
  have hmeas k i : AEStronglyMeasurable (fun z : X => eval k i z
      (ClockMainRmsData.iterate P hR hc hsmall clock label hV Hlo hup k i z) - eval k i z (Y k i z)) lawM :=
    ((ClockMainRmsData.evaluator_measurable P hR hc hsmall clock label hV Hlo hup hK hC hy k i _
      (ClockMainRmsData.iterate_measurable P hR hc hsmall clock label hV Hlo hup hK hC hy k i)).sub
      (ClockMainRmsData.evaluator_measurable P hR hc hsmall clock label hV Hlo hup hK hC hy k i _
        (ClockMainRmsData.benchmark_measurable P hR hc hsmall clock label hV Hlo hup hK hC hy k i))).aestronglyMeasurable
  exact SharedLayerRms.iterate_error_bound direct target reply initial nu0 (A P clock) (C P clock) eval refs noise sigma lawM
    ⟨2*P.delta,mul_nonneg (show (0:ℝ)≤2 by norm_num) P.delta_pos.le⟩ (a P) resBudget (a_pos P).le
    (by exact mul_nonneg (mul_nonneg (mul_nonneg (div_nonneg (rF_pos P).le (by norm_num))
      (ClockQuadraturePower.orderConstant_nonneg P.K)) (Real.sqrt_nonneg _)) (pow_nonneg P.delta_pos.le _))
    (childBudget (d := d) P)
    (fun i => ClockCollocation.sum_abs_matrix_le_quarter P.delta P.delta_pos P.K clock (0:ℝ) 0 i)
    (ClockMainRmsData.evaluator_lipschitz P hR hc hsmall clock label hV Hlo hup hK hC hy)
    hmeas hinit hres hresBound hchild hchildBound

/-- Literal finite budget, including the actual source order constant. -/
def budget : ℝ :=
  ((2*P.delta)*a P)^(P.K+4) * (ClockCollocation.rF P.delta*Real.sqrt (d:ℝ)) +
    Collocation.forcingSum ((2*P.delta)*a P)
      (fun k => (ClockCollocation.rF P.delta/2)*ClockQuadraturePower.orderConstant P.K*
        Real.sqrt (d:ℝ)*P.delta^(P.K+6) +
        SharedLayerRms.childRowBudget (A P clock) (childBudget (d := d) P) k) (P.K+4)

theorem budget_nonneg : 0≤budget (d := d) P clock := by
  unfold budget Collocation.forcingSum
  apply add_nonneg
  · exact mul_nonneg (pow_nonneg (mul_nonneg (mul_nonneg (show (0:ℝ)≤2 by norm_num) P.delta_pos.le) (a_pos P).le) _)
      (mul_nonneg (rF_pos P).le (Real.sqrt_nonneg _))
  · apply Finset.sum_nonneg
    intro k _
    apply mul_nonneg (pow_nonneg (mul_nonneg (mul_nonneg (show (0:ℝ)≤2 by norm_num) P.delta_pos.le) (a_pos P).le) _)
    exact add_nonneg
      (mul_nonneg (mul_nonneg (mul_nonneg (div_nonneg (rF_pos P).le (by norm_num))
        (ClockQuadraturePower.orderConstant_nonneg P.K)) (Real.sqrt_nonneg _)) (pow_nonneg P.delta_pos.le _))
      (norm_nonneg _)

/-- All finite numerical inputs have been paid internally on the actual kernel. -/
theorem closed_iterate_error_bound :
    ∃ herr : ∀ i, MemLp (err (P.K+4) i) 2 lawM,
      Collocation.rawNodeErrorNorm lawM (err (P.K+4)) herr ≤ budget (d := d) P clock := by
  obtain ⟨herr,hbound⟩ := iterate_error_bound P hR hc hsmall clock label hK hC hy hV hm hlo hup hyMean
  have h0 : Collocation.rawNodeErrorNorm lawM (err 0) (herr 0) ≤ ClockCollocation.rF P.delta*Real.sqrt (d:ℝ) := by
    apply (pi_norm_le_iff_of_nonneg (mul_nonneg (rF_pos P).le (Real.sqrt_nonneg _))).2
    intro i
    exact (initial_bound P hR hc hsmall clock label hK hC hy hV hm hlo hup hyMean i).choose_spec
  refine ⟨herr (P.K+4),?_⟩
  unfold budget
  exact (hbound (P.K+4)).trans (add_le_add
    (mul_le_mul_of_nonneg_left h0 (pow_nonneg (mul_nonneg (mul_nonneg (show (0:ℝ)≤2 by norm_num) P.delta_pos.le) (a_pos P).le) (P.K+4))) le_rfl)

/-- Error of the literal reached source state against its retained Gaussian center. -/
def stateError (i : Index P) (z : X) : Point d :=
  storedPoint (ClockMainStateReadout.state P hR hc hsmall clock label (gradient V) z.1.1.1.1 z.1.1.1.2 z.2).env
    ((ClockMainStateReadout.state P hR hc hsmall clock label (gradient V) z.1.1.1.1 z.1.1.1.2 z.2).old i) -
  (target i z + rhoC P • z.1.2.2 i)

theorem stateError_eq_ae : ∀ᵐ z ∂lawM, ∀ i,
    stateError P hR hc hsmall clock label hV hm hlo hup i z = err (P.K+4) i z := by
  filter_upwards [ClockChronologicalBenchmark.kernel_benchmark_ae P hR hc hsmall clock label hK hC hy hV Hlo hup hyMean
    target (sourceLaw P hR hc hsmall clock label hV hm hlo hup)] with z hz
  intro i
  unfold stateError ClockMainRmsData.error
  rw [ClockMainRmsData.state_eq_iterate P hR hc hsmall clock label hV Hlo hup,← hz i]
  rfl

/-- Actual stored centers satisfy the closed bound on the constructed whole-tape law. -/
theorem state_error_bound :
    ∃ hstate : ∀ i, MemLp (stateError P hR hc hsmall clock label hV hm hlo hup i) 2 lawM,
      Collocation.rawNodeErrorNorm lawM (stateError P hR hc hsmall clock label hV hm hlo hup) hstate ≤ budget (d := d) P clock := by
  obtain ⟨herr,hbound⟩ := closed_iterate_error_bound P hR hc hsmall clock label hK hC hy hV hm hlo hup hyMean
  have hae i : stateError P hR hc hsmall clock label hV hm hlo hup i =ᵐ[lawM] err (P.K+4) i :=
    (stateError_eq_ae P hR hc hsmall clock label hK hC hy hV hm hlo hup hyMean).mono fun z hz => hz i
  have hs i := (herr i).ae_eq (hae i).symm
  refine ⟨hs,?_⟩
  have he : (fun i => (hs i).toLp (stateError P hR hc hsmall clock label hV hm hlo hup i)) =
      (fun i => (herr i).toLp (err (P.K+4) i)) :=
    funext fun i => MemLp.toLp_congr (hs i) (herr i) (hae i)
  change ‖fun i => (hs i).toLp (stateError P hR hc hsmall clock label hV hm hlo hup i)‖≤_
  rw [he]
  exact hbound

/-- Each executed node has both L2 and square-energy bounds, with no supplied accuracy. -/
theorem node_error_bound (i : Index P) :
    ∃ h : MemLp (stateError P hR hc hsmall clock label hV hm hlo hup i) 2 lawM,
      ‖h.toLp (stateError P hR hc hsmall clock label hV hm hlo hup i)‖≤budget (d := d) P clock ∧
      (∫ z,‖stateError P hR hc hsmall clock label hV hm hlo hup i z‖^2 ∂lawM)≤(budget (d := d) P clock)^2 := by
  obtain ⟨hs,hbound⟩ := state_error_bound P hR hc hsmall clock label hK hC hy hV hm hlo hup hyMean
  have hi := (norm_le_pi_norm (fun j => (hs j).toLp (stateError P hR hc hsmall clock label hV hm hlo hup j)) i).trans hbound
  refine ⟨hs i,hi,?_⟩
  rw [← Analysis.DominatedLp.norm_sq_toLp (hs i)]
  exact (sq_le_sq₀ (norm_nonneg _) (budget_nonneg (d := d) P clock)).2 hi

end AcceleratedLogConcave.Root.ClockMainRms
