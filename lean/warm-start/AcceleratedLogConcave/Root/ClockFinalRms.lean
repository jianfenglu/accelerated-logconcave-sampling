import AcceleratedLogConcave.Root.ClockMainTerminalState
import AcceleratedLogConcave.Root.ClockMainRmsPayment
import AcceleratedLogConcave.Root.ClockFinalQuadrature
import AcceleratedLogConcave.Oracle.ReplaySeedMeasurability

/-! Actual final-child RMS on the constructed completed Clock law. Every
callback keeps the literal designated seed; only its evaluated center moves. -/
noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
namespace AcceleratedLogConcave.Root.ClockFinalRms
open Oracle Oracle.AffineLowering Oracle.TapeLowering Oracle.NoisyLayer
open Oracle.CanonicalTapeLaw Oracle.CanonicalTapeMeasurability Oracle.ReplaySeedMeasurability
open Oracle.TailOccurrenceCut Oracle.TailOccurrenceCut.TailCut
open ClockChronologicalCoupling ClockNoisyLayer Numerics
local instance canonicalTapeSpace {d c : ℕ} {Γ : Ctx} {τ : Ty} (p : Prog c Γ τ) :
    MeasurableSpace (Tape d p) := tapeSpace d p
local instance canonicalResidualSpace {c : ℕ} (p : Program c .point) :
    MeasurableSpace (ResidualTape p) := residualSpace p
local instance canonicalPrefixSpace {d c : ℕ} {Γ Δ : Ctx} {τ σ : Ty}
    {p : Prog c Γ τ} {q : Prog c Δ σ} (cut : TailCut q p) :
    MeasurableSpace (Prefix d cut) := prefixSpace d cut
variable (P : SourceSchedule) (hR : P.R≤1/2) (hc : 0<P.csch) (hsmall : P.csch<1/160)
  (clock : ClockLaw.Clock) (label : ℕ) (hK : 10≤P.K) (hC : 8≤P.Csch)
  (hy : CubicScheduleThreshold.threshold P≤P.y)
  {d : ℕ} {V : Point d→ℝ} (hV : ContDiff ℝ 2 V) {m : ℝ} (hm : 0<m)
  (hlo : ∀ z v,m*‖v‖^2≤fderiv ℝ (fderiv ℝ V) z v v)
  (hup : ∀ z v,fderiv ℝ (fderiv ℝ V) z v v≤‖v‖^2)
  (hyMean : MeanSourceScalarAbsorption.threshold P≤P.y)
local notation "Hlo" => OuterRootFlowIdentification.lower_nonneg hm hlo
local notation "host" => Host P hR hc hsmall clock label
local notation "X" => History P d × Tape d host
local notation "W" => X × (Index P→Point d)
local notation "batch" => ClockFinalBatchCoupling.data P hR hc hsmall clock label hK hC hy
local notation "cut" => ClockFinalBatchCoupling.batchCut P hR hc hsmall clock label hK hC hy
local notation "Eactual" => ClockFinalEvaluator.actualCenter P hR hc hsmall clock label hK hC hy (gradient V)
local notation "Ebench" => ClockFinalEvaluator.benchmarkCenter P hR hc hsmall clock label hV hup hm hlo
local notation "eval" => ClockFinalEvaluator.evaluator P hR hc hsmall clock label hK hC hy (gradient V)
local notation "err" => ClockFinalEvaluator.finalError P hR hc hsmall clock label hV hup hm hlo
local notation "benchErr" => ClockFinalChildRms.benchmarkError P hR hc hsmall clock label hK hC hy hV hm hlo hup

/-- The actual completed kernel acts on the untouched original full source law. -/
def law : Measure W :=
  ClockFinalBatchCoupling.completedKernel P hR hc hsmall clock label hK hC hy hV Hlo hup hyMean ∘ₘ
    ClockMainRms.sourceLaw P hR hc hsmall clock label hV hm hlo hup
local notation "lawF" => law P hR hc hsmall clock label hK hC hy hV hm hlo hup hyMean

theorem original_preserving : MeasurePreserving (Prod.fst : W→X) lawF
    (ClockMainRms.law P hR hc hsmall clock label hK hC hy hV hm hlo hup hyMean) := by
  refine ⟨measurable_fst,?_⟩
  rw [law,ClockFinalBatchCoupling.completedKernel,← Measure.comp_assoc,
    Measure.map_comp _ _ measurable_fst,← Kernel.fst_eq,
    ClockFinalBatchCoupling.original_preserved,Measure.id_comp]
  rfl

include hV in
private theorem store_measurable (q : Ref (terminalCursor P hR hc hsmall clock label).ctx .point) :
    Measurable (fun z : X => storedPoint
      (ClockFinalEvaluator.store P hR hc hsmall clock label hK hC hy (gradient V) z) q) := by
  have hs := ((measurePreserving_split (Probability.CanonicalNativeTapeLaw.primitiveLaws d) cut).measurable.comp
    (measurable_snd : Measurable (Prod.snd : X→_))).fst
  have he : OperationalMeasurability.EnvPathMeasurable (fun _ : X => (Env.empty : Env d [])) := by
    intro ty ref
    cases ref
  exact envAt_pathMeasurable (gradient V) (ClockOriginalGradientKernel.originalGradient_measurable hV) cut
    (ClockFinalEvaluator.input P hR hc hsmall clock label) (fun _ : X => Env.empty)
    (fun z : X => (split cut z.2).1) (fun _ => measurable_const)
    (by unfold ClockFinalEvaluator.input; fun_prop) (by unfold ClockFinalEvaluator.input; fun_prop)
    he hs q

include hV in
/-- Joint candidate measurability for the literal same-seed final evaluator. -/
theorem evaluator_measurable (i : Index P) (candidate : X→Point d) (hymeas : Measurable candidate) :
    Measurable (fun z : X => eval i z (candidate z)) := by
  have ht := ((measurable_pi_apply i).comp
    ((measurePreserving_split (Probability.CanonicalNativeTapeLaw.primitiveLaws d) cut).measurable.comp
      (measurable_snd : Measurable (Prod.snd : X→_))).snd.fst)
  have hu := (DesignatedChildAbsorbedLaw.tapeSeed_preserving
    (Probability.CanonicalNativeTapeLaw.primitiveLaws d) ((batch).child i).program ((batch).child i).enumeration
    ((batch).slot i) ((batch).old i) ((batch).designated i) ((batch).auxiliary i)).measurable.comp ht
  have hP := store_measurable P hR hc hsmall clock label hK hC hy hV ((batch).designated i)
  have hseed := (measurable_transformedSeed (d := d) ((batch).child i).program ((batch).child i).enumeration
    (CovarianceSetup.childRoot ((batch).rho i) ((batch).radius i) ((batch).child i).shiftVector)).comp
    (hP.prodMk hu)
  exact program_point_of_measurable ((batch).child i).program (gradient V)
    (ClockOriginalGradientKernel.originalGradient_measurable hV)
    (fun _ => ((batch).child i).coefficient) candidate
    (fun z => ClockFinalEvaluator.designated P hR hc hsmall clock label hK hC hy (gradient V) i z)
    (fun z => (transformedSeed ((batch).child i).program ((batch).child i).enumeration
      (CovarianceSetup.childRoot ((batch).rho i) ((batch).radius i) ((batch).child i).shiftVector)
      (ClockFinalEvaluator.designated P hR hc hsmall clock label hK hC hy (gradient V) i z,
        ClockFinalEvaluator.seed P hR hc hsmall clock label hK hC hy i z)).2)
    measurable_const hymeas hP hseed.snd

include hV in
theorem actualCenter_measurable (i : Index P) : Measurable (Eactual i) :=
  store_measurable P hR hc hsmall clock label hK hC hy hV ((terminalCursor P hR hc hsmall clock label).old i)

theorem benchmarkCenter_measurable (i : Index P) : Measurable (Ebench i) :=
  ((center_measurable P clock hV Hlo hup i).comp measurable_fst.fst).add
    (((measurable_pi_apply i).comp measurable_fst.snd.snd).const_smul (rhoC P))

/-- Final augmentation copies the original main-state error, including its complete tape. -/
theorem center_error_bound (i : Index P) :
    ∃ h : MemLp (fun z : W => Eactual i z.1-Ebench i z.1) 2 lawF,
      ‖h.toLp (fun z : W => Eactual i z.1-Ebench i z.1)‖≤ClockMainRms.budget (d := d) P clock := by
  obtain ⟨hmem,hbound,_⟩ := ClockMainRms.node_error_bound P hR hc hsmall clock label hK hC hy hV hm hlo hup hyMean i
  have hp := original_preserving P hR hc hsmall clock label hK hC hy hV hm hlo hup hyMean
  have hmapped := hmem.comp_measurePreserving hp
  have he : (fun z : W => Eactual i z.1-Ebench i z.1) =
      ClockMainRms.stateError P hR hc hsmall clock label hV hm hlo hup i ∘ Prod.fst := by
    funext z
    rw [ClockMainTerminalState.actualCenter_eq_state P hR hc hsmall clock label hK hC hy]
    rfl
  have hae : (fun z : W => Eactual i z.1-Ebench i z.1) =ᵐ[lawF]
      ClockMainRms.stateError P hR hc hsmall clock label hV hm hlo hup i ∘ Prod.fst :=
    Filter.Eventually.of_forall (congrFun he)
  have ha := hmapped.ae_eq hae.symm
  refine ⟨ha,?_⟩
  rw [MemLp.toLp_congr ha hmapped hae,← Lp.toLp_compMeasurePreserving hmem hp,Lp.norm_compMeasurePreserving]
  exact hbound

/-- Both the genuine main-state movement and the actual lower final error are paid. -/
theorem final_error_bound (i : Index P) :
    ∃ h : MemLp (err i) 2 lawF,
      ‖h.toLp (err i)‖≤2*P.delta*ClockMainRms.budget (d := d) P clock +
        Real.sqrt ((4*ClockRetainedFinalSplice.width P clock i*P.delta^(P.K:ℝ))^2*(10*(d:ℝ))) := by
  let D := fun z : W => Eactual i z.1-Ebench i z.1
  let move := fun z : W => eval i z.1 (Eactual i z.1)-eval i z.1 (Ebench i z.1)
  obtain ⟨hD,hDb⟩ := center_error_bound P hR hc hsmall clock label hK hC hy hV hm hlo hup hyMean i
  obtain ⟨hb,_,hbb⟩ := ClockFinalChildRms.benchmark_error_bound P hR hc hsmall clock label hK hC hy hV hm hlo hup hyMean i
  have hmeas : AEStronglyMeasurable move lawF :=
    (((evaluator_measurable P hR hc hsmall clock label hK hC hy hV i _
      (actualCenter_measurable P hR hc hsmall clock label hK hC hy hV i)).comp measurable_fst).sub
      ((evaluator_measurable P hR hc hsmall clock label hK hC hy hV i _
        (benchmarkCenter_measurable P hR hc hsmall clock label hV hm hlo hup i)).comp measurable_fst)).aestronglyMeasurable
  have hstable (z : W) : LipschitzWith ⟨2*P.delta,mul_nonneg (by norm_num) P.delta_pos.le⟩ (eval i z.1) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    change ‖eval i z.1 x-eval i z.1 y‖≤2*P.delta*‖x-y‖
    exact ClockFinalEvaluator.evaluator_sub_le P hR hc hsmall clock label hK hC hy hV Hlo hup i z.1 x y
  have hmove : MemLp move 2 lawF := SharedLayerRms.memLp_fixedTape_sub
    (fun z : W => eval i z.1) (fun z : W => Eactual i z.1) (fun z : W => Ebench i z.1)
    ⟨2*P.delta,mul_nonneg (by norm_num) P.delta_pos.le⟩ hstable hmeas hD
  have hmb := SharedLayerRms.norm_toLp_fixedTape_sub_le
    (fun z : W => eval i z.1) (fun z : W => Eactual i z.1) (fun z : W => Ebench i z.1)
    ⟨2*P.delta,mul_nonneg (by norm_num) P.delta_pos.le⟩ hstable hD hmove
  have he : err i=move+benchErr i := by
    funext z
    dsimp only [Pi.add_apply,move,ClockFinalEvaluator.finalError]
    rw [ClockFinalEvaluator.finalReply_eq_evaluator P hR hc hsmall clock label hK hC hy,
      ClockFinalEvaluator.benchmarkError_eq_evaluator P hR hc hsmall clock label hK hC hy]
    module
  have hae : err i =ᵐ[lawF] move+benchErr i := Filter.Eventually.of_forall (congrFun he)
  have hout := (hmove.add hb).ae_eq hae.symm
  refine ⟨hout,?_⟩
  rw [MemLp.toLp_congr hout (hmove.add hb) hae,MemLp.toLp_add hmove hb]
  exact (norm_add_le _ _).trans (add_le_add (hmb.trans
    (mul_le_mul_of_nonneg_left hDb (mul_nonneg (by norm_num) P.delta_pos.le))) hbb)
end AcceleratedLogConcave.Root.ClockFinalRms
