import AcceleratedLogConcave.Root.ClockMainErrorTransport
import AcceleratedLogConcave.Root.ClockChronologicalPast
import AcceleratedLogConcave.Root.ClockChronologicalBenchmark
import AcceleratedLogConcave.Root.ClockMainReadout
import AcceleratedLogConcave.Root.ClockOriginalGradientKernel

/-! Exact error distribution of the actual main callback at the source
Gaussian benchmark. Its full completed lower seed and original tape are kept. -/
noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
namespace AcceleratedLogConcave.Root.ClockMainErrorHistory
open Oracle Oracle.AffineLowering Oracle.TapeLowering Oracle.NoisyLayer
open Oracle.RecursiveMeanProgram Oracle.RecursiveMeanContinuation
open Oracle.TailOccurrenceCut Oracle.PrivateCausalLayer Oracle.PrivateCausalAdvance
open TailCut Oracle.CanonicalTapeMeasurability Oracle.CanonicalTapeLaw
open ClockChronologicalCoupling ClockChronologicalLowerProjection ClockNoisyLayer
local instance canonicalTapeSpace {d c : ℕ} {Γ : Ctx} {τ : Ty} (p : Prog c Γ τ) :
    MeasurableSpace (Tape d p) := tapeSpace d p
variable (P : SourceSchedule) (hR : P.R≤1/2) (hc : 0<P.csch) (hsmall : P.csch<1/160)
  (clock : ClockLaw.Clock) (label : ℕ) (hK : 10≤P.K) (hC : 8≤P.Csch)
  (hy : CubicScheduleThreshold.threshold P≤P.y)
  {d : ℕ} {V : Point d→ℝ} (hV : ContDiff ℝ 2 V)
  (hlo : ∀ z v,0≤fderiv ℝ (fderiv ℝ V) z v v)
  (hup : ∀ z v,fderiv ℝ (fderiv ℝ V) z v v≤‖v‖^2)
  (hyMean : MeanSourceScalarAbsorption.threshold P≤P.y)
local notation "Xmain" => History P d × Tape d (Host P hR hc hsmall clock label)
local notation "F" => scaledPotential V (Real.sqrt P.delta)
local notation "sigma" => CovarianceSetup.sigma (N P) (rhoC P) (a P)

open ClockMainErrorTransport
local instance tape_probability {c : ℕ} {Γ : Ctx} {τ : Ty} (p : Prog c Γ τ) :
    IsProbabilityMeasure (tapeLaw (Probability.CanonicalNativeTapeLaw.primitiveLaws d) p) := tapeLaw_probability _ _
def stageError (k : ℕ) (hk : k<(P.K+4)) (i : Index P) (z : Xmain) : Point d :=
  ClockMainReadout.evaluator P hR hc hsmall clock label (gradient V)
    (fun _ _ => 0) k i z.2
      (center P clock hV hlo hup i z.1.1 + (rhoC P) • ClockChronologicalBenchmark.comparisonNoise P hR hc hsmall clock label k hk.le z i) -
    Gibbs.primitiveMean (scaledPotential V (Real.sqrt P.delta)) (center P clock hV hlo hup i z.1.1) (radius P clock i) -
      (CovarianceSetup.sigma (N P) (rhoC P) (a P)) • ClockChronologicalBenchmark.returnedReference P hR hc hsmall clock label k i z

private theorem comparison_record (k : ℕ) (hk : k<(P.K+4)) (z : Xmain × (Index P → Point d)) :
    ClockChronologicalBenchmark.comparisonNoise P hR hc hsmall clock label k hk.le
      (record P hR hc hsmall clock label hK hC hy
        (stage P hR hc hsmall clock label k hk.le).1
        (stage_positive P hR hc hsmall clock label k hk) ⟨k,hk⟩ z) =
    ClockChronologicalBenchmark.comparisonNoise P hR hc hsmall clock label k hk.le z.1 := by
  cases k with
  | zero => rfl
  | succ k =>
    dsimp only [ClockChronologicalBenchmark.comparisonNoise,record]
    rw [Function.update_of_ne]
    intro he
    have hh := congrArg Fin.val he
    change k = k+1 at hh
    omega

theorem stageError_record (k : ℕ) (hk : k<(P.K+4)) (i : Index P) (z : Xmain × (Index P → Point d))
    (hcomparison : z.1.1.2.2 = ClockChronologicalBenchmark.comparisonNoise P hR hc hsmall clock label k hk.le z.1) :
    stageError P hR hc hsmall clock label hV hlo hup k hk i
      (record P hR hc hsmall clock label hK hC hy
        (stage P hR hc hsmall clock label k hk.le).1
        (stage_positive P hR hc hsmall clock label k hk) ⟨k,hk⟩ z) =
    benchmarkError P hR hc hsmall clock label hV hlo hup k i z := by
  unfold stageError
  rw [comparison_record P hR hc hsmall clock label hK hC hy k hk z,← hcomparison]
  simp only [ClockChronologicalBenchmark.returnedReference,dite_eq_left hk,record,Function.update_self]
  rfl

include hK hC hy in
theorem stageError_measurable (k : ℕ) (hk : k<P.K+4) (i : Index P) :
    Measurable (stageError P hR hc hsmall clock label hV hlo hup k hk i) := by
  have hcenter := (center_measurable P clock hV hlo hup i).comp
    (measurable_fst.fst : Measurable (fun z : Xmain => z.1.1))
  have hn := (measurable_pi_apply i).comp
    (ClockChronologicalBenchmark.comparisonNoise_measurable (d := d) P hR hc hsmall clock label hK hC hy k hk.le)
  have hF : ContDiff ℝ 2 (scaledPotential V (Real.sqrt P.delta)) :=
    hV.comp (contDiff_id.const_smul (Real.sqrt P.delta))
  have hu := (Gibbs.primitive_mean_lipschitz hF P.delta_pos.le
    (ClockMeanChildAccuracy.scaled_hessian_nonneg P hV hlo)
    (ClockMeanChildAccuracy.scaled_hessian_upper P hV hup) (radius_pos P clock i)).continuous.measurable.comp hcenter
  have hp := ClockMainReadout.evaluator_measurable P hR hc hsmall clock label hK hC hy
    (gradient V) (ClockOriginalGradientKernel.originalGradient_measurable hV) (fun _ _ => 0)
    k hk i (fun z : Xmain => z.2) measurable_snd
    (fun z : Xmain => center P clock hV hlo hup i z.1.1 + rhoC P •
      ClockChronologicalBenchmark.comparisonNoise P hR hc hsmall clock label k hk.le z i)
    (hcenter.add (hn.const_smul (rhoC P)))
  exact (hp.sub hu).sub ((ClockChronologicalBenchmark.returnedReference_measurable
    P hR hc hsmall clock label k i).const_smul sigma)

/-- The error immediately after its actual child executes has exactly the
lower-call retained error law, using only almost-everywhere benchmark support. -/
theorem stage_error_law (νInput : Measure (Point d × Point d)) [IsProbabilityMeasure νInput] (k : ℕ) (hk : k<(P.K+4)) (i : Index P)
 :
    (stageLaw P hR hc hsmall clock label hK hC hy hV hlo hup hyMean (νInput.prod (tapeLaw (Probability.CanonicalNativeTapeLaw.primitiveLaws d) (Host P hR hc hsmall clock label))) (k+1) (by omega)).map
      (stageError P hR hc hsmall clock label hV hlo hup k hk i) =
    ((νInput.prod ((stdGaussian (Point d)).prod (Measure.pi fun _ : Index P => stdGaussian (Point d)))) ⊗ₘ ((lower P hR hc hsmall clock label hK hC hy hV hlo hup hyMean (stage P hR hc hsmall clock label k hk.le).1 (stage_positive P hR hc hsmall clock label k hk)).joint i).comap (center P clock hV hlo hup i) (center_measurable P clock hV hlo hup i)).map
      (lowerError P hR hc hsmall clock hV hlo hup i) := by
  let s := (stage P hR hc hsmall clock label k hk.le).1
  let hs := stage_positive P hR hc hsmall clock label k hk
  let oldLaw := stageLaw P hR hc hsmall clock label hK hC hy hV hlo hup hyMean (νInput.prod (tapeLaw (Probability.CanonicalNativeTapeLaw.primitiveLaws d) (Host P hR hc hsmall clock label))) k hk.le
  let adjoined := adjoin P hR hc hsmall clock label hK hC hy hV hlo hup hyMean s hs  ∘ₘ oldLaw
  let recordFn := record (d := d) P hR hc hsmall clock label hK hC hy s hs ⟨k,hk⟩
  let err := stageError P hR hc hsmall clock label hV hlo hup k hk i
  have hrm : Measurable recordFn := record_measurable P hR hc hsmall clock label hK hC hy s hs ⟨k,hk⟩
  have hem : Measurable err := stageError_measurable P hR hc hsmall clock label hK hC hy hV hlo hup k hk i
  have hfst : MeasurePreserving (Prod.fst : Xmain × (Index P → Point d) → Xmain) adjoined oldLaw := by
    refine ⟨measurable_fst,?_⟩
    rw [Measure.map_comp _ _ measurable_fst,← Kernel.fst_eq,adjoin_original,Measure.id_comp]
  have hcomparisonEvent := hfst.quasiMeasurePreserving.ae
    (ClockChronologicalBenchmark.iteration_comparisonNoise_ae P hR hc hsmall clock label hK hC hy hV hlo hup hyMean k hk.le (νInput.prod (tapeLaw (Probability.CanonicalNativeTapeLaw.primitiveLaws d) (Host P hR hc hsmall clock label))))
  have hae : err ∘ recordFn =ᵐ[adjoined]
      benchmarkError P hR hc hsmall clock label hV hlo hup k i := by
    filter_upwards [hcomparisonEvent] with z hz
    exact stageError_record P hR hc hsmall clock label hK hC hy hV hlo hup k hk i z hz
  have hstage : stageLaw P hR hc hsmall clock label hK hC hy hV hlo hup hyMean (νInput.prod (tapeLaw (Probability.CanonicalNativeTapeLaw.primitiveLaws d) (Host P hR hc hsmall clock label))) (k+1) (by omega) = adjoined.map recordFn := by
    unfold stageLaw
    rw [iteration,← Measure.comp_assoc]
    exact (Measure.map_comp oldLaw _ hrm).symm
  rw [hstage,Measure.map_map hem hrm,Measure.map_congr hae]
  exact benchmark_error_law P hR hc hsmall clock label hK hC hy hV hlo hup hyMean νInput k hk i


/-- Original source and the recorded finite reference prefix, with no loss of
uniform, Gaussian, or residual coordinates. -/
abbrev PastSample (k : ℕ) :=
  ((Base P d ×
    Tape d (Host P hR hc hsmall clock label)) × (Fin k → Index P → Point d))

def restorePast (k : ℕ) (_hk : k≤(P.K+4))
    (z : PastSample (d := d) P hR hc hsmall clock label k) : Xmain :=
  ((z.1.1,((fun j => if hj : (j:ℕ)<k then z.2 ⟨j,hj⟩ else 0),fun _ => 0)),z.1.2)

theorem restorePast_measurable (k : ℕ) (hk : k≤(P.K+4)) :
    Measurable (restorePast (d := d) P hR hc hsmall clock label k hk) := by
  have href : Measurable (fun z : PastSample (d := d) P hR hc hsmall clock label k =>
      fun j : Fin (P.K+4) => if hj : (j:ℕ)<k then z.2 ⟨j,hj⟩ else (0 : Index P → Point d)) := by
    apply Measurable.of_eval
    intro j
    by_cases hj : (j:ℕ)<k
    · simp only [dite_eq_left hj]
      exact (measurable_pi_apply (⟨j,hj⟩ : Fin k)).comp measurable_snd
    · simp only [dite_eq_right hj]
      exact measurable_const
  exact (measurable_fst.fst.prodMk (href.prodMk measurable_const)).prodMk measurable_fst.snd

theorem restorePast_reference (k : ℕ) (hk : k≤(P.K+4)) (j : ℕ) (hj : j<k) (i : Index P) (z : Xmain) :
    ClockChronologicalBenchmark.returnedReference P hR hc hsmall clock label j i
      (restorePast P hR hc hsmall clock label k hk
        (ClockChronologicalPast.past P hR hc hsmall clock label k hk z)) =
    ClockChronologicalBenchmark.returnedReference P hR hc hsmall clock label j i z := by
  simp only [ClockChronologicalBenchmark.returnedReference,dite_eq_left (lt_of_lt_of_le hj hk),
    restorePast,ClockChronologicalPast.past,dite_eq_left hj]

theorem restorePast_comparison (k : ℕ) (hk : k≤(P.K+4)) (j : ℕ) (hj : j≤k) (z : Xmain) :
    ClockChronologicalBenchmark.comparisonNoise P hR hc hsmall clock label j (hj.trans hk)
      (restorePast P hR hc hsmall clock label k hk
        (ClockChronologicalPast.past P hR hc hsmall clock label k hk z)) =
    ClockChronologicalBenchmark.comparisonNoise P hR hc hsmall clock label j (hj.trans hk) z := by
  cases j with
  | zero => rfl
  | succ j =>
    simp only [ClockChronologicalBenchmark.comparisonNoise,restorePast,
      ClockChronologicalPast.past,dite_eq_left (show j<k by omega)]

theorem restorePast_error (k : ℕ) (hk : k<(P.K+4)) (i : Index P) (z : Xmain) :
    stageError P hR hc hsmall clock label hV hlo hup k hk i
      (restorePast P hR hc hsmall clock label (k+1) (by omega)
        (ClockChronologicalPast.past P hR hc hsmall clock label (k+1) (by omega) z)) =
    stageError P hR hc hsmall clock label hV hlo hup k hk i z := by
  unfold stageError
  rw [restorePast_comparison P hR hc hsmall clock label (k+1) (by omega) k (by omega),
    restorePast_reference P hR hc hsmall clock label (k+1) (by omega) k (by omega)]
  rfl

/-- Every later actual main extension preserves this child's complete error
law, jointly retaining all source coordinates used in its evaluation. -/
theorem loop_error_law (νInput : Measure (Point d × Point d)) [IsProbabilityMeasure νInput] (k : ℕ) (hk : k<(P.K+4)) (i : Index P) :
    (kernel P hR hc hsmall clock label hK hC hy hV hlo hup hyMean ∘ₘ (νInput.prod (tapeLaw (Probability.CanonicalNativeTapeLaw.primitiveLaws d) (Host P hR hc hsmall clock label)))).map
      (stageError P hR hc hsmall clock label hV hlo hup k hk i) =
    (stageLaw P hR hc hsmall clock label hK hC hy hV hlo hup hyMean (νInput.prod (tapeLaw (Probability.CanonicalNativeTapeLaw.primitiveLaws d) (Host P hR hc hsmall clock label))) (k+1) (by omega)).map
      (stageError P hR hc hsmall clock label hV hlo hup k hk i) := by
  let err := stageError P hR hc hsmall clock label hV hlo hup k hk i
  let read := err ∘ restorePast P hR hc hsmall clock label (k+1) (by omega)
  have hem : Measurable err := stageError_measurable P hR hc hsmall clock label hK hC hy hV hlo hup k hk i
  have hrm : Measurable read := hem.comp (restorePast_measurable P hR hc hsmall clock label (k+1) (by omega))
  have hp := ClockChronologicalPast.past_measurable (d := d) P hR hc hsmall clock label (k+1) (by omega)
  have h := congrArg (fun ν => ν.map read)
    (ClockChronologicalPast.kernel_past P hR hc hsmall clock label hK hC hy hV hlo hup hyMean (k+1) (by omega) (νInput.prod (tapeLaw (Probability.CanonicalNativeTapeLaw.primitiveLaws d) (Host P hR hc hsmall clock label))))
  rw [Measure.map_map hrm hp,Measure.map_map hrm hp] at h
  have he : read ∘ ClockChronologicalPast.past P hR hc hsmall clock label (k+1) (by omega) = err := by
    funext z
    exact restorePast_error P hR hc hsmall clock label hV hlo hup k hk i z
  rw [he] at h
  exact h

end AcceleratedLogConcave.Root.ClockMainErrorHistory
