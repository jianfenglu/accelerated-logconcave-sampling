import AcceleratedLogConcave.Root.ClockChronologicalLowerProjection
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
namespace AcceleratedLogConcave.Root.ClockMainErrorTransport
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
local notation "X" => History P d × Tape d (Host P hR hc hsmall clock label)
local notation "F" => scaledPotential V (Real.sqrt P.delta)
local notation "sigma" => CovarianceSetup.sigma (N P) (rhoC P) (a P)

def lowerError (i : Index P)
    (z : Base P d × ((Point d × Tape d (child P hR hc hsmall clock i).program) × Point d)) : Point d :=
  FreshChildRunShift.lowerError (child P hR hc hsmall clock i).program (gradient V)
    (coeff P hR hc hsmall clock i) (center P clock hV hlo hup i z.1)
    (Gibbs.primitiveMean F (center P clock hV hlo hup i z.1) (radius P clock i)) sigma z.2

def benchmarkError (k : ℕ) (i : Index P) (z : X × (Index P → Point d)) : Point d :=
  ClockMainReadout.evaluator P hR hc hsmall clock label (gradient V) (fun _ _ => 0)
    k i z.1.2 (center P clock hV hlo hup i z.1.1.1 + rhoC P • z.1.1.2.2 i) -
      Gibbs.primitiveMean F (center P clock hV hlo hup i z.1.1.1) (radius P clock i) - sigma • z.2 i

/-- Deterministic completed-source absorption for the exact scheduled child,
with its actual table, designated input and entire mixed tape. -/
theorem benchmarkError_eq_lowerError (k : ℕ) (hk : k<P.K+4) (i : Index P)
    (z : X × (Index P → Point d)) :
    benchmarkError P hR hc hsmall clock label hV hlo hup k i z =
      lowerError P hR hc hsmall clock hV hlo hup i
        (mainLowerProjection P hR hc hsmall clock label hK hC hy k hk i z) := by
  let s := (stage P hR hc hsmall clock label k hk.le).1
  let hs := stage_positive P hR hc hsmall clock label k hk
  let B := data P hR hc hsmall clock label hK hC hy s hs
  let w := (z.1.1.2.2 i,(split (batchCut P hR hc hsmall clock label hK hC hy s hs) z.1.2).2.1 i)
  have hshift := (OuterMainStability.main_queryShift_and_mass P hK hc hsmall hC hy (N P) i clock).1
  have hrun := FreshChildRunShift.run_completedSource (child P hR hc hsmall clock i).program
    (e P hR hc hsmall clock i) (B.slot i) (B.old i) (B.designated i) (B.auxiliary i)
    (rhoC P) (radius P clock i) P.Ds (shiftVector P hR hc hsmall clock i)
    (coeff P hR hc hsmall clock i) (B.rho_nonneg i) (B.radius_pos i) B.Ds_pos
    (B.shift_budget i) (B.small i) hshift (gradient V) (center P clock hV hlo hup i z.1.1.1) w
  have hv := congrArg (fun out => (show Point d from out.value)) hrun
  unfold benchmarkError
  rw [ClockMainReadout.evaluator_eq_run P hR hc hsmall clock label hK hC hy k hk]
  unfold lowerError FreshChildRunShift.lowerError
  rw [sub_add_eq_sub_sub]
  change _ = (show Point d from (run (child P hR hc hsmall clock i).program (gradient V)
    ⟨coeff P hR hc hsmall clock i,center P clock hV hlo hup i z.1.1.1,
      (FreshChildAbsorbedLaw.completedSource (child P hR hc hsmall clock i).program
        (e P hR hc hsmall clock i) (B.slot i) (B.old i) (B.designated i) (B.auxiliary i)
        (rhoC P) (radius P clock i) (shiftVector P hR hc hsmall clock i) w).1⟩ Env.empty
      (FreshChildAbsorbedLaw.completedSource (child P hR hc hsmall clock i).program
        (e P hR hc hsmall clock i) (B.slot i) (B.old i) (B.designated i) (B.auxiliary i)
        (rhoC P) (radius P clock i) (shiftVector P hR hc hsmall clock i) w).2).value) -
    Gibbs.primitiveMean F (center P clock hV hlo hup i z.1.1.1) (radius P clock i) - sigma • z.2 i
  rw [hv]
  rfl

theorem lowerError_measurable (i : Index P) :
    Measurable (lowerError P hR hc hsmall clock hV hlo hup i) := by
  have hF : ContDiff ℝ 2 F := hV.comp (contDiff_id.const_smul (Real.sqrt P.delta))
  have hu := (Gibbs.primitive_mean_lipschitz hF P.delta_pos.le
    (ClockMeanChildAccuracy.scaled_hessian_nonneg P hV hlo)
    (ClockMeanChildAccuracy.scaled_hessian_upper P hV hup)
    (radius_pos P clock i)).continuous.measurable.comp (center_measurable P clock hV hlo hup i)
  have hp := program_point_of_measurable (child P hR hc hsmall clock i).program (gradient V)
    (ClockOriginalGradientKernel.originalGradient_measurable hV)
    (fun _ => coeff P hR hc hsmall clock i)
    (fun z : Base P d × ((Point d × Tape d (child P hR hc hsmall clock i).program) × Point d) =>
      center P clock hV hlo hup i z.1)
    (fun z => z.2.1.1) (fun z => z.2.1.2) measurable_const
    ((center_measurable P clock hV hlo hup i).comp measurable_fst)
    measurable_snd.fst.fst measurable_snd.fst.snd
  exact hp.sub ((hu.comp measurable_fst).add (measurable_snd.snd.const_smul sigma))

/-- No supplied occurrence law: the original canonical tape and concrete
finite coupling supply the exact standalone lower-error distribution. -/
theorem benchmark_error_law (ν : Measure (Point d × Point d)) [IsProbabilityMeasure ν]
    (k : ℕ) (hk : k<P.K+4) (i : Index P) :
    (adjoin P hR hc hsmall clock label hK hC hy hV hlo hup hyMean
      (stage P hR hc hsmall clock label k hk.le).1 (stage_positive P hR hc hsmall clock label k hk) ∘ₘ
      stageLaw P hR hc hsmall clock label hK hC hy hV hlo hup hyMean
        (ν.prod (tapeLaw (Probability.CanonicalNativeTapeLaw.primitiveLaws d) (Host P hR hc hsmall clock label))) k hk.le).map
        (benchmarkError P hR hc hsmall clock label hV hlo hup k i) =
    ((ν.prod ((stdGaussian (Point d)).prod (Measure.pi fun _ : Index P => stdGaussian (Point d)))) ⊗ₘ
      ((lower P hR hc hsmall clock label hK hC hy hV hlo hup hyMean
        (stage P hR hc hsmall clock label k hk.le).1 (stage_positive P hR hc hsmall clock label k hk)).joint i).comap
        (center P clock hV hlo hup i) (center_measurable P clock hV hlo hup i)).map
          (lowerError P hR hc hsmall clock hV hlo hup i) := by
  have hp := mainLowerProjection_preserving P hR hc hsmall clock label hK hC hy hV hlo hup hyMean ν k hk i
  have hm := lowerError_measurable P hR hc hsmall clock hV hlo hup i
  have he : benchmarkError P hR hc hsmall clock label hV hlo hup k i =
      lowerError P hR hc hsmall clock hV hlo hup i ∘
        mainLowerProjection P hR hc hsmall clock label hK hC hy k hk i := by
    funext z
    exact benchmarkError_eq_lowerError P hR hc hsmall clock label hK hC hy hV hlo hup k hk i z
  rw [he,← Measure.map_map hm hp.measurable,hp.map_eq]

end AcceleratedLogConcave.Root.ClockMainErrorTransport
