import AcceleratedLogConcave.Root.ClockMainStateReadout
import AcceleratedLogConcave.Root.ClockMainErrorHistory

/-! The actual Clock numerical iteration on its retained carrier. The only
post-horizon extension is the constant primitive mean, so its error is zero. -/
noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
open MeasureTheory
namespace AcceleratedLogConcave.Root.ClockMainRmsData
open Oracle Oracle.AffineLowering Oracle.TapeLowering Oracle.NoisyLayer
open Oracle.RecursiveMeanProgram Oracle.RecursiveMeanContinuation Oracle.TailOccurrenceCut.TailCut
open Oracle.CanonicalTapeMeasurability Oracle.CanonicalTapeLaw
open ClockChronologicalCoupling ClockNoisyLayer Numerics
local instance canonicalTapeSpace {d c : ℕ} {Γ : Ctx} {τ : Ty} (p : Prog c Γ τ) :
    MeasurableSpace (Tape d p) := tapeSpace d p
local instance canonicalPrefixSpace {d c : ℕ} {Γ Δ : Ctx} {τ σ : Ty}
    {p : Prog c Γ τ} {q : Prog c Δ σ} (cut : Oracle.TailOccurrenceCut.TailCut q p) :
    MeasurableSpace (Prefix d cut) := prefixSpace d cut
variable (P : SourceSchedule) (hR : P.R≤1/2) (hc : 0<P.csch) (hsmall : P.csch<1/160)
  (clock : ClockLaw.Clock) (label : ℕ) {d : ℕ}
abbrev Sample := History P d × Tape d (Host P hR hc hsmall clock label)
local notation "X" => Sample (d := d) P hR hc hsmall clock label
local notation "c" => ClockNoisyLayer.c P hR hc hsmall clock
local notation "p" => ClockNoisyLayer.p P hR hc hsmall clock
local notation "en" => ClockNoisyLayer.e P hR hc hsmall clock
local notation "finish" => ClockRetainedFinalSplice.finish P hR hc hsmall clock label
local notation "sigma" => CovarianceSetup.sigma (N P) (rhoC P) (a P)

def direct (i : Index P) (z : X) : Point d :=
  ClockMainStateReadout.direct P hR hc hsmall clock label z.1.1.1.1 z.1.1.1.2 i z.2

def initial (i : Index P) (z : X) : Point d :=
  ClockMainStateReadout.initial P hR hc hsmall clock label z.1.1.1.1 z.1.1.1.2 i z.2

def initialNoise (i : Index P) (z : X) : Point d :=
  rhoC P • ClockChronologicalBenchmark.initialNoise P hR hc hsmall clock label z.2 i

def noise (k : ℕ) (i : Index P) (z : X) : Point d :=
  ClockChronologicalBenchmark.residualNoise P hR hc hsmall clock label k i z.2

def reference (k : ℕ) (i : Index P) (z : X) : Point d :=
  ClockChronologicalBenchmark.returnedReference P hR hc hsmall clock label k i z

private theorem coordinates_measurable :
    Measurable (ClockMainStateReadout.coordinates (d := d) P hR hc hsmall clock label) :=
  (ClockInitialComparison.coordinates_measurable P hR hc hsmall clock label).comp
    (measurePreserving_split (Probability.CanonicalNativeTapeLaw.primitiveLaws d)
      (entry P hR hc hsmall clock label).cut).measurable.fst

theorem direct_measurable (i : Index P) : Measurable (direct (d := d) P hR hc hsmall clock label i) := by
  have he := (coordinates_measurable (d := d) P hR hc hsmall clock label).fst.comp
    (measurable_snd : Measurable (Prod.snd : X→_))
  change Measurable (fun z : X => z.1.1.1.1 +
    (ClockCollocation.rF P.delta*ClockCollocation.u P.delta P.K clock i) •
      (ClockPublicSetup.s • z.1.1.1.2 + ClockPublicSetup.noise •
        (ClockMainStateReadout.coordinates P hR hc hsmall clock label z.2).1))
  exact measurable_fst.fst.fst.fst.add
    (((measurable_fst.fst.fst.snd.const_smul ClockPublicSetup.s).add
      (he.const_smul ClockPublicSetup.noise)).const_smul
        (ClockCollocation.rF P.delta*ClockCollocation.u P.delta P.K clock i))

theorem initial_measurable (i : Index P) : Measurable (initial (d := d) P hR hc hsmall clock label i) := by
  have hz := (measurable_pi_apply i).comp
    ((coordinates_measurable (d := d) P hR hc hsmall clock label).snd.snd.comp
      (measurable_snd : Measurable (Prod.snd : X→_)))
  exact (direct_measurable P hR hc hsmall clock label i).add (hz.const_smul (rhoC P))

variable {V : Point d→ℝ} (hV : ContDiff ℝ 2 V)
  (hlo : ∀ z v,0≤fderiv ℝ (fderiv ℝ V) z v v)
  (hup : ∀ z v,fderiv ℝ (fderiv ℝ V) z v v≤‖v‖^2)

def target (i : Index P) (z : X) : Point d := center P clock hV hlo hup i z.1.1

def reply (i : Index P) (z : X) : Point d :=
  Gibbs.primitiveMean (scaledPotential V (Real.sqrt P.delta))
    (target P hR hc hsmall clock label hV hlo hup i z) (radius P clock i)

def evaluator := MeanExecutionSchedule.evaluator c p finish en
  (T P hR hc hsmall clock) (coeff P hR hc hsmall clock) (gradient V) (P.K+4)
  (fun z : X => ClockChronologicalExecution.raw P hR hc hsmall clock label z.2)
  (reply P hR hc hsmall clock label hV hlo hup)

def iterate := SharedLayerRms.iterate (direct (d := d) P hR hc hsmall clock label)
  (A P clock) (C P clock) (evaluator P hR hc hsmall clock label hV hlo hup)
  (noise P hR hc hsmall clock label) (initial P hR hc hsmall clock label)

def benchmark := SharedLayerRms.benchmark (target P hR hc hsmall clock label hV hlo hup)
  (A P clock) (C P clock) sigma (reference P hR hc hsmall clock label)
  (noise P hR hc hsmall clock label) (initialNoise P hR hc hsmall clock label)

def error (k : ℕ) (i : Index P) (z : X) : Point d :=
  iterate P hR hc hsmall clock label hV hlo hup k i z - benchmark P hR hc hsmall clock label hV hlo hup k i z

private theorem inputAt_some {n d C : ℕ} {Ξ : Ctx} {τ : Ty}
    (cc : Fin n→ℕ) (pp : ∀ i,Program (cc i) .point)
    (ff : ∀ {Δ : Ctx}, (Fin n→Ref Δ .point)→(Fin n→Ref Δ .point)→RefMap Ξ Δ→Prog C Δ τ)
    (N : ℕ) {Γ : Ctx} {old dd : Fin n→Ref Γ .point} {saved : RefMap Ξ Γ}
    (data : RawData cc pp ff d N old dd saved) (k : ℕ) (hk : k<N) :
    ∃ v, MeanExecutionSchedule.inputAt cc pp ff N data k=some v := by
  induction N generalizing Γ k with
  | zero => omega
  | succ N ih =>
    cases k with
    | zero => exact ⟨data.1,rfl⟩
    | succ k => exact ih data.2 k (by omega)

/-- On every executed index the calibrated callback is the literal source callback. -/
theorem evaluator_eq_source (k : ℕ) (hk : k<P.K+4) (i : Index P) (z : X) (y : Point d) :
    evaluator P hR hc hsmall clock label hV hlo hup k i z y =
      ClockMainReadout.evaluator P hR hc hsmall clock label (gradient V) (fun _ _=>0) k i z.2 y := by
  obtain ⟨v,hv⟩ := inputAt_some c p finish (P.K+4)
    (ClockChronologicalExecution.raw P hR hc hsmall clock label z.2) k hk
  simp only [evaluator,ClockMainReadout.evaluator,MeanExecutionSchedule.evaluator,hv]

/-- No lower-call property is required after the real horizon. -/
theorem evaluator_after (k : ℕ) (hk : P.K+4≤k) (i : Index P) (z : X) (y : Point d) :
    evaluator P hR hc hsmall clock label hV hlo hup k i z y = reply P hR hc hsmall clock label hV hlo hup i z := by
  unfold evaluator MeanExecutionSchedule.evaluator
  rw [MeanExecutionSchedule.inputAt_none c p finish (P.K+4) _ k hk]

theorem target_measurable (i : Index P) : Measurable (target P hR hc hsmall clock label hV hlo hup i) :=
  (center_measurable P clock hV hlo hup i).comp measurable_fst.fst

theorem reply_measurable (i : Index P) : Measurable (reply P hR hc hsmall clock label hV hlo hup i) := by
  have hF : ContDiff ℝ 2 (scaledPotential V (Real.sqrt P.delta)) := hV.comp (contDiff_id.const_smul _)
  exact (Gibbs.primitive_mean_lipschitz hF P.delta_pos.le
    (ClockMeanChildAccuracy.scaled_hessian_nonneg P hV hlo)
    (ClockMeanChildAccuracy.scaled_hessian_upper P hV hup) (radius_pos P clock i)).continuous.measurable.comp
      (target_measurable P hR hc hsmall clock label hV hlo hup i)

variable (hK : 10≤P.K) (hC : 8≤P.Csch) (hy : CubicScheduleThreshold.threshold P≤P.y)
include hK hC hy in
theorem evaluator_measurable (k : ℕ) (i : Index P) (y : X→Point d) (hymeas : Measurable y) :
    Measurable (fun z => evaluator P hR hc hsmall clock label hV hlo hup k i z (y z)) := by
  by_cases hk : k<P.K+4
  · have he : (fun z => evaluator P hR hc hsmall clock label hV hlo hup k i z (y z)) =
        (fun z => ClockMainReadout.evaluator P hR hc hsmall clock label (gradient V) (fun _ _=>0) k i z.2 (y z)) :=
      funext fun z => evaluator_eq_source P hR hc hsmall clock label hV hlo hup k hk i z (y z)
    rw [he]
    exact ClockMainReadout.evaluator_measurable P hR hc hsmall clock label hK hC hy
      (gradient V) (ClockOriginalGradientKernel.originalGradient_measurable hV) (fun _ _=>0) k hk i
      Prod.snd measurable_snd y hymeas
  · have he : (fun z => evaluator P hR hc hsmall clock label hV hlo hup k i z (y z)) = reply P hR hc hsmall clock label hV hlo hup i :=
      funext fun z => evaluator_after P hR hc hsmall clock label hV hlo hup k (by omega) i z (y z)
    rw [he]
    exact reply_measurable P hR hc hsmall clock label hV hlo hup i

include hK hC hy in
theorem evaluator_lipschitz (k : ℕ) (i : Index P) (z : X) :
    LipschitzWith ⟨2*P.delta,mul_nonneg (by norm_num) P.delta_pos.le⟩
      (evaluator P hR hc hsmall clock label hV hlo hup k i z) := by
  by_cases hk : k<P.K+4
  · have he : evaluator P hR hc hsmall clock label hV hlo hup k i z =
        ClockMainReadout.evaluator P hR hc hsmall clock label (gradient V) (fun _ _=>0) k i z.2 :=
      funext fun y => evaluator_eq_source P hR hc hsmall clock label hV hlo hup k hk i z y
    rw [he]
    exact ClockMainReadout.evaluator_lipschitz P hR hc hsmall clock label hK hC hy hV hlo hup (fun _ _=>0) k i z.2
  · have he : evaluator P hR hc hsmall clock label hV hlo hup k i z = fun _ => reply P hR hc hsmall clock label hV hlo hup i z :=
      funext fun y => evaluator_after P hR hc hsmall clock label hV hlo hup k (by omega) i z y
    rw [he]
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simp only [dist_self]
    positivity

include hK hC hy in
theorem noise_measurable (k : ℕ) (i : Index P) : Measurable (noise (d := d) P hR hc hsmall clock label k i) := by
  by_cases hk : k<P.K+4
  · exact (ClockChronologicalBenchmark.residualNoise_measurable P hR hc hsmall clock label hK hC hy k hk i).comp measurable_snd
  · have he : noise (d := d) P hR hc hsmall clock label k i = 0 := by
      funext z
      unfold noise ClockChronologicalBenchmark.residualNoise MeanExecutionSchedule.residualNoise
      rw [MeanExecutionSchedule.inputAt_none c p finish (P.K+4) _ k (by omega)]
      rfl
    rw [he]
    exact measurable_const

include hK hC hy in
theorem iterate_measurable (k : ℕ) (i : Index P) : Measurable (iterate P hR hc hsmall clock label hV hlo hup k i) := by
  induction k generalizing i with
  | zero => exact initial_measurable P hR hc hsmall clock label i
  | succ k ih =>
    change Measurable (fun z : X => direct P hR hc hsmall clock label i z +
      (∑ j, A P clock i j • evaluator P hR hc hsmall clock label hV hlo hup k j z
        (iterate P hR hc hsmall clock label hV hlo hup k j z)) +
      ∑ j, C P clock i j • noise P hR hc hsmall clock label k j z)
    exact ((direct_measurable P hR hc hsmall clock label i).add
      (Finset.measurable_sum Finset.univ fun j _ =>
        (evaluator_measurable P hR hc hsmall clock label hV hlo hup hK hC hy k j _ (ih j)).const_smul (A P clock i j))).add
      (Finset.measurable_sum Finset.univ fun j _ => (noise_measurable P hR hc hsmall clock label hK hC hy k j).const_smul (C P clock i j))

include hK hC hy in
theorem benchmark_measurable (k : ℕ) (i : Index P) : Measurable (benchmark P hR hc hsmall clock label hV hlo hup k i) := by
  cases k with
  | zero =>
    change Measurable (fun z : X => target P hR hc hsmall clock label hV hlo hup i z +
      rhoC P • ClockChronologicalBenchmark.initialNoise P hR hc hsmall clock label z.2 i)
    exact (target_measurable P hR hc hsmall clock label hV hlo hup i).add
      (((measurable_pi_apply i).comp
        ((ClockChronologicalBenchmark.initialNoise_measurable P hR hc hsmall clock label).comp
          (measurable_snd : Measurable (Prod.snd : X→_)))).const_smul (rhoC P))
  | succ k =>
    change Measurable (fun z : X => target P hR hc hsmall clock label hV hlo hup i z +
      (∑ j, A P clock i j • (sigma • reference P hR hc hsmall clock label k j z)) +
      ∑ j, C P clock i j • noise P hR hc hsmall clock label k j z)
    exact ((target_measurable P hR hc hsmall clock label hV hlo hup i).add
      (Finset.measurable_sum Finset.univ fun j _ =>
        ((ClockChronologicalBenchmark.returnedReference_measurable P hR hc hsmall clock label k j).const_smul sigma).const_smul (A P clock i j))).add
      (Finset.measurable_sum Finset.univ fun j _ => (noise_measurable P hR hc hsmall clock label hK hC hy k j).const_smul (C P clock i j))

/-- The calibrated benchmark error is precisely the earlier retained child error. -/
theorem childError_eq (k : ℕ) (hk : k<P.K+4) (i : Index P) (z : X) :
    SharedLayerRms.childError (evaluator P hR hc hsmall clock label hV hlo hup)
      (benchmark P hR hc hsmall clock label hV hlo hup) (reply P hR hc hsmall clock label hV hlo hup)
      sigma (reference P hR hc hsmall clock label) k i z =
    ClockMainErrorHistory.stageError P hR hc hsmall clock label hV hlo hup k hk i z := by
  unfold SharedLayerRms.childError
  rw [show benchmark P hR hc hsmall clock label hV hlo hup k i z =
    target P hR hc hsmall clock label hV hlo hup i z + rhoC P •
      ClockChronologicalBenchmark.comparisonNoise P hR hc hsmall clock label k hk.le z i from
    ClockChronologicalBenchmark.benchmark_eq_comparisonNoise P hR hc hsmall clock label k hk.le _ z i]
  rw [evaluator_eq_source P hR hc hsmall clock label hV hlo hup k hk]
  rfl

theorem childError_after (k : ℕ) (hk : P.K+4≤k) (i : Index P) (z : X) :
    SharedLayerRms.childError (evaluator P hR hc hsmall clock label hV hlo hup)
      (benchmark P hR hc hsmall clock label hV hlo hup) (reply P hR hc hsmall clock label hV hlo hup)
      sigma (reference P hR hc hsmall clock label) k i z = 0 := by
  simp only [SharedLayerRms.childError,evaluator_after P hR hc hsmall clock label hV hlo hup k hk,
    reference,ClockChronologicalBenchmark.returnedReference,dite_eq_right (by omega : ¬k<P.K+4),smul_zero,sub_self]

/-- The actual reached source state equals this calibrated iteration. -/
theorem state_eq_iterate (i : Index P) (z : X) :
    storedPoint (ClockMainStateReadout.state P hR hc hsmall clock label (gradient V) z.1.1.1.1 z.1.1.1.2 z.2).env
      ((ClockMainStateReadout.state P hR hc hsmall clock label (gradient V) z.1.1.1.1 z.1.1.1.2 z.2).old i) =
    iterate P hR hc hsmall clock label hV hlo hup (P.K+4) i z := by
  rw [ClockMainStateReadout.state_eq_iterate P hR hc hsmall clock label (gradient V) _ _ (fun _ _=>0)]
  have he (k : ℕ) (hk : k≤P.K+4) (j : Index P) :
      SharedLayerRms.iterate
        (ClockMainStateReadout.direct P hR hc hsmall clock label z.1.1.1.1 z.1.1.1.2)
        (A P clock) (C P clock)
        (ClockMainReadout.evaluator P hR hc hsmall clock label (gradient V) (fun _ _=>0))
        (MeanExecutionSchedule.residualNoise c p finish (P.K+4) (ClockChronologicalExecution.raw P hR hc hsmall clock label))
        (ClockMainStateReadout.initial P hR hc hsmall clock label z.1.1.1.1 z.1.1.1.2) k j z.2 =
      iterate P hR hc hsmall clock label hV hlo hup k j z := by
    induction k generalizing j with
    | zero => rfl
    | succ k ih =>
      dsimp only [iterate] at ih ⊢
      dsimp only [SharedLayerRms.iterate,SharedLayerRms.layer]
      simp only [← evaluator_eq_source P hR hc hsmall clock label hV hlo hup k (by omega), ih (by omega)]
      rfl
  exact he (P.K+4) le_rfl i
end AcceleratedLogConcave.Root.ClockMainRmsData
