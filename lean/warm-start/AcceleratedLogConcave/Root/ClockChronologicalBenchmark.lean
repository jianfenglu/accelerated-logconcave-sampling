import AcceleratedLogConcave.Root.ClockChronologicalPast
import AcceleratedLogConcave.Root.ClockInitialComparison
import AcceleratedLogConcave.Numerics.SharedLayerRms
import AcceleratedLogConcave.Oracle.PrivateChronologicalCoupling

/-! Exact complete unread-suffix law of the actual finite retained Clock loop. -/
noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
namespace AcceleratedLogConcave.Root.ClockChronologicalBenchmark
open Oracle Oracle.AffineLowering Oracle.TapeLowering Oracle.NoisyLayer
open Oracle.RecursiveMeanProgram Oracle.RecursiveMeanContinuation
open Oracle.TailOccurrenceCut Oracle.PrivateCausalLayer Oracle.PrivateCausalAdvance
open TailCut Oracle.CanonicalTapeMeasurability Oracle.CanonicalTapeLaw
open ClockChronologicalCoupling ClockChronologicalExecution ClockNoisyLayer Numerics
local instance canonicalPrefixSpace {d c : ℕ} {Γ Δ : Ctx} {τ σ : Ty}
    {p : Prog c Γ τ} {q : Prog c Δ σ} (cut : TailCut q p) :
    MeasurableSpace (Prefix d cut) := prefixSpace d cut
local instance canonicalTapeSpace {d c : ℕ} {Γ : Ctx} {τ : Ty} (p : Prog c Γ τ) :
    MeasurableSpace (Tape d p) := tapeSpace d p
variable (P : SourceSchedule) (hR : P.R≤1/2) (hc : 0<P.csch) (hsmall : P.csch<1/160)
  (clock : ClockLaw.Clock) (label : ℕ) (hK : 10≤P.K) (hC : 8≤P.Csch)
  (hy : CubicScheduleThreshold.threshold P≤P.y)
  {d : ℕ} {V : Point d→ℝ} (hV : ContDiff ℝ 2 V)
  (hlo : ∀ z v,0≤fderiv ℝ (fderiv ℝ V) z v v)
  (hup : ∀ z v,fderiv ℝ (fderiv ℝ V) z v v≤‖v‖^2)
  (hyMean : MeanSourceScalarAbsorption.threshold P≤P.y)

def initialNoise (sample : Tape d (Host P hR hc hsmall clock label)) : Index P → Point d :=
  (ClockInitialComparison.coordinates P hR hc hsmall clock label
    (split (entry P hR hc hsmall clock label).cut sample).1).2.2

theorem initialNoise_measurable : Measurable (initialNoise (d := d) P hR hc hsmall clock label) :=
  ((ClockInitialComparison.coordinates_measurable P hR hc hsmall clock label).comp
    (measurePreserving_split (Probability.CanonicalNativeTapeLaw.primitiveLaws d)
      (entry P hR hc hsmall clock label).cut).measurable.fst).snd.snd

local notation "X" => History P d ×
  Tape d (Host P hR hc hsmall clock label)
def residualNoise (k : ℕ) (i : Index P) (sample : Tape d (Host P hR hc hsmall clock label)) : Point d :=
  MeanExecutionSchedule.residualNoise (c P hR hc hsmall clock) (p P hR hc hsmall clock) (ClockRetainedFinalSplice.finish P hR hc hsmall clock label) (P.K+4) (raw P hR hc hsmall clock label) k i sample
local notation "Bmat" => A P clock
local notation "rho" => rhoC P
local notation "Cmat" => C P clock
local notation "sigma" => CovarianceSetup.sigma (N P) (rhoC P) (a P)
private theorem noise_mul_comparisonUpdate (g z : Index P → Point d) (i : Index P) :
    rho • comparisonUpdate P clock (g,z) i =
      (∑ j, Bmat i j • (sigma • g j)) + ∑ j,Cmat i j • z j := by
  have hp := rhoC_pos P
  simp only [comparisonUpdate,ResidualGaussianRecombination.recombine,ClockNoisyLayer.C,smul_smul,
    mul_inv_cancel₀ (ne_of_gt hp),one_smul]
/-- The recorded reference array, extended by zero outside actual execution. -/
def returnedReference (k : ℕ) (i : Index P) (z : X) : Point d :=
  if hk : k<(P.K+4) then z.1.2.1 ⟨k,hk⟩ i else 0

theorem returnedReference_measurable (k : ℕ) (i : Index P) :
    Measurable (returnedReference (d := d) P hR hc hsmall clock label k i) := by
  unfold returnedReference
  split_ifs <;> fun_prop

/-- The comparison reconstructed from the actual initial occurrence or the
last returned vector and the same physical residual occurrence. -/
def comparisonNoise : (k : ℕ) → (hk : k≤(P.K+4)) → X → Index P → Point d
  | 0, _, z => fun i => initialNoise P hR hc hsmall clock label z.2 i
  | k+1, hk, z => comparisonUpdate P clock ((z.1.2.1 ⟨k,by omega⟩),
      (fun i => residualNoise P hR hc hsmall clock label k i z.2))

include hK hC hy in
theorem residualNoise_measurable (k : ℕ) (hk : k<(P.K+4)) (i : Index P) :
    Measurable (residualNoise (d := d) P hR hc hsmall clock label k i) := by
  have he : residualNoise (d := d) P hR hc hsmall clock label k i =
      (fun sample => (show Point d from ((split (afterBatch (batchCut P hR hc hsmall clock label hK hC hy
        (stage P hR hc hsmall clock label k hk.le).1
        (stage_positive P hR hc hsmall clock label k hk))) sample).2.1 i).1)) := by
    funext sample
    exact (stage_residual P hR hc hsmall clock label hK hC hy k hk i sample).symm
  rw [he]
  exact ((measurable_pi_apply i).comp
    (measurePreserving_split (Probability.CanonicalNativeTapeLaw.primitiveLaws d) (afterBatch (batchCut P hR hc hsmall clock label hK hC hy
      (stage P hR hc hsmall clock label k hk.le).1
      (stage_positive P hR hc hsmall clock label k hk)))).measurable.snd.fst).fst

include hK hC hy in
theorem comparisonNoise_measurable (k : ℕ) (hk : k≤(P.K+4)) :
    Measurable (comparisonNoise (d := d) P hR hc hsmall clock label k hk) := by
  cases k with
  | zero =>
    exact (initialNoise_measurable P hR hc hsmall clock label).comp measurable_snd
  | succ k =>
    have hf : Measurable (fun z : X => z.1.2.1 (⟨k,by omega⟩ : Fin (P.K+4))) := by fun_prop
    have hz : Measurable (fun z : X => fun i =>
        residualNoise P hR hc hsmall clock label k i z.2) :=
      Measurable.of_eval fun i =>
        (residualNoise_measurable P hR hc hsmall clock label hK hC hy k (by omega) i).comp measurable_snd
    have he : comparisonNoise (d := d) P hR hc hsmall clock label (k+1) hk =
        (fun z : X => comparisonUpdate P clock ((z.1.2.1 (⟨k,by omega⟩ : Fin (P.K+4))),
          (fun i => residualNoise P hR hc hsmall clock label k i z.2))) := by
      funext z
      rfl
    rw [he]
    apply Measurable.of_eval
    intro i
    exact ((Finset.measurable_sum Finset.univ (fun j _ =>
      (((measurable_pi_apply j).comp hf).const_smul sigma).const_smul (Bmat i j))).add
      (Finset.measurable_sum Finset.univ (fun j _ =>
        ((measurable_pi_apply j).comp hz).const_smul (Cmat i j)))).const_smul rho⁻¹

/-- This is the existing SharedLayerRms benchmark with the literal recorded
references and raw residual schedule, before any probability or Gaussian law. -/
theorem benchmark_eq_comparisonNoise (k : ℕ) (hk : k≤(P.K+4)) (Phi : Index P → X → Point d)
    (z : X) (i : Index P) :
    SharedLayerRms.benchmark Phi Bmat Cmat sigma
      (returnedReference P hR hc hsmall clock label)
      (fun k i z => residualNoise P hR hc hsmall clock label k i z.2)
      (fun i z => rho • initialNoise P hR hc hsmall clock label z.2 i) k i z =
        Phi i z + rho • comparisonNoise P hR hc hsmall clock label k hk z i := by
  cases k with
  | zero => rfl
  | succ k =>
    dsimp only [SharedLayerRms.benchmark,SharedLayerRms.benchmarkLayer,comparisonNoise]
    rw [noise_mul_comparisonUpdate P clock]
    simp only [returnedReference,dite_eq_left (show k<(P.K+4) by omega)]
    abel

/-- A concrete executed record satisfies the next benchmark identity
pointwise; its complete input tape remains the same tape. -/
theorem record_comparisonNoise (k : ℕ) (hk : k<(P.K+4))
    (z : X × (Index P → Point d)) :
    (record P hR hc hsmall clock label hK hC hy
      (stage P hR hc hsmall clock label k hk.le).1
      (stage_positive P hR hc hsmall clock label k hk) ⟨k,hk⟩ z).1.2.2 =
    comparisonNoise P hR hc hsmall clock label (k+1) (by omega)
      (record P hR hc hsmall clock label hK hC hy
        (stage P hR hc hsmall clock label k hk.le).1
        (stage_positive P hR hc hsmall clock label k hk) ⟨k,hk⟩ z) := by
  dsimp only [record,comparisonNoise]
  rw [Function.update_self]
  congr 1
  refine Prod.ext ?_ ?_
  · rfl
  funext i
  exact stage_residual P hR hc hsmall clock label hK hC hy k hk i z.1.2
private theorem step_ae_of_record (s : Cursor P hR hc hsmall clock label) (hs : 0<s.remaining)
    (k : Fin (P.K+4))
    (z : X) (Q : X → Prop) (hQ : MeasurableSet {w | Q w})
    (hrecord : ∀ g, Q (record P hR hc hsmall clock label hK hC hy s hs k (z,g))) :
    ∀ᵐ w ∂ClockChronologicalCoupling.step P hR hc hsmall clock label hK hC hy hV hlo hup hyMean s hs k z,
      Q w := by
  rw [ClockChronologicalCoupling.step,Kernel.map_apply _
    (record_measurable P hR hc hsmall clock label hK hC hy s hs k)]
  apply (ae_map_iff (record_measurable P hR hc hsmall clock label hK hC hy s hs k).aemeasurable hQ).2
  rw [adjoin,CausalTailHistory.onTape,Kernel.prod_apply,Kernel.id_apply,Measure.dirac_prod]
  apply (ae_map_iff (measurable_const.prodMk measurable_id).aemeasurable
    ((record_measurable P hR hc hsmall clock label hK hC hy s hs k) hQ)).2
  exact Filter.Eventually.of_forall hrecord

/-- A real executed layer, on every entering history and original tape,
records precisely the next raw-schedule benchmark comparison. -/
theorem step_comparisonNoise_ae (k : ℕ) (hk : k<(P.K+4))
    (z : X) :
    ∀ᵐ w ∂ClockChronologicalCoupling.step P hR hc hsmall clock label hK hC hy hV hlo hup hyMean
      (stage P hR hc hsmall clock label k hk.le).1
      (stage_positive P hR hc hsmall clock label k hk) ⟨k,hk⟩ z,
      w.1.2.2 = comparisonNoise P hR hc hsmall clock label (k+1) (by omega) w := by
  apply step_ae_of_record P hR hc hsmall clock label hK hC hy hV hlo hup hyMean _ _ _ z _
    (measurableSet_eq_fun measurable_fst.snd.snd
      (comparisonNoise_measurable P hR hc hsmall clock label hK hC hy (k+1) (by omega)))
  intro g
  exact record_comparisonNoise P hR hc hsmall clock label hK hC hy k hk (z,g)


include hK hC hy in
private theorem comparisonNoise_event (k : ℕ) (hk : k≤(P.K+4)) :
    MeasurableSet {z : X | z.1.2.2 = comparisonNoise P hR hc hsmall clock label k hk z} :=
  measurableSet_eq_fun measurable_fst.snd.snd
    (comparisonNoise_measurable P hR hc hsmall clock label hK hC hy k hk)

/-- The literal initial noise readout agrees pointwise with initialization. -/
theorem prepare_comparisonNoise (z : (Point d × Point d) × Tape d (Host P hR hc hsmall clock label)) :
    (prepare P hR hc hsmall clock label z).1.2.2 =
      comparisonNoise P hR hc hsmall clock label 0 (Nat.zero_le _)
        (prepare P hR hc hsmall clock label z) := by
  rfl

include hK hC hy in
theorem initial_comparisonNoise_ae (μ : Measure ((Point d × Point d) × Tape d (Host P hR hc hsmall clock label))) :
    ∀ᵐ z ∂μ.map (prepare P hR hc hsmall clock label),
      z.1.2.2 = comparisonNoise P hR hc hsmall clock label 0 (Nat.zero_le _) z := by
  apply (ae_map_iff (prepare_measurable P hR hc hsmall clock label).aemeasurable
    (comparisonNoise_event P hR hc hsmall clock label hK hC hy 0 (Nat.zero_le _))).2
  exact Filter.Eventually.of_forall (prepare_comparisonNoise P hR hc hsmall clock label)

theorem iteration_comparisonNoise_ae (k : ℕ) (hk : k≤(P.K+4))
    (μ : Measure ((Point d × Point d) × Tape d (Host P hR hc hsmall clock label))) :
    ∀ᵐ z ∂iteration P hR hc hsmall clock label hK hC hy hV hlo hup hyMean k hk ∘ₘ
        μ.map (prepare P hR hc hsmall clock label),
      z.1.2.2 = comparisonNoise P hR hc hsmall clock label k hk z := by
  cases k with
  | zero =>
    simpa only [iteration,Measure.id_comp] using
      initial_comparisonNoise_ae P hR hc hsmall clock label hK hC hy μ
  | succ k =>
    rw [iteration,← Measure.comp_assoc]
    apply Measure.ae_comp_of_ae_ae (comparisonNoise_event P hR hc hsmall clock label hK hC hy (k+1) hk)
    exact Filter.Eventually.of_forall fun z =>
      step_comparisonNoise_ae P hR hc hsmall clock label hK hC hy hV hlo hup hyMean k (by omega) z

/-- Final finite-loop support on an arbitrary original input/tape law. -/
theorem kernel_comparisonNoise_ae
    (μ : Measure ((Point d × Point d) × Tape d (Host P hR hc hsmall clock label))) :
    ∀ᵐ z ∂kernel P hR hc hsmall clock label hK hC hy hV hlo hup hyMean ∘ₘ μ,
      z.1.2.2 = comparisonNoise P hR hc hsmall clock label (P.K+4) le_rfl z := by
  rw [kernel,← Measure.comp_assoc,Measure.deterministic_comp_eq_map]
  exact iteration_comparisonNoise_ae P hR hc hsmall clock label hK hC hy hV hlo hup hyMean (P.K+4) le_rfl μ

/-- Correct child-width benchmark on the actual final chronological law. -/
theorem kernel_benchmark_ae (Phi : Index P → X → Point d)
    (μ : Measure ((Point d × Point d) × Tape d (Host P hR hc hsmall clock label))) :
    ∀ᵐ z ∂kernel P hR hc hsmall clock label hK hC hy hV hlo hup hyMean ∘ₘ μ, ∀ i,
      SharedLayerRms.benchmark Phi Bmat Cmat sigma
        (returnedReference P hR hc hsmall clock label)
        (fun k i z => residualNoise P hR hc hsmall clock label k i z.2)
        (fun i z => rho • initialNoise P hR hc hsmall clock label z.2 i) (P.K+4) i z =
          Phi i z + rho • z.1.2.2 i := by
  filter_upwards [kernel_comparisonNoise_ae P hR hc hsmall clock label hK hC hy hV hlo hup hyMean μ] with z hz
  intro i
  rw [benchmark_eq_comparisonNoise P hR hc hsmall clock label (P.K+4) le_rfl,← hz]

end AcceleratedLogConcave.Root.ClockChronologicalBenchmark
