import AcceleratedLogConcave.Oracle.PrivateCompletedCoupling
import AcceleratedLogConcave.Oracle.PrivateChronologicalExecution

/-! Exact source and benchmark support of the completed private coupling.
The unchanged whole tape, original parent and all returned reference slots
are kept in the actual augmented sample. -/
noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal
namespace AcceleratedLogConcave.Oracle.PrivateCompletedRms
open Numerics Numerics.AffineGraph AffineLowering TapeLowering NoisyLayer
open RecursiveMeanProgram RecursiveMeanContinuation SourceMeanLayer SourceExecutableTables CovarianceSetup
open TailOccurrenceCut TailCut CanonicalTapeLaw CanonicalTapeMeasurability
open PrivateChronologicalCoupling

local instance canonicalTapeSpace {d c : ℕ} {Γ : Ctx} {τ : Ty} (p : Prog c Γ τ) :
    MeasurableSpace (Tape d p) := tapeSpace d p
local instance canonicalPrefixSpace {d c : ℕ} {Γ Δ : Ctx} {τ σ : Ty}
    {p : Prog c Γ τ} {q : Prog c Δ σ} (cut : TailCut q p) :
    MeasurableSpace (Prefix d cut) := prefixSpace d cut

variable {m n d : ℕ} (S : SamplingGeometry m) (e : Fin n ≃ S.Node)
  (r Ds : ℝ) (main final : Fin n → ExecutableData) (N : ℕ)
abbrev Sample := (History d N n × Tape d (Host S e r Ds main final N)) × (Fin n → Point d)
local notation "Ω" => Sample (d := d) S e r Ds main final N

def tape (z : Ω) : Tape d (Host S e r Ds main final N) := z.1.2

def mainReference (k : ℕ) (i : Fin n) (z : Ω) : Point d :=
  PrivateChronologicalExecution.returnedReference S e r Ds main final N k i z.1

def finalReference (i : Fin n) (z : Ω) : Point d := z.2 i

theorem tape_measurable : Measurable (tape (d := d) S e r Ds main final N) := measurable_fst.snd

theorem mainReference_measurable (k : ℕ) (i : Fin n) :
    Measurable (mainReference (d := d) S e r Ds main final N k i) :=
  (PrivateChronologicalExecution.returnedReference_measurable S e r Ds main final N k i).comp measurable_fst

theorem finalReference_measurable (i : Fin n) :
    Measurable (finalReference (d := d) S e r Ds main final N i) :=
  (measurable_pi_apply i).comp measurable_snd

variable (hr : 0<r) (hDs : 0<Ds)
  (hmass : ∀ i, shiftSq (main i).shiftVector ≤ Ds^2)
  (hfinalMass : ∀ i, shiftSq (final i).shiftVector ≤ Ds^2)
  (L : PrimitiveLaws d) (hL : L.pointDraw = stdGaussian (Point d))
  {F : Point d → ℝ} (hF : ContDiff ℝ 2 F) {ell : ℝ} (hell : 0≤ell)
  (hlo : ∀ z v, 0≤fderiv ℝ (fderiv ℝ F) z v v)
  (hup : ∀ z v, fderiv ℝ (fderiv ℝ F) z v v≤ell*‖v‖^2)
  (Jf : FreshChildBatchCoupling.Lower L (PrivateFinalCoupling.data S e r Ds main final N hr hDs hfinalMass
    (terminalCursor S e r Ds main final N).old))
  (J : ∀ (k : ℕ) (hk : k<N), FreshChildBatchCoupling.Lower L
    (PrivateChronologicalCoupling.data S e r Ds main final N hr hDs hmass
      (stage S e r Ds main final N k hk.le).1
      (stage_positive S e r Ds main final N k hk)))

/-- The measure is the concrete completed kernel at the actual center. -/
def law (x : Point d) : Measure Ω :=
  PrivateCompletedCoupling.kernel S e r Ds main final N hr hDs hmass hfinalMass L hL hF hell hlo hup Jf J x

instance law_probability (x : Point d) : IsProbabilityMeasure
    (law S e r Ds main final N hr hDs hmass hfinalMass L hL hF hell hlo hup Jf J x) := by
  unfold law
  infer_instance

local notation "μ" => law S e r Ds main final N hr hDs hmass hfinalMass L hL hF hell hlo hup Jf J
local notation "prior" => PrivateChronologicalCoupling.kernel S e r Ds main final N hr hDs hmass L hL hF hell hlo hup J

/-- The final augmentation preserves the complete finite-loop state. -/
theorem prior_preserving (x : Point d) : MeasurePreserving Prod.fst (μ x) (prior x) := by
  refine ⟨measurable_fst,?_⟩
  exact congrArg (fun k => k x)
    (PrivateCompletedCoupling.kernel_prior S e r Ds main final N hr hDs hmass hfinalMass L hL hF hell hlo hup Jf J)

/-- The unchanged complete actual tape has its canonical law after all main
and final reference extensions. No source-coordinate law is assumed. -/
theorem tape_preserving (x : Point d) :
    MeasurePreserving (tape S e r Ds main final N) (μ x)
      (tapeLaw L (Host S e r Ds main final N)) := by
  have h := congrArg (fun ν => ν.map Prod.snd)
    (PrivateCompletedCoupling.kernel_original S e r Ds main final N hr hDs hmass hfinalMass
      L hL hF hell hlo hup Jf J x)
  have hm : Measurable (fun z : Ω => original S e r Ds main final N z.1) :=
    (original_measurable S e r Ds main final N).comp measurable_fst
  rw [Measure.map_map measurable_snd hm,
    Measure.map_map measurable_snd (by fun_prop)] at h
  change (μ x).map (tape S e r Ds main final N) =
    (FreshChildRetainedCoupling.sourceLaw L (Host S e r Ds main final N)).map Prod.snd at h
  let _ : IsProbabilityMeasure L.pointDraw := L.point_probability
  let _ : IsProbabilityMeasure (tapeLaw L (Host S e r Ds main final N)) := tapeLaw_probability L _
  rw [FreshChildRetainedCoupling.sourceLaw,← Measure.snd,Measure.snd_prod] at h
  exact ⟨tape_measurable S e r Ds main final N,h⟩

/-- Past returned references keep their exact joint law with the stored coarse
source and full tape, also after adjoining the actual final child batch. -/
theorem past_law (x : Point d) (k : ℕ) (hk : k≤N) :
    (μ x).map (fun z => PrivateChronologicalExecution.past S e r Ds main final N k hk z.1) =
    (iteration S e r Ds main final N hr hDs hmass L hL hF hell hlo hup J k hk ∘ₘ
      initial S e r Ds main final N L x).map
        (PrivateChronologicalExecution.past S e r Ds main final N k hk) := by
  calc
    _ = ((μ x).map Prod.fst).map (PrivateChronologicalExecution.past S e r Ds main final N k hk) :=
      (Measure.map_map (PrivateChronologicalExecution.past_measurable S e r Ds main final N k hk) measurable_fst).symm
    _ = _ := by
      rw [(prior_preserving S e r Ds main final N hr hDs hmass hfinalMass L hL hF hell hlo hup Jf J x).map_eq]
      exact PrivateChronologicalExecution.kernel_past S e r Ds main final N hr hDs hmass L hL hF hell hlo hup J k hk x

/-- The stored coarse center/setup coordinates are the actual center and
literal setup occurrence, even after all conditional reference extensions. -/
theorem source_support (x : Point d) :
    ∀ᵐ z ∂μ x, z.1.1.1.1.1 = x ∧
      z.1.1.1.1.2 = (show Point d from (tape S e r Ds main final N z).2.1) := by
  let view := PrivateChronologicalExecution.sourceView (d := d) S e r Ds main final N
  let Q : (((Point d × Point d) × Point d) × Tape d (Host S e r Ds main final N)) → Prop :=
    fun a => a.1.1.1=x ∧ a.1.1.2=(show Point d from a.2.2.1)
  have hQ : MeasurableSet {a | Q a} :=
    (measurableSet_eq_fun (by fun_prop) measurable_const).inter
      (measurableSet_eq_fun (by fun_prop) (by fun_prop))
  have hview : Measurable view := PrivateChronologicalExecution.sourceView_measurable S e r Ds main final N
  have hi : ∀ᵐ w ∂initial S e r Ds main final N L x, Q (view w) := by
    rw [initial,Kernel.map_apply _ (initializeState_measurable S e r Ds main final N),
      Kernel.prod_apply,Kernel.id_apply,Measure.dirac_prod]
    apply (ae_map_iff (initializeState_measurable S e r Ds main final N).aemeasurable
      (hview hQ)).2
    apply (ae_map_iff (measurable_const.prodMk measurable_id).aemeasurable
      ((initializeState_measurable S e r Ds main final N) (hview hQ))).2
    exact Filter.Eventually.of_forall fun _ => ⟨rfl,rfl⟩
  have hi' : ∀ᵐ a ∂(initial S e r Ds main final N L x).map view, Q a :=
    (ae_map_iff hview.aemeasurable hQ).2 hi
  rw [← PrivateChronologicalExecution.kernel_sourceView S e r Ds main final N hr hDs hmass L hL hF hell hlo hup J x] at hi'
  have hp := ae_of_ae_map hview.aemeasurable hi'
  exact (prior_preserving S e r Ds main final N hr hDs hmass hfinalMass L hL hF hell hlo hup Jf J x).quasiMeasurePreserving.ae hp

local notation "A" => samplingMatrix S e r
local notation "rho" => samplingNoise S r Ds
local notation "Cmat" => residualRoot A rho (r^2)
local notation "sigma" => RecursiveMeanPublicTable.mainWidth n r (S.R) Ds (r^2)

/-- Exact benchmark support on the completed sample, for the very readouts
consumed by PrivateSamplingRetainedRms. -/
theorem actual_benchmark_ae (x : Point d) :
    ∀ᵐ z ∂μ x, ∀ i,
      SharedLayerRms.benchmark
        (fun i z => PrivateSamplingRetainedRms.reference S e r Ds main final N hF hell hlo hup x hr i
          (tape S e r Ds main final N z)) A Cmat sigma
        (SourceMeanRetainedRms.finiteReference N (mainReference S e r Ds main final N))
        (fun k i z => PrivateSamplingExecutionSchedule.residualNoise S e r Ds main final N k i
          (tape S e r Ds main final N z))
        (fun i z => PrivateSamplingRetainedRms.initialNoise S e r Ds main final N i
          (tape S e r Ds main final N z)) N i z =
      PrivateSamplingRetainedRms.reference S e r Ds main final N hF hell hlo hup x hr i
        (tape S e r Ds main final N z) + rho • z.1.1.2.2 i := by
  have h := (prior_preserving S e r Ds main final N hr hDs hmass hfinalMass L hL hF hell hlo hup Jf J x).quasiMeasurePreserving.ae
    (PrivateChronologicalExecution.kernel_actual_benchmark_ae S e r Ds main final N hr hDs hmass L hL hF hell hlo hup J x)
  filter_upwards [h] with z hz
  intro i
  cases N <;> simpa only [SharedLayerRms.benchmark,SharedLayerRms.benchmarkLayer,
    SourceMeanRetainedRms.finiteReference,mainReference,tape] using hz i

end AcceleratedLogConcave.Oracle.PrivateCompletedRms
