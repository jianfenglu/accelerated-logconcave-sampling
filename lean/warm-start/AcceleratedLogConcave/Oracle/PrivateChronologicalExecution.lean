import AcceleratedLogConcave.Oracle.PrivateChronologicalCoupling
import AcceleratedLogConcave.Oracle.PrivateSamplingRetainedRms

/-! Same-tape operational identities for the finite chronological coupling.
The stored comparison and returned references are related to the existing
SharedLayerRms benchmark; no state equation or accuracy conclusion is assumed. -/
noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace AcceleratedLogConcave.Oracle.PrivateChronologicalExecution
open Numerics Numerics.AffineGraph AffineLowering TapeLowering NoisyLayer
open RecursiveMeanProgram RecursiveMeanContinuation SourceMeanLayer SourceExecutableTables CovarianceSetup
open TailOccurrenceCut TailCut CanonicalTapeLaw CanonicalTapeMeasurability
open PrivateCausalLayer PrivateCausalAdvance PrivateChronologicalCoupling

local instance canonicalTapeSpace {d c : ℕ} {Γ : Ctx} {τ : Ty} (p : Prog c Γ τ) :
    MeasurableSpace (Tape d p) := tapeSpace d p

local instance canonicalPrefixSpace {d c : ℕ} {Γ Δ : Ctx} {τ σ : Ty}
    {p : Prog c Γ τ} {q : Prog c Δ σ} (cut : TailCut q p) :
    MeasurableSpace (Prefix d cut) := prefixSpace d cut

section Routing
variable {m n d : ℕ} (S : SamplingGeometry m) (e : Fin n ≃ S.Node)
  (r Ds : ℝ) (main final : Fin n → ExecutableData) (N : ℕ)
local notation "cfg" => samplingConfig main final N
local notation "c" => (fun i => (main i).size)
local notation "p" => (fun i => (main i).program)
local notation "en" => (fun i => (main i).enumeration)
local notation "finish" => PrivateSamplingExecutionSchedule.finisher main final N

/-- The complete original suffix at a reached cursor, in the already defined
raw schedule coordinates. Uniform/residual source coordinates remain present. -/
def cursorRaw (s : Cursor S e r Ds main final N)
    (sample : Tape d (Host S e r Ds main final N)) :=
  rawTapeEquiv c p (cfg).mainSlots en (cfg).layerOrigin (cfg).mainDesignated (cfg).mainResidual
    (cfg).mainAuxiliary finish d s.remaining s.old s.direct s.saved (split s.cut sample).2

private theorem cursor_inputAt_advance (s : Cursor S e r Ds main final N)
    (hs : 0<s.remaining) (j : ℕ) (sample : Tape d (Host S e r Ds main final N)) :
    MeanExecutionSchedule.inputAt c p finish s.remaining
      (cursorRaw S e r Ds main final N s sample) (j+1) =
    MeanExecutionSchedule.inputAt c p finish (advance S e r Ds main final N s hs).remaining
      (cursorRaw S e r Ds main final N (advance S e r Ds main final N s hs) sample) j := by
  cases s with
  | mk remaining ctx old direct saved cut =>
    cases remaining with
    | zero => cases Nat.not_lt_zero _ hs
    | succ remaining =>
      dsimp only [cursorRaw,advance,focus,Loop,afterLayer]
      simp only [split_afterBatch]
      rfl

/-- Chronological index zero is the first executed source layer. This exact
suffix identity does not reverse the syntax's remaining-layer origin labels. -/
theorem stage_inputAt (k : ℕ) (hk : k≤N) (j : ℕ)
    (sample : Tape d (Host S e r Ds main final N)) :
    MeanExecutionSchedule.inputAt c p finish N
      (PrivateSamplingExecutionSchedule.raw S e r Ds main final N sample) (k+j) =
    MeanExecutionSchedule.inputAt c p finish
      (stage S e r Ds main final N k hk).1.remaining
      (cursorRaw S e r Ds main final N (stage S e r Ds main final N k hk).1 sample) j := by
  induction k generalizing j with
  | zero => simp only [Nat.zero_add]; rfl
  | succ k ih =>
    rw [show k+1+j = k+(j+1) by omega,ih (by omega) (j+1)]
    exact cursor_inputAt_advance S e r Ds main final N _ _ j sample

variable (hr : 0<r) (hDs : 0<Ds)
  (hmass : ∀ i, CovarianceSetup.shiftSq (main i).shiftVector ≤ Ds^2)

private theorem cursor_residual (s : Cursor S e r Ds main final N) (hs : 0<s.remaining)
    (i : Fin n) (sample : Tape d (Host S e r Ds main final N)) :
    (show Point d from ((split (afterBatch (batchCut S e r Ds main final N hr hDs hmass s hs)) sample).2.1 i).1) =
    match MeanExecutionSchedule.inputAt c p finish s.remaining
      (cursorRaw S e r Ds main final N s sample) 0 with
    | some v => v.2 i
    | none => 0 := by
  cases s with
  | mk remaining ctx old direct saved cut =>
    cases remaining with
    | zero => cases Nat.not_lt_zero _ hs
    | succ remaining =>
      simp only [batchCut,focus,cursorRaw,Loop,split_afterBatch]
      rfl

/-- The residual used by the actual chronological record is exactly the
existing raw-schedule residual occurrence at elapsed k. -/
theorem stage_residual (k : ℕ) (hk : k<N) (i : Fin n)
    (sample : Tape d (Host S e r Ds main final N)) :
    (show Point d from ((split (afterBatch (batchCut S e r Ds main final N hr hDs hmass
      (stage S e r Ds main final N k hk.le).1
      (stage_positive S e r Ds main final N k hk))) sample).2.1 i).1) =
    PrivateSamplingExecutionSchedule.residualNoise S e r Ds main final N k i sample := by
  have h := stage_inputAt (d := d) S e r Ds main final N k hk.le 0 sample
  rw [Nat.add_zero] at h
  have hc := cursor_residual S e r Ds main final N hr hDs hmass
    (stage S e r Ds main final N k hk.le).1
    (stage_positive S e r Ds main final N k hk) i sample
  unfold PrivateSamplingExecutionSchedule.residualNoise MeanExecutionSchedule.residualNoise
  cases hcur : MeanExecutionSchedule.inputAt (fun i => (main i).size) (fun i => (main i).program)
      (PrivateSamplingExecutionSchedule.finisher main final N)
      (stage S e r Ds main final N k hk.le).1.remaining
      (cursorRaw S e r Ds main final N (stage S e r Ds main final N k hk.le).1 sample) 0 <;>
    simp only [hcur] at h hc <;> simp only [h] <;> exact hc

end Routing

section HistoryPersistence
variable {m n d : ℕ} (S : SamplingGeometry m) (e : Fin n ≃ S.Node)
  (r Ds : ℝ) (main final : Fin n → ExecutableData) (N : ℕ)

/-- All original source coordinates and the first k recorded returned vectors.
Keeping the complete original tape makes this useful for later child errors. -/
def past (k : ℕ) (hk : k≤N)
    (z : History d N n × Tape d (Host S e r Ds main final N)) :=
  ((z.1.1,z.2), fun j : Fin k => z.1.2.1 ⟨j,lt_of_lt_of_le j.2 hk⟩)

theorem past_measurable (k : ℕ) (hk : k≤N) :
    Measurable (past (d := d) S e r Ds main final N k hk) := by
  exact (measurable_fst.fst.prodMk measurable_snd).prodMk
    (Measurable.of_eval fun j => (measurable_pi_apply _).comp measurable_fst.snd.fst)

variable (hr : 0<r) (hDs : 0<Ds)
  (hmass : ∀ i, CovarianceSetup.shiftSq (main i).shiftVector ≤ Ds^2)

theorem past_record (s : Cursor S e r Ds main final N) (hs : 0<s.remaining)
    (k : ℕ) (hk : k≤N) (j : Fin N) (hj : k≤j)
    (z : (History d N n × Tape d (Host S e r Ds main final N)) × (Fin n → Point d)) :
    past S e r Ds main final N k hk
      (record S e r Ds main final N hr hDs hmass s hs j z) =
    past S e r Ds main final N k hk z.1 := by
  apply Prod.ext
  · rfl
  · funext i
    apply Function.update_of_ne
    intro h
    have hv := congrArg Fin.val h
    change (i:ℕ) = (j:ℕ) at hv
    omega

variable (L : PrimitiveLaws d) (hL : L.pointDraw = stdGaussian (Point d))
  {F : Point d → ℝ} (hF : ContDiff ℝ 2 F) {ell : ℝ} (hell : 0≤ell)
  (hlo : ∀ z v, 0≤fderiv ℝ (fderiv ℝ F) z v v)
  (hup : ∀ z v, fderiv ℝ (fderiv ℝ F) z v v≤ell*‖v‖^2)

theorem step_past (s : Cursor S e r Ds main final N) (hs : 0<s.remaining)
    (k : ℕ) (hk : k≤N) (j : Fin N) (hj : k≤j)
    (J : FreshChildBatchCoupling.Lower L (data S e r Ds main final N hr hDs hmass s hs)) :
    (step S e r Ds main final N hr hDs hmass L hL hF hell hlo hup s hs j J).map
      (past S e r Ds main final N k hk) =
    Kernel.deterministic (past S e r Ds main final N k hk)
      (past_measurable S e r Ds main final N k hk) := by
  rw [PrivateChronologicalCoupling.step,← Kernel.map_comp_right _
    (record_measurable S e r Ds main final N hr hDs hmass L s hs j)
    (past_measurable S e r Ds main final N k hk)]
  have he : past (d := d) S e r Ds main final N k hk ∘
      record S e r Ds main final N hr hDs hmass s hs j =
      past S e r Ds main final N k hk ∘ Prod.fst := by
    funext z
    exact past_record S e r Ds main final N hr hDs hmass s hs k hk j hj z
  rw [he,Kernel.map_comp_right _ measurable_fst (past_measurable S e r Ds main final N k hk),
    ← Kernel.fst_eq,adjoin_original,Kernel.id_map]

variable
  (J : ∀ (j : ℕ) (hj : j<N), FreshChildBatchCoupling.Lower L
    (data S e r Ds main final N hr hDs hmass
      (stage S e r Ds main final N j hj.le).1
      (stage_positive S e r Ds main final N j hj)))

/-- Later actual layers preserve all already recorded returned references
jointly with the full original seed. This is a kernel identity, before choosing
a probability law or an external center. -/
theorem iteration_past (k l : ℕ) (hk : k≤N) (hkl : k≤l) (hl : l≤N) :
    (iteration S e r Ds main final N hr hDs hmass L hL hF hell hlo hup J l hl).map
      (past S e r Ds main final N k hk) =
    (iteration S e r Ds main final N hr hDs hmass L hL hF hell hlo hup J k hk).map
      (past S e r Ds main final N k hk) := by
  induction l, hkl using Nat.le_induction with
  | base => rfl
  | succ l hkl ih =>
    rw [iteration,Kernel.map_comp,step_past S e r Ds main final N hr hDs hmass L hL hF hell hlo hup
      _ _ k hk ⟨l,by omega⟩ hkl,Kernel.deterministic_comp_eq_map]
    exact ih (by omega)
/-- Read any completed prefix of returned references from the final finite
loop law without changing its joint law with the complete original source. -/
theorem kernel_past (k : ℕ) (hk : k≤N) (x : Point d) :
    (kernel S e r Ds main final N hr hDs hmass L hL hF hell hlo hup J x).map
      (past S e r Ds main final N k hk) =
    (iteration S e r Ds main final N hr hDs hmass L hL hF hell hlo hup J k hk ∘ₘ
      initial S e r Ds main final N L x).map (past S e r Ds main final N k hk) := by
  rw [kernel,Kernel.comp_apply,Measure.map_comp _ _ (past_measurable S e r Ds main final N k hk),
    iteration_past S e r Ds main final N hr hDs hmass L hL hF hell hlo hup J k N hk hk le_rfl,
    Measure.map_comp _ _ (past_measurable S e r Ds main final N k hk)]

/-- The stored coarse source triple and the entire original tape. In
particular the stored setup position is retained together with its occurrence. -/
def sourceView (z : History d N n × Tape d (Host S e r Ds main final N)) := (z.1.1,z.2)

theorem sourceView_measurable : Measurable (sourceView (d := d) S e r Ds main final N) :=
  measurable_fst.fst.prodMk measurable_snd

/-- Actual coarse/source consistency, as an exact measure equality.
The stored center/setup position/parent momentum are not independently sampled. -/
theorem kernel_sourceView (x : Point d) :
    (kernel S e r Ds main final N hr hDs hmass L hL hF hell hlo hup J x).map
      (sourceView S e r Ds main final N) =
    (initial S e r Ds main final N L x).map (sourceView S e r Ds main final N) := by
  have h := congrArg (fun ν => ν.map Prod.fst)
    (kernel_past S e r Ds main final N hr hDs hmass L hL hF hell hlo hup J 0 (by omega) x)
  rw [Measure.map_map measurable_fst (past_measurable S e r Ds main final N 0 (by omega)),
    Measure.map_map measurable_fst (past_measurable S e r Ds main final N 0 (by omega)),
    iteration,Measure.id_comp] at h
  exact h

end HistoryPersistence

section Benchmark
variable {m n d : ℕ} (S : SamplingGeometry m) (e : Fin n ≃ S.Node)
  (r Ds : ℝ) (main final : Fin n → ExecutableData) (N : ℕ)
local notation "X" => History d N n × Tape d (Host S e r Ds main final N)
local notation "A" => samplingMatrix S e r
local notation "rho" => samplingNoise S r Ds
local notation "Cmat" => residualRoot A rho (r^2)
local notation "sigma" => RecursiveMeanPublicTable.mainWidth n r (S.R) Ds (r^2)

/-- The recorded reference array, extended by zero outside actual execution. -/
def returnedReference (k : ℕ) (i : Fin n) (z : X) : Point d :=
  if hk : k<N then z.1.2.1 ⟨k,hk⟩ i else 0

theorem returnedReference_measurable (k : ℕ) (i : Fin n) :
    Measurable (returnedReference (d := d) S e r Ds main final N k i) := by
  unfold returnedReference
  split_ifs <;> fun_prop

/-- The comparison reconstructed from the actual initial occurrence or the
last returned vector and the same physical residual occurrence. -/
def comparisonNoise : (k : ℕ) → (hk : k≤N) → X → Fin n → Point d
  | 0, _, z => fun i => (z.2.2.2.2.2.2.1 i).1
  | k+1, hk, z => nextComparison S e r Ds (z.1.2.1 ⟨k,by omega⟩)
      (fun i => PrivateSamplingExecutionSchedule.residualNoise S e r Ds main final N k i z.2)

variable (hr : 0<r) (hDs : 0<Ds)
  (hmass : ∀ i, CovarianceSetup.shiftSq (main i).shiftVector ≤ Ds^2)
  (L : PrimitiveLaws d)

include hr hDs hmass L in
theorem residualNoise_measurable (k : ℕ) (hk : k<N) (i : Fin n) :
    Measurable (PrivateSamplingExecutionSchedule.residualNoise (d := d) S e r Ds main final N k i) := by
  have he : PrivateSamplingExecutionSchedule.residualNoise (d := d) S e r Ds main final N k i =
      (fun sample => (show Point d from ((split (afterBatch (batchCut S e r Ds main final N hr hDs hmass
        (stage S e r Ds main final N k hk.le).1
        (stage_positive S e r Ds main final N k hk))) sample).2.1 i).1)) := by
    funext sample
    exact (stage_residual S e r Ds main final N hr hDs hmass k hk i sample).symm
  rw [he]
  exact ((measurable_pi_apply i).comp
    (measurePreserving_split L (afterBatch (batchCut S e r Ds main final N hr hDs hmass
      (stage S e r Ds main final N k hk.le).1
      (stage_positive S e r Ds main final N k hk)))).measurable.snd.fst).fst

include hr hDs hmass L in
theorem comparisonNoise_measurable (k : ℕ) (hk : k≤N) :
    Measurable (comparisonNoise (d := d) S e r Ds main final N k hk) := by
  cases k with
  | zero => unfold comparisonNoise; fun_prop
  | succ k =>
    have hf : Measurable (fun z : X => z.1.2.1 (⟨k,by omega⟩ : Fin N)) := by fun_prop
    have hz : Measurable (fun z : X => fun i =>
        PrivateSamplingExecutionSchedule.residualNoise S e r Ds main final N k i z.2) :=
      Measurable.of_eval fun i =>
        (residualNoise_measurable S e r Ds main final N hr hDs hmass L k (by omega) i).comp measurable_snd
    have he : comparisonNoise (d := d) S e r Ds main final N (k+1) hk =
        (fun z : X => nextComparison S e r Ds (z.1.2.1 (⟨k,by omega⟩ : Fin N))
          (fun i => PrivateSamplingExecutionSchedule.residualNoise S e r Ds main final N k i z.2)) := by
      funext z
      rfl
    rw [he]
    apply Measurable.of_eval
    intro i
    exact ((Finset.measurable_sum Finset.univ (fun j _ =>
      (((measurable_pi_apply j).comp hf).const_smul sigma).const_smul (A i j))).add
      (Finset.measurable_sum Finset.univ (fun j _ =>
        ((measurable_pi_apply j).comp hz).const_smul (Cmat i j)))).const_smul rho⁻¹

include hr hDs in
/-- This is the existing SharedLayerRms benchmark with the literal recorded
references and raw residual schedule, before any probability or Gaussian law. -/
theorem benchmark_eq_comparisonNoise (k : ℕ) (hk : k≤N) (Phi : Fin n → X → Point d)
    (z : X) (i : Fin n) :
    SharedLayerRms.benchmark Phi A Cmat sigma
      (returnedReference S e r Ds main final N)
      (fun k i z => PrivateSamplingExecutionSchedule.residualNoise S e r Ds main final N k i z.2)
      (fun i z => rho • (show Point d from (z.2.2.2.2.2.2.1 i).1)) k i z =
        Phi i z + rho • comparisonNoise S e r Ds main final N k hk z i := by
  cases k with
  | zero => rfl
  | succ k =>
    dsimp only [SharedLayerRms.benchmark,SharedLayerRms.benchmarkLayer,comparisonNoise]
    rw [noise_mul_nextComparison S e r Ds hr hDs]
    simp only [returnedReference,dite_eq_left (show k<N by omega)]
    abel

/-- A concrete executed record satisfies the next benchmark identity
pointwise; its complete input tape remains the same tape. -/
theorem record_comparisonNoise (k : ℕ) (hk : k<N)
    (z : X × (Fin n → Point d)) :
    (record S e r Ds main final N hr hDs hmass
      (stage S e r Ds main final N k hk.le).1
      (stage_positive S e r Ds main final N k hk) ⟨k,hk⟩ z).1.2.2 =
    comparisonNoise S e r Ds main final N (k+1) (by omega)
      (record S e r Ds main final N hr hDs hmass
        (stage S e r Ds main final N k hk.le).1
        (stage_positive S e r Ds main final N k hk) ⟨k,hk⟩ z) := by
  dsimp only [record,comparisonNoise]
  rw [Function.update_self]
  congr 1
  funext i
  exact stage_residual S e r Ds main final N hr hDs hmass k hk i z.1.2
variable (hL : L.pointDraw = stdGaussian (Point d))
  {F : Point d → ℝ} (hF : ContDiff ℝ 2 F) {ell : ℝ} (hell : 0≤ell)
  (hlo : ∀ z v, 0≤fderiv ℝ (fderiv ℝ F) z v v)
  (hup : ∀ z v, fderiv ℝ (fderiv ℝ F) z v v≤ell*‖v‖^2)

private theorem step_ae_of_record (s : Cursor S e r Ds main final N) (hs : 0<s.remaining)
    (k : Fin N) (J : FreshChildBatchCoupling.Lower L (data S e r Ds main final N hr hDs hmass s hs))
    (z : X) (Q : X → Prop) (hQ : MeasurableSet {w | Q w})
    (hrecord : ∀ g, Q (record S e r Ds main final N hr hDs hmass s hs k (z,g))) :
    ∀ᵐ w ∂PrivateChronologicalCoupling.step S e r Ds main final N hr hDs hmass L hL hF hell hlo hup s hs k J z,
      Q w := by
  rw [PrivateChronologicalCoupling.step,Kernel.map_apply _
    (record_measurable S e r Ds main final N hr hDs hmass L s hs k)]
  apply (ae_map_iff (record_measurable S e r Ds main final N hr hDs hmass L s hs k).aemeasurable hQ).2
  rw [adjoin,CausalTailHistory.onTape,Kernel.prod_apply,Kernel.id_apply,Measure.dirac_prod]
  apply (ae_map_iff (measurable_const.prodMk measurable_id).aemeasurable
    ((record_measurable S e r Ds main final N hr hDs hmass L s hs k) hQ)).2
  exact Filter.Eventually.of_forall hrecord

/-- A real executed layer, on every entering history and original tape,
records precisely the next raw-schedule benchmark comparison. -/
theorem step_comparisonNoise_ae (k : ℕ) (hk : k<N)
    (J : FreshChildBatchCoupling.Lower L (data S e r Ds main final N hr hDs hmass
      (stage S e r Ds main final N k hk.le).1
      (stage_positive S e r Ds main final N k hk))) (z : X) :
    ∀ᵐ w ∂PrivateChronologicalCoupling.step S e r Ds main final N hr hDs hmass L hL hF hell hlo hup
      (stage S e r Ds main final N k hk.le).1
      (stage_positive S e r Ds main final N k hk) ⟨k,hk⟩ J z,
      w.1.2.2 = comparisonNoise S e r Ds main final N (k+1) (by omega) w := by
  apply step_ae_of_record S e r Ds main final N hr hDs hmass L hL hF hell hlo hup _ _ _ J z _
    (measurableSet_eq_fun measurable_fst.snd.snd
      (comparisonNoise_measurable S e r Ds main final N hr hDs hmass L (k+1) (by omega)))
  intro g
  exact record_comparisonNoise S e r Ds main final N hr hDs hmass k hk (z,g)

include hr hDs hmass L in
private theorem comparisonNoise_event (k : ℕ) (hk : k≤N) :
    MeasurableSet {w : X | w.1.2.2 = comparisonNoise S e r Ds main final N k hk w} :=
  measurableSet_eq_fun measurable_fst.snd.snd
    (comparisonNoise_measurable S e r Ds main final N hr hDs hmass L k hk)

include hr hDs hmass in
/-- The actual initial comparison is the literal initialization occurrence. -/
theorem initial_comparisonNoise_ae (x : Point d) :
    ∀ᵐ w ∂initial S e r Ds main final N L x,
      w.1.2.2 = comparisonNoise S e r Ds main final N 0 (by omega) w := by
  rw [initial,Kernel.map_apply _ (initializeState_measurable S e r Ds main final N)]
  apply (ae_map_iff (initializeState_measurable S e r Ds main final N).aemeasurable
    (comparisonNoise_event S e r Ds main final N hr hDs hmass L 0 (by omega))).2
  exact Filter.Eventually.of_forall fun _ => rfl

variable
  (J : ∀ (j : ℕ) (hj : j<N), FreshChildBatchCoupling.Lower L
    (data S e r Ds main final N hr hDs hmass
      (stage S e r Ds main final N j hj.le).1
      (stage_positive S e r Ds main final N j hj)))

/-- The comparison at every actual finite stage is the benchmark read from
that very sample's returned array and complete original tape. -/
theorem iteration_comparisonNoise_ae (k : ℕ) (hk : k≤N) (x : Point d) :
    ∀ᵐ w ∂iteration S e r Ds main final N hr hDs hmass L hL hF hell hlo hup J k hk ∘ₘ
      initial S e r Ds main final N L x,
      w.1.2.2 = comparisonNoise S e r Ds main final N k hk w := by
  cases k with
  | zero =>
    simpa only [iteration,Measure.id_comp] using
      initial_comparisonNoise_ae S e r Ds main final N hr hDs hmass L x
  | succ k =>
    rw [iteration,← Measure.comp_assoc]
    apply Measure.ae_comp_of_ae_ae (comparisonNoise_event S e r Ds main final N hr hDs hmass L (k+1) hk)
    exact Filter.Eventually.of_forall fun z =>
      step_comparisonNoise_ae S e r Ds main final N hr hDs hmass L hL hF hell hlo hup k (by omega) _ z

/-- Final finite-loop support, including the zero-layer source program. -/
theorem kernel_comparisonNoise_ae (x : Point d) :
    ∀ᵐ w ∂kernel S e r Ds main final N hr hDs hmass L hL hF hell hlo hup J x,
      w.1.2.2 = comparisonNoise S e r Ds main final N N le_rfl w := by
  simpa only [kernel,Kernel.comp_apply] using
    iteration_comparisonNoise_ae S e r Ds main final N hr hDs hmass L hL hF hell hlo hup J N le_rfl x

/-- The finite truncation in the pre-existing RMS adapter leaves the actual
recorded reference readout unchanged. -/
theorem finiteReference_returnedReference :
    SourceMeanRetainedRms.finiteReference N (returnedReference (d := d) S e r Ds main final N) =
      returnedReference S e r Ds main final N := by
  funext k i z
  by_cases hk : k<N <;> simp [SourceMeanRetainedRms.finiteReference,returnedReference,hk]

/-- The concrete actual-flow benchmark used by PrivateSamplingRetainedRms,
with its unchanged tape, equals the chronological final comparison state. -/
theorem kernel_actual_benchmark_ae (x : Point d) :
    ∀ᵐ w ∂kernel S e r Ds main final N hr hDs hmass L hL hF hell hlo hup J x,
      ∀ i,
      SharedLayerRms.benchmark
        (fun j (z : X) => PrivateSamplingRetainedRms.reference S e r Ds main final N hF hell hlo hup x hr j z.2)
        A Cmat sigma
        (SourceMeanRetainedRms.finiteReference N (returnedReference S e r Ds main final N))
        (fun k i z => PrivateSamplingExecutionSchedule.residualNoise S e r Ds main final N k i z.2)
        (fun i z => PrivateSamplingRetainedRms.initialNoise S e r Ds main final N i z.2) N i w =
      PrivateSamplingRetainedRms.reference S e r Ds main final N hF hell hlo hup x hr i w.2 +
        rho • w.1.2.2 i := by
  rw [finiteReference_returnedReference]
  filter_upwards [kernel_comparisonNoise_ae S e r Ds main final N hr hDs hmass L hL hF hell hlo hup J x]
    with w hw
  intro i
  have H := benchmark_eq_comparisonNoise S e r Ds main final N hr hDs N le_rfl
    (fun j (z : X) => PrivateSamplingRetainedRms.reference S e r Ds main final N hF hell hlo hup x hr j z.2) w i
  rw [← hw] at H
  exact H
end Benchmark


end AcceleratedLogConcave.Oracle.PrivateChronologicalExecution
