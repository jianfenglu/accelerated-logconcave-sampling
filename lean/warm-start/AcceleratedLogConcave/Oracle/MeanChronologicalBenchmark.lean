import AcceleratedLogConcave.Oracle.MeanChronologicalPast
import AcceleratedLogConcave.Oracle.SourceMeanRetainedRms

/-! Actual same-tape mean benchmark, using the source MAIN-child width
rather than the different parent output width. -/
noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace AcceleratedLogConcave.Oracle.MeanChronologicalBenchmark
open Numerics Numerics.AffineGraph AffineLowering TapeLowering NoisyLayer CovarianceSetup
open SourceExecutableTables TailOccurrenceCut TailCut CanonicalTapeLaw CanonicalTapeMeasurability
open MeanChronologicalCoupling MeanChronologicalExecution PrivateCausalLayer PrivateCausalAdvance
local instance canonicalTapeSpace {d c : ℕ} {Γ : Ctx} {τ : Ty} (p : Prog c Γ τ) :
    MeasurableSpace (Tape d p) := tapeSpace d p
local instance canonicalPrefixSpace {d c : ℕ} {Γ Δ : Ctx} {τ σ : Ty}
    {p : Prog c Γ τ} {q : Prog c Δ σ} (cut : TailCut q p) :
    MeasurableSpace (Prefix d cut) := prefixSpace d cut
variable {m n a h d : ℕ} (M : MeanGeometry m) (nodes : Fin n ≃ M.MeanNode)
  (anchors : Fin a ≃ M.Anchor) (seeds : Fin h ≃ Fin m × M.Kernel)
  (main : Fin n → ExecutableData) (final : Fin m → ExecutableData)
  (sampling : ExecutableData) (N : ℕ)
  {A : Type*} [MeasurableSpace A]
local notation "X" => History (d := d) M nodes anchors seeds main final sampling N A ×
  Tape d (Host M nodes anchors seeds main final sampling N)
def residualNoise (k : ℕ) (i : Fin n) (sample : Tape d (Host M nodes anchors seeds main final sampling N)) : Point d :=
  SourceMeanExecutionRms.noise M nodes main final sampling N
    (bodyTape M nodes anchors seeds main final sampling N) k i sample
variable (r Ds σ δ t scale : ℝ)
local notation "Bmat" => (fun i j => M.matrix r σ (nodes i) (nodes j))
local notation "rho" => RecursiveMeanPublicTable.centerNoise r M.R Ds
local notation "bound" => SourceMeanExecutable.rowBound (m := m) r σ δ t scale
local notation "Cmat" => residualRoot Bmat rho bound
local notation "sigma" => CovarianceSetup.sigma n rho bound
private theorem noise_mul_comparisonUpdate (hr : 0<r) (hDs : 0<Ds)
    (g z : Fin n → Point d) (i : Fin n) :
    rho • comparisonUpdate M nodes r Ds σ δ t scale (g,z) i =
      (∑ j, Bmat i j • (sigma • g j)) + ∑ j,Cmat i j • z j := by
  have hp := RecursiveExecutableDomain.center_noise_pos M r Ds hr hDs
  simp only [comparisonUpdate,ResidualGaussianRecombination.recombine,smul_smul,
    mul_inv_cancel₀ (ne_of_gt hp),one_smul]
/-- The recorded reference array, extended by zero outside actual execution. -/
def returnedReference (k : ℕ) (i : Fin n) (z : X) : Point d :=
  if hk : k<N then z.1.2.1 ⟨k,hk⟩ i else 0

theorem returnedReference_measurable (k : ℕ) (i : Fin n) :
    Measurable (returnedReference (d := d) (A := A) M nodes anchors seeds main final sampling N k i) := by
  unfold returnedReference
  split_ifs <;> fun_prop

/-- The comparison reconstructed from the actual initial occurrence or the
last returned vector and the same physical residual occurrence. -/
def comparisonNoise : (k : ℕ) → (hk : k≤N) → X → Fin n → Point d
  | 0, _, z => fun i => ((bodyTape M nodes anchors seeds main final sampling N z.2).1 i).1
  | k+1, hk, z => comparisonUpdate M nodes r Ds σ δ t scale ((z.1.2.1 ⟨k,by omega⟩),
      (fun i => residualNoise M nodes anchors seeds main final sampling N k i z.2))

variable (hr : 0<r) (hDs : 0<Ds)
  (hmass : ∀ i, CovarianceSetup.shiftSq (main i).shiftVector ≤ Ds^2)
  (L : PrimitiveLaws d)

include hr hDs hmass L in
theorem residualNoise_measurable (k : ℕ) (hk : k<N) (i : Fin n) :
    Measurable (residualNoise (d := d) M nodes anchors seeds main final sampling N k i) := by
  have he : residualNoise (d := d) M nodes anchors seeds main final sampling N k i =
      (fun sample => (show Point d from ((split (afterBatch (batchCut M nodes anchors seeds main final sampling N r Ds hr hDs hmass
        (stage M nodes anchors seeds main final sampling N k hk.le).1
        (stage_positive M nodes anchors seeds main final sampling N k hk))) sample).2.1 i).1)) := by
    funext sample
    exact (stage_residual M nodes anchors seeds main final sampling N r Ds hr hDs hmass k hk i sample).symm
  rw [he]
  exact ((measurable_pi_apply i).comp
    (measurePreserving_split L (afterBatch (batchCut M nodes anchors seeds main final sampling N r Ds hr hDs hmass
      (stage M nodes anchors seeds main final sampling N k hk.le).1
      (stage_positive M nodes anchors seeds main final sampling N k hk)))).measurable.snd.fst).fst

include hr hDs hmass L in
theorem comparisonNoise_measurable (k : ℕ) (hk : k≤N) :
    Measurable (comparisonNoise (d := d) (A := A) M nodes anchors seeds main final sampling N r Ds σ δ t scale k hk) := by
  cases k with
  | zero =>
    have hb := (measurePreserving_split L (MeanMainBatchCoupling.bodyCut M nodes anchors seeds main final sampling N)).measurable.snd
    apply Measurable.of_eval
    intro i
    exact ((measurable_pi_apply i).comp (hb.comp measurable_snd).fst).fst
  | succ k =>
    have hf : Measurable (fun z : X => z.1.2.1 (⟨k,by omega⟩ : Fin N)) := by fun_prop
    have hz : Measurable (fun z : X => fun i =>
        residualNoise M nodes anchors seeds main final sampling N k i z.2) :=
      Measurable.of_eval fun i =>
        (residualNoise_measurable M nodes anchors seeds main final sampling N r Ds hr hDs hmass L k (by omega) i).comp measurable_snd
    have he : comparisonNoise (d := d) (A := A) M nodes anchors seeds main final sampling N r Ds σ δ t scale (k+1) hk =
        (fun z : X => comparisonUpdate M nodes r Ds σ δ t scale ((z.1.2.1 (⟨k,by omega⟩ : Fin N)),
          (fun i => residualNoise M nodes anchors seeds main final sampling N k i z.2))) := by
      funext z
      rfl
    rw [he]
    apply Measurable.of_eval
    intro i
    exact ((Finset.measurable_sum Finset.univ (fun j _ =>
      (((measurable_pi_apply j).comp hf).const_smul sigma).const_smul (Bmat i j))).add
      (Finset.measurable_sum Finset.univ (fun j _ =>
        ((measurable_pi_apply j).comp hz).const_smul (Cmat i j)))).const_smul rho⁻¹

include hr hDs in
omit [MeasurableSpace A] in
/-- This is the existing SharedLayerRms benchmark with the literal recorded
references and raw residual schedule, before any probability or Gaussian law. -/
theorem benchmark_eq_comparisonNoise (k : ℕ) (hk : k≤N) (Phi : Fin n → X → Point d)
    (z : X) (i : Fin n) :
    SharedLayerRms.benchmark Phi Bmat Cmat sigma
      (returnedReference M nodes anchors seeds main final sampling N)
      (fun k i z => residualNoise M nodes anchors seeds main final sampling N k i z.2)
      (fun i z => rho • (show Point d from ((bodyTape M nodes anchors seeds main final sampling N z.2).1 i).1)) k i z =
        Phi i z + rho • comparisonNoise M nodes anchors seeds main final sampling N r Ds σ δ t scale k hk z i := by
  cases k with
  | zero => rfl
  | succ k =>
    dsimp only [SharedLayerRms.benchmark,SharedLayerRms.benchmarkLayer,comparisonNoise]
    rw [noise_mul_comparisonUpdate M nodes r Ds σ δ t scale hr hDs]
    simp only [returnedReference,dite_eq_left (show k<N by omega)]
    abel

omit [MeasurableSpace A] in
/-- A concrete executed record satisfies the next benchmark identity
pointwise; its complete input tape remains the same tape. -/
theorem record_comparisonNoise (k : ℕ) (hk : k<N)
    (z : X × (Fin n → Point d)) :
    (record M nodes anchors seeds main final sampling N r Ds hr hDs hmass σ δ t scale
      (stage M nodes anchors seeds main final sampling N k hk.le).1
      (stage_positive M nodes anchors seeds main final sampling N k hk) ⟨k,hk⟩ z).1.2.2 =
    comparisonNoise M nodes anchors seeds main final sampling N r Ds σ δ t scale (k+1) (by omega)
      (record M nodes anchors seeds main final sampling N r Ds hr hDs hmass σ δ t scale
        (stage M nodes anchors seeds main final sampling N k hk.le).1
        (stage_positive M nodes anchors seeds main final sampling N k hk) ⟨k,hk⟩ z) := by
  dsimp only [record,comparisonNoise]
  rw [Function.update_self]
  congr 1
  refine Prod.ext ?_ ?_
  · rfl
  funext i
  exact stage_residual M nodes anchors seeds main final sampling N r Ds hr hDs hmass k hk i z.1.2
variable (hL : L.pointDraw = stdGaussian (Point d))
  (x P referencePosition : A → Point d) (hx : Measurable x) (hP : Measurable P)
  (hreference : Measurable referencePosition)
  {F : Point d → ℝ} (hF : ContDiff ℝ 2 F) {ell : ℝ} (hell : 0≤ell)
  (hlo : ∀ z v, 0≤fderiv ℝ (fderiv ℝ F) z v v)
  (hup : ∀ z v, fderiv ℝ (fderiv ℝ F) z v v≤ell*‖v‖^2)

variable (hσ : 0<σ) (hsmall : r^2*ell≤1/2)

private theorem step_ae_of_record (s : Cursor M nodes anchors seeds main final sampling N) (hs : 0<s.remaining)
    (k : Fin N) (J : FreshChildBatchCoupling.Lower L (data M nodes anchors seeds main final sampling N r Ds hr hDs hmass s hs))
    (z : X) (Q : X → Prop) (hQ : MeasurableSet {w | Q w})
    (hrecord : ∀ g, Q (record M nodes anchors seeds main final sampling N r Ds hr hDs hmass σ δ t scale s hs k (z,g))) :
    ∀ᵐ w ∂MeanChronologicalCoupling.step M nodes anchors seeds main final sampling N r Ds hr hDs hmass L hL x P referencePosition hx hP hreference hF hell hlo hup σ hσ hsmall δ t scale s hs k J z,
      Q w := by
  rw [MeanChronologicalCoupling.step,Kernel.map_apply _
    (record_measurable M nodes anchors seeds main final sampling N r Ds hr hDs hmass L σ δ t scale s hs k)]
  apply (ae_map_iff (record_measurable M nodes anchors seeds main final sampling N r Ds hr hDs hmass L σ δ t scale s hs k).aemeasurable hQ).2
  rw [adjoin,CausalTailHistory.onTape,Kernel.prod_apply,Kernel.id_apply,Measure.dirac_prod]
  apply (ae_map_iff (measurable_const.prodMk measurable_id).aemeasurable
    ((record_measurable M nodes anchors seeds main final sampling N r Ds hr hDs hmass L σ δ t scale s hs k) hQ)).2
  exact Filter.Eventually.of_forall hrecord

/-- A real executed layer, on every entering history and original tape,
records precisely the next raw-schedule benchmark comparison. -/
theorem step_comparisonNoise_ae (k : ℕ) (hk : k<N)
    (J : FreshChildBatchCoupling.Lower L (data M nodes anchors seeds main final sampling N r Ds hr hDs hmass
      (stage M nodes anchors seeds main final sampling N k hk.le).1
      (stage_positive M nodes anchors seeds main final sampling N k hk))) (z : X) :
    ∀ᵐ w ∂MeanChronologicalCoupling.step M nodes anchors seeds main final sampling N r Ds hr hDs hmass L hL x P referencePosition hx hP hreference hF hell hlo hup σ hσ hsmall δ t scale
      (stage M nodes anchors seeds main final sampling N k hk.le).1
      (stage_positive M nodes anchors seeds main final sampling N k hk) ⟨k,hk⟩ J z,
      w.1.2.2 = comparisonNoise M nodes anchors seeds main final sampling N r Ds σ δ t scale (k+1) (by omega) w := by
  apply step_ae_of_record M nodes anchors seeds main final sampling N r Ds σ δ t scale hr hDs hmass L hL x P referencePosition hx hP hreference hF hell hlo hup hσ hsmall _ _ _ J z _
    (measurableSet_eq_fun measurable_fst.snd.snd
      (comparisonNoise_measurable M nodes anchors seeds main final sampling N r Ds σ δ t scale hr hDs hmass L (k+1) (by omega)))
  intro g
  exact record_comparisonNoise M nodes anchors seeds main final sampling N r Ds σ δ t scale hr hDs hmass k hk (z,g)


include hr hDs hmass L in
private theorem comparisonNoise_event (k : ℕ) (hk : k≤N) :
    MeasurableSet {z : X | z.1.2.2 = comparisonNoise M nodes anchors seeds main final sampling N r Ds σ δ t scale k hk z} :=
  measurableSet_eq_fun measurable_fst.snd.snd
    (comparisonNoise_measurable M nodes anchors seeds main final sampling N r Ds σ δ t scale hr hDs hmass L k hk)

omit [MeasurableSpace A] in
/-- The literal initial noise readout agrees pointwise with initialization. -/
theorem prepare_comparisonNoise (z : A × Tape d (Host M nodes anchors seeds main final sampling N)) :
    (MeanInitialComparison.prepare M nodes anchors seeds main final sampling N z).1.2.2 =
      comparisonNoise M nodes anchors seeds main final sampling N r Ds σ δ t scale 0 (by omega)
        (MeanInitialComparison.prepare M nodes anchors seeds main final sampling N z) := by
  rfl

include hr hDs hmass L in
theorem initial_comparisonNoise_ae (μ : Measure (A × Tape d (Host M nodes anchors seeds main final sampling N))) :
    ∀ᵐ z ∂μ.map (MeanInitialComparison.prepare M nodes anchors seeds main final sampling N),
      z.1.2.2 = comparisonNoise M nodes anchors seeds main final sampling N r Ds σ δ t scale 0 (by omega) z := by
  apply (ae_map_iff (MeanInitialComparison.prepare_measurable M nodes anchors seeds main final sampling N L).aemeasurable
    (comparisonNoise_event M nodes anchors seeds main final sampling N r Ds σ δ t scale hr hDs hmass L 0 (by omega))).2
  exact Filter.Eventually.of_forall (prepare_comparisonNoise M nodes anchors seeds main final sampling N r Ds σ δ t scale)

variable (J : ∀ (k : ℕ) (hk : k<N), FreshChildBatchCoupling.Lower L
  (data M nodes anchors seeds main final sampling N r Ds hr hDs hmass
    (stage M nodes anchors seeds main final sampling N k hk.le).1
    (stage_positive M nodes anchors seeds main final sampling N k hk)))

theorem iteration_comparisonNoise_ae (k : ℕ) (hk : k≤N)
    (μ : Measure (A × Tape d (Host M nodes anchors seeds main final sampling N))) :
    ∀ᵐ z ∂iteration M nodes anchors seeds main final sampling N r Ds hr hDs hmass L hL x P referencePosition hx hP hreference
      hF hell hlo hup σ hσ hsmall δ t scale J k hk ∘ₘ
        μ.map (MeanInitialComparison.prepare M nodes anchors seeds main final sampling N),
      z.1.2.2 = comparisonNoise M nodes anchors seeds main final sampling N r Ds σ δ t scale k hk z := by
  cases k with
  | zero =>
    simpa only [iteration,Measure.id_comp] using
      initial_comparisonNoise_ae M nodes anchors seeds main final sampling N r Ds σ δ t scale hr hDs hmass L μ
  | succ k =>
    rw [iteration,← Measure.comp_assoc]
    apply Measure.ae_comp_of_ae_ae (comparisonNoise_event M nodes anchors seeds main final sampling N r Ds σ δ t scale hr hDs hmass L (k+1) hk)
    exact Filter.Eventually.of_forall fun z =>
      step_comparisonNoise_ae M nodes anchors seeds main final sampling N r Ds σ δ t scale hr hDs hmass L hL x P referencePosition hx hP hreference hF hell hlo hup hσ hsmall k (by omega) _ z

/-- Final finite-loop support, including N=0, on an arbitrary incoming law. -/
theorem kernel_comparisonNoise_ae
    (μ : Measure (A × Tape d (Host M nodes anchors seeds main final sampling N))) :
    ∀ᵐ z ∂kernel M nodes anchors seeds main final sampling N r Ds hr hDs hmass L hL x P referencePosition hx hP hreference
      hF hell hlo hup σ hσ hsmall δ t scale J ∘ₘ μ,
      z.1.2.2 = comparisonNoise M nodes anchors seeds main final sampling N r Ds σ δ t scale N le_rfl z := by
  rw [kernel,← Measure.comp_assoc,Measure.deterministic_comp_eq_map]
  exact iteration_comparisonNoise_ae M nodes anchors seeds main final sampling N r Ds σ δ t scale hr hDs hmass L hL x P referencePosition hx hP hreference hF hell hlo hup hσ hsmall J N le_rfl μ

/-- Correct child-width benchmark on the actual final chronological law. -/
theorem kernel_benchmark_ae (Phi : Fin n → X → Point d)
    (μ : Measure (A × Tape d (Host M nodes anchors seeds main final sampling N))) :
    ∀ᵐ z ∂kernel M nodes anchors seeds main final sampling N r Ds hr hDs hmass L hL x P referencePosition hx hP hreference
      hF hell hlo hup σ hσ hsmall δ t scale J ∘ₘ μ, ∀ i,
      SharedLayerRms.benchmark Phi Bmat Cmat sigma
        (returnedReference M nodes anchors seeds main final sampling N)
        (fun k i z => residualNoise M nodes anchors seeds main final sampling N k i z.2)
        (fun i z => rho • (show Point d from ((bodyTape M nodes anchors seeds main final sampling N z.2).1 i).1)) N i z =
          Phi i z + rho • z.1.2.2 i := by
  filter_upwards [kernel_comparisonNoise_ae M nodes anchors seeds main final sampling N r Ds σ δ t scale hr hDs hmass L hL x P referencePosition hx hP hreference hF hell hlo hup hσ hsmall J μ] with z hz
  intro i
  rw [benchmark_eq_comparisonNoise M nodes anchors seeds main final sampling N r Ds σ δ t scale hr hDs N le_rfl,← hz]

end AcceleratedLogConcave.Oracle.MeanChronologicalBenchmark
