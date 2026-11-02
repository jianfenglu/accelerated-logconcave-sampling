import AcceleratedLogConcave.Oracle.MeanCompletedCoupling
import AcceleratedLogConcave.Oracle.MeanChronologicalPast
import AcceleratedLogConcave.Oracle.MeanChronologicalBenchmark
import AcceleratedLogConcave.Oracle.MeanChronologicalLowerProjection
import AcceleratedLogConcave.Oracle.MeanCompletedMainReadout
import AcceleratedLogConcave.Oracle.FreshChildRunShift
import AcceleratedLogConcave.Oracle.FreshChildBatchErrorTransfer
import AcceleratedLogConcave.Oracle.MeanChronologicalLaws
import AcceleratedLogConcave.Oracle.MeanChronologicalSuffix
import AcceleratedLogConcave.Oracle.PrivateChronologicalLaws

/-! Joint Gaussian comparison laws of the actual finite mean-main coupling.
The static coarse host retains incoming correlations and the original parent.
Only the complete unread tape is a fresh product factor. -/
noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace AcceleratedLogConcave.Oracle.MeanMainErrorTransport
open Numerics Numerics.AffineGraph AffineLowering TapeLowering NoisyLayer
open RecursiveMeanProgram RecursiveMeanContinuation SourceMeanLayer SourceMeanExecutable
open TailOccurrenceCut TailCut CanonicalTapeLaw CanonicalTapeMeasurability
open PrivateCausalLayer PrivateCausalAdvance MeanChronologicalCoupling MeanChronologicalSuffix
local instance canonicalTapeSpace {d c : ℕ} {Γ : Ctx} {τ : Ty} (p : Prog c Γ τ) :
    MeasurableSpace (Tape d p) := tapeSpace d p
local instance canonicalPrefixSpace {d c : ℕ} {Γ Δ : Ctx} {τ σ : Ty}
    {p : Prog c Γ τ} {q : Prog c Δ σ} (cut : TailCut q p) :
    MeasurableSpace (Prefix d cut) := prefixSpace d cut
variable {m n a h d : ℕ} (M : MeanGeometry m) (nodes : Fin n ≃ M.MeanNode)
  (anchors : Fin a ≃ M.Anchor) (seeds : Fin h ≃ Fin m × M.Kernel)
  (main : Fin n → ExecutableData) (final : Fin m → ExecutableData) (sampling : ExecutableData) (N : ℕ)
  (r Ds : ℝ) (hr : 0<r) (hDs : 0<Ds)
  (hmass : ∀ i,CovarianceSetup.shiftSq (main i).shiftVector≤Ds^2)
  {A : Type*} [MeasurableSpace A]
  (L : PrimitiveLaws d) (hL : L.pointDraw=stdGaussian (Point d))
  (x P referencePosition : A → Point d) (hx : Measurable x) (hP : Measurable P)
  (hreference : Measurable referencePosition)
  {F : Point d → ℝ} (hF : ContDiff ℝ 2 F) {ell : ℝ} (hell : 0≤ell)
  (hlo : ∀ z v,0≤fderiv ℝ (fderiv ℝ F) z v v)
  (hup : ∀ z v,fderiv ℝ (fderiv ℝ F) z v v≤ell*‖v‖^2)
  (σ : ℝ) (hσ : 0<σ) (hsmall : r^2*ell≤1/2) (δ t w : ℝ)
local instance : MeasurableSpace
    (Prefix d (MeanMainBatchCoupling.bodyCut M nodes anchors seeds main final sampling N)) := prefixSpace d _

local notation "Xmain" => History (d := d) M nodes anchors seeds main final sampling N A ×
  Tape d (Host M nodes anchors seeds main final sampling N)
local notation "centersM" => MeanChronologicalHost.center M nodes anchors seeds main final sampling N x P referencePosition hF hell hlo hup r σ hr hσ hsmall
local notation "hcentersM" => MeanChronologicalHost.center_measurable M nodes anchors seeds main final sampling N x P referencePosition hx hP hreference hF hell hlo hup r σ hr hσ hsmall
variable (J : ∀ (k : ℕ) (hk : k<N),FreshChildBatchCoupling.Lower L
  (data M nodes anchors seeds main final sampling N r Ds hr hDs hmass
    (stage M nodes anchors seeds main final sampling N k hk.le).1 (stage_positive M nodes anchors seeds main final sampling N k hk)))
open MeanChronologicalLowerProjection
variable (G : Point d → Point d) (hG : Measurable G)
local notation "rho" => RecursiveMeanPublicTable.centerNoise r M.R Ds
local notation "childWidth" => CovarianceSetup.sigma n rho (rowBound (m := m) r σ δ t w)
/-- Literal executed main callback at its Gaussian benchmark, before recording
this child's reference. The source tape and designated input are unchanged. -/
def benchmarkError (k : ℕ) (i : Fin n) (z : Xmain × (Fin n → Point d)) : Point d :=
  SourceMeanExecutionRms.evaluator M nodes r Ds main final sampling N G
    (MeanChronologicalExecution.bodyTape M nodes anchors seeds main final sampling N)
    (fun _ _ => 0) k i z.1.2 (centersM i z.1.1.1 + rho • z.1.1.2.2 i) -
      Gibbs.primitiveMean F (centersM i z.1.1.1) (M.radius r (nodes i)) - childWidth • z.2 i

def lowerError (i : Fin n) (z : Coarse (d := d) M nodes anchors seeds main final sampling N A ×
    ((Point d × Tape d (main i).program) × Point d)) : Point d :=
  FreshChildRunShift.lowerError (main i).program G (main i).coefficient
    (centersM i z.1) (Gibbs.primitiveMean F (centersM i z.1) (M.radius r (nodes i))) childWidth z.2

omit [MeasurableSpace A] in
/-- Same full source seed, exact QueryShift absorption, and lower reference. -/
theorem benchmarkError_eq_lowerError (k : ℕ) (hk : k<N) (i : Fin n)
    (hshift : ChildAbsorption.QueryShift (main i).program (main i).enumeration (main i).coefficient
      (M.radius r (nodes i)) (main i).shiftVector) (z : Xmain × (Fin n → Point d)) :
    benchmarkError M nodes anchors seeds main final sampling N r Ds hr x P referencePosition hF hell hlo hup σ hσ hsmall δ t w G k i z =
      lowerError M nodes anchors seeds main final sampling N r Ds hr x P referencePosition hF hell hlo hup σ hσ hsmall δ t w G i
        (mainLowerProjection M nodes anchors seeds main final sampling N r Ds hr hDs hmass k hk i z) := by
  let s := (stage M nodes anchors seeds main final sampling N k hk.le).1
  let hs := stage_positive M nodes anchors seeds main final sampling N k hk
  let B := data M nodes anchors seeds main final sampling N r Ds hr hDs hmass s hs
  let raw := (z.1.1.2.2 i,(split (batchCut M nodes anchors seeds main final sampling N r Ds hr hDs hmass s hs) z.1.2).2.1 i)
  have hrun := FreshChildRunShift.run_completedSource (main i).program (main i).enumeration
    (B.slot i) (B.old i) (B.designated i) (B.auxiliary i) rho (M.radius r (nodes i)) Ds
    (main i).shiftVector (main i).coefficient (B.rho_nonneg i) (B.radius_pos i)
    B.Ds_pos (B.shift_budget i) (B.small i) hshift G (centersM i z.1.1.1) raw
  have hv := congrArg (fun out => (show Point d from out.value)) hrun
  unfold benchmarkError
  rw [MeanCompletedMainReadout.evaluator_eq_run M nodes anchors seeds main final sampling N r Ds hr hDs hmass k hk]
  unfold lowerError FreshChildRunShift.lowerError
  rw [sub_add_eq_sub_sub]
  change _ = (show Point d from (run (main i).program G
    ⟨(main i).coefficient,centersM i z.1.1.1,
      (FreshChildAbsorbedLaw.completedSource (main i).program (main i).enumeration
        (B.slot i) (B.old i) (B.designated i) (B.auxiliary i) rho (M.radius r (nodes i)) (main i).shiftVector raw).1⟩
      Env.empty (FreshChildAbsorbedLaw.completedSource (main i).program (main i).enumeration
        (B.slot i) (B.old i) (B.designated i) (B.auxiliary i) rho (M.radius r (nodes i)) (main i).shiftVector raw).2).value) -
      (Gibbs.primitiveMean F (centersM i z.1.1.1) (M.radius r (nodes i))) - childWidth • z.2 i
  rw [hv]
  rfl

include hx hP hreference hG in
theorem lowerError_measurable (i : Fin n) :
    Measurable (lowerError M nodes anchors seeds main final sampling N r Ds hr x P referencePosition hF hell hlo hup σ hσ hsmall δ t w G i) := by
  have hc := hcentersM i
  have hu := (Gibbs.primitive_mean_lipschitz hF hell hlo hup (M.radius_pos r hr (nodes i))).continuous.measurable.comp hc
  have hp := CanonicalTapeMeasurability.program_point_of_measurable (main i).program G hG
    (fun _ => (main i).coefficient)
    (fun z : Coarse (d := d) M nodes anchors seeds main final sampling N A ×
      ((Point d × Tape d (main i).program) × Point d) => centersM i z.1)
    (fun z => z.2.1.1) (fun z => z.2.1.2)
    measurable_const (hc.comp measurable_fst) measurable_snd.fst.fst measurable_snd.fst.snd
  exact hp.sub ((hu.comp measurable_fst).add (measurable_snd.snd.const_smul childWidth))

variable (ha : 0<rowBound (m := m) r σ δ t w)
    (hA : ∀ i,∑ j,|M.matrix r σ (nodes i) (nodes j)|≤rowBound (m := m) r σ δ t w)
    (ρ : Measure (A × Tape d (Host M nodes anchors seeds main final sampling N))) [IsProbabilityMeasure ρ]
    (μ : Measure (A × Prefix d (MeanMainBatchCoupling.bodyCut M nodes anchors seeds main final sampling N))) [IsProbabilityMeasure μ]
    (hsplit : ρ.map (CausalTailHistory.unpack (MeanMainBatchCoupling.bodyCut M nodes anchors seeds main final sampling N))=
      μ.prod (tapeLaw L (body (a := a) (h := h) M nodes main final sampling N)))

include hx hP hreference hG ha hA hsplit in
/-- Exact error distribution of the actually adjoined child, on the same
full source. The target law is the lower kernel at the source benchmark center. -/
theorem benchmark_error_law (k : ℕ) (hk : k<N) (i : Fin n)
    (hshift : ChildAbsorption.QueryShift (main i).program (main i).enumeration (main i).coefficient
      (M.radius r (nodes i)) (main i).shiftVector) :
    (adjoin M nodes anchors seeds main final sampling N r Ds hr hDs hmass L hL x P referencePosition hx hP hreference hF hell hlo hup σ hσ hsmall
      (stage M nodes anchors seeds main final sampling N k hk.le).1
      (stage_positive M nodes anchors seeds main final sampling N k hk) (J k hk) ∘ₘ
        stageLaw M nodes anchors seeds main final sampling N r Ds hr hDs hmass L hL x P referencePosition hx hP hreference hF hell hlo hup σ hσ hsmall δ t w J ρ k hk.le).map
      (benchmarkError M nodes anchors seeds main final sampling N r Ds hr x P referencePosition hF hell hlo hup σ hσ hsmall δ t w G k i) =
    (μ ⊗ₘ ((J k hk).joint i).comap (centersM i) (hcentersM i)).map
      (lowerError M nodes anchors seeds main final sampling N r Ds hr x P referencePosition hF hell hlo hup σ hσ hsmall δ t w G i) := by
  have hp := mainLowerProjection_preserving M nodes anchors seeds main final sampling N r Ds hr hDs hmass L hL x P referencePosition hx hP hreference hF hell hlo hup σ hσ hsmall δ t w J ha hA ρ μ hsplit k hk i
  have hmeas := lowerError_measurable M nodes anchors seeds main final sampling N r Ds hr x P referencePosition hx hP hreference hF hell hlo hup σ hσ hsmall δ t w G hG i
  have he : benchmarkError M nodes anchors seeds main final sampling N r Ds hr x P referencePosition hF hell hlo hup σ hσ hsmall δ t w G k i =
      lowerError M nodes anchors seeds main final sampling N r Ds hr x P referencePosition hF hell hlo hup σ hσ hsmall δ t w G i ∘
        mainLowerProjection M nodes anchors seeds main final sampling N r Ds hr hDs hmass k hk i := by
    funext z
    exact benchmarkError_eq_lowerError M nodes anchors seeds main final sampling N r Ds hr hDs hmass x P referencePosition hF hell hlo hup σ hσ hsmall δ t w G k hk i hshift z
  rw [he,← Measure.map_map hmeas hp.measurable,hp.map_eq]

/-- The actual kth benchmark error after recording the kth returned reference.
The comparison is reconstructed from the unchanged source and previous refs. -/
def stageError (k : ℕ) (hk : k<N) (i : Fin n) (z : Xmain) : Point d :=
  SourceMeanExecutionRms.evaluator M nodes r Ds main final sampling N G
    (MeanChronologicalExecution.bodyTape M nodes anchors seeds main final sampling N)
    (fun _ _ => 0) k i z.2
      (centersM i z.1.1 + rho • MeanChronologicalBenchmark.comparisonNoise M nodes anchors seeds main final sampling N r Ds σ δ t w k hk.le z i) -
    Gibbs.primitiveMean F (centersM i z.1.1) (M.radius r (nodes i)) -
      childWidth • MeanChronologicalBenchmark.returnedReference M nodes anchors seeds main final sampling N k i z

omit [MeasurableSpace A] in
private theorem comparison_record (k : ℕ) (hk : k<N) (z : Xmain × (Fin n → Point d)) :
    MeanChronologicalBenchmark.comparisonNoise M nodes anchors seeds main final sampling N r Ds σ δ t w k hk.le
      (record M nodes anchors seeds main final sampling N r Ds hr hDs hmass σ δ t w
        (stage M nodes anchors seeds main final sampling N k hk.le).1
        (stage_positive M nodes anchors seeds main final sampling N k hk) ⟨k,hk⟩ z) =
    MeanChronologicalBenchmark.comparisonNoise M nodes anchors seeds main final sampling N r Ds σ δ t w k hk.le z.1 := by
  cases k with
  | zero => rfl
  | succ k =>
    dsimp only [MeanChronologicalBenchmark.comparisonNoise,record]
    rw [Function.update_of_ne]
    intro he
    have hh := congrArg Fin.val he
    change k = k+1 at hh
    omega

omit [MeasurableSpace A] in
theorem stageError_record (k : ℕ) (hk : k<N) (i : Fin n) (z : Xmain × (Fin n → Point d))
    (hcomparison : z.1.1.2.2 = MeanChronologicalBenchmark.comparisonNoise M nodes anchors seeds main final sampling N r Ds σ δ t w k hk.le z.1) :
    stageError M nodes anchors seeds main final sampling N r Ds hr x P referencePosition hF hell hlo hup σ hσ hsmall δ t w G k hk i
      (record M nodes anchors seeds main final sampling N r Ds hr hDs hmass σ δ t w
        (stage M nodes anchors seeds main final sampling N k hk.le).1
        (stage_positive M nodes anchors seeds main final sampling N k hk) ⟨k,hk⟩ z) =
    benchmarkError M nodes anchors seeds main final sampling N r Ds hr x P referencePosition hF hell hlo hup σ hσ hsmall δ t w G k i z := by
  unfold stageError
  rw [comparison_record M nodes anchors seeds main final sampling N r Ds hr hDs hmass σ δ t w k hk z,← hcomparison]
  simp only [MeanChronologicalBenchmark.returnedReference,dite_eq_left hk,record,Function.update_self]
  rfl

include hx hP hreference hG L hDs hmass in
theorem stageError_measurable (k : ℕ) (hk : k<N) (i : Fin n) :
    Measurable (stageError M nodes anchors seeds main final sampling N r Ds hr x P referencePosition hF hell hlo hup σ hσ hsmall δ t w G k hk i) := by
  let seed := MeanCompletedMainReadout.cursorSeed (d := d) M nodes anchors seeds main final sampling N r Ds hr hDs hmass
    (stage M nodes anchors seeds main final sampling N k hk.le).1 (stage_positive M nodes anchors seeds main final sampling N k hk) i
  have hs := (MeanCompletedMainReadout.cursorSeed_measurable M nodes anchors seeds main final sampling N r Ds hr hDs hmass L
    (stage M nodes anchors seeds main final sampling N k hk.le).1 (stage_positive M nodes anchors seeds main final sampling N k hk) i).comp
      (measurable_snd : Measurable (Prod.snd : Xmain → _))
  have hc := (hcentersM i).comp (measurable_fst.fst : Measurable (fun z : Xmain => z.1.1))
  have hn := (measurable_pi_apply i).comp (MeanChronologicalBenchmark.comparisonNoise_measurable (A := A) M nodes anchors seeds main final sampling N r Ds σ δ t w hr hDs hmass L k hk.le)
  have hu := (Gibbs.primitive_mean_lipschitz hF hell hlo hup (M.radius_pos r hr (nodes i))).continuous.measurable.comp hc
  have hp := CanonicalTapeMeasurability.program_point_of_measurable (main i).program G hG
    (fun _ => (main i).coefficient) (fun z : Xmain => centersM i z.1.1 + rho • MeanChronologicalBenchmark.comparisonNoise M nodes anchors seeds main final sampling N r Ds σ δ t w k hk.le z i)
    (fun z => (seed z.2).1) (fun z => (seed z.2).2) measurable_const
    (hc.add (hn.const_smul rho)) hs.fst hs.snd
  have href := (MeanChronologicalBenchmark.returnedReference_measurable (d := d) (A := A) M nodes anchors seeds main final sampling N k i).const_smul childWidth
  have he : stageError M nodes anchors seeds main final sampling N r Ds hr x P referencePosition hF hell hlo hup σ hσ hsmall δ t w G k hk i =
      (fun z : Xmain => (show Point d from (run (main i).program G
        ⟨(main i).coefficient,centersM i z.1.1 + rho • MeanChronologicalBenchmark.comparisonNoise M nodes anchors seeds main final sampling N r Ds σ δ t w k hk.le z i,(seed z.2).1⟩ Env.empty (seed z.2).2).value) -
        Gibbs.primitiveMean F (centersM i z.1.1) (M.radius r (nodes i)) - childWidth • MeanChronologicalBenchmark.returnedReference M nodes anchors seeds main final sampling N k i z) := by
    funext z
    unfold stageError
    rw [MeanCompletedMainReadout.evaluator_eq_run M nodes anchors seeds main final sampling N r Ds hr hDs hmass k hk]
  rw [he]
  exact (hp.sub hu).sub href

include hx hP hreference hG ha hA hsplit in
/-- The error immediately after its actual child executes has exactly the
lower-call retained error law, using only almost-everywhere benchmark support. -/
theorem stage_error_law (k : ℕ) (hk : k<N) (i : Fin n)
    (hshift : ChildAbsorption.QueryShift (main i).program (main i).enumeration (main i).coefficient
      (M.radius r (nodes i)) (main i).shiftVector) :
    (stageLaw M nodes anchors seeds main final sampling N r Ds hr hDs hmass L hL x P referencePosition hx hP hreference hF hell hlo hup σ hσ hsmall δ t w J ρ (k+1) (by omega)).map
      (stageError M nodes anchors seeds main final sampling N r Ds hr x P referencePosition hF hell hlo hup σ hσ hsmall δ t w G k hk i) =
    (μ ⊗ₘ ((J k hk).joint i).comap (centersM i) (hcentersM i)).map
      (lowerError M nodes anchors seeds main final sampling N r Ds hr x P referencePosition hF hell hlo hup σ hσ hsmall δ t w G i) := by
  let s := (stage M nodes anchors seeds main final sampling N k hk.le).1
  let hs := stage_positive M nodes anchors seeds main final sampling N k hk
  let oldLaw := stageLaw M nodes anchors seeds main final sampling N r Ds hr hDs hmass L hL x P referencePosition hx hP hreference hF hell hlo hup σ hσ hsmall δ t w J ρ k hk.le
  let adjoined := adjoin M nodes anchors seeds main final sampling N r Ds hr hDs hmass L hL x P referencePosition hx hP hreference hF hell hlo hup σ hσ hsmall s hs (J k hk) ∘ₘ oldLaw
  let recordFn := record (d := d) (A := A) M nodes anchors seeds main final sampling N r Ds hr hDs hmass σ δ t w s hs ⟨k,hk⟩
  let err := stageError M nodes anchors seeds main final sampling N r Ds hr x P referencePosition hF hell hlo hup σ hσ hsmall δ t w G k hk i
  have hrm : Measurable recordFn := record_measurable M nodes anchors seeds main final sampling N r Ds hr hDs hmass L σ δ t w s hs ⟨k,hk⟩
  have hem : Measurable err := stageError_measurable M nodes anchors seeds main final sampling N r Ds hr hDs hmass L x P referencePosition hx hP hreference hF hell hlo hup σ hσ hsmall δ t w G hG k hk i
  have hfst : MeasurePreserving (Prod.fst : Xmain × (Fin n → Point d) → Xmain) adjoined oldLaw := by
    refine ⟨measurable_fst,?_⟩
    rw [Measure.map_comp _ _ measurable_fst,← Kernel.fst_eq,adjoin_original,Measure.id_comp]
  have hc := hfst.quasiMeasurePreserving.ae
    (MeanChronologicalBenchmark.iteration_comparisonNoise_ae M nodes anchors seeds main final sampling N r Ds σ δ t w hr hDs hmass L hL x P referencePosition hx hP hreference hF hell hlo hup hσ hsmall J k hk.le ρ)
  have hae : err ∘ recordFn =ᵐ[adjoined]
      benchmarkError M nodes anchors seeds main final sampling N r Ds hr x P referencePosition hF hell hlo hup σ hσ hsmall δ t w G k i := by
    filter_upwards [hc] with z hz
    exact stageError_record M nodes anchors seeds main final sampling N r Ds hr hDs hmass x P referencePosition hF hell hlo hup σ hσ hsmall δ t w G k hk i z hz
  have hstage : stageLaw M nodes anchors seeds main final sampling N r Ds hr hDs hmass L hL x P referencePosition hx hP hreference hF hell hlo hup σ hσ hsmall δ t w J ρ (k+1) (by omega) = adjoined.map recordFn := by
    unfold stageLaw
    rw [iteration,← Measure.comp_assoc]
    exact (Measure.map_comp oldLaw _ hrm).symm
  rw [hstage,Measure.map_map hem hrm,Measure.map_congr hae]
  exact benchmark_error_law M nodes anchors seeds main final sampling N r Ds hr hDs hmass L hL x P referencePosition hx hP hreference hF hell hlo hup σ hσ hsmall δ t w J G hG ha hA ρ μ hsplit k hk i hshift


/-- Original source and the recorded finite reference prefix, with no loss of
uniform, Gaussian, or residual coordinates. -/
abbrev PastSample (k : ℕ) :=
  ((Coarse (d := d) M nodes anchors seeds main final sampling N A ×
    Tape d (Host M nodes anchors seeds main final sampling N)) × (Fin k → Fin n → Point d))

def restorePast (k : ℕ) (_hk : k≤N)
    (z : PastSample (d := d) (A := A) M nodes anchors seeds main final sampling N k) : Xmain :=
  ((z.1.1,((fun j => if hj : (j:ℕ)<k then z.2 ⟨j,hj⟩ else 0),fun _ => 0)),z.1.2)

theorem restorePast_measurable (k : ℕ) (hk : k≤N) :
    Measurable (restorePast (d := d) (A := A) M nodes anchors seeds main final sampling N k hk) := by
  have href : Measurable (fun z : PastSample (d := d) (A := A) M nodes anchors seeds main final sampling N k =>
      fun j : Fin N => if hj : (j:ℕ)<k then z.2 ⟨j,hj⟩ else (0 : Fin n → Point d)) := by
    apply Measurable.of_eval
    intro j
    by_cases hj : (j:ℕ)<k
    · simp only [dite_eq_left hj]
      exact (measurable_pi_apply (⟨j,hj⟩ : Fin k)).comp measurable_snd
    · simp only [dite_eq_right hj]
      exact measurable_const
  exact (measurable_fst.fst.prodMk (href.prodMk measurable_const)).prodMk measurable_fst.snd

omit [MeasurableSpace A] in
theorem restorePast_reference (k : ℕ) (hk : k≤N) (j : ℕ) (hj : j<k) (i : Fin n) (z : Xmain) :
    MeanChronologicalBenchmark.returnedReference M nodes anchors seeds main final sampling N j i
      (restorePast M nodes anchors seeds main final sampling N k hk
        (MeanChronologicalPast.past M nodes anchors seeds main final sampling N k hk z)) =
    MeanChronologicalBenchmark.returnedReference M nodes anchors seeds main final sampling N j i z := by
  simp only [MeanChronologicalBenchmark.returnedReference,dite_eq_left (lt_of_lt_of_le hj hk),
    restorePast,MeanChronologicalPast.past,dite_eq_left hj]

omit [MeasurableSpace A] in
theorem restorePast_comparison (k : ℕ) (hk : k≤N) (j : ℕ) (hj : j≤k) (z : Xmain) :
    MeanChronologicalBenchmark.comparisonNoise M nodes anchors seeds main final sampling N r Ds σ δ t w j (hj.trans hk)
      (restorePast M nodes anchors seeds main final sampling N k hk
        (MeanChronologicalPast.past M nodes anchors seeds main final sampling N k hk z)) =
    MeanChronologicalBenchmark.comparisonNoise M nodes anchors seeds main final sampling N r Ds σ δ t w j (hj.trans hk) z := by
  cases j with
  | zero => rfl
  | succ j =>
    simp only [MeanChronologicalBenchmark.comparisonNoise,restorePast,
      MeanChronologicalPast.past,dite_eq_left (show j<k by omega)]

omit [MeasurableSpace A] in
theorem restorePast_error (k : ℕ) (hk : k<N) (i : Fin n) (z : Xmain) :
    stageError M nodes anchors seeds main final sampling N r Ds hr x P referencePosition hF hell hlo hup σ hσ hsmall δ t w G k hk i
      (restorePast M nodes anchors seeds main final sampling N (k+1) (by omega)
        (MeanChronologicalPast.past M nodes anchors seeds main final sampling N (k+1) (by omega) z)) =
    stageError M nodes anchors seeds main final sampling N r Ds hr x P referencePosition hF hell hlo hup σ hσ hsmall δ t w G k hk i z := by
  unfold stageError
  rw [restorePast_comparison M nodes anchors seeds main final sampling N r Ds σ δ t w (k+1) (by omega) k (by omega),
    restorePast_reference M nodes anchors seeds main final sampling N (k+1) (by omega) k (by omega)]
  rfl

omit [IsProbabilityMeasure ρ] in
include hx hP hreference hG in
/-- Every later actual main extension preserves this child's complete error
law, jointly retaining all source coordinates used in its evaluation. -/
theorem loop_error_law (k : ℕ) (hk : k<N) (i : Fin n) :
    (kernel M nodes anchors seeds main final sampling N r Ds hr hDs hmass L hL x P referencePosition hx hP hreference hF hell hlo hup σ hσ hsmall δ t w J ∘ₘ ρ).map
      (stageError M nodes anchors seeds main final sampling N r Ds hr x P referencePosition hF hell hlo hup σ hσ hsmall δ t w G k hk i) =
    (stageLaw M nodes anchors seeds main final sampling N r Ds hr hDs hmass L hL x P referencePosition hx hP hreference hF hell hlo hup σ hσ hsmall δ t w J ρ (k+1) (by omega)).map
      (stageError M nodes anchors seeds main final sampling N r Ds hr x P referencePosition hF hell hlo hup σ hσ hsmall δ t w G k hk i) := by
  let err := stageError M nodes anchors seeds main final sampling N r Ds hr x P referencePosition hF hell hlo hup σ hσ hsmall δ t w G k hk i
  let read := err ∘ restorePast M nodes anchors seeds main final sampling N (k+1) (by omega)
  have hem : Measurable err := stageError_measurable M nodes anchors seeds main final sampling N r Ds hr hDs hmass L x P referencePosition hx hP hreference hF hell hlo hup σ hσ hsmall δ t w G hG k hk i
  have hrm : Measurable read := hem.comp (restorePast_measurable M nodes anchors seeds main final sampling N (k+1) (by omega))
  have hp := MeanChronologicalPast.past_measurable (d := d) (A := A) M nodes anchors seeds main final sampling N (k+1) (by omega)
  have h := congrArg (fun ν => ν.map read)
    (MeanChronologicalPast.kernel_past M nodes anchors seeds main final sampling N r Ds hr hDs hmass σ δ t w L hL x P referencePosition hx hP hreference hF hell hlo hup hσ hsmall J (k+1) (by omega) ρ)
  rw [Measure.map_map hrm hp,Measure.map_map hrm hp] at h
  have he : read ∘ MeanChronologicalPast.past M nodes anchors seeds main final sampling N (k+1) (by omega) = err := by
    funext z
    exact restorePast_error M nodes anchors seeds main final sampling N r Ds hr x P referencePosition hF hell hlo hup σ hσ hsmall δ t w G k hk i z
  rw [he] at h
  exact h

variable (base : Point d)
  (hfinalMass : ∀ i,CovarianceSetup.shiftSq (final i).shiftVector≤Ds^2)
  (Jfinal : DesignatedChildBatchCoupling.Lower L
    (MeanFinalBatchCoupling.data M nodes anchors seeds main final sampling N r Ds hr hDs hfinalMass))

include hx hP hreference hG ha hA hsplit in
/-- Actual completed finite mean program: each earlier main child error has
its lower retained error law even after the designated paid-final extension. -/
theorem completed_error_law (k : ℕ) (hk : k<N) (i : Fin n)
    (hshift : ChildAbsorption.QueryShift (main i).program (main i).enumeration (main i).coefficient
      (M.radius r (nodes i)) (main i).shiftVector) :
    (MeanCompletedCoupling.kernel M nodes anchors seeds main final sampling N r Ds hr hDs hmass L hL x P referencePosition hx hP hreference hF hell hlo hup σ hσ hsmall δ t w base hfinalMass G hG J Jfinal ∘ₘ ρ).map
      ((stageError M nodes anchors seeds main final sampling N r Ds hr x P referencePosition hF hell hlo hup σ hσ hsmall δ t w G k hk i) ∘ Prod.fst) =
    (μ ⊗ₘ ((J k hk).joint i).comap (centersM i) (hcentersM i)).map
      (lowerError M nodes anchors seeds main final sampling N r Ds hr x P referencePosition hF hell hlo hup σ hσ hsmall δ t w G i) := by
  have hem := stageError_measurable M nodes anchors seeds main final sampling N r Ds hr hDs hmass L x P referencePosition hx hP hreference hF hell hlo hup σ hσ hsmall δ t w G hG k hk i
  rw [← Measure.map_map hem measurable_fst,MeanCompletedCoupling.kernel,
    ← Measure.comp_assoc,Measure.map_comp _ _ measurable_fst,← Kernel.fst_eq,
    MeanCompletedCoupling.finishKernel_original,Measure.id_comp,
    loop_error_law M nodes anchors seeds main final sampling N r Ds hr hDs hmass L hL x P referencePosition hx hP hreference hF hell hlo hup σ hσ hsmall δ t w J G hG ρ k hk i]
  exact stage_error_law M nodes anchors seeds main final sampling N r Ds hr hDs hmass L hL x P referencePosition hx hP hreference hF hell hlo hup σ hσ hsmall δ t w J G hG ha hA ρ μ hsplit k hk i hshift

end AcceleratedLogConcave.Oracle.MeanMainErrorTransport
