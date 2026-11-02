import AcceleratedLogConcave.Oracle.MeanCompletedChildAccuracy
import AcceleratedLogConcave.Oracle.MeanFinalOracleError

/-! Actual completed paid-final error moments from the LOWER retained
full-seed coupling. The incoming assembled Pi remains correlated with its
original parent; the final source observation and whole correction suffix
are derived from the actual chronological kernel. -/
noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace AcceleratedLogConcave.Oracle.MeanCompletedFinalAccuracy
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

local notation "C" => Coarse (d := d) M nodes anchors seeds main final sampling N A
local notation "D" => MeanJointReference.data M hF hell hlo hup r σ hr hσ hsmall
local notation "seed" => MeanChronologicalFinalObservation.benchmarkSeed M nodes anchors seeds main final sampling N r hr x P referencePosition hF hell hlo hup σ hσ hsmall
local notation "rho" => RecursiveMeanPublicTable.centerNoise r M.R Ds
local notation "childWidth" => CovarianceSetup.sigma n rho (rowBound (m := m) r σ δ t w)


variable (base : Point d)
  (hfinalMass : ∀ i,CovarianceSetup.shiftSq (final i).shiftVector≤Ds^2)
  (G : Point d → Point d) (hG : Measurable G)
  (J : ∀ (k : ℕ) (hk : k<N),FreshChildBatchCoupling.Lower L
    (data M nodes anchors seeds main final sampling N r Ds hr hDs hmass
      (stage M nodes anchors seeds main final sampling N k hk.le).1
      (stage_positive M nodes anchors seeds main final sampling N k hk)))
  (Jfinal : DesignatedChildBatchCoupling.Lower L
    (MeanFinalBatchCoupling.data M nodes anchors seeds main final sampling N r Ds hr hDs hfinalMass))
local notation "B" => MeanFinalBatchCoupling.data M nodes anchors seeds main final sampling N r Ds hr hDs hfinalMass
local notation "cut" => MeanFinalBatchCoupling.batchCut M nodes anchors seeds main final sampling N r Ds hr hDs hfinalMass
local instance : MeasurableSpace (Prefix d cut) := prefixSpace d cut
local instance : MeasurableSpace (Prefix d (afterBatch cut)) := prefixSpace d (afterBatch cut)
local notation "input" => MeanChronologicalFinalObservation.sourceInput M nodes anchors seeds main final sampling N r Ds x P σ δ t w
local notation "coarse" => MeanChronologicalFinalProjection.finalCoarse M nodes anchors seeds main final sampling N r Ds hr hDs x P referencePosition hF hell hlo hup σ hσ hsmall base hfinalMass
local notation "hcoarse" => MeanChronologicalFinalProjection.finalCoarse_measurable M nodes anchors seeds main final sampling N r Ds hr hDs x P referencePosition hx hP hreference hF hell hlo hup σ hσ hsmall base hfinalMass
local notation "comparison" => MeanChronologicalFinalProjection.finalComparison M nodes anchors seeds main final sampling N r Ds hr hDs hfinalMass
local notation "hcomparison" => MeanChronologicalFinalProjection.finalComparison_measurable (d := d) (A := A) M nodes anchors seeds main final sampling N r Ds hr hDs hfinalMass
local notation "obs" => MeanChronologicalFinalProjection.finalObservation M nodes anchors seeds main final sampling N r Ds hr hDs x P referencePosition hF hell hlo hup σ hσ hsmall δ t w base hfinalMass G
local notation "ho" => MeanChronologicalFinalProjection.finalObservation_measurable M nodes anchors seeds main final sampling N r Ds hr hDs x P referencePosition hx hP hreference hF hell hlo hup σ hσ hsmall δ t w base hfinalMass G hG
local notation "hc" => MeanBenchmarkMoments.finalCenter_measurable (D base)
local notation "width" => RecursiveMeanPublicTable.finalWidth M.R σ
local notation "Kfinal" => MeanCompletedCoupling.finishKernel M nodes anchors seeds main final sampling N r Ds hr hDs L hL x P referencePosition hx hP hreference hF hell hlo hup σ hσ hsmall δ t w base hfinalMass G hG Jfinal

/-- The literal designated paid-final callback at the source benchmark. It
retains the complete original tape and the returned final reference vector. -/
def finalError (i : Fin m) : (Xmain × (Fin m → Point d)) → Point d :=
  MeanFinalOracleError.error (D base) nodes anchors seeds main final sampling N Ds hDs hfinalMass
    G input coarse comparison i

variable (ha : 0<rowBound (m := m) r σ δ t w)
    (hA : ∀ i,∑ j,|M.matrix r σ (nodes i) (nodes j)|≤rowBound (m := m) r σ δ t w)
    (ρ : Measure (A × Tape d (Host M nodes anchors seeds main final sampling N))) [IsProbabilityMeasure ρ]
    (μ : Measure (Coarse (d := d) M nodes anchors seeds main final sampling N A)) [IsProbabilityMeasure μ]
    (hsplit : ρ.map (CausalTailHistory.unpack (MeanMainBatchCoupling.bodyCut M nodes anchors seeds main final sampling N))=
      μ.prod (tapeLaw L (body (a := a) (h := h) M nodes main final sampling N)))
    (hincoming : μ.map (MeanCompletedAugmentedLaws.incomingAugmented M nodes anchors seeds main final sampling N r hr x P referencePosition hF hell hlo hup σ hσ hsmall base)=
      ((stdGaussian (Point d)).prod (MeanFlowLp.seedMeasure (MeanJointReference.data M hF hell hlo hup r σ hr hσ hsmall base))).prod
        (Measure.pi fun _ : Fin m => stdGaussian (Point d)))
local notation "completedLaw" => MeanCompletedCoupling.kernel M nodes anchors seeds main final sampling N r Ds hr hDs hmass L hL x P referencePosition hx hP hreference hF hell hlo hup σ hσ hsmall δ t w base hfinalMass G hG J Jfinal ∘ₘ ρ
local notation "Err" => finalError M nodes anchors seeds main final sampling N r Ds hr hDs x P referencePosition hF hell hlo hup σ hσ hsmall δ t w base hfinalMass G

omit [IsProbabilityMeasure μ] in
include hx hP hreference hincoming in
/-- Project the genuine original-input/phase/Pi assembly joint. The
assembled Pi is never replaced by a newly independent Gaussian sample. -/
theorem inventory_law_of_incoming :
    μ.map (MeanChronologicalFinalProjection.incomingInventory M nodes anchors seeds main final sampling N r hr x P referencePosition hF hell hlo hup σ hσ hsmall base)=
      (MeanFlowLp.seedMeasure (D base)).prod (Measure.pi fun _ : Fin m => stdGaussian (Point d)) := by
  have hp : MeasurePreserving
      (MeanCompletedAugmentedLaws.incomingAugmented M nodes anchors seeds main final sampling N r hr x P referencePosition hF hell hlo hup σ hσ hsmall base)
      μ (((stdGaussian (Point d)).prod (MeanFlowLp.seedMeasure (D base))).prod
        (Measure.pi fun _ : Fin m => stdGaussian (Point d))) :=
    ⟨MeanCompletedAugmentedLaws.incomingAugmented_measurable M nodes anchors seeds main final sampling N r hr
      x P referencePosition hx hP hreference hF hell hlo hup σ hσ hsmall base,hincoming⟩
  exact (((measurePreserving_snd (μ := stdGaussian (Point d)) (ν := MeanFlowLp.seedMeasure (D base))).prod
    (MeasurePreserving.id (Measure.pi fun _ : Fin m => stdGaussian (Point d)))).comp hp).map_eq

include hx hP hreference hG ha hA hsplit hincoming in
/-- Actual designated-final LOWER accuracy is averaged with the proved
stationary source-center moment. All observation, tape and comparison laws
are supplied by the constructed finite main chronology. -/
theorem completed_final_error_bound (i : Fin m) (amplitude : ℝ)
    (hshift : ChildAbsorption.QueryShift (final i).program (final i).enumeration (final i).coefficient
      (r*M.R) (final i).shiftVector)
    (hfiber : ∀ y : Point d,
      MemLp (DesignatedChildRunShift.lowerError (final i).program G (final i).coefficient y
        (Gibbs.primitiveMean F y (r*M.R)) width) 2 (Jfinal.joint i y))
    (hbound : ∀ y : Point d,
      (∫ z, ‖DesignatedChildRunShift.lowerError (final i).program G (final i).coefficient y
        (Gibbs.primitiveMean F y (r*M.R)) width z‖^2 ∂Jfinal.joint i y) ≤
          (amplitude*Gibbs.primitiveScale F y)^2) :
    ∃ hi : MemLp (Err i) 2 completedLaw,
      (∫ z, ‖Err i z‖^2 ∂completedLaw) ≤
        amplitude^2*MeanBenchmarkMoments.finalScaleSquareBudget (D base) ∧
      ‖hi.toLp (Err i)‖ ≤
        Real.sqrt (amplitude^2*MeanBenchmarkMoments.finalScaleSquareBudget (D base)) := by
  obtain ⟨ν,hν,hcut,_,hprojection⟩ := MeanChronologicalFinalProjection.kernel_final_observation_laws
    M nodes anchors seeds main final sampling N r Ds hr hDs hmass L hL x P referencePosition hx hP hreference
    hF hell hlo hup σ hσ hsmall δ t w base hfinalMass G hG J ha hA ρ μ hsplit
    (inventory_law_of_incoming M nodes anchors seeds main final sampling N r hr x P referencePosition hx hP hreference
      hF hell hlo hup σ hσ hsmall base μ hincoming)
  let _ : IsProbabilityMeasure ν := hν
  let oldLaw := MeanChronologicalCoupling.kernel M nodes anchors seeds main final sampling N r Ds hr hDs hmass
    L hL x P referencePosition hx hP hreference hF hell hlo hup σ hσ hsmall δ t w J ∘ₘ ρ
  let err := DesignatedChildBatchErrorTransfer.lowerError B (MeanBenchmarkMoments.finalCenter (D base))
    i G (MeanBenchmarkMoments.finalMean (D base) i) width
  have hmeas : StronglyMeasurable err :=
    DesignatedChildBatchErrorTransfer.lowerError_stronglyMeasurable B (MeanBenchmarkMoments.finalCenter (D base)) hc
      i G hG (MeanBenchmarkMoments.finalMean (D base) i) (MeanBenchmarkMoments.finalMean_measurable (D base) i) width
  have hcost : Integrable (fun s : MeanFlowLp.Seed (D base) =>
      (amplitude*MeanBenchmarkMoments.nodeScale (D base) (.center M i) s)^2) (MeanFlowLp.seedMeasure (D base)) := by
    simpa only [mul_pow] using (MeanBenchmarkMoments.node_scale_square_integrable (D base) (.center M i)).const_mul (amplitude^2)
  have hp := DesignatedChildBatchErrorTransfer.averaged_error_memLp_of_bound L B Jfinal
    (MeanBenchmarkMoments.finalCenter (D base)) hc (MeanFlowLp.seedMeasure (D base)) i err hmeas
    (Filter.Eventually.of_forall fun s => hfiber (MeanBenchmarkMoments.finalCenter (D base) i s))
    (fun s => amplitude*MeanBenchmarkMoments.nodeScale (D base) (.center M i) s) hcost
    (Filter.Eventually.of_forall fun s => hbound (MeanBenchmarkMoments.finalCenter (D base) i s))
  let : ∀ j, IsProbabilityMeasure (tapeLaw L (DesignatedChildBatchCoupling.program B j)) :=
    fun j => tapeLaw_probability L _
  let : IsProbabilityMeasure (advancedLaw L cut ν) := by unfold advancedLaw; infer_instance
  let E := DesignatedChildBatchBenchmarkError.sourceError B (MeanBenchmarkMoments.finalCenter (D base)) obs
    i G (MeanBenchmarkMoments.finalMean (D base) i) width
  have hE : MemLp E 2 (DesignatedChildBatchErrorTransfer.observedLaw L hL B Jfinal
      (MeanBenchmarkMoments.finalCenter (D base)) hc (advancedLaw L cut ν) obs ho) :=
    DesignatedChildBatchBenchmarkError.source_error_memLp B (MeanBenchmarkMoments.finalCenter (D base)) obs L hL Jfinal hc
      (advancedLaw L cut ν) (MeanFlowLp.seedMeasure (D base)) ho hprojection i G
      (MeanBenchmarkMoments.finalMean (D base) i) width hshift hp.1
  have hEsq := DesignatedChildBatchBenchmarkError.source_error_square_integral B
    (MeanBenchmarkMoments.finalCenter (D base)) obs L hL Jfinal hc
    (advancedLaw L cut ν) (MeanFlowLp.seedMeasure (D base)) ho hprojection i G
    (MeanBenchmarkMoments.finalMean (D base) i) width hshift hp.1
  have hwhole := MeanFinalBatchCoupling.whole_suffix M nodes anchors seeds main final sampling N r Ds hr hDs hfinalMass
    G hG input (fun _ => measurable_const) (hx.comp measurable_fst.fst) (hP.comp measurable_fst.fst)
    L hL Jfinal coarse hcoarse (MeanBenchmarkMoments.finalCenter (D base)) hc comparison hcomparison oldLaw ν hcut
  have hfull := FreshChildBatchErrorTransfer.full_sample_error_memLp L (afterBatch cut)
    (Kfinal ∘ₘ oldLaw) _ hwhole E hE
  have hfullsq := FreshChildBatchErrorTransfer.full_sample_error_square_integral L (afterBatch cut)
    (Kfinal ∘ₘ oldLaw) _ hwhole E hE
  have hierr := (memLp_two_iff_integrable_sq_norm hp.1.aestronglyMeasurable).mp hp.1
  have hpay : (∫ z, ‖E z‖^2 ∂DesignatedChildBatchErrorTransfer.observedLaw L hL B Jfinal
      (MeanBenchmarkMoments.finalCenter (D base)) hc (advancedLaw L cut ν) obs ho) ≤
      amplitude^2*MeanBenchmarkMoments.finalScaleSquareBudget (D base) := by
    rw [hEsq]
    have hh := hp.2
    rw [Measure.integral_compProd hierr] at hh
    apply hh.trans
    simp_rw [mul_pow]
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left (MeanBenchmarkMoments.final_scale_square_integral_le (D base) i) (sq_nonneg amplitude)
  have he : Kfinal ∘ₘ oldLaw = completedLaw := by
    rw [MeanCompletedCoupling.kernel,←Measure.comp_assoc]
  rw [he] at hfull hfullsq
  change MemLp (Err i) 2 completedLaw at hfull
  have hs : (∫ z, ‖Err i z‖^2 ∂completedLaw) ≤
      amplitude^2*MeanBenchmarkMoments.finalScaleSquareBudget (D base) := hfullsq.trans_le hpay
  refine ⟨hfull,hs,?_⟩
  apply FreshChildBatchErrorTransfer.norm_toLp_le_of_square_integral _ _ hfull _ (Real.sqrt_nonneg _)
  rw [Real.sq_sqrt (le_trans (integral_nonneg fun _ => sq_nonneg _) hs)]
  exact hs

end AcceleratedLogConcave.Oracle.MeanCompletedFinalAccuracy
