import AcceleratedLogConcave.Oracle.PrivateCompletedCoupling
import AcceleratedLogConcave.Oracle.PrivateChronologicalFinish

/-! Actual final-batch laws appended to the finite chronological coupling.
The augmented coarse datum retains external center, setup seed and original P. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option quotPrecheck false
set_option maxHeartbeats 1200000
open MeasureTheory ProbabilityTheory
namespace AcceleratedLogConcave.Oracle.PrivateCompletedLaws
open Numerics.AffineGraph TapeLowering CanonicalTapeLaw CanonicalTapeMeasurability
open TailOccurrenceCut TailCut PrivateChronologicalCoupling PrivateCausalLayer
local instance canonicalTapeSpace {d c : ℕ} {Γ : Ctx} {τ : Ty} (p : Prog c Γ τ) :
    MeasurableSpace (Tape d p) := tapeSpace d p
variable {m n d : ℕ} (S : SamplingGeometry m) (e : Fin n ≃ S.Node)
  (r Ds : ℝ) (main final : Fin n → ExecutableData) (N : ℕ)
  (hr : 0 < r) (hDs : 0 < Ds)
  (hfinalMass : ∀ i, CovarianceSetup.shiftSq (final i).shiftVector ≤ Ds^2)
local notation "cut" => terminalCut S e r Ds main final N
local notation "old" => (terminalCursor S e r Ds main final N).old
local notation "direct" => (terminalCursor S e r Ds main final N).saved (RefMap.shiftMany n .here)
local notation "B" => PrivateFinalCoupling.data S e r Ds main final N hr hDs hfinalMass old
local instance : MeasurableSpace (Prefix d cut) := prefixSpace d cut
local instance : MeasurableSpace (Prefix d (afterBatch cut)) := prefixSpace d (afterBatch cut)

/-- Actual augmented coarse datum and current comparison paired with the
literal final child tapes, after precisely their consumed batch. -/
def observed (z : History d N n × Prefix d (afterBatch cut)) :
    ((Point d × Point d) × Point d) × (∀ i, FreshChildBatchCoupling.Raw d B i) :=
  (z.1.1,fun i => (z.1.2.2 i,(batchParts cut z.2).2 i))

theorem observed_measurable : Measurable (observed (d := d) S e r Ds main final N hr hDs hfinalMass) := by
  have hp : Measurable (fun z : History d N n × Prefix d (afterBatch cut) =>
      batchParts cut z.2) := (measurable_batchParts (d := d) cut).comp measurable_snd
  exact measurable_fst.fst.prodMk (Measurable.of_eval fun i =>
    (((measurable_pi_apply i).comp measurable_fst.snd.snd).prodMk
      ((measurable_pi_apply i).comp hp.snd)))

variable (L : PrimitiveLaws d)

theorem observation_law
    (μ : Measure (History d N n × Prefix d cut)) [IsProbabilityMeasure μ]
    (ν : Measure ((Point d × Point d) × Point d)) [IsProbabilityMeasure ν]
    (hcomparison : μ.map (fun z => (z.1.1,z.1.2.2)) =
      ν.prod (Measure.pi fun _ : Fin n => stdGaussian (Point d))) :
    (advancedLaw L cut μ).map (observed S e r Ds main final N hr hDs hfinalMass) =
      ν.prod (Measure.pi (FreshChildBatchCoupling.rawLaw L B)) := by
  let _ : ∀ i, IsProbabilityMeasure (tapeLaw L (FreshChildBatchCoupling.program B i)) :=
    fun i => tapeLaw_probability L _
  have hp : MeasurePreserving (fun z : History d N n × Prefix d cut => (z.1.1,z.1.2.2)) μ
      (ν.prod (Measure.pi fun _ : Fin n => stdGaussian (Point d))) :=
    ⟨measurable_fst.fst.prodMk measurable_fst.snd.snd,hcomparison⟩
  have h := ((MeasurePreserving.id ν).prod (FreshChildBatchCoupling.rawSplit_preserving L B).symm).comp
    ((measurePreserving_prodAssoc ν (Measure.pi fun _ : Fin n => stdGaussian (Point d))
      (Measure.pi fun i => tapeLaw L (FreshChildBatchCoupling.program B i))).comp
        (hp.prod (MeasurePreserving.id (Measure.pi fun i => tapeLaw L (FreshChildBatchCoupling.program B i)))))
  rw [advancedLaw,Measure.map_map
    (observed_measurable S e r Ds main final N hr hDs hfinalMass) (measurable_advanceHistory _)]
  simpa [Function.comp_def,observed,advanceHistory,batchParts_append,
    FreshChildBatchCoupling.program, PrivateFinalCoupling.data, SourceExecutableTables.samplingConfig,
    FreshChildBatchCoupling.rawSplit,MeasurableEquiv.prodAssoc,Equiv.prodAssoc,Prod.map] using h.map_eq

variable (hL : L.pointDraw = stdGaussian (Point d))
  {F : Point d → ℝ} (hF : ContDiff ℝ 2 F) {ell : ℝ} (hell : 0 ≤ ell)
  (hlo : ∀ z v, 0 ≤ fderiv ℝ (fderiv ℝ F) z v v)
  (hup : ∀ z v, fderiv ℝ (fderiv ℝ F) z v v ≤ ell*‖v‖^2)
  (Jf : FreshChildBatchCoupling.Lower L
    (PrivateFinalCoupling.data S e r Ds main final N hr hDs hfinalMass
      (terminalCursor S e r Ds main final N).old))

def conditional : Kernel (History d N n × Prefix d (afterBatch cut)) (Fin n → Point d) :=
  PrivateFinalCoupling.referenceConditional S e r Ds main final N hr hDs hfinalMass old direct cut
    L hL Jf (fun z => z.1.1.1) (by fun_prop)
    (jointPhi S e hF hell hlo hup hr) (fun i => (jointPhi_continuous S e hF hell hlo hup hr i).measurable)
    (fun i z => z.1.2.2 i) (by intro i; fun_prop)

instance conditional_markov : IsMarkovKernel
    (conditional S e r Ds main final N hr hDs hfinalMass L hL hF hell hlo hup Jf) := by
  unfold conditional
  infer_instance

theorem conditional_augmented_coarse :
    conditional S e r Ds main final N hr hDs hfinalMass L hL hF hell hlo hup Jf =
      (FreshChildBatchCoupling.referenceBatch L hL B Jf
        (fun i (c : (Point d × Point d) × Point d) => jointPhi S e hF hell hlo hup hr i c.1)
        (fun i => (jointPhi_continuous S e hF hell hlo hup hr i).measurable.comp measurable_fst)).comap
          (observed S e r Ds main final N hr hDs hfinalMass)
          (observed_measurable S e r Ds main final N hr hDs hfinalMass) := by
  ext z : 1
  simp only [conditional,PrivateFinalCoupling.referenceConditional,Kernel.comap_apply,
    FreshChildBatchCoupling.referenceBatch,
    Conditional.MeanReferenceLayer.finiteProduct_apply n _ (fun _ => inferInstance),Kernel.comap_apply]
  rfl

theorem returned_reference_law
    (μ : Measure (History d N n × Prefix d cut)) [IsProbabilityMeasure μ]
    (ν : Measure ((Point d × Point d) × Point d)) [IsProbabilityMeasure ν]
    (hcomparison : μ.map (fun z => (z.1.1,z.1.2.2)) =
      ν.prod (Measure.pi fun _ : Fin n => stdGaussian (Point d))) :
    ((advancedLaw L cut μ) ⊗ₘ conditional S e r Ds main final N hr hDs hfinalMass L hL hF hell hlo hup Jf).map
      (fun z => (z.1.1.1,z.2)) = ν.prod (Measure.pi fun _ : Fin n => stdGaussian (Point d)) := by
  rw [conditional_augmented_coarse]
  exact FreshChildBatchCoupling.projected_coarse_reference_law L hL B Jf
    (fun i (c : (Point d × Point d) × Point d) => jointPhi S e hF hell hlo hup hr i c.1)
    (fun i => (jointPhi_continuous S e hF hell hlo hup hr i).measurable.comp measurable_fst)
    (advancedLaw L cut μ) ν (observed S e r Ds main final N hr hDs hfinalMass)
    (observed_measurable S e r Ds main final N hr hDs hfinalMass)
    (observation_law S e r Ds main final N hr hDs hfinalMass L μ ν hcomparison)


variable (hmass : ∀ i, CovarianceSetup.shiftSq (main i).shiftVector ≤ Ds^2)
  (J : ∀ (k : ℕ) (hk : k<N), FreshChildBatchCoupling.Lower L
    (PrivateChronologicalCoupling.data S e r Ds main final N hr hDs hmass
      (stage S e r Ds main final N k hk.le).1
      (stage_positive S e r Ds main final N k hk)))

/-- The constructed completed kernel has a fresh *whole* literal suffix,
with its actual returned-reference vector jointly Gaussian over the augmented
coarse host. Neither property is an input to this theorem. -/
theorem kernel_final_split (hm : 0<m) (x : Point d) :
    ∃ (η : Measure ((History d N n × Prefix d (afterBatch cut)) × (Fin n → Point d))),
      IsProbabilityMeasure η ∧
      (PrivateCompletedCoupling.kernel S e r Ds main final N hr hDs hmass hfinalMass
        L hL hF hell hlo hup Jf J x).map (CausalTailHistory.unpackExtended (afterBatch cut)) =
        η.prod (tapeLaw L (PrivateFinalCoupling.suffix main final N direct)) ∧
      η.map (fun z => (z.1.1.1,z.2)) =
        (PrivateChronologicalLaws.coarseLaw x).prod
          (Measure.pi fun _ : Fin n => stdGaussian (Point d)) := by
  obtain ⟨μ,hμ,hsplit,hcomparison⟩ :=
    PrivateChronologicalFinish.kernel_terminalCut_laws S e r Ds main final N
      hr hDs hmass L hL hF hell hlo hup J hm x
  let _ := hμ
  let _ : IsProbabilityMeasure (advancedLaw L cut μ) :=
    PrivateChronologicalLaws.advanced_probability L cut μ
  let η := (advancedLaw L cut μ) ⊗ₘ
    conditional S e r Ds main final N hr hDs hfinalMass L hL hF hell hlo hup Jf
  refine ⟨η,inferInstance,?_,?_⟩
  · rw [PrivateCompletedCoupling.kernel,Kernel.comp_apply,PrivateCompletedCoupling.finalKernel]
    exact CausalTailHistory.whole_suffix_fresh_of_split L (afterBatch cut) _
      (advancedLaw L cut μ) (advanced_split_of_split L cut _ μ hsplit)
      (PrivateCompletedCoupling.finalConditional S e r Ds main final N hr hDs hfinalMass
        L hL hF hell hlo hup Jf)
  · exact returned_reference_law S e r Ds main final N hr hDs hfinalMass
      L hL hF hell hlo hup Jf μ (PrivateChronologicalLaws.coarseLaw x) hcomparison


/-- Literal completed execution observation: augmented coarse host, actual
returned final reference vector, and the two distinct unread Gaussian draws. -/
def finalObservation
    (z : ((History d N n × Tape d (Host S e r Ds main final N)) × (Fin n → Point d))) :
    (((Point d × Point d) × Point d) × (Fin n → Point d)) × (Point d × Point d) :=
  let u := CausalTailHistory.unpackExtended (afterBatch cut) z
  ((u.1.1.1.1,u.1.2),(u.2.1,u.2.2.1))

/-- Full joint law, including original P, rather than coordinate Gaussian
marginals. The only supplied coupling laws belong to strictly lower children. -/
theorem kernel_final_joint (hm : 0<m) (x : Point d) :
    (PrivateCompletedCoupling.kernel S e r Ds main final N hr hDs hmass hfinalMass
      L hL hF hell hlo hup Jf J x).map (finalObservation S e r Ds main final N) =
      ((PrivateChronologicalLaws.coarseLaw x).prod
        (Measure.pi fun _ : Fin n => stdGaussian (Point d))).prod
          ((stdGaussian (Point d)).prod (stdGaussian (Point d))) := by
  obtain ⟨η,hη,hsplit,href⟩ := kernel_final_split S e r Ds main final N hr hDs hfinalMass
    L hL hF hell hlo hup Jf hmass J hm x
  let _ := hη
  have hp : MeasurePreserving
      (fun z : (History d N n × Prefix d (afterBatch cut)) × (Fin n → Point d) =>
        (z.1.1.1,z.2)) η
      ((PrivateChronologicalLaws.coarseLaw x).prod
        (Measure.pi fun _ : Fin n => stdGaussian (Point d))) := ⟨by fun_prop,href⟩
  let _ : IsProbabilityMeasure (tapeLaw L (PrivateFinalCoupling.suffix main final N direct)) :=
    tapeLaw_probability L _
  have ht := hp.prod (PrivateFinalGaussian.suffix_residual_reserve
    main final N direct L hL)
  have hu : MeasurePreserving (CausalTailHistory.unpackExtended (afterBatch cut))
      (PrivateCompletedCoupling.kernel S e r Ds main final N hr hDs hmass hfinalMass
        L hL hF hell hlo hup Jf J x)
      (η.prod (tapeLaw L (PrivateFinalCoupling.suffix main final N direct))) :=
    ⟨CausalTailHistory.measurable_unpackExtended L _,hsplit⟩
  exact (ht.comp hu).map_eq

end AcceleratedLogConcave.Oracle.PrivateCompletedLaws
