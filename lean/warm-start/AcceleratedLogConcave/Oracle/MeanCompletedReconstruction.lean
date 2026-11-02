import AcceleratedLogConcave.Oracle.MeanCompletedAugmentedLaws

/-! Original designated momentum reconstructed from the actual reserved
assembly coordinate, actual phase G0 and retained active-final Pi values. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
namespace AcceleratedLogConcave.Oracle.MeanCompletedReconstruction
open Numerics Numerics.AffineGraph AffineLowering TapeLowering NoisyLayer SourceMeanExecutable
open TailOccurrenceCut TailCut CanonicalTapeLaw CanonicalTapeMeasurability
open PrivateCausalLayer MeanChronologicalCoupling MeanChronologicalFinalObservation MeanCompletedAugmentedLaws

section Inventory
variable {m d : ℕ} (D : MeanFlowLp.Data (Fin d) m)

def inventory (z : (Point d × MeanFlowLp.Seed D) × (Fin m → Point d × Point d)) :
    Option (Fin (m+1)) → Point d
  | none => z.1.1
  | some i => Fin.cases z.1.2.1.ofLp.2 (fun j => (z.2 j).1) i

theorem inventory_measurable : Measurable (inventory D) := by
  apply Measurable.of_eval
  intro i
  cases i with
  | none => exact measurable_fst.fst
  | some i =>
    refine Fin.cases ?_ (fun j => ?_) i
    · exact (WithLp.prod_continuous_ofLp 2 (Point d) (Point d)).snd.measurable.comp measurable_fst.snd.fst
    · exact ((measurable_pi_apply j).comp measurable_snd).fst

def reconstruct (z : (Point d × MeanFlowLp.Seed D) × (Fin m → Point d × Point d)) : Point d :=
  Probability.MixedResidualAbsorption.reconstruct (assembly D.G) (inventory D z)

theorem reconstruct_measurable : Measurable (reconstruct D) := by
  have hi := inventory_measurable D
  unfold reconstruct Probability.MixedResidualAbsorption.reconstruct
  fun_prop
end Inventory
local instance canonicalTapeSpace {d c : ℕ} {Γ : Ctx} {τ : Ty} (p : Prog c Γ τ) :
    MeasurableSpace (Tape d p) := tapeSpace d p
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




variable (base : Point d)
  (hfinalMass : ∀ i,CovarianceSetup.shiftSq (final i).shiftVector≤Ds^2)
  (G : Point d → Point d) (hG : Measurable G)
local instance : MeasurableSpace (Prefix d (MeanFinalBatchCoupling.batchCut M nodes anchors seeds main final sampling N r Ds hr hDs hfinalMass)) := prefixSpace d _
local instance : MeasurableSpace (Prefix d (afterBatch (MeanFinalBatchCoupling.batchCut M nodes anchors seeds main final sampling N r Ds hr hDs hfinalMass))) := prefixSpace d _
local instance : MeasurableSpace
    (Prefix d (MeanFinalBatchCoupling.batchCut M nodes anchors seeds main final sampling N r Ds hr hDs hfinalMass)) := prefixSpace d _
local instance : MeasurableSpace
    (Prefix d (afterBatch (MeanFinalBatchCoupling.batchCut M nodes anchors seeds main final sampling N r Ds hr hDs hfinalMass))) := prefixSpace d _




omit [MeasurableSpace A] in
/-- OriginalP is algebraically determined by the literal assembly reserve,
G0 in the actual phase seed, and the stored active designated inputs. -/
theorem static_reconstruction (c : Coarse (d := d) M nodes anchors seeds main final sampling N A) (ref : Fin m → Point d) :
    reconstruct (MeanJointReference.data M hF hell hlo hup r σ hr hσ hsmall base) ((staticGE M nodes anchors seeds main final sampling N P c,benchmarkSeed M nodes anchors seeds main final sampling N r hr x P referencePosition hF hell hlo hup σ hσ hsmall base c),fun i => (staticPi M nodes anchors seeds main final sampling N P c i,ref i))=P c.1 := by
  let raw := MeanChronologicalHost.raw M nodes anchors seeds main final sampling N c.2
  let z := (MeasurableEquiv.piOptionEquivProd (fun _ : Option (Fin (m+1)) => Point d)).symm (raw,P c.1)
  have hi : inventory (MeanJointReference.data M hF hell hlo hup r σ hr hσ hsmall base) ((staticGE M nodes anchors seeds main final sampling N P c,benchmarkSeed M nodes anchors seeds main final sampling N r hr x P referencePosition hF hell hlo hup σ hσ hsmall base c),fun i => (staticPi M nodes anchors seeds main final sampling N P c i,ref i))=
      Conditional.GaussianAssembly.assemble (assembly M) z := by
    apply funext
    intro i
    cases i with
    | none => rfl
    | some i =>
      refine Fin.cases ?_ (fun j => ?_) i
      · rfl
      · rfl
  unfold reconstruct
  rw [hi]
  exact Probability.MixedResidualAbsorption.reconstruct_assemble (MeanAssemblyJointLaw.assembly_mass M) z

omit [MeasurableSpace A] in
theorem retainedPairs_readout (z : (History (d := d) M nodes anchors seeds main final sampling N A × Tape d (Host M nodes anchors seeds main final sampling N)) × (Fin m → Point d)) :
    MeanCompletedAugmentedLaws.retainedAugmentedPairs M nodes anchors seeds main final sampling N r Ds hr hDs x P referencePosition hF hell hlo hup σ hσ hsmall δ t w base hfinalMass G z=((staticGE M nodes anchors seeds main final sampling N P z.1.1.1,benchmarkSeed M nodes anchors seeds main final sampling N r hr x P referencePosition hF hell hlo hup σ hσ hsmall base z.1.1.1),
      fun i => (storedPi M nodes anchors seeds main final sampling N r Ds hr hDs x P σ δ t w hfinalMass G (z.1.1,(split (MeanFinalBatchCoupling.batchCut M nodes anchors seeds main final sampling N r Ds hr hDs hfinalMass) z.1.2).1) i,z.2 i)) := by
  simp only [MeanCompletedAugmentedLaws.retainedAugmentedPairs,MeanFinalBatchJointLaw.retainedPairs,
    MeanFinalBatchCoupling.observation,split_afterBatch,batchParts_append]
  rfl

omit [MeasurableSpace A] in
theorem reconstruction_of_stored (z : (History (d := d) M nodes anchors seeds main final sampling N A × Tape d (Host M nodes anchors seeds main final sampling N)) × (Fin m → Point d))
    (hz : staticPi M nodes anchors seeds main final sampling N P z.1.1.1=storedPi M nodes anchors seeds main final sampling N r Ds hr hDs x P σ δ t w hfinalMass G (z.1.1,(split (MeanFinalBatchCoupling.batchCut M nodes anchors seeds main final sampling N r Ds hr hDs hfinalMass) z.1.2).1)) :
    reconstruct (MeanJointReference.data M hF hell hlo hup r σ hr hσ hsmall base) (MeanCompletedAugmentedLaws.retainedAugmentedPairs M nodes anchors seeds main final sampling N r Ds hr hDs x P referencePosition hF hell hlo hup σ hσ hsmall δ t w base hfinalMass G z)=P z.1.1.1.1 := by
  have he : MeanCompletedAugmentedLaws.retainedAugmentedPairs M nodes anchors seeds main final sampling N r Ds hr hDs x P referencePosition hF hell hlo hup σ hσ hsmall δ t w base hfinalMass G z=((staticGE M nodes anchors seeds main final sampling N P z.1.1.1,benchmarkSeed M nodes anchors seeds main final sampling N r hr x P referencePosition hF hell hlo hup σ hσ hsmall base z.1.1.1),fun i => (staticPi M nodes anchors seeds main final sampling N P z.1.1.1 i,z.2 i)) := by
    rw [retainedPairs_readout]
    congr 1
    apply funext
    intro i
    exact Prod.ext (congrFun hz i).symm rfl
  rw [he]
  exact static_reconstruction M nodes anchors seeds main final sampling N r hr x P referencePosition hF hell hlo hup σ hσ hsmall base z.1.1.1 z.2

include L hx hP hreference hG in
theorem retainedPairs_measurable : Measurable (MeanCompletedAugmentedLaws.retainedAugmentedPairs M nodes anchors seeds main final sampling N r Ds hr hDs x P referencePosition hF hell hlo hup σ hσ hsmall δ t w base hfinalMass G) := by
  have hsplit := (measurePreserving_split L (afterBatch (MeanFinalBatchCoupling.batchCut M nodes anchors seeds main final sampling N r Ds hr hDs hfinalMass))).measurable
  have hp : Measurable (fun z : (History (d := d) M nodes anchors seeds main final sampling N A × Tape d (Host M nodes anchors seeds main final sampling N)) × (Fin m → Point d) => (z.1.1,(split (afterBatch (MeanFinalBatchCoupling.batchCut M nodes anchors seeds main final sampling N r Ds hr hDs hfinalMass)) z.1.2).1)) :=
    measurable_fst.fst.prodMk (hsplit.fst.comp measurable_fst.snd)
  have ho := (finalAugObservation_measurable M nodes anchors seeds main final sampling N r Ds hr hDs x P referencePosition hx hP hreference hF hell hlo hup σ hσ hsmall δ t w base hfinalMass G hG).comp hp
  dsimp only [MeanCompletedAugmentedLaws.retainedAugmentedPairs,MeanFinalBatchJointLaw.retainedPairs]
  exact ho.fst.prodMk (Measurable.of_eval fun i =>
    (((measurable_pi_apply i).comp ho.snd).snd.fst.prodMk
      ((measurable_pi_apply i).comp measurable_snd)))

variable (Jall : ∀ (k : ℕ) (hk : k<N),FreshChildBatchCoupling.Lower L
  (data M nodes anchors seeds main final sampling N r Ds hr hDs hmass (stage M nodes anchors seeds main final sampling N k hk.le).1 (stage_positive M nodes anchors seeds main final sampling N k hk)))
  (Jfinal : DesignatedChildBatchCoupling.Lower L (MeanFinalBatchCoupling.data M nodes anchors seeds main final sampling N r Ds hr hDs hfinalMass))

/-- Reconstruction holds on the constructed complete source coupling itself,
including its original input; no independence involving originalP is used. -/
theorem kernel_reconstruction_ae (ρ : Measure (A × Tape d (Host M nodes anchors seeds main final sampling N))) :
    ∀ᵐ z ∂MeanCompletedCoupling.kernel M nodes anchors seeds main final sampling N r Ds hr hDs hmass L hL x P referencePosition hx hP hreference hF hell hlo hup σ hσ hsmall δ t w base hfinalMass G hG Jall Jfinal ∘ₘ ρ,
      reconstruct (MeanJointReference.data M hF hell hlo hup r σ hr hσ hsmall base) (MeanCompletedAugmentedLaws.retainedAugmentedPairs M nodes anchors seeds main final sampling N r Ds hr hDs x P referencePosition hF hell hlo hup σ hσ hsmall δ t w base hfinalMass G z)=P z.1.1.1.1 := by
  have hfirst : (MeanCompletedCoupling.kernel M nodes anchors seeds main final sampling N r Ds hr hDs hmass L hL x P referencePosition hx hP hreference hF hell hlo hup σ hσ hsmall δ t w base hfinalMass G hG Jall Jfinal ∘ₘ ρ).map Prod.fst=
      MeanChronologicalCoupling.kernel M nodes anchors seeds main final sampling N r Ds hr hDs hmass L hL x P referencePosition hx hP hreference hF hell hlo hup σ hσ hsmall δ t w Jall ∘ₘ ρ := by
    rw [MeanCompletedCoupling.kernel,← Measure.comp_assoc,Measure.map_comp _ _ measurable_fst,
      ← Kernel.fst_eq,MeanCompletedCoupling.finishKernel_original,Measure.id_comp]
  have hp : MeasurePreserving Prod.fst (MeanCompletedCoupling.kernel M nodes anchors seeds main final sampling N r Ds hr hDs hmass L hL x P referencePosition hx hP hreference hF hell hlo hup σ hσ hsmall δ t w base hfinalMass G hG Jall Jfinal ∘ₘ ρ)
      (MeanChronologicalCoupling.kernel M nodes anchors seeds main final sampling N r Ds hr hDs hmass L hL x P referencePosition hx hP hreference hF hell hlo hup σ hσ hsmall δ t w Jall ∘ₘ ρ) := ⟨measurable_fst,hfirst⟩
  filter_upwards [hp.quasiMeasurePreserving.ae (kernel_staticPi_stored_ae M nodes anchors seeds main final sampling N r Ds hr hDs hmass L hL x P referencePosition hx hP hreference hF hell hlo hup σ hσ hsmall δ t w Jall hfinalMass G ρ)] with z hz
  exact reconstruction_of_stored M nodes anchors seeds main final sampling N r Ds hr hDs x P referencePosition hF hell hlo hup σ hσ hsmall δ t w base hfinalMass G z hz

/-- Exact joint law including originalP. The right side reconstructs it
from the same assembly inventory and therefore preserves its correlations. -/
theorem kernel_original_augmented_law
    (ha : 0<rowBound (m := m) r σ δ t w)
    (hA : ∀ i,∑ j,|M.matrix r σ (nodes i) (nodes j)|≤rowBound (m := m) r σ δ t w)
    (ρ : Measure (A × Tape d (Host M nodes anchors seeds main final sampling N))) [IsProbabilityMeasure ρ]
    (μ : Measure (Coarse (d := d) M nodes anchors seeds main final sampling N A)) [IsProbabilityMeasure μ]
    (hsplit : ρ.map (CausalTailHistory.unpack (MeanMainBatchCoupling.bodyCut M nodes anchors seeds main final sampling N))=
      μ.prod (tapeLaw L (body (a := a) (h := h) M nodes main final sampling N)))
    (hincoming : μ.map (incomingAugmented M nodes anchors seeds main final sampling N r hr x P referencePosition hF hell hlo hup σ hσ hsmall base)=
      ((stdGaussian (Point d)).prod (MeanFlowLp.seedMeasure (MeanJointReference.data M hF hell hlo hup r σ hr hσ hsmall base))).prod
        (Measure.pi fun _ : Fin m => stdGaussian (Point d))) :
    (MeanCompletedCoupling.kernel M nodes anchors seeds main final sampling N r Ds hr hDs hmass L hL x P referencePosition hx hP hreference hF hell hlo hup σ hσ hsmall δ t w base hfinalMass G hG Jall Jfinal ∘ₘ ρ).map (fun z => (P z.1.1.1.1,MeanCompletedAugmentedLaws.retainedAugmentedPairs M nodes anchors seeds main final sampling N r Ds hr hDs x P referencePosition hF hell hlo hup σ hσ hsmall δ t w base hfinalMass G z))=
      (((stdGaussian (Point d)).prod (MeanFlowLp.seedMeasure (MeanJointReference.data M hF hell hlo hup r σ hr hσ hsmall base))) ⊗ₘ
          DesignatedChildBatchJointTransfer.averagedPairs L hL (MeanFinalBatchCoupling.data M nodes anchors seeds main final sampling N r Ds hr hDs hfinalMass) Jfinal (fun i (z : Point d × MeanFlowLp.Seed (MeanJointReference.data M hF hell hlo hup r σ hr hσ hsmall base)) => MeanBenchmarkMoments.finalCenter (MeanJointReference.data M hF hell hlo hup r σ hr hσ hsmall base) i z.2) (fun i => (MeanBenchmarkMoments.finalCenter_measurable (MeanJointReference.data M hF hell hlo hup r σ hr hσ hsmall base) i).comp measurable_snd)).map (fun y => (reconstruct (MeanJointReference.data M hF hell hlo hup r σ hr hσ hsmall base) y,y)) := by
  have hlaw := MeanCompletedAugmentedLaws.kernel_augmented_pairs_law M nodes anchors seeds main final sampling N r Ds hr hDs hmass L hL x P referencePosition hx hP hreference hF hell hlo hup σ hσ hsmall δ t w base hfinalMass G hG Jall Jfinal ha hA ρ μ hsplit hincoming
  have hread := retainedPairs_measurable M nodes anchors seeds main final sampling N r Ds hr hDs L x P referencePosition hx hP hreference hF hell hlo hup σ hσ hsmall δ t w base hfinalMass G hG
  have hmrec := reconstruct_measurable (MeanJointReference.data M hF hell hlo hup r σ hr hσ hsmall base)
  have hpair : Measurable (fun y : (Point d × MeanFlowLp.Seed (MeanJointReference.data M hF hell hlo hup r σ hr hσ hsmall base)) × (Fin m → Point d × Point d) => (reconstruct (MeanJointReference.data M hF hell hlo hup r σ hr hσ hsmall base) y,y)) := hmrec.prodMk measurable_id
  rw [← hlaw,Measure.map_map hpair hread]
  apply Measure.map_congr
  filter_upwards [kernel_reconstruction_ae M nodes anchors seeds main final sampling N r Ds hr hDs hmass L hL x P referencePosition hx hP hreference hF hell hlo hup σ hσ hsmall δ t w base hfinalMass G hG Jall Jfinal ρ] with z hz
  exact Prod.ext hz.symm rfl

end AcceleratedLogConcave.Oracle.MeanCompletedReconstruction
