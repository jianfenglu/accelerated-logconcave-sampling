import AcceleratedLogConcave.Oracle.MeanCompletedReference
import AcceleratedLogConcave.Oracle.MeanOriginalBounds

/-! Exact physical centering defect of the constructed mean reference.
The retained reference is normalized: physical output is the primitive mean
plus sigma times that reference. Original P and all Pi corrections remain
literal and cancel by the proved assembly reconstruction. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace AcceleratedLogConcave.Oracle.MeanCompletedQuadrature
open Numerics Numerics.MeanFlowLp Numerics.MeanResidualBridge Numerics.MeanCollocationLp
open Numerics.AffineGraph Conditional Conditional.MeanReferenceLayer Conditional.MeanReferenceSeedLaw
section PairAlgebra
variable {D m : ℕ} (d : MeanFlowLp.Data (Fin D) m) (C : Children d)
local notation "Pair" => (Point D × Seed d) × (Fin m → Point D × Point D)

/-- Reconstructed original input in physical output units. -/
theorem physical_originalInput (z : Pair) :
    d.sigma • originalInput d C (seedBase d z.1,z.2) =
      (d.sigma/2) • z.1.2.1.snd+
        (∑ i,(GaussLegendre.weight m i*C.scale i) • (z.2 i).1)+C.beta • z.1.1 := by
  have hb : GaussianAssembly.mass (GaussianAssembly.inventoryCoefficients (d.sigma/2) (GaussLegendre.weight m) C.scale)+C.beta^2=d.sigma^2 := by
    rw [GaussianAssembly.mass_inventoryCoefficients]
    exact C.budget
  have hr := GaussianAssembly.reserve_eq_budget d.hsigma C.beta_pos hb
  unfold originalInput coefficients
  rw [hr]
  simp only [seedBase,smul_add,Finset.smul_sum,smul_smul,Fintype.sum_option,
    GaussianAssembly.inventoryCoefficients,Option.elim_none,Option.elim_some]
  have hc (a : ℝ) : d.sigma*(a/d.sigma)=a := by field_simp [d.hsigma.ne']
  simp only [hc]
  rfl

/-- Final row using the same retained designated/reference pairs as the
source parent, with no law or accuracy input. -/
def pairedTarget (z : Pair) : Point D :=
  d.sigma • originalInput d C (seedBase d z.1,z.2)+
    ∑ i,GaussLegendre.weight m i •
      (MeanBenchmarkMoments.finalMean d i z.1.2+C.scale i • ((z.2 i).2-(z.2 i).1))

/-- Exact physical target difference, including the original endpoint score.
The reserve and returned references cancel without any independence claim. -/
theorem paired_target_sub_physical_reference (z : Pair) :
    pairedTarget d C z-
      (Gibbs.primitiveMean d.F d.x d.r+d.sigma • referenceOutput d C (seedBase d z.1,z.2)) =
        MeanOriginalBounds.quadratureError d z.1.2 := by
  unfold pairedTarget
  rw [physical_originalInput]
  have hs : d.sigma*d.sigma⁻¹=1 := mul_inv_cancel₀ d.hsigma.ne'
  dsimp only [Conditional.MeanReferenceSeedLaw.referenceOutput,seedBase]
  rw [smul_smul,hs,one_smul]
  have hp : (CenteringFlowLp.phase (kernelData d) (d.sigma/2) (half_pos d.hsigma) 1
      (WithLp.toLp 2 z.1.2.1.ofLp)).snd=score d 1 z.1.2 := by
    simp only [WithLp.toLp_ofLp]
    rfl
  rw [hp]
  dsimp only [MeanOriginalBounds.quadratureError,MeanOriginalBounds.referenceOutput,
    rawTerminalTarget,MeanGeometry.meanOutput,FiniteGraph.collect,FiniteGraph.requests,
    MeanCollocationLp.rawGraph,MeanGeometry.graph,MeanBenchmarkMoments.finalMean,
    MeanBenchmarkMoments.finalCenter]
  simp only [MeanGeometry.center_radius,smul_add,smul_sub,Finset.sum_add_distrib,
    Finset.sum_sub_distrib,mul_smul]
  abel


end PairAlgebra
section Actual
open AffineLowering TapeLowering NoisyLayer SourceMeanExecutable
open TailOccurrenceCut TailCut CanonicalTapeLaw CanonicalTapeMeasurability
open PrivateCausalLayer MeanChronologicalCoupling MeanChronologicalFinalObservation MeanCompletedAugmentedLaws
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




variable (Jall : ∀ (k : ℕ) (hk : k<N),FreshChildBatchCoupling.Lower L
  (data M nodes anchors seeds main final sampling N r Ds hr hDs hmass (stage M nodes anchors seeds main final sampling N k hk.le).1 (stage_positive M nodes anchors seeds main final sampling N k hk)))
  (Jfinal : DesignatedChildBatchCoupling.Lower L (MeanFinalBatchCoupling.data M nodes anchors seeds main final sampling N r Ds hr hDs hfinalMass))


variable (hm : 0<m) (ht : 0<t) (q : ℝ)


local notation "datum" => MeanJointReference.data M hF hell hlo hup r σ hr hσ hsmall base
local notation "children" => MeanCompletedReference.referenceChildren M hF hell hlo hup r σ hr hσ hsmall base hm t ht q
local notation "Sample" => (History (d := d) M nodes anchors seeds main final sampling N A ×
  Tape d (Host M nodes anchors seeds main final sampling N)) × (Fin m → Point d)
local notation "pairs" => MeanCompletedAugmentedLaws.retainedAugmentedPairs M nodes anchors seeds main final sampling N r Ds hr hDs x P referencePosition hF hell hlo hup σ hσ hsmall δ t w base hfinalMass G

/-- The concrete numerical paid target uses the actual stored original Pi,
returned final references and original P of the constructed source sample. -/
def numericalTarget (z : Sample) : Point d :=
  let y := pairs z
  σ • P z.1.1.1.1+∑ i,GaussLegendre.weight m i •
    (MeanBenchmarkMoments.finalMean datum i y.1.2+
      RecursiveMeanPublicTable.finalWidth M.R σ • ((y.2 i).2-(y.2 i).1))

omit [MeasurableSpace A] in
theorem numericalTarget_eq_pairedTarget (z : Sample)
    (hz : MeanCompletedReconstruction.reconstruct datum (pairs z)=P z.1.1.1.1) :
    numericalTarget M nodes anchors seeds main final sampling N r Ds hr hDs x P referencePosition hF hell hlo hup σ hσ hsmall δ t w base hfinalMass G z =
      pairedTarget datum children (pairs z) := by
  have hw (i : Fin m) : (children).scale i=RecursiveMeanPublicTable.finalWidth M.R σ := by
    change M.R*Real.sqrt 3*σ/4=M.R*(Real.sqrt 3*σ/2)/2
    ring
  unfold numericalTarget pairedTarget
  rw [MeanCompletedReference.originalInput_eq_reconstruct, hz]
  simp only [hw]
  rfl

/-- Exact final centering defect on the actual constructed completed kernel.
The right physical reference is mean + sigma times the normalized returned
reference; original-source retention supplies reconstruction internally. -/
theorem kernel_target_sub_reference
    (ρ : Measure (A × Tape d (Host M nodes anchors seeds main final sampling N))) :
    ∀ᵐ z ∂MeanCompletedCoupling.kernel M nodes anchors seeds main final sampling N r Ds hr hDs hmass L hL x P referencePosition hx hP hreference hF hell hlo hup σ hσ hsmall δ t w base hfinalMass G hG Jall Jfinal ∘ₘ ρ,
      numericalTarget M nodes anchors seeds main final sampling N r Ds hr hDs x P referencePosition hF hell hlo hup σ hσ hsmall δ t w base hfinalMass G z-
        (Gibbs.primitiveMean F base r+σ • MeanCompletedReference.readout M nodes anchors seeds main final sampling N r Ds hr hDs x P referencePosition hF hell hlo hup σ hσ hsmall δ t w base hfinalMass G hm ht q z)=
          MeanOriginalBounds.quadratureError datum (pairs z).1.2 := by
  filter_upwards [MeanCompletedReconstruction.kernel_reconstruction_ae M nodes anchors seeds main final sampling N r Ds hr hDs hmass L hL x P referencePosition hx hP hreference hF hell hlo hup σ hσ hsmall δ t w base hfinalMass G hG Jall Jfinal ρ] with z hz
  rw [numericalTarget_eq_pairedTarget M nodes anchors seeds main final sampling N r Ds hr hDs x P referencePosition hF hell hlo hup σ hσ hsmall δ t w base hfinalMass G hm ht q z hz]
  exact paired_target_sub_physical_reference datum children (pairs z)

/-- The actual completed coupling's original mean-flow seed has precisely
its original-data source law. Only the incoming source factorization is used;
no returned-child Gaussian identification or error hypothesis is needed. -/
theorem kernel_seed_preserving
    (ha : 0<rowBound (m := m) r σ δ t w)
    (hA : ∀ i,∑ j,|M.matrix r σ (nodes i) (nodes j)|≤rowBound (m := m) r σ δ t w)
    (ρ : Measure (A × Tape d (Host M nodes anchors seeds main final sampling N))) [IsProbabilityMeasure ρ]
    (μ : Measure (Coarse (d := d) M nodes anchors seeds main final sampling N A)) [IsProbabilityMeasure μ]
    (hsplit : ρ.map (CausalTailHistory.unpack (MeanMainBatchCoupling.bodyCut M nodes anchors seeds main final sampling N))=
      μ.prod (tapeLaw L (body (a := a) (h := h) M nodes main final sampling N)))
    (hincoming : μ.map (incomingAugmented M nodes anchors seeds main final sampling N r hr x P referencePosition hF hell hlo hup σ hσ hsmall base)=
      ((stdGaussian (Point d)).prod (seedMeasure datum)).prod (Measure.pi fun _ : Fin m => stdGaussian (Point d))) :
    MeasurePreserving (fun z : Sample => (pairs z).1.2)
      (MeanCompletedCoupling.kernel M nodes anchors seeds main final sampling N r Ds hr hDs hmass L hL x P referencePosition hx hP hreference hF hell hlo hup σ hσ hsmall δ t w base hfinalMass G hG Jall Jfinal ∘ₘ ρ)
      (seedMeasure datum) := by
  let η := (stdGaussian (Point d)).prod (seedMeasure datum)
  let κ := DesignatedChildBatchJointTransfer.averagedPairs L hL
    (MeanFinalBatchCoupling.data M nodes anchors seeds main final sampling N r Ds hr hDs hfinalMass) Jfinal
    (fun i (z : Point d × Seed datum) => MeanBenchmarkMoments.finalCenter datum i z.2)
    (fun i => (MeanBenchmarkMoments.finalCenter_measurable datum i).comp measurable_snd)
  have hpairs : MeasurePreserving pairs
      (MeanCompletedCoupling.kernel M nodes anchors seeds main final sampling N r Ds hr hDs hmass L hL x P referencePosition hx hP hreference hF hell hlo hup σ hσ hsmall δ t w base hfinalMass G hG Jall Jfinal ∘ₘ ρ)
      (η ⊗ₘ κ) :=
    ⟨MeanCompletedReconstruction.retainedPairs_measurable M nodes anchors seeds main final sampling N r Ds hr hDs L x P referencePosition hx hP hreference hF hell hlo hup σ hσ hsmall δ t w base hfinalMass G hG,
      kernel_augmented_pairs_law M nodes anchors seeds main final sampling N r Ds hr hDs hmass L hL x P referencePosition hx hP hreference hF hell hlo hup σ hσ hsmall δ t w base hfinalMass G hG Jall Jfinal ha hA ρ μ hsplit hincoming⟩
  have hf : MeasurePreserving Prod.fst (η ⊗ₘ κ) η := ⟨measurable_fst,Measure.fst_compProd η κ⟩
  exact (measurePreserving_snd (μ := stdGaussian (Point d)) (ν := seedMeasure datum)).comp (hf.comp hpairs)

/-- Original-data endpoint quadrature in L² on the actual full completed
source law, including its exact physical normalization. -/
theorem kernel_quadrature_bound
    (ha : 0<rowBound (m := m) r σ δ t w)
    (hA : ∀ i,∑ j,|M.matrix r σ (nodes i) (nodes j)|≤rowBound (m := m) r σ δ t w)
    (ρ : Measure (A × Tape d (Host M nodes anchors seeds main final sampling N))) [IsProbabilityMeasure ρ]
    (μ : Measure (Coarse (d := d) M nodes anchors seeds main final sampling N A)) [IsProbabilityMeasure μ]
    (hsplit : ρ.map (CausalTailHistory.unpack (MeanMainBatchCoupling.bodyCut M nodes anchors seeds main final sampling N))=
      μ.prod (tapeLaw L (body (a := a) (h := h) M nodes main final sampling N)))
    (hincoming : μ.map (incomingAugmented M nodes anchors seeds main final sampling N r hr x P referencePosition hF hell hlo hup σ hσ hsmall base)=
      ((stdGaussian (Point d)).prod (seedMeasure datum)).prod (Measure.pi fun _ : Fin m => stdGaussian (Point d)))
    (hm2 : 2≤m) :
    ∃ hq : MemLp (fun z : Sample =>
      numericalTarget M nodes anchors seeds main final sampling N r Ds hr hDs x P referencePosition hF hell hlo hup σ hσ hsmall δ t w base hfinalMass G z-
        (Gibbs.primitiveMean F base r+σ • MeanCompletedReference.readout M nodes anchors seeds main final sampling N r Ds hr hDs x P referencePosition hF hell hlo hup σ hσ hsmall δ t w base hfinalMass G hm ht q z)) 2
          (MeanCompletedCoupling.kernel M nodes anchors seeds main final sampling N r Ds hr hDs hmass L hL x P referencePosition hx hP hreference hF hell hlo hup σ hσ hsmall δ t w base hfinalMass G hG Jall Jfinal ∘ₘ ρ),
      ‖hq.toLp _‖≤MeanOriginalBounds.quadratureBudget datum := by
  have hp := kernel_seed_preserving M nodes anchors seeds main final sampling N r Ds hr hDs hmass L hL x P referencePosition hx hP hreference hF hell hlo hup σ hσ hsmall δ t w base hfinalMass G hG Jall Jfinal ha hA ρ μ hsplit hincoming
  let hi := (MeanOriginalBounds.quadrature_memLp datum).comp_measurePreserving hp
  have he : (fun z : Sample =>
      numericalTarget M nodes anchors seeds main final sampling N r Ds hr hDs x P referencePosition hF hell hlo hup σ hσ hsmall δ t w base hfinalMass G z-
        (Gibbs.primitiveMean F base r+σ • MeanCompletedReference.readout M nodes anchors seeds main final sampling N r Ds hr hDs x P referencePosition hF hell hlo hup σ hσ hsmall δ t w base hfinalMass G hm ht q z)) =ᵐ[_]
      (fun z : Sample => MeanOriginalBounds.quadratureError datum (pairs z).1.2) :=
    kernel_target_sub_reference M nodes anchors seeds main final sampling N r Ds hr hDs hmass L hL x P referencePosition hx hP hreference hF hell hlo hup σ hσ hsmall δ t w base hfinalMass G hG Jall Jfinal hm ht q ρ
  let hq := hi.ae_eq he.symm
  refine ⟨hq,?_⟩
  have heLp : hq.toLp _=hi.toLp _ := Lp.ext (hq.coeFn_toLp.trans (he.trans hi.coeFn_toLp.symm))
  rw [heLp]
  change ‖Lp.compMeasurePreserving _ hp ((MeanOriginalBounds.quadrature_memLp datum).toLp _)‖≤_
  rw [Lp.norm_compMeasurePreserving]
  exact MeanOriginalBounds.quadrature_norm_le datum hm2

end Actual
end AcceleratedLogConcave.Oracle.MeanCompletedQuadrature
