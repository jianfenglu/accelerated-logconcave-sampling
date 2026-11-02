import AcceleratedLogConcave.Oracle.MeanCompletedReconstruction
import AcceleratedLogConcave.Conditional.MeanReferenceSeedLaw

/-! Identification of the actual completed designated-final coupling with
the prescribed recursive parent reference, retaining the original input. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
namespace AcceleratedLogConcave.Oracle.MeanCompletedReference
open Numerics Numerics.AffineGraph AffineLowering TapeLowering NoisyLayer SourceMeanExecutable
open TailOccurrenceCut TailCut CanonicalTapeLaw CanonicalTapeMeasurability
open PrivateCausalLayer MeanChronologicalCoupling MeanChronologicalFinalObservation MeanCompletedAugmentedLaws
open Conditional.MeanReferenceSeedLaw

section Geometry
variable {m d : ℕ} (M : MeanGeometry m)
  {F : Point d → ℝ} (hF : ContDiff ℝ 2 F) {ell : ℝ} (hell : 0≤ell)
  (hlo : ∀ z v,0≤fderiv ℝ (fderiv ℝ F) z v v)
  (hup : ∀ z v,fderiv ℝ (fderiv ℝ F) z v v≤ell*‖v‖^2)
  (r σ : ℝ) (hr : 0<r) (hσ : 0<σ) (hsmall : r^2*ell≤1/2) (base : Point d)

def parentTheta : Conditional.SourceParameters (Point d) ell :=
  ⟨(base,r,σ),hr,hσ,hsmall⟩

def referenceChildren (hm : 0<m) (t : ℝ) (ht : 0<t) (q : ℝ) :
    Conditional.MeanReferenceLayer.Children (MeanJointReference.data M hF hell hlo hup r σ hr hσ hsmall base) :=
  Conditional.RecursiveReference.sourceChildren hF hell hlo hup M hm
    (Conditional.RecursiveReference.referenceFamily hF hell hlo hup M hm t ht (q-t))
    (parentTheta r σ hr hσ hsmall base)

theorem referenceChildren_coefficients (hm : 0<m) (t : ℝ) (ht : 0<t) (q : ℝ) :
    Conditional.MeanReferenceLayer.coefficients (MeanJointReference.data M hF hell hlo hup r σ hr hσ hsmall base)
      (referenceChildren M hF hell hlo hup r σ hr hσ hsmall base hm t ht q)=Conditional.TerminalChildrenParentFamily.normalizedCoefficients M := by
  exact Conditional.RecursiveReference.coefficients_sourceChildren hF hell hlo hup M hm
    (Conditional.RecursiveReference.referenceFamily hF hell hlo hup M hm t ht (q-t))
    (parentTheta r σ hr hσ hsmall base)

private theorem assembly_mass_eq :
    Conditional.GaussianAssembly.mass (assembly M)=
      Conditional.GaussianAssembly.mass (Conditional.TerminalChildrenParentFamily.normalizedCoefficients M) := by
  simp only [Conditional.GaussianAssembly.mass,assembly,
    Conditional.TerminalChildrenParentFamily.normalizedCoefficients,
    Fin.sum_univ_succ,Fintype.sum_option,Fin.cases_zero,Fin.cases_succ]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  ring

private theorem assembly_sum_eq (g : Point d) (p : Fin m → Point d) :
    (∑ i : Option (Fin m),Conditional.TerminalChildrenParentFamily.normalizedCoefficients M i • i.elim g p)=
      ∑ i : Fin (m+1),assembly M i • Fin.cases g p i := by
  simp only [assembly,Conditional.TerminalChildrenParentFamily.normalizedCoefficients,
    Fin.sum_univ_succ,Fintype.sum_option,Fin.cases_zero,Fin.cases_succ,
    Option.elim_none,Option.elim_some]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  ring

/-- The reference family's recovered input is exactly the executable
assembly reconstruction, including its reserve coefficient. -/
theorem originalInput_eq_reconstruct (hm : 0<m) (t : ℝ) (ht : 0<t) (q : ℝ)
    (z : (Point d × MeanFlowLp.Seed (MeanJointReference.data M hF hell hlo hup r σ hr hσ hsmall base)) × (Fin m → Point d × Point d)) :
    originalInput (MeanJointReference.data M hF hell hlo hup r σ hr hσ hsmall base)
      (referenceChildren M hF hell hlo hup r σ hr hσ hsmall base hm t ht q)
      (seedBase (MeanJointReference.data M hF hell hlo hup r σ hr hσ hsmall base) z.1,z.2)=
        MeanCompletedReconstruction.reconstruct (MeanJointReference.data M hF hell hlo hup r σ hr hσ hsmall base) z := by
  unfold originalInput
  rw [referenceChildren_coefficients]
  change (∑ i : Option (Fin m),Conditional.TerminalChildrenParentFamily.normalizedCoefficients M i •
      i.elim z.1.2.1.ofLp.2 (fun j => (z.2 j).1))+
    Conditional.GaussianAssembly.reserve (Conditional.TerminalChildrenParentFamily.normalizedCoefficients M) • z.1.1 =
      (∑ i : Fin (m+1),assembly M i • Fin.cases z.1.2.1.ofLp.2 (fun j => (z.2 j).1) i)+
        Conditional.GaussianAssembly.reserve (assembly M) • z.1.1
  rw [assembly_sum_eq,Conditional.GaussianAssembly.reserve,Conditional.GaussianAssembly.reserve,assembly_mass_eq]

end Geometry
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

/-- The actual lower standalone retained law is the sole recursive premise.
Every center, radius and physical child width is the prescribed source value. -/
theorem averagedPairs_eq_seedPairs
    (hretained : ∀ i y, (Jfinal.joint i y).map (fun z => (z.1.1,z.2)) =
      (stdGaussian (Point d)) ⊗ₘ
        ((Conditional.RecursiveReference.referenceFamily hF hell hlo hup M hm t ht (q-t)).kernel.comap
          (fun p => (Conditional.RecursiveReference.childParameters hell M (parentTheta r σ hr hσ hsmall base) y,p)) measurable_prodMk_left)) :
    DesignatedChildBatchJointTransfer.averagedPairs L hL (MeanFinalBatchCoupling.data M nodes anchors seeds main final sampling N r Ds hr hDs hfinalMass) Jfinal
      (fun i (z : Point d × MeanFlowLp.Seed (MeanJointReference.data M hF hell hlo hup r σ hr hσ hsmall base)) => MeanBenchmarkMoments.finalCenter (MeanJointReference.data M hF hell hlo hup r σ hr hσ hsmall base) i z.2) (fun i => (MeanBenchmarkMoments.finalCenter_measurable (MeanJointReference.data M hF hell hlo hup r σ hr hσ hsmall base) i).comp measurable_snd) =
        seedPairs (MeanJointReference.data M hF hell hlo hup r σ hr hσ hsmall base) (referenceChildren M hF hell hlo hup r σ hr hσ hsmall base hm t ht q) := by
  ext z : 1
  rw [DesignatedChildBatchJointTransfer.averagedPairs_apply,seedPairs,Kernel.comap_apply,pairedChildren_apply]
  congr 1
  apply funext
  intro i
  rw [hretained]
  have hc : MeanBenchmarkMoments.finalCenter (MeanJointReference.data M hF hell hlo hup r σ hr hσ hsmall base) i z.2 =
      Conditional.MeanReferenceLayer.stateCenter (MeanJointReference.data M hF hell hlo hup r σ hr hσ hsmall base) i (seedBase (MeanJointReference.data M hF hell hlo hup r σ hr hσ hsmall base) z) := by
    simp only [MeanBenchmarkMoments.finalCenter,MeanResidualBridge.rawReference,
      MeanResidualBridge.rawCurves,AffineResidual.Mean.Curves.reference,
      MeanGeometry.MeanNode.center,MeanFlowLp.position,MeanFlowLp.phase,
      Conditional.MeanReferenceLayer.stateCenter,seedBase,WithLp.toLp_ofLp,
      MeanGeometry.centerNode,GaussLegendre.cellNode,zero_add,one_mul]
  rw [hc]
  congr 1

/-- Literal physical parent-reference readout of the completed source
coupling: actual phase score, returned final references and assembly reserve. -/
def readout (z : (History (d := d) M nodes anchors seeds main final sampling N A × Tape d (Host M nodes anchors seeds main final sampling N)) × (Fin m → Point d)) : Point d :=
  let y := retainedAugmentedPairs M nodes anchors seeds main final sampling N r Ds hr hDs x P referencePosition hF hell hlo hup σ hσ hsmall δ t w base hfinalMass G z
  referenceOutput (MeanJointReference.data M hF hell hlo hup r σ hr hσ hsmall base) (referenceChildren M hF hell hlo hup r σ hr hσ hsmall base hm t ht q) (seedBase (MeanJointReference.data M hF hell hlo hup r σ hr hσ hsmall base) y.1,y.2)

include L hx hP hreference hG in
theorem readout_measurable : Measurable (readout M nodes anchors seeds main final sampling N r Ds hr hDs x P referencePosition hF hell hlo hup σ hσ hsmall δ t w base hfinalMass G hm ht q) := by
  have hread := MeanCompletedReconstruction.retainedPairs_measurable M nodes anchors seeds main final sampling N r Ds hr hDs L x P referencePosition hx hP hreference hF hell hlo hup σ hσ hsmall δ t w base hfinalMass G hG
  exact (referenceOutput_measurable (MeanJointReference.data M hF hell hlo hup r σ hr hσ hsmall base) (referenceChildren M hF hell hlo hup r σ hr hσ hsmall base hm t ht q)).comp
    ((((seedBase_measurable (MeanJointReference.data M hF hell hlo hup r σ hr hσ hsmall base)).comp hread.fst).prodMk hread.snd))

/-- The constructed full-tape coupling has exactly the prescribed recursive
retained parent reference law at the original input. Only lower retained laws
enter recursively; the input is never made independent of its assembly. -/
theorem kernel_retained_reference_law
    (hq : (1/2 : ℝ)<q)
    (hretained : ∀ i y, (Jfinal.joint i y).map (fun z => (z.1.1,z.2)) =
      (stdGaussian (Point d)) ⊗ₘ
        ((Conditional.RecursiveReference.referenceFamily hF hell hlo hup M hm t ht (q-t)).kernel.comap
          (fun p => (Conditional.RecursiveReference.childParameters hell M (parentTheta r σ hr hσ hsmall base) y,p)) measurable_prodMk_left))
    (ha : 0<rowBound (m := m) r σ δ t w)
    (hA : ∀ i,∑ j,|M.matrix r σ (nodes i) (nodes j)|≤rowBound (m := m) r σ δ t w)
    (ρ : Measure (A × Tape d (Host M nodes anchors seeds main final sampling N))) [IsProbabilityMeasure ρ]
    (μ : Measure (Coarse (d := d) M nodes anchors seeds main final sampling N A)) [IsProbabilityMeasure μ]
    (hsplit : ρ.map (CausalTailHistory.unpack (MeanMainBatchCoupling.bodyCut M nodes anchors seeds main final sampling N))=
      μ.prod (tapeLaw L (body (a := a) (h := h) M nodes main final sampling N)))
    (hincoming : μ.map (incomingAugmented M nodes anchors seeds main final sampling N r hr x P referencePosition hF hell hlo hup σ hσ hsmall base)=
      ((stdGaussian (Point d)).prod (MeanFlowLp.seedMeasure (MeanJointReference.data M hF hell hlo hup r σ hr hσ hsmall base))).prod
        (Measure.pi fun _ : Fin m => stdGaussian (Point d))) :
    (MeanCompletedCoupling.kernel M nodes anchors seeds main final sampling N r Ds hr hDs hmass L hL x P referencePosition hx hP hreference hF hell hlo hup σ hσ hsmall δ t w base hfinalMass G hG Jall Jfinal ∘ₘ ρ).map (fun z => (P z.1.1.1.1,
      readout M nodes anchors seeds main final sampling N r Ds hr hDs x P referencePosition hF hell hlo hup σ hσ hsmall δ t w base hfinalMass G hm ht q z)) =
        (stdGaussian (Point d)) ⊗ₘ
          ((Conditional.RecursiveReference.referenceFamily hF hell hlo hup M hm t ht q).kernel.comap
            (fun p => (parentTheta r σ hr hσ hsmall base,p)) measurable_prodMk_left) := by
  have hlaw := MeanCompletedAugmentedLaws.kernel_augmented_pairs_law M nodes anchors seeds main final sampling N r Ds hr hDs hmass L hL x P referencePosition hx hP hreference hF hell hlo hup σ hσ hsmall δ t w base hfinalMass G hG Jall Jfinal ha hA ρ μ hsplit hincoming
  rw [averagedPairs_eq_seedPairs M nodes anchors seeds main final sampling N r Ds hr hDs L hL hF hell hlo hup σ hσ hsmall t base hfinalMass Jfinal hm ht q hretained] at hlaw
  have hread := MeanCompletedReconstruction.retainedPairs_measurable M nodes anchors seeds main final sampling N r Ds hr hDs L x P referencePosition hx hP hreference hF hell hlo hup σ hσ hsmall δ t w base hfinalMass G hG
  have hg : Measurable (fun y : (Point d × MeanFlowLp.Seed (MeanJointReference.data M hF hell hlo hup r σ hr hσ hsmall base)) × (Fin m → Point d × Point d) =>
      (originalInput (MeanJointReference.data M hF hell hlo hup r σ hr hσ hsmall base) (referenceChildren M hF hell hlo hup r σ hr hσ hsmall base hm t ht q) (seedBase (MeanJointReference.data M hF hell hlo hup r σ hr hσ hsmall base) y.1,y.2),
        referenceOutput (MeanJointReference.data M hF hell hlo hup r σ hr hσ hsmall base) (referenceChildren M hF hell hlo hup r σ hr hσ hsmall base hm t ht q) (seedBase (MeanJointReference.data M hF hell hlo hup r σ hr hσ hsmall base) y.1,y.2))) :=
    ((originalInput_measurable (MeanJointReference.data M hF hell hlo hup r σ hr hσ hsmall base) (referenceChildren M hF hell hlo hup r σ hr hσ hsmall base hm t ht q)).prodMk
      (referenceOutput_measurable (MeanJointReference.data M hF hell hlo hup r σ hr hσ hsmall base) (referenceChildren M hF hell hlo hup r σ hr hσ hsmall base hm t ht q))).comp
        (((seedBase_measurable (MeanJointReference.data M hF hell hlo hup r σ hr hσ hsmall base)).comp measurable_fst).prodMk measurable_snd)
  have h := congrArg (fun ν : Measure ((Point d × MeanFlowLp.Seed (MeanJointReference.data M hF hell hlo hup r σ hr hσ hsmall base)) × (Fin m → Point d × Point d)) =>
    ν.map (fun y => (originalInput (MeanJointReference.data M hF hell hlo hup r σ hr hσ hsmall base) (referenceChildren M hF hell hlo hup r σ hr hσ hsmall base hm t ht q) (seedBase (MeanJointReference.data M hF hell hlo hup r σ hr hσ hsmall base) y.1,y.2),
      referenceOutput (MeanJointReference.data M hF hell hlo hup r σ hr hσ hsmall base) (referenceChildren M hF hell hlo hup r σ hr hσ hsmall base hm t ht q) (seedBase (MeanJointReference.data M hF hell hlo hup r σ hr hσ hsmall base) y.1,y.2)))) hlaw
  rw [Measure.map_map hg hread] at h
  rw [seed_retained_law] at h
  have hsection := Conditional.RecursiveReference.referenceFamily_section hF hell hlo hup M hm t ht q hq (parentTheta r σ hr hσ hsmall base)
  change _=Conditional.MeanReferenceLayer.parentKernel
    (MeanJointReference.data M hF hell hlo hup r σ hr hσ hsmall base)
    (referenceChildren M hF hell hlo hup r σ hr hσ hsmall base hm t ht q) at hsection
  rw [← hsection] at h
  refine (Measure.map_congr ?_).trans h
  filter_upwards [MeanCompletedReconstruction.kernel_reconstruction_ae M nodes anchors seeds main final sampling N r Ds hr hDs hmass L hL x P referencePosition hx hP hreference hF hell hlo hup σ hσ hsmall δ t w base hfinalMass G hG Jall Jfinal ρ] with z hz
  apply Prod.ext
  · exact (originalInput_eq_reconstruct M hF hell hlo hup r σ hr hσ hsmall base hm t ht q (retainedAugmentedPairs M nodes anchors seeds main final sampling N r Ds hr hDs x P referencePosition hF hell hlo hup σ hσ hsmall δ t w base hfinalMass G z)).trans hz |>.symm
  · rfl

end AcceleratedLogConcave.Oracle.MeanCompletedReference
