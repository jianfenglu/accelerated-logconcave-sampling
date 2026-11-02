import AcceleratedLogConcave.Oracle.MeanChronologicalFinalObservation

/-! The actual designated final observation law, obtained from constructed
mean chronology and the incoming benchmark-seed/assembled-Pi joint law. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set
open MeasureTheory.Measure
namespace AcceleratedLogConcave.Oracle.MeanChronologicalFinalProjection
open Numerics Numerics.AffineGraph AffineLowering TapeLowering NoisyLayer
open RecursiveMeanProgram RecursiveMeanContinuation SourceMeanLayer SourceMeanExecutable
open TailOccurrenceCut TailCut CanonicalTapeLaw CanonicalTapeMeasurability
open PrivateCausalLayer PrivateCausalAdvance MeanChronologicalCoupling MeanChronologicalFinalObservation

private def pairSplit {N : ℕ} (U V : Fin N → Type*)
    [∀ i,MeasurableSpace (U i)] [∀ i,MeasurableSpace (V i)] :
    (∀ i,U i × V i) ≃ᵐ ((∀ i,U i) × (∀ i,V i)) where
  toFun w := (fun i => (w i).1,fun i => (w i).2)
  invFun z i := (z.1 i,z.2 i)
  left_inv _ := rfl
  right_inv _ := rfl
  measurable_toFun := (Measurable.of_eval fun i => (measurable_pi_apply i).fst).prodMk
    (Measurable.of_eval fun i => (measurable_pi_apply i).snd)
  measurable_invFun := Measurable.of_eval fun i =>
    ((measurable_pi_apply i).comp measurable_fst).prodMk ((measurable_pi_apply i).comp measurable_snd)

private theorem pairSplit_preserving {N : ℕ} (U V : Fin N → Type*)
    [∀ i,MeasurableSpace (U i)] [∀ i,MeasurableSpace (V i)]
    (μ : ∀ i,Measure (U i)) (ν : ∀ i,Measure (V i))
    [∀ i,SigmaFinite (μ i)] [∀ i,SigmaFinite (ν i)] :
    MeasurePreserving (pairSplit U V) (Measure.pi fun i => (μ i).prod (ν i))
      ((Measure.pi μ).prod (Measure.pi ν)) := by
  refine ⟨(pairSplit U V).measurable,?_⟩
  refine (FiniteSpanningSetsIn.ext ?_ (isPiSystem_pi.prod isPiSystem_pi)
    ((FiniteSpanningSetsIn.pi fun i => (μ i).toFiniteSpanningSetsIn).prod
      (FiniteSpanningSetsIn.pi fun i => (ν i).toFiniteSpanningSetsIn)) ?_).symm
  · refine (generateFrom_eq_prod generateFrom_pi generateFrom_pi ?_ ?_).symm
    · exact (FiniteSpanningSetsIn.pi fun i => (μ i).toFiniteSpanningSetsIn).isCountablySpanning
    · exact (FiniteSpanningSetsIn.pi fun i => (ν i).toFiniteSpanningSetsIn).isCountablySpanning
  · rintro _ ⟨s,⟨s,_,rfl⟩,⟨_,⟨t,_,rfl⟩,rfl⟩⟩
    rw [MeasurableEquiv.map_apply]
    have he : (pairSplit U V) ⁻¹' (univ.pi s ×ˢ univ.pi t)=univ.pi (fun i => s i ×ˢ t i) := by
      ext z
      simp [pairSplit,Set.mem_pi,forall_and]
    rw [he]
    simp_rw [Measure.prod_prod,Measure.pi_pi,Measure.prod_prod,Finset.prod_mul_distrib]

private theorem raw_preserving {N C d : ℕ} {Γ : Ctx}
    (L : PrimitiveLaws d) (hL : L.pointDraw=stdGaussian (Point d))
    (B : DesignatedChildBatchCoupling.Data N C Γ) :
    let : ∀ i,MeasurableSpace (Tape d (DesignatedChildBatchCoupling.program B i)) := fun _ => tapeSpace d _
    MeasurePreserving (fun z : ((Fin N → Point d) × (Fin N → Point d)) ×
      (∀ i,Tape d (DesignatedChildBatchCoupling.program B i)) => fun i => (z.1.1 i,(z.1.2 i,z.2 i)))
      (((Measure.pi fun _ : Fin N => stdGaussian (Point d)).prod
        (Measure.pi fun _ : Fin N => stdGaussian (Point d))).prod
          (Measure.pi fun i => tapeLaw L (DesignatedChildBatchCoupling.program B i)))
      (Measure.pi (DesignatedChildBatchCoupling.rawLaw L B)) := by
  let : ∀ i,MeasurableSpace (Tape d (DesignatedChildBatchCoupling.program B i)) := fun _ => tapeSpace d _
  let : ∀ i,IsProbabilityMeasure (tapeLaw L (DesignatedChildBatchCoupling.program B i)) :=
    fun i => tapeLaw_probability L _
  have h1 := (pairSplit_preserving (fun _ : Fin N => Point d)
    (fun i => Tape d (DesignatedChildBatchCoupling.program B i))
    (fun _ => stdGaussian (Point d)) (fun i => tapeLaw L (DesignatedChildBatchCoupling.program B i))).symm
  have h2 := (pairSplit_preserving (fun _ : Fin N => Point d)
    (fun i => Point d × Tape d (DesignatedChildBatchCoupling.program B i))
    (fun _ => stdGaussian (Point d))
    (fun i => (stdGaussian (Point d)).prod (tapeLaw L (DesignatedChildBatchCoupling.program B i)))).symm
  have hp := h2.comp (((MeasurePreserving.id (Measure.pi fun _ : Fin N => stdGaussian (Point d))).prod h1).comp
    (measurePreserving_prodAssoc (Measure.pi fun _ : Fin N => stdGaussian (Point d))
      (Measure.pi fun _ : Fin N => stdGaussian (Point d))
      (Measure.pi fun i => tapeLaw L (DesignatedChildBatchCoupling.program B i))))
  change MeasurePreserving (fun z : ((Fin N → Point d) × (Fin N → Point d)) ×
      (∀ i,Tape d (DesignatedChildBatchCoupling.program B i)) => fun i => (z.1.1 i,(z.1.2 i,z.2 i))) _ _ at hp
  change MeasurePreserving _ _ (Measure.pi fun i => (stdGaussian (Point d)).prod
    (L.pointDraw.prod (tapeLaw L (DesignatedChildBatchCoupling.program B i))))
  rw [hL]
  exact hp


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

def incomingInventory (c : Coarse (d := d) M nodes anchors seeds main final sampling N A) := (benchmarkSeed M nodes anchors seeds main final sampling N r hr x P referencePosition hF hell hlo hup σ hσ hsmall base c,staticPi M nodes anchors seeds main final sampling N P c)

include hx hP hreference in
theorem incomingInventory_measurable :
    Measurable (incomingInventory M nodes anchors seeds main final sampling N r hr x P referencePosition hF hell hlo hup σ hσ hsmall base) :=
  (benchmarkSeed_measurable M nodes anchors seeds main final sampling N r hr x P referencePosition hx hP hreference hF hell hlo hup σ hσ hsmall base).prodMk (staticPi_measurable M nodes anchors seeds main final sampling N P hP)

def finalCoarse (z : History (d := d) M nodes anchors seeds main final sampling N A × Prefix d (MeanFinalBatchCoupling.batchCut M nodes anchors seeds main final sampling N r Ds hr hDs hfinalMass)) := benchmarkSeed M nodes anchors seeds main final sampling N r hr x P referencePosition hF hell hlo hup σ hσ hsmall base z.1.1

def finalComparison (i : Fin m)
    (z : History (d := d) M nodes anchors seeds main final sampling N A × Prefix d (MeanFinalBatchCoupling.batchCut M nodes anchors seeds main final sampling N r Ds hr hDs hfinalMass)) := z.1.2.2 (centerIndex M nodes i)

include hx hP hreference in
theorem finalCoarse_measurable :
    Measurable (finalCoarse M nodes anchors seeds main final sampling N r Ds hr hDs x P referencePosition hF hell hlo hup σ hσ hsmall base hfinalMass) :=
  (benchmarkSeed_measurable M nodes anchors seeds main final sampling N r hr x P referencePosition hx hP hreference hF hell hlo hup σ hσ hsmall base).comp measurable_fst.fst

theorem finalComparison_measurable (i : Fin m) :
    Measurable (finalComparison (d := d) (A := A) M nodes anchors seeds main final sampling N r Ds hr hDs hfinalMass i) := by
  exact (measurable_pi_apply (centerIndex M nodes i)).comp measurable_fst.snd.snd

def finalObservation := MeanFinalBatchCoupling.observation M nodes anchors seeds main final sampling N r Ds hr hDs hfinalMass G
  (sourceInput M nodes anchors seeds main final sampling N r Ds x P σ δ t w)
  (finalCoarse M nodes anchors seeds main final sampling N r Ds hr hDs x P referencePosition hF hell hlo hup σ hσ hsmall base hfinalMass)
  (finalComparison M nodes anchors seeds main final sampling N r Ds hr hDs hfinalMass)

include hx hP hreference hG in
theorem finalObservation_measurable :
    Measurable (finalObservation M nodes anchors seeds main final sampling N r Ds hr hDs x P referencePosition hF hell hlo hup σ hσ hsmall δ t w base hfinalMass G) :=
  MeanFinalBatchCoupling.observation_measurable M nodes anchors seeds main final sampling N r Ds hr hDs hfinalMass G hG
    (sourceInput M nodes anchors seeds main final sampling N r Ds x P σ δ t w) (fun _ => measurable_const)
    (hx.comp measurable_fst.fst) (hP.comp measurable_fst.fst)
    (finalCoarse M nodes anchors seeds main final sampling N r Ds hr hDs x P referencePosition hF hell hlo hup σ hσ hsmall base hfinalMass)
    (finalCoarse_measurable M nodes anchors seeds main final sampling N r Ds hr hDs x P referencePosition hx hP hreference hF hell hlo hup σ hσ hsmall base hfinalMass)
    (finalComparison M nodes anchors seeds main final sampling N r Ds hr hDs hfinalMass) (finalComparison_measurable M nodes anchors seeds main final sampling N r Ds hr hDs hfinalMass)

include hx hP hreference hG hL in
/-- The only joint law needed before chronology is named explicitly: the
actual benchmark phase seed and incoming assembled designated inventory.
The final observed source law is derived after consuming the actual batch. -/
theorem final_observation_law
    (μ : Measure (Coarse (d := d) M nodes anchors seeds main final sampling N A)) [IsProbabilityMeasure μ]
    (ν : Measure (History (d := d) M nodes anchors seeds main final sampling N A × Prefix d (MeanFinalBatchCoupling.batchCut M nodes anchors seeds main final sampling N r Ds hr hDs hfinalMass))) [IsProbabilityMeasure ν]
    (hincoming : μ.map (incomingInventory M nodes anchors seeds main final sampling N r hr x P referencePosition hF hell hlo hup σ hσ hsmall base)=
      (MeanFlowLp.seedMeasure (MeanJointReference.data M hF hell hlo hup r σ hr hσ hsmall base)).prod (Measure.pi fun _ : Fin m => stdGaussian (Point d)))
    (hcomparison : ν.map (fun z => (z.1.1,z.1.2.2))=
      μ.prod (Measure.pi fun _ : Fin n => stdGaussian (Point d)))
    (hPi : ∀ᵐ z ∂ν,staticPi M nodes anchors seeds main final sampling N P z.1.1=storedPi M nodes anchors seeds main final sampling N r Ds hr hDs x P σ δ t w hfinalMass G z) :
    (advancedLaw L (MeanFinalBatchCoupling.batchCut M nodes anchors seeds main final sampling N r Ds hr hDs hfinalMass) ν).map
      (finalObservation M nodes anchors seeds main final sampling N r Ds hr hDs x P referencePosition hF hell hlo hup σ hσ hsmall δ t w base hfinalMass G)=
        (MeanFlowLp.seedMeasure (MeanJointReference.data M hF hell hlo hup r σ hr hσ hsmall base)).prod (Measure.pi (DesignatedChildBatchCoupling.rawLaw L
          (MeanFinalBatchCoupling.data M nodes anchors seeds main final sampling N r Ds hr hDs hfinalMass))) := by
  let γ := stdGaussian (Point d)
  let γm := Measure.pi fun _ : Fin m => γ
  let ξ := MeanFlowLp.seedMeasure (MeanJointReference.data M hF hell hlo hup r σ hr hσ hsmall base)
  let Bd := MeanFinalBatchCoupling.data M nodes anchors seeds main final sampling N r Ds hr hDs hfinalMass
  let τs := Measure.pi fun i => tapeLaw L (DesignatedChildBatchCoupling.program Bd i)
  let : ∀ i,IsProbabilityMeasure (tapeLaw L (DesignatedChildBatchCoupling.program Bd i)) :=
    fun i => tapeLaw_probability L _
  let : IsProbabilityMeasure τs := by dsimp [τs]; infer_instance
  have hi : MeasurePreserving
      (incomingInventory M nodes anchors seeds main final sampling N r hr x P referencePosition hF hell hlo hup σ hσ hsmall base) μ (ξ.prod γm) :=
    ⟨incomingInventory_measurable M nodes anchors seeds main final sampling N r hr x P referencePosition hx hP hreference hF hell hlo hup σ hσ hsmall base,hincoming⟩
  have hc : MeasurePreserving (fun z : History (d := d) M nodes anchors seeds main final sampling N A × Prefix d (MeanFinalBatchCoupling.batchCut M nodes anchors seeds main final sampling N r Ds hr hDs hfinalMass) =>
      (z.1.1,z.1.2.2)) ν (μ.prod (Measure.pi fun _ : Fin n => γ)) :=
    ⟨measurable_fst.fst.prodMk measurable_fst.snd.snd,hcomparison⟩
  have hb := ((MeasurePreserving.id ξ).prod (Measure.measurePreserving_swap (μ := γm) (ν := γm))).comp
    ((measurePreserving_prodAssoc ξ γm γm).comp
      ((hi.prod (centerComparison_preserving (d := d) M nodes)).comp hc))
  have hp := ((MeasurePreserving.id ξ).prod (raw_preserving L hL Bd)).comp
    ((measurePreserving_prodAssoc ξ (γm.prod γm) τs).comp (hb.prod (MeasurePreserving.id τs)))
  have hAE : (fun z => finalObservation M nodes anchors seeds main final sampling N r Ds hr hDs x P referencePosition hF hell hlo hup σ hσ hsmall δ t w base hfinalMass G
      (advanceHistory (MeanFinalBatchCoupling.batchCut M nodes anchors seeds main final sampling N r Ds hr hDs hfinalMass) z)) =ᵐ[ν.prod τs]
      (fun z => (benchmarkSeed M nodes anchors seeds main final sampling N r hr x P referencePosition hF hell hlo hup σ hσ hsmall base z.1.1.1,fun i => (z.1.1.2.2 (centerIndex M nodes i),(staticPi M nodes anchors seeds main final sampling N P z.1.1.1 i,z.2 i)))) := by
    filter_upwards [((measurePreserving_fst (μ := ν) (ν := τs)).quasiMeasurePreserving.ae hPi)] with z hz
    simp only [finalObservation,MeanFinalBatchCoupling.observation,advanceHistory,batchParts_append,finalCoarse,finalComparison]
    apply Prod.ext
    · rfl
    · apply funext
      intro i
      exact congrArg (fun p : Point d =>
        (z.1.1.2.2 (centerIndex M nodes i),(p,z.2 i))) (congrFun hz i).symm
  rw [advancedLaw,Measure.map_map
    (finalObservation_measurable M nodes anchors seeds main final sampling N r Ds hr hDs x P referencePosition hx hP hreference hF hell hlo hup σ hσ hsmall δ t w base hfinalMass G hG)
    (measurable_advanceHistory _)]
  change (ν.prod τs).map (fun z =>
    finalObservation M nodes anchors seeds main final sampling N r Ds hr hDs x P referencePosition hF hell hlo hup σ hσ hsmall δ t w base hfinalMass G
      (advanceHistory (MeanFinalBatchCoupling.batchCut M nodes anchors seeds main final sampling N r Ds hr hDs hfinalMass) z)) = _
  rw [Measure.map_congr hAE]
  change MeasurePreserving (fun z :
      (History (d := d) M nodes anchors seeds main final sampling N A ×
        Prefix d (MeanFinalBatchCoupling.batchCut M nodes anchors seeds main final sampling N r Ds hr hDs hfinalMass)) ×
      (∀ i,Tape d (DesignatedChildBatchCoupling.program Bd i)) =>
    (benchmarkSeed M nodes anchors seeds main final sampling N r hr x P referencePosition hF hell hlo hup σ hσ hsmall base z.1.1.1,
      fun i => (z.1.1.2.2 (centerIndex M nodes i),(staticPi M nodes anchors seeds main final sampling N P z.1.1.1 i,z.2 i)))) _ _ at hp
  exact hp.map_eq

variable (Jall : ∀ (k : ℕ) (hk : k<N),FreshChildBatchCoupling.Lower L
  (data M nodes anchors seeds main final sampling N r Ds hr hDs hmass (stage M nodes anchors seeds main final sampling N k hk.le).1 (stage_positive M nodes anchors seeds main final sampling N k hk)))

include hG in
/-- Full final source observation supplied by the constructed finite kernel.
The only source joint law is the incoming benchmark-seed/assembled-Pi law;
all final comparison, prefix and literal child-tape factors are proved. -/
theorem kernel_final_observation_laws
    (ha : 0<rowBound (m := m) r σ δ t w)
    (hA : ∀ i,∑ j,|M.matrix r σ (nodes i) (nodes j)|≤rowBound (m := m) r σ δ t w)
    (ρ : Measure (A × Tape d (Host M nodes anchors seeds main final sampling N))) [IsProbabilityMeasure ρ]
    (μ : Measure (Coarse (d := d) M nodes anchors seeds main final sampling N A)) [IsProbabilityMeasure μ]
    (hsplit : ρ.map (CausalTailHistory.unpack (MeanMainBatchCoupling.bodyCut M nodes anchors seeds main final sampling N))=
      μ.prod (tapeLaw L (body (a := a) (h := h) M nodes main final sampling N)))
    (hincoming : μ.map (incomingInventory M nodes anchors seeds main final sampling N r hr x P referencePosition hF hell hlo hup σ hσ hsmall base)=
      (MeanFlowLp.seedMeasure (MeanJointReference.data M hF hell hlo hup r σ hr hσ hsmall base)).prod (Measure.pi fun _ : Fin m => stdGaussian (Point d))) :
    ∃ (ν : Measure (History (d := d) M nodes anchors seeds main final sampling N A × Prefix d (MeanFinalBatchCoupling.batchCut M nodes anchors seeds main final sampling N r Ds hr hDs hfinalMass))),IsProbabilityMeasure ν ∧
      (kernel M nodes anchors seeds main final sampling N r Ds hr hDs hmass L hL x P referencePosition hx hP hreference hF hell hlo hup σ hσ hsmall δ t w Jall ∘ₘ ρ).map (CausalTailHistory.unpack (MeanFinalBatchCoupling.batchCut M nodes anchors seeds main final sampling N r Ds hr hDs hfinalMass))=
        ν.prod (tapeLaw L (.batch finalOrigin
          (DesignatedChildBatchCoupling.program (MeanFinalBatchCoupling.data M nodes anchors seeds main final sampling N r Ds hr hDs hfinalMass))
          (MeanFinalBatchCoupling.suffix M nodes anchors seeds main final sampling N))) ∧
      ν.map (fun z => (z.1.1,z.1.2.2))=μ.prod (Measure.pi fun _ : Fin n => stdGaussian (Point d)) ∧
      (advancedLaw L (MeanFinalBatchCoupling.batchCut M nodes anchors seeds main final sampling N r Ds hr hDs hfinalMass) ν).map (finalObservation M nodes anchors seeds main final sampling N r Ds hr hDs x P referencePosition hF hell hlo hup σ hσ hsmall δ t w base hfinalMass G)=
        (MeanFlowLp.seedMeasure (MeanJointReference.data M hF hell hlo hup r σ hr hσ hsmall base)).prod (Measure.pi (DesignatedChildBatchCoupling.rawLaw L
          (MeanFinalBatchCoupling.data M nodes anchors seeds main final sampling N r Ds hr hDs hfinalMass))) := by
  obtain ⟨ν,hν,hcut,hcomparison⟩ := MeanChronologicalFinalLaws.kernel_finalBatch_laws M nodes anchors seeds main final sampling N r Ds hr hDs hmass L hL x P referencePosition hx hP hreference hF hell hlo hup σ hσ hsmall δ t w Jall
    hfinalMass ha hA ρ μ hsplit
  let _ : IsProbabilityMeasure ν := hν
  refine ⟨ν,hν,hcut,hcomparison,?_⟩
  have hPi := prefix_staticPi_stored_ae M nodes anchors seeds main final sampling N r Ds hr hDs hmass L hL x P referencePosition hx hP hreference hF hell hlo hup σ hσ hsmall δ t w Jall hfinalMass G hG ρ ν hcut
  exact final_observation_law M nodes anchors seeds main final sampling N r Ds hr hDs L hL x P referencePosition hx hP hreference
    hF hell hlo hup σ hσ hsmall δ t w base hfinalMass G hG μ ν hincoming hcomparison hPi

end AcceleratedLogConcave.Oracle.MeanChronologicalFinalProjection
