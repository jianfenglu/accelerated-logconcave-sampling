import AcceleratedLogConcave.Root.ClockFinalAssemblySupport
import AcceleratedLogConcave.Root.ClockChronologicalLaws

/-! Joint original split and Gaussian assembly at the actual final Clock
cut. The assembly reserve remains present alongside every designated Pi and
the full current comparison vector. -/
noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option quotPrecheck false
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set
open MeasureTheory.Measure
namespace AcceleratedLogConcave.Root.ClockFinalObservationLaw
open Oracle Oracle.AffineLowering Oracle.TapeLowering Oracle.NoisyLayer
open Oracle.CanonicalTapeLaw Oracle.CanonicalTapeMeasurability
open Oracle.TailOccurrenceCut Oracle.TailOccurrenceCut.TailCut Oracle.PrivateCausalLayer
open ClockChronologicalCoupling ClockNoisyLayer
local instance canonicalTapeSpace {d c : ℕ} {Γ : Ctx} {τ : Ty} (p : Prog c Γ τ) :
    MeasurableSpace (Tape d p) := tapeSpace d p
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



variable (P : SourceSchedule) (hR : P.R≤1/2) (hc : 0<P.csch) (hsmall : P.csch<1/160)
  (clock : ClockLaw.Clock) (label : ℕ) {d : ℕ}
local notation "γ" => stdGaussian (Point d)
local notation "γZ" => Measure.pi (fun _ : Index P => stdGaussian (Point d))

/-- The genuine coarse source datum plus the reserve and designated inputs
assembled from the originally recorded split draw and raw array. -/
def baseAssembly (b : Base P d) : ((Point d × Point d) × Point d) × (Index P → Point d) :=
  let H0 := ClockPublicSetup.splitValues b.1.2 b.2.1 1
  (((b.1.1,ClockPublicSetup.splitValues b.1.2 b.2.1 0),
      ClockRetainedFinalSplice.reserveValue P clock H0 b.2.2),
    ClockRetainedFinalSplice.activeValues P clock H0 b.2.2)

theorem baseAssembly_measurable : Measurable (baseAssembly (d := d) P clock) := by
  unfold baseAssembly ClockPublicSetup.splitValues ClockRetainedFinalSplice.reserveValue
    ClockRetainedFinalSplice.activeValues Conditional.GaussianAssembly.residual
    Conditional.GaussianAssembly.active Conditional.GaussianAssembly.noiseSum
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one]
  fun_prop

/-- Gaussian assembly is applied jointly after the original orthogonal split;
its reserve is not replaced by an independent sample. -/
theorem baseAssembly_preserving (μX : Measure (Point d)) [IsProbabilityMeasure μX] :
    MeasurePreserving (baseAssembly P clock)
      ((μX.prod γ).prod ((γ).prod γZ)) (((μX.prod γ).prod γ).prod γZ) := by
  let a := ClockRetainedFinalSplice.coefficient P clock
  have hs : MeasurePreserving (fun z : Point d × (Index P → Point d) =>
      (Conditional.GaussianAssembly.residual a z.1 z.2,
        Conditional.GaussianAssembly.active a z.1 z.2)) ((γ).prod γZ) ((γ).prod γZ) := by
    have hsplit : MeasurePreserving
        (fun z : Point d × (Index P → Point d) => fun i : Option (Index P) =>
          i.elim (Conditional.GaussianAssembly.residual a z.1 z.2)
            (Conditional.GaussianAssembly.active a z.1 z.2))
        ((γ).prod γZ) (Measure.pi fun _ : Option (Index P) => γ) := by
      refine ⟨?_,Conditional.GaussianAssembly.literal_split_joint_law
        (ClockRetainedFinalSplice.coefficient_admissible P clock)⟩
      apply Measurable.of_eval
      intro i
      cases i <;> dsimp [Conditional.GaussianAssembly.residual,
        Conditional.GaussianAssembly.active,Conditional.GaussianAssembly.noiseSum] <;> fun_prop
    exact (Conditional.MeanReferenceLayer.option_split (ι := Fin d) (J := Index P)).comp hsplit
  have h1 := (measurePreserving_prodAssoc (μX.prod γ) γ γZ).symm
  have hphase := Kinetic.phaseSplit_measurePreserving μX ClockPublicSetup.s ClockPublicSetup.noise
    Kinetic.source_split_coefficients
  change MeasurePreserving _ ((μX.prod γ).prod γ) ((μX.prod γ).prod γ) at hphase
  have h2 := hphase.prod (MeasurePreserving.id γZ)
  have h3 := measurePreserving_prodAssoc (μX.prod γ) γ γZ
  have h4 := (MeasurePreserving.id (μX.prod γ)).prod hs
  have h5 := (measurePreserving_prodAssoc (μX.prod γ) γ γZ).symm
  exact h5.comp (h4.comp (h3.comp (h2.comp h1)))

/-- Keep the reserve jointly with the full current and designated arrays. -/
def comparisonAssembly (z : Base P d × (Index P → Point d)) :
    ((Point d × Point d) × Point d) × ((Index P → Point d) × (Index P → Point d)) :=
  ((baseAssembly P clock z.1).1,(z.2,(baseAssembly P clock z.1).2))
theorem comparisonAssembly_measurable : Measurable (comparisonAssembly (d := d) P clock) :=
  ((baseAssembly_measurable P clock).comp measurable_fst).fst.prodMk
    (measurable_snd.prodMk ((baseAssembly_measurable P clock).comp measurable_fst).snd)

theorem comparisonAssembly_preserving (μX : Measure (Point d)) [IsProbabilityMeasure μX] :
    MeasurePreserving (comparisonAssembly P clock)
      (((μX.prod γ).prod ((γ).prod γZ)).prod γZ)
      (((μX.prod γ).prod γ).prod ((γZ).prod γZ)) := by
  have h1 := (baseAssembly_preserving P clock μX).prod (MeasurePreserving.id γZ)
  have h2 := measurePreserving_prodAssoc ((μX.prod γ).prod γ) γZ γZ
  have h3 := (MeasurePreserving.id ((μX.prod γ).prod γ)).prod
    (Measure.measurePreserving_swap (μ := γZ) (ν := γZ))
  exact h3.comp (h2.comp h1)

variable (hK : 10≤P.K) (hC : 8≤P.Csch) (hy : CubicScheduleThreshold.threshold P≤P.y)
  {V : Point d→ℝ} (hV : ContDiff ℝ 2 V)
  (hlo : ∀ z v,0≤fderiv ℝ (fderiv ℝ V) z v v)
  (hup : ∀ z v,fderiv ℝ (fderiv ℝ V) z v v≤‖v‖^2)
  (hyMean : MeanSourceScalarAbsorption.threshold P≤P.y)
local notation "host" => Host P hR hc hsmall clock label
local notation "batch" => ClockFinalBatchCoupling.data P hR hc hsmall clock label hK hC hy
local notation "cut" => ClockFinalBatchCoupling.batchCut P hR hc hsmall clock label hK hC hy
local notation "L" => Probability.CanonicalNativeTapeLaw.primitiveLaws d
local instance cutPrefixSpace : MeasurableSpace (Prefix d cut) := prefixSpace d cut
local instance afterPrefixSpace : MeasurableSpace (Prefix d (afterBatch cut)) := prefixSpace d (afterBatch cut)

private def finishCut (s : Cursor P hR hc hsmall clock label) (hs : s.remaining=0) :
    TailCut (ClockRetainedFinalSplice.finish P hR hc hsmall clock label s.old s.direct s.saved) host := by
  have h := s.cut
  rw [hs] at h
  exact h

private theorem finish_laws_of_zero (s : Cursor P hR hc hsmall clock label) (hs : s.remaining=0)
    (ρ : Measure (History P d × Tape d host)) (ν : Measure (Base P d))
    (h : let : MeasurableSpace (Prefix d s.cut) := prefixSpace d s.cut
      ∃ μ : Measure (History P d × Prefix d s.cut),IsProbabilityMeasure μ ∧
        ρ.map (CausalTailHistory.unpack s.cut)=μ.prod (tapeLaw L
          (Loop P hR hc hsmall clock label s.remaining s.old s.direct s.saved)) ∧
        μ.map (fun z => (z.1.1,z.1.2.2))=ν.prod γZ) :
    let : MeasurableSpace (Prefix d (finishCut P hR hc hsmall clock label s hs)) := prefixSpace d _
    ∃ μ : Measure (History P d × Prefix d (finishCut P hR hc hsmall clock label s hs)),IsProbabilityMeasure μ ∧
      ρ.map (CausalTailHistory.unpack (finishCut P hR hc hsmall clock label s hs))=
        μ.prod (tapeLaw L (ClockRetainedFinalSplice.finish P hR hc hsmall clock label s.old s.direct s.saved)) ∧
      μ.map (fun z => (z.1.1,z.1.2.2))=ν.prod γZ := by
  cases s with
  | mk remaining ctx old direct saved curCut =>
    cases remaining with
    | zero => exact h
    | succ remaining => change remaining+1=0 at hs; omega

/-- The actual completed main law at the literal designated-child cut. -/
theorem kernel_terminalCut_laws (μX : Measure (Point d)) [IsProbabilityMeasure μX] :
    ∃ μ : Measure (History P d × Prefix d cut),IsProbabilityMeasure μ ∧
      (ClockChronologicalCoupling.kernel P hR hc hsmall clock label hK hC hy hV hlo hup hyMean ∘ₘ
        ((μX.prod γ).prod (tapeLaw L host))).map (CausalTailHistory.unpack cut)=
        μ.prod (tapeLaw L (.batch [] (DesignatedChildBatchCoupling.program batch)
          (ClockFinalBatchCoupling.suffix P hR hc hsmall clock label))) ∧
      μ.map (fun z => (z.1.1,z.1.2.2))=((μX.prod γ).prod ((γ).prod γZ)).prod γZ := by
  exact finish_laws_of_zero P hR hc hsmall clock label
    (terminalCursor P hR hc hsmall clock label) (terminal_remaining P hR hc hsmall clock label) _ _
    (ClockChronologicalLaws.kernel_terminal_laws P hR hc hsmall clock label hK hC hy hV hlo hup hyMean (μX.prod γ))

/-- Actual stored Pi is the literal initial assembly on the reached prefix.
The support comes from the finite main kernel, for any original source law. -/
theorem prefix_designated_ae
    (source : Measure ((Point d × Point d) × Tape d host))
    (μ : Measure (History P d × Prefix d cut)) [SFinite μ]
    (hsplit : (ClockChronologicalCoupling.kernel P hR hc hsmall clock label hK hC hy hV hlo hup hyMean ∘ₘ source).map
      (CausalTailHistory.unpack cut)=μ.prod (tapeLaw L
        (.batch [] (DesignatedChildBatchCoupling.program batch)
          (ClockFinalBatchCoupling.suffix P hR hc hsmall clock label)))) :
    ∀ᵐ z ∂μ,(fun i => ClockFinalBatchCoupling.storedPi (V := V) P hR hc hsmall clock label hK hC hy i z)=
      (baseAssembly P clock z.1.1).2 := by
  let prefixReadout := fun z : History P d × Tape d host => (z.1,(split cut z.2).1)
  have hp : MeasurePreserving prefixReadout
      (ClockChronologicalCoupling.kernel P hR hc hsmall clock label hK hC hy hV hlo hup hyMean ∘ₘ source) μ :=
    ⟨(CausalTailHistory.measurable_unpack L cut).fst,
      ClockChronologicalLaws.prefixLaw_eq_of_split P hR hc hsmall clock label cut _ μ hsplit⟩
  have he : MeasurableSet {z : History P d × Prefix d cut |
      (fun i => ClockFinalBatchCoupling.storedPi (V := V) P hR hc hsmall clock label hK hC hy i z)=
        (baseAssembly P clock z.1.1).2} :=
    measurableSet_eq_fun (Measurable.of_eval fun i =>
      ClockFinalBatchCoupling.storedPi_measurable P hR hc hsmall clock label hK hC hy hV i)
      (((baseAssembly_measurable P clock).comp measurable_fst.fst).snd)
  rw [← hp.map_eq]
  apply (ae_map_iff hp.measurable.aemeasurable he).2
  filter_upwards [ClockFinalAssemblySupport.kernel_sourceBase_ae P hR hc hsmall clock label hK hC hy hV hlo hup hyMean source] with z hz
  funext i
  have he0 := congrArg (fun b : Base P d => b.2.1) hz
  have hraw := congrArg (fun b : Base P d => b.2.2) hz
  change z.1.1.2.1=ClockFinalAssemblyReadout.splitDraw P hR hc hsmall clock label z.2 at he0
  change z.1.1.2.2=ClockFinalAssemblyReadout.assemblyRaw P hR hc hsmall clock label z.2 at hraw
  have ht := ClockFinalAssemblyReadout.terminal_designated_assembled P hR hc hsmall clock label
    (gradient V) z.1.1.1.1 z.1.1.1.2 z.2 i
  change ClockFinalBatchCoupling.storedPi (V := V) P hR hc hsmall clock label hK hC hy i (prefixReadout z)=_ at ht
  change ClockFinalBatchCoupling.storedPi (V := V) P hR hc hsmall clock label hK hC hy i (prefixReadout z)=
    ClockRetainedFinalSplice.activeValues P clock
      (ClockPublicSetup.splitValues z.1.1.1.2 z.1.1.2.1 1) z.1.1.2.2 i
  rw [he0,hraw]
  exact ht

/-- The larger coarse datum keeps the actual comparison reserve. -/
def observation (z : History P d × Prefix d (afterBatch cut)) :
    ((Point d × Point d) × Point d) × (∀ i,DesignatedChildBatchCoupling.Raw d batch i) :=
  ((baseAssembly P clock z.1.1).1,
    (ClockFinalBatchCoupling.observation (V := V) P hR hc hsmall clock label hK hC hy z).2)

include hV in
theorem observation_measurable : Measurable (observation (V := V) P hR hc hsmall clock label hK hC hy) :=
  (((baseAssembly_measurable P clock).comp measurable_fst.fst).fst).prodMk
    (ClockFinalBatchCoupling.observation_measurable P hR hc hsmall clock label hK hC hy hV).snd

include hV in
/-- Appending the actual final child tapes gives the complete coarse/raw law,
including the same initial reserve and every actual stored Pi. -/
theorem final_observation_law (μX : Measure (Point d)) [IsProbabilityMeasure μX]
    (μ : Measure (History P d × Prefix d cut)) [IsProbabilityMeasure μ]
    (hcomparison : μ.map (fun z => (z.1.1,z.1.2.2))=((μX.prod γ).prod ((γ).prod γZ)).prod γZ)
    (hPi : ∀ᵐ z ∂μ,(fun i => ClockFinalBatchCoupling.storedPi (V := V) P hR hc hsmall clock label hK hC hy i z)=
      (baseAssembly P clock z.1.1).2) :
    (advancedLaw L cut μ).map (observation (V := V) P hR hc hsmall clock label hK hC hy)=
      ((μX.prod γ).prod γ).prod (Measure.pi (DesignatedChildBatchCoupling.rawLaw L batch)) := by
  let ξ := (μX.prod γ).prod γ
  let τs := Measure.pi fun i => tapeLaw L (DesignatedChildBatchCoupling.program batch i)
  let _ : ∀ i,IsProbabilityMeasure (tapeLaw L (DesignatedChildBatchCoupling.program batch i)) :=
    fun i => tapeLaw_probability L _
  let _ : IsProbabilityMeasure τs := by unfold τs; infer_instance
  have hcmp : MeasurePreserving (fun z : History P d × Prefix d cut => (z.1.1,z.1.2.2)) μ
      (((μX.prod γ).prod ((γ).prod γZ)).prod γZ) :=
    ⟨measurable_fst.fst.prodMk measurable_fst.snd.snd,hcomparison⟩
  have hb := (comparisonAssembly_preserving P clock μX).comp hcmp
  have hp := ((MeasurePreserving.id ξ).prod (raw_preserving L rfl batch)).comp
    ((measurePreserving_prodAssoc ξ ((γZ).prod γZ) τs).comp (hb.prod (MeasurePreserving.id τs)))
  have hAE : (fun z => observation (V := V) P hR hc hsmall clock label hK hC hy (advanceHistory cut z)) =ᵐ[μ.prod τs]
      (fun z => ((baseAssembly P clock z.1.1.1).1,
        fun i => (z.1.1.2.2 i,((baseAssembly P clock z.1.1.1).2 i,z.2 i)))) := by
    filter_upwards [((measurePreserving_fst (μ := μ) (ν := τs)).quasiMeasurePreserving.ae hPi)] with z hz
    simp only [observation,ClockFinalBatchCoupling.observation,advanceHistory,batchParts_append]
    apply Prod.ext
    · rfl
    · funext i
      exact congrArg (fun p : Point d => (z.1.1.2.2 i,(p,z.2 i))) (congrFun hz i)
  rw [advancedLaw,Measure.map_map
    (observation_measurable P hR hc hsmall clock label hK hC hy hV) (measurable_advanceHistory cut)]
  change (μ.prod τs).map (fun z => observation (V := V) P hR hc hsmall clock label hK hC hy (advanceHistory cut z)) = _
  rw [Measure.map_congr hAE]
  exact hp.map_eq

/-- The actual finite main kernel supplies all final observation laws.
There is no lower-kernel, stored-noise law, or accuracy premise. -/
theorem kernel_observation_laws (μX : Measure (Point d)) [IsProbabilityMeasure μX] :
    ∃ μ : Measure (History P d × Prefix d cut),IsProbabilityMeasure μ ∧
      (ClockChronologicalCoupling.kernel P hR hc hsmall clock label hK hC hy hV hlo hup hyMean ∘ₘ
        ((μX.prod γ).prod (tapeLaw L host))).map (CausalTailHistory.unpack cut)=
        μ.prod (tapeLaw L (.batch [] (DesignatedChildBatchCoupling.program batch)
          (ClockFinalBatchCoupling.suffix P hR hc hsmall clock label))) ∧
      (advancedLaw L cut μ).map (observation (V := V) P hR hc hsmall clock label hK hC hy)=
        ((μX.prod γ).prod γ).prod (Measure.pi (DesignatedChildBatchCoupling.rawLaw L batch)) := by
  obtain ⟨μ,hμ,hsplit,hcomparison⟩ := kernel_terminalCut_laws P hR hc hsmall clock label hK hC hy hV hlo hup hyMean μX
  let _ : IsProbabilityMeasure μ := hμ
  refine ⟨μ,hμ,hsplit,?_⟩
  exact final_observation_law P hR hc hsmall clock label hK hC hy hV μX μ hcomparison
    (prefix_designated_ae P hR hc hsmall clock label hK hC hy hV hlo hup hyMean _ μ hsplit)

end AcceleratedLogConcave.Root.ClockFinalObservationLaw
