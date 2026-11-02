import AcceleratedLogConcave.Oracle.MeanChronologicalFinalLaws

/-! Joint Gaussian comparison laws of the actual finite mean-main coupling.
The static coarse host retains incoming correlations and the original parent.
Only the complete unread tape is a fresh product factor. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace AcceleratedLogConcave.Oracle.MeanChronologicalFinalObservation
open Numerics Numerics.AffineGraph AffineLowering TapeLowering NoisyLayer
open RecursiveMeanProgram RecursiveMeanContinuation SourceMeanLayer SourceMeanExecutable
open TailOccurrenceCut TailCut CanonicalTapeLaw CanonicalTapeMeasurability
open PrivateCausalLayer PrivateCausalAdvance MeanChronologicalCoupling MeanChronologicalSupport
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



/-- Actual phase seed: retained private reference, actual assembly G0 and
literal flow seeds, with no originalP conditioning. -/
def benchmarkSeed (base : Point d) (c : Coarse (d := d) M nodes anchors seeds main final sampling N A) :
    MeanFlowLp.Seed (MeanJointReference.data M hF hell hlo hup r σ hr hσ hsmall base) :=
  MeanJointReference.seed M hF hell hlo hup r σ hr hσ hsmall base
    (MeanChronologicalHost.phaseInput M nodes anchors seeds main final sampling N x P referencePosition c).2

include hx hP hreference in
theorem benchmarkSeed_measurable (base : Point d) :
    Measurable (benchmarkSeed M nodes anchors seeds main final sampling N r hr x P referencePosition hF hell hlo hup σ hσ hsmall base) := by
  have hp := (MeanChronologicalHost.phaseInput_measurable M nodes anchors seeds main final sampling N x P referencePosition hx hP hreference).snd
  have hw : Measurable (fun z : MeanJointReference.Host (d := d) M => (WithLp.toLp 2 z.1,z.2)) :=
    ((WithLp.prod_continuous_toLp 2 (Point d) (Point d)).measurable.comp measurable_fst).prodMk measurable_snd
  exact hw.comp hp

def staticPi (c : Coarse (d := d) M nodes anchors seeds main final sampling N A) (i : Fin m) : Point d :=
  Conditional.GaussianAssembly.active (assembly M) (P c.1)
    (MeanChronologicalHost.raw M nodes anchors seeds main final sampling N c.2) i.succ

include hP in
theorem staticPi_measurable : Measurable (staticPi (d := d) M nodes anchors seeds main final sampling N P) := by
  have hp := (MeanChronologicalHost.raw_measurable (d := d) M nodes anchors seeds main final sampling N).comp
    (measurable_snd : Measurable (Prod.snd : Coarse (d := d) M nodes anchors seeds main final sampling N A → _))
  apply Measurable.of_eval
  intro i
  unfold staticPi Conditional.GaussianAssembly.active Conditional.GaussianAssembly.noiseSum
  fun_prop

def actualPi (z : A × Tape d (Host M nodes anchors seeds main final sampling N)) (i : Fin m) : Point d :=
  Conditional.GaussianAssembly.active (assembly M) (P z.1)
    (MeanAssemblyJointLaw.raw M nodes anchors seeds main final sampling N z.2) i.succ

include hP hL in
theorem actualPi_measurable : Measurable (actualPi (d := d) M nodes anchors seeds main final sampling N P) := by
  have hr := (MeanAssemblyJointLaw.raw_preserving M nodes anchors seeds main final sampling N L hL).measurable.comp
    (measurable_snd : Measurable (Prod.snd : A × Tape d (Host M nodes anchors seeds main final sampling N) → _))
  apply Measurable.of_eval
  intro i
  unfold actualPi Conditional.GaussianAssembly.active Conditional.GaussianAssembly.noiseSum
  fun_prop

variable (Jall : ∀ (k : ℕ) (hk : k<N),FreshChildBatchCoupling.Lower L
  (data M nodes anchors seeds main final sampling N r Ds hr hDs hmass (stage M nodes anchors seeds main final sampling N k hk.le).1 (stage_positive M nodes anchors seeds main final sampling N k hk)))

/-- The retained static Pi is the assembly of the SAME original source tape.
This is a support theorem of the constructed finite kernel. -/
theorem kernel_staticPi_actual_ae (ρ : Measure (A × Tape d (Host M nodes anchors seeds main final sampling N))) :
    ∀ᵐ z ∂kernel M nodes anchors seeds main final sampling N r Ds hr hDs hmass L hL x P referencePosition hx hP hreference hF hell hlo hup σ hσ hsmall δ t w Jall ∘ₘ ρ,staticPi M nodes anchors seeds main final sampling N P z.1.1=actualPi M nodes anchors seeds main final sampling N P (z.1.1.1,z.2) :=
  kernel_readout_ae M nodes anchors seeds main final sampling N r Ds hr hDs hmass L hL x P referencePosition hx hP hreference hF hell hlo hup σ hσ hsmall δ t w Jall (staticPi M nodes anchors seeds main final sampling N P) (staticPi_measurable M nodes anchors seeds main final sampling N P hP)
    (actualPi M nodes anchors seeds main final sampling N P) (actualPi_measurable M nodes anchors seeds main final sampling N L hL P hP) (fun _ => rfl) ρ

def centerIndex (i : Fin m) : Fin n := nodes.symm (.center M i)

theorem centerIndex_injective : Function.Injective (centerIndex M nodes) :=
  nodes.symm.injective.comp (MeanGeometry.MeanNode.center_injective M)

theorem centerComparison_preserving :
    MeasurePreserving (fun z : Fin n → Point d => fun i => z (centerIndex M nodes i))
      (Measure.pi fun _ : Fin n => stdGaussian (Point d))
      (Measure.pi fun _ : Fin m => stdGaussian (Point d)) :=
  ⟨by fun_prop,PrivateSamplingTapeProjections.pi_selection _ _ (centerIndex_injective M nodes)⟩



/-- The original public mean table and retained original input on history. -/
def sourceInput (v : History (d := d) M nodes anchors seeds main final sampling N A) : Inputs d (size (a := a) main final sampling) :=
  ⟨table M nodes anchors r σ Ds δ t w main final sampling,x v.1.1,P v.1.1⟩

variable (hfinalMass : ∀ i,CovarianceSetup.shiftSq (final i).shiftVector≤Ds^2)
  (G : Point d → Point d) (hG : Measurable G)

def finalCut := MeanFinalBatchCoupling.batchCut M nodes anchors seeds main final sampling N r Ds hr hDs hfinalMass
local instance : MeasurableSpace (Prefix d (finalCut M nodes anchors seeds main final sampling N r Ds hr hDs hfinalMass)) := prefixSpace d _
local instance : MeasurableSpace (Prefix d (afterBatch (finalCut M nodes anchors seeds main final sampling N r Ds hr hDs hfinalMass))) := prefixSpace d _

def storedPi (z : History (d := d) M nodes anchors seeds main final sampling N A × Prefix d (finalCut M nodes anchors seeds main final sampling N r Ds hr hDs hfinalMass))
    (i : Fin m) : Point d :=
  MeanFinalBatchCoupling.storedPi M nodes anchors seeds main final sampling N r Ds hr hDs hfinalMass G (sourceInput M nodes anchors seeds main final sampling N r Ds x P σ δ t w) i z

include hx hP hG in
theorem storedPi_measurable : Measurable (storedPi (d := d) M nodes anchors seeds main final sampling N r Ds hr hDs x P σ δ t w hfinalMass G) := by
  apply Measurable.of_eval
  intro i
  exact MeanFinalBatchCoupling.storedPi_measurable M nodes anchors seeds main final sampling N r Ds hr hDs hfinalMass G hG
    (sourceInput M nodes anchors seeds main final sampling N r Ds x P σ δ t w) (fun _ => measurable_const)
    (hx.comp measurable_fst.fst) (hP.comp measurable_fst.fst) i

/-- The original stored designated inputs at the canonical final cut equal
the retained incoming assembly, on the actual constructed mean kernel. -/
theorem kernel_staticPi_stored_ae (ρ : Measure (A × Tape d (Host M nodes anchors seeds main final sampling N))) :
    ∀ᵐ z ∂kernel M nodes anchors seeds main final sampling N r Ds hr hDs hmass L hL x P referencePosition hx hP hreference hF hell hlo hup σ hσ hsmall δ t w Jall ∘ₘ ρ,staticPi M nodes anchors seeds main final sampling N P z.1.1=
      storedPi M nodes anchors seeds main final sampling N r Ds hr hDs x P σ δ t w hfinalMass G (z.1,(split (finalCut M nodes anchors seeds main final sampling N r Ds hr hDs hfinalMass) z.2).1) := by
  filter_upwards [kernel_staticPi_actual_ae M nodes anchors seeds main final sampling N r Ds hr hDs hmass L hL x P referencePosition hx hP hreference hF hell hlo hup σ hσ hsmall δ t w Jall ρ] with z hz
  apply funext
  intro i
  have he := MeanFinalAssemblyReadout.final_designated_assembled M nodes anchors seeds main final sampling N G r σ Ds δ t w
    (x z.1.1.1) (P z.1.1.1) z.2 i
  change storedPi M nodes anchors seeds main final sampling N r Ds hr hDs x P σ δ t w hfinalMass G
    (z.1,(split (finalCut M nodes anchors seeds main final sampling N r Ds hr hDs hfinalMass) z.2).1) i=actualPi M nodes anchors seeds main final sampling N P (z.1.1.1,z.2) i at he
  exact (congrFun hz i).trans he.symm

include hG in
/-- Same-tape stored-Pi identification transferred to the actual reached
prefix law. It is not inferred from the coarse/current Gaussian marginal. -/
theorem prefix_staticPi_stored_ae
    (ρ : Measure (A × Tape d (Host M nodes anchors seeds main final sampling N)))
    (ν : Measure (History (d := d) M nodes anchors seeds main final sampling N A × Prefix d (finalCut M nodes anchors seeds main final sampling N r Ds hr hDs hfinalMass))) [SFinite ν]
    (hsplit : (kernel M nodes anchors seeds main final sampling N r Ds hr hDs hmass L hL x P referencePosition hx hP hreference hF hell hlo hup σ hσ hsmall δ t w Jall ∘ₘ ρ).map (CausalTailHistory.unpack (finalCut M nodes anchors seeds main final sampling N r Ds hr hDs hfinalMass))=
      ν.prod (tapeLaw L (.batch finalOrigin
        (DesignatedChildBatchCoupling.program (MeanFinalBatchCoupling.data M nodes anchors seeds main final sampling N r Ds hr hDs hfinalMass))
        (MeanFinalBatchCoupling.suffix M nodes anchors seeds main final sampling N)))) :
    ∀ᵐ z ∂ν,staticPi M nodes anchors seeds main final sampling N P z.1.1=storedPi M nodes anchors seeds main final sampling N r Ds hr hDs x P σ δ t w hfinalMass G z := by
  have hp := MeanChronologicalLaws.prefixLaw_eq_of_split M nodes anchors seeds main final sampling N L (finalCut M nodes anchors seeds main final sampling N r Ds hr hDs hfinalMass)
    (kernel M nodes anchors seeds main final sampling N r Ds hr hDs hmass L hL x P referencePosition hx hP hreference hF hell hlo hup σ hσ hsmall δ t w Jall ∘ₘ ρ) ν hsplit
  have hm : Measurable (fun z : History (d := d) M nodes anchors seeds main final sampling N A × Tape d (Host M nodes anchors seeds main final sampling N) =>
      (z.1,(split (finalCut M nodes anchors seeds main final sampling N r Ds hr hDs hfinalMass) z.2).1)) :=
    (CausalTailHistory.measurable_unpack L (finalCut M nodes anchors seeds main final sampling N r Ds hr hDs hfinalMass)).fst
  rw [← hp]
  apply (ae_map_iff hm.aemeasurable
    (measurableSet_eq_fun ((staticPi_measurable M nodes anchors seeds main final sampling N P hP).comp measurable_fst.fst)
      (storedPi_measurable M nodes anchors seeds main final sampling N r Ds hr hDs x P hx hP σ δ t w hfinalMass G hG))).2
  exact kernel_staticPi_stored_ae M nodes anchors seeds main final sampling N r Ds hr hDs hmass L hL x P referencePosition hx hP hreference hF hell hlo hup σ hσ hsmall δ t w Jall hfinalMass G ρ

end AcceleratedLogConcave.Oracle.MeanChronologicalFinalObservation
