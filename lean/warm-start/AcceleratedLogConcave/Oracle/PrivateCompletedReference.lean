import AcceleratedLogConcave.Oracle.PrivateCompletedLaws

/-! Actual completed private reference readout, including its joint law with
original parent momentum. All Gaussian factors come from the constructed
chronological kernel and the literal unread suffix. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option quotPrecheck false
open MeasureTheory ProbabilityTheory
namespace AcceleratedLogConcave.Oracle.PrivateCompletedReference
open Numerics Numerics.AffineGraph TapeLowering CanonicalTapeLaw CanonicalTapeMeasurability
open TailOccurrenceCut TailCut PrivateChronologicalCoupling PrivateCausalLayer
local instance canonicalTapeSpace {d c : ℕ} {Γ : Ctx} {τ : Ty} (p : Prog c Γ τ) :
    MeasurableSpace (Tape d p) := tapeSpace d p
variable {m n d : ℕ} (S : SamplingGeometry m) (e : Fin n ≃ S.Node)
  (r Ds : ℝ) (main final : Fin n → ExecutableData) (N : ℕ)
  (hr : 0 < r) (hDs : 0 < Ds)
  (hmass : ∀ i, CovarianceSetup.shiftSq (main i).shiftVector ≤ Ds^2)
  (hfinalMass : ∀ i, CovarianceSetup.shiftSq (final i).shiftVector ≤ Ds^2)
  (L : PrimitiveLaws d) (hL : L.pointDraw = stdGaussian (Point d))
  {F : Point d → ℝ} (hF : ContDiff ℝ 2 F) {ell : ℝ} (hell : 0 ≤ ell)
  (hlo : ∀ z v, 0 ≤ fderiv ℝ (fderiv ℝ F) z v v)
  (hup : ∀ z v, fderiv ℝ (fderiv ℝ F) z v v ≤ ell*‖v‖^2)
  (Jf : FreshChildBatchCoupling.Lower L
    (PrivateFinalCoupling.data S e r Ds main final N hr hDs hfinalMass
      (terminalCursor S e r Ds main final N).old))
  (J : ∀ (k : ℕ) (hk : k<N), FreshChildBatchCoupling.Lower L
    (PrivateChronologicalCoupling.data S e r Ds main final N hr hDs hmass
      (stage S e r Ds main final N k hk.le).1
      (stage_positive S e r Ds main final N k hk)))

private theorem rearrange (x : Point d) :
    MeasurePreserving (fun z : ((((Point d × Point d) × Point d) × (Fin n → Point d)) ×
      (Point d × Point d)) =>
      (z.1.1.2,((z.1.1.1.2,(z.1.2,z.2.1)),z.2.2)))
      (((PrivateChronologicalLaws.coarseLaw x).prod
        (Measure.pi fun _ : Fin n => stdGaussian (Point d))).prod
          ((stdGaussian (Point d)).prod (stdGaussian (Point d))))
      ((stdGaussian (Point d)).prod
        (((stdGaussian (Point d)).prod
          ((Measure.pi fun _ : Fin n => stdGaussian (Point d)).prod (stdGaussian (Point d)))).prod
          (stdGaussian (Point d)))) := by
  let γ := stdGaussian (Point d)
  let γn := Measure.pi fun _ : Fin n => γ
  have hcoarse := (Measure.measurePreserving_swap (μ := γ) (ν := γ)).comp
    ((measurePreserving_snd (μ := Measure.dirac x) (ν := γ)).prod (MeasurePreserving.id γ))
  have hfirst := (hcoarse.prod (MeasurePreserving.id γn)).prod
    (MeasurePreserving.id (γ.prod γ))
  have ha := ((measurePreserving_prodAssoc γ γ γn).prod
    (MeasurePreserving.id (γ.prod γ))).comp hfirst
  have hb := (measurePreserving_prodAssoc γ (γ.prod γn) (γ.prod γ)).comp ha
  have hc := ((measurePreserving_prodAssoc γ γn γ).prod (MeasurePreserving.id γ)).comp
    (measurePreserving_prodAssoc (γ.prod γn) γ γ).symm
  exact ((MeasurePreserving.id γ).prod hc).comp hb

/-- Joint center/seed measurability of the literal Gaussian-start endpoint. -/
theorem readout_joint_continuous : Continuous (fun z : Point d × Point d =>
    PrivateSamplingReferenceLaw.readout S hF hell hlo hup z.1 hr z.2) := by
  have hj : Continuous (fun z : Point d × Point d => (samplingEnd S.τ)⁻¹ •
      (ConditionalSmoothing.jointPath (flowData S hF hell hlo hup hr) (samplingEnd S.τ) z).2) :=
    ((ConditionalSmoothing.continuous_jointPath (flowData S hF hell hlo hup hr)).comp
    (continuous_const.prodMk continuous_id)).snd.const_smul ((samplingEnd S.τ)⁻¹)
  convert hj using 1
  funext z
  rw [ConditionalSmoothing.jointPath_snd_eq_source _ z.1 z.2
    (show samplingEnd S.τ ∈ Set.Icc 0 (flowData S hF hell hlo hup hr).b from
      ⟨S.samplingEnd_pos.le,le_rfl⟩)]
  simp only [PrivateSamplingReferenceLaw.readout, SamplingCenterLp.path,
    SamplingFlowLp.sourcePath, flowData, SamplingFlowLp.sourceTime_eq S.samplingEnd_pos.le
      (show samplingEnd S.τ ∈ Set.Icc 0 (samplingEnd S.τ) from ⟨S.samplingEnd_pos.le,le_rfl⟩)]

/-- Exact affine reference readout on the actual augmented full execution. -/
def output (x : Point d)
    (z : ((History d N n × Tape d (Host S e r Ds main final N)) × (Fin n → Point d))) : Point d :=
  let u := PrivateCompletedLaws.finalObservation S e r Ds main final N z
  PrivateReferenceAssembly.output S e r hr hF hell hlo hup x
    ((u.1.1.1.2,(u.1.2,u.2.1)),u.2.2)

/-- The completed actual augmentation has the required private reference
law jointly with original P. This does not assert that its executed output
is independent of P or has this law. -/
theorem original_reference_law (hm : 0<m) (x : Point d) :
    (PrivateCompletedCoupling.kernel S e r Ds main final N hr hDs hmass hfinalMass
      L hL hF hell hlo hup Jf J x).map
      (fun z => (z.1.1.1.2,output S e r Ds main final N hr hF hell hlo hup x z)) =
      (stdGaussian (Point d)).prod
        (Channels.forward (Conditional.baseLaw F x r) ⟨S.τ^2,by positivity⟩) := by
  have hj := PrivateCompletedLaws.kernel_final_joint S e r Ds main final N hr hDs hfinalMass
    L hL hF hell hlo hup Jf hmass J hm x
  have hmobs : Measurable (PrivateCompletedLaws.finalObservation (d := d) S e r Ds main final N) := by
    unfold PrivateCompletedLaws.finalObservation
    have h := CausalTailHistory.measurable_unpackExtended (d := d) (A := History d N n)
      (B := Fin n → Point d) L (afterBatch (terminalCut S e r Ds main final N))
    exact (h.fst.fst.fst.fst.prodMk h.fst.snd).prodMk (h.snd.fst.prodMk h.snd.snd.fst)
  have hp := (rearrange (n := n) x).comp (show MeasurePreserving
    (PrivateCompletedLaws.finalObservation S e r Ds main final N) _ _ from ⟨hmobs,hj⟩)
  have hout := ((MeasurePreserving.id (stdGaussian (Point d))).prod
    (PrivateReferenceAssembly.output_preserving S e r hm hr hF hell hlo hup x)).comp hp
  exact hout.map_eq


local notation "Completed" => ((History d N n × Tape d (Host S e r Ds main final N)) × (Fin n → Point d))

include L in
private theorem observation_measurable :
    Measurable (PrivateCompletedLaws.finalObservation (d := d) S e r Ds main final N) := by
  unfold PrivateCompletedLaws.finalObservation
  have h := CausalTailHistory.measurable_unpackExtended (d := d) (A := History d N n)
    (B := Fin n → Point d) L (afterBatch (terminalCut S e r Ds main final N))
  exact (h.fst.fst.fst.fst.prodMk h.fst.snd).prodMk (h.snd.fst.prodMk h.snd.snd.fst)

include L in
theorem output_joint_measurable : Measurable (fun z : Point d × Completed =>
    output S e r Ds main final N hr hF hell hlo hup z.1 z.2) := by
  have ho := (observation_measurable S e r Ds main final N L).comp
    (show Measurable (Prod.snd : Point d × Completed → Completed) from measurable_snd)
  have hread := (readout_joint_continuous S r hr hF hell hlo hup).measurable.comp
    (measurable_fst.prodMk ho.fst.fst.fst.snd)
  have hnoise : Measurable (PrivateFinalGaussian.preNoise (d := d) S e r) := by
    unfold PrivateFinalGaussian.preNoise
    fun_prop
  exact (hread.add (hnoise.comp (ho.fst.snd.prodMk ho.snd.fst))).add
    (ho.snd.snd.const_smul (S.τ/2))

/-- Actual complete source seed coupled with the literal completed reference
row; center dependence is measurable, not a separately chosen disintegration. -/
def retainedKernel : Kernel (Point d)
    ((Point d × Tape d (Host S e r Ds main final N)) × Point d) :=
  (PrivateCompletedCoupling.kernel S e r Ds main final N hr hDs hmass hfinalMass
    L hL hF hell hlo hup Jf J).map (fun z =>
      ((z.1.1.1.2,z.1.2),output S e r Ds main final N hr hF hell hlo hup z.1.1.1.1.1 z))

include L in
theorem retained_readout_measurable : Measurable (fun z : Completed =>
    ((z.1.1.1.2,z.1.2),output S e r Ds main final N hr hF hell hlo hup z.1.1.1.1.1 z)) := by
  have ho := observation_measurable S e r Ds main final N L
  have hx : Measurable (fun z : Completed => z.1.1.1.1.1) := measurable_fst.fst.fst.fst.fst
  have hread := (readout_joint_continuous S r hr hF hell hlo hup).measurable.comp
    (hx.prodMk ho.fst.fst.fst.snd)
  have hnoise : Measurable (PrivateFinalGaussian.preNoise (d := d) S e r) := by
    unfold PrivateFinalGaussian.preNoise
    fun_prop
  have hout := (hread.add (hnoise.comp (ho.fst.snd.prodMk ho.snd.fst))).add
    (ho.snd.snd.const_smul (S.τ/2))
  exact (measurable_fst.fst.fst.snd.prodMk measurable_fst.snd).prodMk hout

instance retainedKernel_markov : IsMarkovKernel
    (retainedKernel S e r Ds main final N hr hDs hmass hfinalMass L hL hF hell hlo hup Jf J) := by
  unfold retainedKernel
  exact Kernel.IsMarkovKernel.map _ (retained_readout_measurable S e r Ds main final N hr L hF hell hlo hup)

theorem stored_center_ae (x : Point d) :
    ∀ᵐ z ∂PrivateCompletedCoupling.kernel S e r Ds main final N hr hDs hmass hfinalMass
      L hL hF hell hlo hup Jf J x, z.1.1.1.1.1=x := by
  have hm := (original_measurable (d := d) S e r Ds main final N).comp
    (show Measurable (Prod.fst : Completed → _) from measurable_fst)
  have hp := PrivateCompletedCoupling.kernel_original S e r Ds main final N hr hDs hmass hfinalMass
    L hL hF hell hlo hup Jf J x
  have hset : MeasurableSet {w : (Point d × Point d) × Tape d (Host S e r Ds main final N) |
      w.1.1=x} := measurableSet_eq_fun measurable_fst.fst measurable_const
  apply (ae_map_iff hm.aemeasurable hset).1
  change ∀ᵐ y ∂Measure.map (fun z : Completed => original S e r Ds main final N z.1) _, y.1.1=x
  rw [hp]
  have hsrc : Measurable (fun z : Point d × Tape d (Host S e r Ds main final N) => ((x,z.1),z.2)) := by fun_prop
  apply (ae_map_iff hsrc.aemeasurable hset).2
  exact Filter.Eventually.of_forall fun _ => rfl


/-- Exact full canonical seed marginal, including all uniforms and residual
coordinates. The reference readout never replaces the original source. -/
theorem retainedKernel_source (x : Point d) :
    (retainedKernel S e r Ds main final N hr hDs hmass hfinalMass L hL hF hell hlo hup Jf J x).map
      Prod.fst = FreshChildRetainedCoupling.sourceLaw L (Host S e r Ds main final N) := by
  rw [retainedKernel,Kernel.map_apply _
    (retained_readout_measurable S e r Ds main final N hr L hF hell hlo hup),
    Measure.map_map measurable_fst (retained_readout_measurable S e r Ds main final N hr L hF hell hlo hup)]
  have hp := congrArg (fun μ => μ.map (fun z : (Point d × Point d) × Tape d (Host S e r Ds main final N) =>
    (z.1.2,z.2))) (PrivateCompletedCoupling.kernel_original S e r Ds main final N hr hDs hmass hfinalMass
      L hL hF hell hlo hup Jf J x)
  have horg : Measurable (fun z : Completed => original S e r Ds main final N z.1) :=
    (original_measurable S e r Ds main final N).comp measurable_fst
  rw [Measure.map_map (by fun_prop) horg,
    Measure.map_map (by fun_prop) (by fun_prop)] at hp
  simpa only [Function.comp_def,original,Prod.mk.eta,Measure.map_id'] using hp

/-- The exact lower-coupling contract on retained original P and reference
output, derived from the completed execution rather than assumed. -/
theorem retainedKernel_reference (hm : 0<m) (x : Point d) :
    (retainedKernel S e r Ds main final N hr hDs hmass hfinalMass L hL hF hell hlo hup Jf J x).map
      (fun z => (z.1.1,z.2)) =
      (stdGaussian (Point d)).prod
        (Channels.forward (Conditional.baseLaw F x r) ⟨S.τ^2,by positivity⟩) := by
  rw [retainedKernel,Kernel.map_apply _
    (retained_readout_measurable S e r Ds main final N hr L hF hell hlo hup),
    Measure.map_map (by fun_prop) (retained_readout_measurable S e r Ds main final N hr L hF hell hlo hup)]
  calc
    _ = (PrivateCompletedCoupling.kernel S e r Ds main final N hr hDs hmass hfinalMass
        L hL hF hell hlo hup Jf J x).map
        (fun z => (z.1.1.1.2,output S e r Ds main final N hr hF hell hlo hup x z)) := by
      apply Measure.map_congr
      filter_upwards [stored_center_ae S e r Ds main final N hr hDs hmass hfinalMass
        L hL hF hell hlo hup Jf J x] with z hz
      change (z.1.1.1.2,output S e r Ds main final N hr hF hell hlo hup z.1.1.1.1.1 z) = _
      rw [hz]
    _ = _ := original_reference_law S e r Ds main final N hr hDs hmass hfinalMass
      L hL hF hell hlo hup Jf J hm x


theorem retainedKernel_fst :
    (retainedKernel S e r Ds main final N hr hDs hmass hfinalMass L hL hF hell hlo hup Jf J).fst =
      Kernel.const (Point d) (FreshChildRetainedCoupling.sourceLaw L (Host S e r Ds main final N)) := by
  ext x : 1
  exact retainedKernel_source S e r Ds main final N hr hDs hmass hfinalMass
    L hL hF hell hlo hup Jf J x

end AcceleratedLogConcave.Oracle.PrivateCompletedReference
