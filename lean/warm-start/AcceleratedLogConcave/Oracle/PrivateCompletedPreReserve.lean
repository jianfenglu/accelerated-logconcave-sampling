import AcceleratedLogConcave.Oracle.PrivateCompletedRms

/-! Remove the same literal final reserve from the already constructed
completed reference. Its pre-reserve law is proved from the full chronological
joint, rather than inferred from marginal Gaussian variances. -/
noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace AcceleratedLogConcave.Oracle.PrivateCompletedPreReserve
open Numerics Numerics.AffineGraph TapeLowering CanonicalTapeLaw CanonicalTapeMeasurability
open TailOccurrenceCut TailCut PrivateChronologicalCoupling PrivateCausalLayer
local instance canonicalTapeSpace {d c : ℕ} {Γ : Ctx} {τ : Ty} (p : Prog c Γ τ) :
    MeasurableSpace (Tape d p) := tapeSpace d p
variable {m n d : ℕ} (S : SamplingGeometry m) (e : Fin n ≃ S.Node)
  (r Ds : ℝ) (main final : Fin n → ExecutableData) (N : ℕ)
local notation "Host" => PrivateChronologicalCoupling.Host S e r Ds main final N
local notation "Seed" => (Point d × Tape d Host) × Point d
local notation "Completed" => (History d N n × Tape d Host) × (Fin n → Point d)

def reserve (ω : Tape d Host) : Point d :=
  PrivateSamplingTapeProjections.coordinates (SourceExecutableTables.samplingConfig main final N) ω
    (.inr (.inr (.inr ())))

theorem reserve_measurable : Measurable (reserve (d := d) S e r Ds main final N) := by
  change Measurable (fun ω : Tape d Host => (splitTape Host ω).1
    (PrivateSamplingTapeProjections.slot (SourceExecutableTables.samplingConfig main final N)
      (.inr (.inr (.inr ())))))
  exact (measurable_pi_apply _).comp (measurable_splitTape d Host).fst

/-- Full retained source and reference determine the pre-reserve reference
by removing the actual tape coordinate used by the interpreter. -/
def preReference (z : Seed) : Point d := z.2-(S.τ/2) • reserve S e r Ds main final N z.1.2

theorem preReference_measurable : Measurable (preReference (d := d) S e r Ds main final N) :=
  by
    unfold preReference
    exact measurable_snd.sub (((reserve_measurable S e r Ds main final N).comp measurable_fst.snd).const_smul (S.τ/2))

variable (hr : 0<r) (hDs : 0<Ds)
  (hmass : ∀ i, CovarianceSetup.shiftSq (main i).shiftVector≤Ds^2)
  (hfinalMass : ∀ i, CovarianceSetup.shiftSq (final i).shiftVector≤Ds^2)
  (L : PrimitiveLaws d) (hL : L.pointDraw=stdGaussian (Point d))
  {F : Point d → ℝ} (hF : ContDiff ℝ 2 F) {ell : ℝ} (hell : 0≤ell)
  (hlo : ∀ z w,0≤fderiv ℝ (fderiv ℝ F) z w w)
  (hup : ∀ z w,fderiv ℝ (fderiv ℝ F) z w w≤ell*‖w‖^2)
  (Jf : FreshChildBatchCoupling.Lower L
    (PrivateFinalCoupling.data S e r Ds main final N hr hDs hfinalMass
      (terminalCursor S e r Ds main final N).old))
  (J : ∀ k (hk : k<N), FreshChildBatchCoupling.Lower L
    (PrivateChronologicalCoupling.data S e r Ds main final N hr hDs hmass
      (stage S e r Ds main final N k hk.le).1 (stage_positive S e r Ds main final N k hk)))

private theorem observed_reserve (z : Completed) :
    reserve S e r Ds main final N z.1.2 =
      (PrivateCompletedLaws.finalObservation S e r Ds main final N z).2.2 := by
  rw [reserve,PrivateCompletedRms.reserve_coordinate_eq]
  simp only [PrivateCompletedLaws.finalObservation,CausalTailHistory.unpackExtended,
    CausalTailHistory.unpack,split_afterBatch]

private theorem initial_preserving (x : Point d) :
    MeasurePreserving (fun z : ((Point d × Point d) × Point d) => z.1.2)
      (PrivateChronologicalLaws.coarseLaw x) (stdGaussian (Point d)) :=
  (measurePreserving_snd (μ := Measure.dirac x) (ν := stdGaussian (Point d))).comp
    (measurePreserving_fst (μ := (Measure.dirac x).prod (stdGaussian (Point d)))
      (ν := stdGaussian (Point d)))

/-- Actual joint observation gives the pre-reserve affine reference law. -/
theorem observation_pre_law (hm : 0<m) (x : Point d) :
    (PrivateCompletedCoupling.kernel S e r Ds main final N hr hDs hmass hfinalMass L hL hF hell hlo hup Jf J x).map
      (fun z : Completed =>
        let u := PrivateCompletedLaws.finalObservation S e r Ds main final N z
        PrivateSamplingReferenceLaw.readout S hF hell hlo hup x hr u.1.1.1.2 +
          PrivateFinalGaussian.preNoise S e r (u.1.2,u.2.1)) =
      Channels.forward (Conditional.baseLaw F x r) ⟨3*S.τ^2/4,by positivity⟩ := by
  let γ := stdGaussian (Point d)
  let γn := Measure.pi (fun _ : Fin n => γ)
  have hj := PrivateCompletedLaws.kernel_final_joint S e r Ds main final N hr hDs hfinalMass
    L hL hF hell hlo hup Jf hmass J hm x
  have ho : Measurable (PrivateCompletedLaws.finalObservation (d := d) S e r Ds main final N) := by
    unfold PrivateCompletedLaws.finalObservation
    have h := CausalTailHistory.measurable_unpackExtended (d := d) (A := History d N n)
      (B := Fin n → Point d) L (afterBatch (terminalCut S e r Ds main final N))
    exact (h.fst.fst.fst.fst.prodMk h.fst.snd).prodMk (h.snd.fst.prodMk h.snd.snd.fst)
  have hobs : MeasurePreserving (PrivateCompletedLaws.finalObservation S e r Ds main final N) _ _ := ⟨ho,hj⟩
  have hparts := ((initial_preserving (d := d) x).prod (MeasurePreserving.id γn)).prod
    (measurePreserving_fst (μ := γ) (ν := γ))
  have hraw := (measurePreserving_prodAssoc γ γn γ).comp hparts
  have hnorm := ((MeasurePreserving.id γ).prod
    (PrivateReferenceAssembly.normalized_preNoise_preserving S e r hm hr)).comp (hraw.comp hobs)
  have hp := (PrivateSamplingReferenceLaw.pre_reference_preserving S hF hell hlo hup x hr).comp hnorm
  convert hp.map_eq using 1
  congr 1
  funext z
  dsimp only [Function.comp_apply,Prod.map,Prod.fst,Prod.snd,id_eq]
  rw [smul_smul,mul_inv_cancel₀ (ne_of_gt (div_pos (S.R_pos.trans_le S.R_le_τ) (by positivity))),one_smul]
  rfl

/-- The same full-source retained coupling supplies the exact pre-reserve
reference marginal. No independence is inferred from separate marginals. -/
theorem retained_preReference_law (hm : 0<m) (x : Point d) :
    (PrivateCompletedReference.retainedKernel S e r Ds main final N hr hDs hmass hfinalMass L hL hF hell hlo hup Jf J x).map
      (preReference S e r Ds main final N) =
      Channels.forward (Conditional.baseLaw F x r) ⟨3*S.τ^2/4,by positivity⟩ := by
  rw [PrivateCompletedReference.retainedKernel,Kernel.map_apply _
    (PrivateCompletedReference.retained_readout_measurable S e r Ds main final N hr L hF hell hlo hup),
    Measure.map_map (preReference_measurable S e r Ds main final N)
      (PrivateCompletedReference.retained_readout_measurable S e r Ds main final N hr L hF hell hlo hup)]
  rw [← observation_pre_law S e r Ds main final N hr hDs hmass hfinalMass L hL hF hell hlo hup Jf J hm x]
  apply Measure.map_congr
  filter_upwards [PrivateCompletedReference.stored_center_ae S e r Ds main final N hr hDs hmass hfinalMass L hL hF hell hlo hup Jf J x] with z hz
  dsimp only [Function.comp_apply,preReference]
  rw [hz]
  unfold PrivateCompletedReference.output PrivateReferenceAssembly.output
  dsimp only
  rw [← observed_reserve S e r Ds main final N z]
  module

end AcceleratedLogConcave.Oracle.PrivateCompletedPreReserve
