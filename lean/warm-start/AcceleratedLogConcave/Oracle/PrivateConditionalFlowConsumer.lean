import AcceleratedLogConcave.Oracle.ConditionalSamplingFlowFields
import AcceleratedLogConcave.Oracle.PrivateSamplingFlowResidual
import AcceleratedLogConcave.Oracle.PrivateFirstOccurrenceConsumer
import AcceleratedLogConcave.Oracle.PrivateGeneralOccurrence

/-! Exact Phi/u specialization for the selected PRIVATE prefix.
General-k residual/seed projections remain Dotty's literal projection interface;
this module does not create or assume their factorization. -/
noncomputable section
set_option autoImplicit false
open Set MeasureTheory ProbabilityTheory
open scoped ContDiff
set_option backward.isDefEq.respectTransparency false
namespace AcceleratedLogConcave.Oracle.PrivateConditionalFlowConsumer
open Numerics Numerics.AffineGraph ConditionalSamplingFlowFields
open SourceExecutableTables PrivateSamplingExecutionSchedule
open TailOccurrenceCut TailOccurrenceCut.TailCut
variable {m n d : ℕ} (S : SamplingGeometry m) (e : Fin n ≃ S.Node)
variable {F : Point d → ℝ} (hF : ContDiff ℝ 2 F) {ell : ℝ} (hell : 0 ≤ ell)
  (hlo : ∀ z v, 0 ≤ fderiv ℝ (fderiv ℝ F) z v v)
  (hup : ∀ z v, fderiv ℝ (fderiv ℝ F) z v v ≤ ell*‖v‖^2)
  (x : Point d) {r : ℝ} (hr : 0 < r)

def nodePhi (i : Fin n) : Point d → Point d :=
  Phi hF hell hlo hup x hr S.samplingEnd_pos.le S.samplingEnd_lt_one
    (S.mesh.location m (e i))

def nodeReply (i : Fin n) : Point d → Point d :=
  reply hF hell hlo hup x hr S.samplingEnd_pos.le S.samplingEnd_lt_one
    (S.mesh.location m (e i))

theorem nodePhi_measurable (i : Fin n) : Measurable (nodePhi S e hF hell hlo hup x hr i) :=
  (Phi_continuous hF hell hlo hup x hr S.samplingEnd_pos.le S.samplingEnd_lt_one _).measurable

theorem nodeReply_measurable (i : Fin n) : Measurable (nodeReply S e hF hell hlo hup x hr i) :=
  (reply_continuous hF hell hlo hup x hr S.samplingEnd_pos.le S.samplingEnd_lt_one _).measurable

theorem nodePhi_eq_reference (Ds : ℝ) (main final : Fin n → ExecutableData) (N : ℕ)
    (i : Fin n) (omega : FullTape (d := d) S e r Ds main final N) :
    nodePhi S e hF hell hlo hup x hr i omega.2.1 =
      PrivateSamplingFlowResidual.reference S e r Ds main final N hF hell hlo hup x hr i omega := by
  have hi := S.mesh.location_mem_interval m (e i)
  exact Phi_eq_actual hF hell hlo hup x hr S.samplingEnd_pos.le S.samplingEnd_lt_one
    ⟨hi.1.le,hi.2.le⟩ omega.2.1

theorem nodeReply_eq_reply (Ds : ℝ) (main final : Fin n → ExecutableData) (N : ℕ)
    (i : Fin n) (omega : FullTape (d := d) S e r Ds main final N) :
    nodeReply S e hF hell hlo hup x hr i omega.2.1 =
      PrivateSamplingFlowResidual.reply S e r Ds main final N hF hell hlo hup x hr i omega := by
  have hi := S.mesh.location_mem_interval m (e i)
  rw [nodeReply, reply_eq_primitive hF hell hlo hup x hr S.samplingEnd_pos.le
    S.samplingEnd_lt_one ⟨hi.1.le,hi.2.le⟩]
  change Gibbs.primitiveMean F (nodePhi S e hF hell hlo hup x hr i omega.2.1)
    (S.radius r (e i)) = _
  rw [nodePhi_eq_reference S e hF hell hlo hup x hr Ds main final N i omega]
  rfl

/-- k=0 uses the literal setup Gaussian and initial residual projections already
constructed by Dotty; no arbitrary measurable Phi/u inputs remain. -/
theorem first_prefix_measurable (Ds : ℝ) (main final : Fin n → ExecutableData) (M : ℕ)
    (i : Fin n) :
    @Measurable (Prefix d (PrivateFirstOccurrenceConsumer.firstCut S e r Ds main final M))
      (Point d × (Point d × Point d))
      (prefixSpace d (PrivateFirstOccurrenceConsumer.firstCut S e r Ds main final M)) _
      (PrivateFirstOccurrenceConsumer.prefixW S e r Ds main final M x
        (nodePhi S e hF hell hlo hup x hr) (nodeReply S e hF hell hlo hup x hr) i) :=
  PrivateFirstOccurrenceConsumer.prefixW_measurable S e r Ds main final M x
    (nodePhi S e hF hell hlo hup x hr) (nodeReply S e hF hell hlo hup x hr) i
    (nodePhi_measurable S e hF hell hlo hup x hr i)
    (nodeReply_measurable S e hF hell hlo hup x hr i)

/-- For any fixed k<N the only remaining inputs are literal prefix projections:
setup seed and last-completed-layer residual. Their construction is not repeated
here, and no law or independence assumption is imposed on these maps. -/
theorem general_prefix_measurable (Ds : ℝ) (main final : Fin n → ExecutableData)
    (N k : ℕ) (hk : k<N) (G : Point d → Point d) (hG : Measurable G) (P : Point d)
    (seed : Prefix d (PrivateGeneralOccurrence.privateFocus S e r Ds main final N k hk).cut → Point d)
    (residual : Fin n → Prefix d (PrivateGeneralOccurrence.privateFocus S e r Ds main final N k hk).cut → Point d)
    (hseed : @Measurable _ _ (prefixSpace d (PrivateGeneralOccurrence.privateFocus S e r Ds main final N k hk).cut) _ seed)
    (hresidual : ∀ i, @Measurable _ _ (prefixSpace d (PrivateGeneralOccurrence.privateFocus S e r Ds main final N k hk).cut) _ (residual i))
    (i : Fin n) :
    @Measurable _ _ (prefixSpace d (PrivateGeneralOccurrence.privateFocus S e r Ds main final N k hk).cut) _
      (PrivateGeneralOccurrence.W S e r Ds main final N k hk G x P
        (fun j q => nodePhi S e hF hell hlo hup x hr j (seed q) + samplingNoise S r Ds • residual j q)
        (fun j q => nodeReply S e hF hell hlo hup x hr j (seed q)) i) := by
  let : MeasurableSpace (Prefix d (PrivateGeneralOccurrence.privateFocus S e r Ds main final N k hk).cut) :=
    prefixSpace d (PrivateGeneralOccurrence.privateFocus S e r Ds main final N k hk).cut
  apply PrivateGeneralOccurrence.W_measurable S e r Ds main final N k hk G hG x P
  · exact ((nodePhi_measurable S e hF hell hlo hup x hr i).comp hseed).add
      ((hresidual i).const_smul (samplingNoise S r Ds))
  · exact (nodeReply_measurable S e hF hell hlo hup x hr i).comp hseed

end AcceleratedLogConcave.Oracle.PrivateConditionalFlowConsumer
