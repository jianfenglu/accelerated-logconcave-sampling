import AcceleratedLogConcave.Oracle.PrivateSamplingExecutionSchedule
import AcceleratedLogConcave.Numerics.SamplingFlowLp

/-! Actual PRIVATE reference, initialization and residual. All identities use
original C2 convex/Hessian data. No residual estimate is assumed. The quantitative
cell derivative budget and Gaussian terminal benchmark error remain separate. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ContDiff
namespace AcceleratedLogConcave.Oracle.PrivateSamplingFlowResidual
open Numerics Numerics.AffineGraph SourceExecutableTables
open PrivateSamplingExecutionSchedule PrivateSamplingTapeProjections
open CanonicalTapeLaw CanonicalTapeMeasurability
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
variable {m n d : ℕ} (S : SamplingGeometry m) (e : Fin n ≃ S.Node)
  (r Ds : ℝ) (main final : Fin n → ExecutableData) (N : ℕ)
variable {F : Point d → ℝ} (hF : ContDiff ℝ 2 F) {ell : ℝ}
  (hell : 0 ≤ ell) (hlo : ∀ z v, 0 ≤ fderiv ℝ (fderiv ℝ F) z v v)
  (hup : ∀ z v, fderiv ℝ (fderiv ℝ F) z v v ≤ ell*‖v‖^2)
  (x : Point d) (hr : 0 < r)

/-- The original flow starts from the actual PRIVATE position occurrence. -/
def path (sample : FullTape (d := d) S e r Ds main final N) : ℝ → Point d :=
  Conditional.convexProbabilityFlow hF hell hlo hup x hr S.samplingEnd_pos.le
    (by norm_num) S.samplingEnd_lt_one ⟨0,le_rfl,S.samplingEnd_pos.le⟩ (show Point d from sample.2.1)

def reference (i : Fin n) (sample : FullTape (d := d) S e r Ds main final N) : Point d :=
  x + (r*S.mesh.location m (e i)) • path S e r Ds main final N hF hell hlo hup x hr sample
    (S.mesh.location m (e i))

def curve (sample : FullTape (d := d) S e r Ds main final N) (t : ℝ) : Point d :=
  AffineResidual.Sampling.meanCurve (Gibbs.primitiveMean F) x r
    (path S e r Ds main final N hF hell hlo hup x hr sample) t

def reply (i : Fin n) (sample : FullTape (d := d) S e r Ds main final N) : Point d :=
  Gibbs.primitiveMean F (reference S e r Ds main final N hF hell hlo hup x hr i sample)
    (S.radius r (e i))

theorem reply_eq_curve (i : Fin n) (sample : FullTape (d := d) S e r Ds main final N) :
    reply S e r Ds main final N hF hell hlo hup x hr i sample =
      curve S e r Ds main final N hF hell hlo hup x hr sample (S.mesh.location m (e i)) := rfl

/-- Literal hres identity: the node residual is the quadrature defect scaled
by r^2 times node time, not by any physical backwardEnd factor. -/
theorem residual_eq (i : Fin n) (sample : FullTape (d := d) S e r Ds main final N) :
    SharedLayerRms.residual
      (fun j sample => x + (r*S.mesh.location m (e j)) • (show Point d from sample.2.1))
      (samplingMatrix S e r)
      (reply S e r Ds main final N hF hell hlo hup x hr)
      (reference S e r Ds main final N hF hell hlo hup x hr) i sample =
    (r^2*S.mesh.location m (e i)) •
      ((∫ t in 0..S.mesh.location m (e i), curve S e r Ds main final N hF hell hlo hup x hr sample t) -
        ∑ j, S.row (S.mesh.location m (e i)) (e j) •
          reply S e r Ds main final N hF hell hlo hup x hr j sample) := by
  have hi := S.mesh.location_mem_interval m (e i)
  have hy := AffineFlowIdentities.sampling_source_flowEquation hF hell hlo hup x hr S (show Point d from sample.2.1)
    (S.mesh.location m (e i)) ⟨hi.1.le,hi.2.le⟩
  change path S e r Ds main final N hF hell hlo hup x hr sample (S.mesh.location m (e i)) =
    (show Point d from sample.2.1) - r • (∫ t in 0..S.mesh.location m (e i),
      curve S e r Ds main final N hF hell hlo hup x hr sample t) at hy
  have hsum : (∑ j, samplingMatrix S e r i j •
      reply S e r Ds main final N hF hell hlo hup x hr j sample) =
    (-(r*S.mesh.location m (e i))*r) •
      (∑ j, S.row (S.mesh.location m (e i)) (e j) •
        reply S e r Ds main final N hF hell hlo hup x hr j sample) := by
    simp only [samplingMatrix, Finset.smul_sum, smul_smul]
  simp only [SharedLayerRms.residual, reference, hsum, hy]
  module

/-- Literal initialization error after cancelling the same initial Gaussian.
This retains the nonzero initial primitive mean through the uncentered integral. -/
theorem initial_error_eq (i : Fin n) (sample : FullTape (d := d) S e r Ds main final N) :
    initial S e r Ds main final N x sample i -
      (reference S e r Ds main final N hF hell hlo hup x hr i sample +
        samplingNoise S r Ds •
          (show Point d from ((bodyTape S e r Ds main final N sample).1 i).1)) =
    (r^2*S.mesh.location m (e i)) •
      (∫ t in 0..S.mesh.location m (e i), curve S e r Ds main final N hF hell hlo hup x hr sample t) := by
  have hi := S.mesh.location_mem_interval m (e i)
  have hy := AffineFlowIdentities.sampling_source_flowEquation hF hell hlo hup x hr S (show Point d from sample.2.1)
    (S.mesh.location m (e i)) ⟨hi.1.le,hi.2.le⟩
  change path S e r Ds main final N hF hell hlo hup x hr sample (S.mesh.location m (e i)) =
    (show Point d from sample.2.1) - r • (∫ t in 0..S.mesh.location m (e i),
      curve S e r Ds main final N hF hell hlo hup x hr sample t) at hy
  simp only [initial,reference,hy]
  module

/-- The first Gaussian is a literal occurrence of the complete tape. -/
theorem position_preserving (L : PrimitiveLaws d)
    (hL : L.pointDraw = stdGaussian (Point d)) :
    let : MeasurableSpace (FullTape (d := d) S e r Ds main final N) := tapeSpace d _
    MeasurePreserving (fun sample : FullTape (d := d) S e r Ds main final N =>
      (show Point d from sample.2.1))
      (tapeLaw L (SamplingExecutable.build S e r Ds main final N).program)
      (stdGaussian (Point d)) := by
  let : MeasurableSpace (FullTape (d := d) S e r Ds main final N) := tapeSpace d _
  let cfg := samplingConfig main final N
  let : MeasurableSpace (Tape d (PrivateSamplingProgram.code cfg)) := tapeSpace d _
  have hc : Measurable (coordinates (d := d) cfg) :=
    measurable_pi_iff.mpr fun j => (measurable_pi_apply _).comp
      (measurable_splitTape d (PrivateSamplingProgram.code cfg)).fst
  have hp : MeasurePreserving (coordinates (d := d) cfg)
      (tapeLaw L (PrivateSamplingProgram.code cfg))
      (Measure.pi (fun _ : Index n => stdGaussian (Point d))) :=
    ⟨hc, by rw [map_coordinates, hL]⟩
  exact (measurePreserving_eval (fun _ : Index n => stdGaussian (Point d)) (.inl ())).comp hp

/-- The actual initial error is L2 from the original flow and actual seed law.
No desired initial-error membership is taken as an input. -/
theorem initial_error_memLp (L : PrimitiveLaws d)
    (hL : L.pointDraw = stdGaussian (Point d)) (i : Fin n) :
    let : MeasurableSpace (FullTape (d := d) S e r Ds main final N) := tapeSpace d _
    MemLp (fun sample : FullTape (d := d) S e r Ds main final N =>
      initial S e r Ds main final N x sample i -
        (reference S e r Ds main final N hF hell hlo hup x hr i sample +
          samplingNoise S r Ds •
            (show Point d from ((bodyTape S e r Ds main final N sample).1 i).1))) 2
      (tapeLaw L (SamplingExecutable.build S e r Ds main final N).program) := by
  let : MeasurableSpace (FullTape (d := d) S e r Ds main final N) := tapeSpace d _
  have hi := S.mesh.location_mem_interval m (e i)
  have hm := ((IsGaussian.memLp_two_id (μ := stdGaussian (Point d))).sub
    (SamplingFlowLp.samplingPath_memLp_two hF hell hlo hup x hr S.samplingEnd_pos.le
      S.samplingEnd_lt_one (S.mesh.location m (e i)))).const_smul
        (r*S.mesh.location m (e i))
  have hh := hm.comp_measurePreserving (position_preserving S e r Ds main final N L hL)
  convert hh using 1
  funext sample
  simp only [initial, reference, Function.comp_apply, Pi.smul_apply, Pi.sub_apply, id_eq]
  rw [SamplingFlowLp.sourcePath_eq hF hell hlo hup x hr S.samplingEnd_pos.le
    S.samplingEnd_lt_one ⟨hi.1.le,hi.2.le⟩ (show Point d from sample.2.1)]
  unfold path
  module


/-- Absolute primitive replies at the actual reference nodes are L2. The
constant primitiveMean F x r is retained, never silently centered away. -/
theorem reply_memLp (L : PrimitiveLaws d)
    (hL : L.pointDraw = stdGaussian (Point d)) (i : Fin n) :
    let : MeasurableSpace (FullTape (d := d) S e r Ds main final N) := tapeSpace d _
    MemLp (reply S e r Ds main final N hF hell hlo hup x hr i) 2
      (tapeLaw L (SamplingExecutable.build S e r Ds main final N).program) := by
  let : MeasurableSpace (FullTape (d := d) S e r Ds main final N) := tapeSpace d _
  have hi := S.mesh.location_mem_interval m (e i)
  have hm := (SamplingFlowLp.samplingCenteredReply_memLp_two hF hell hlo hup x hr
    S.samplingEnd_pos.le S.samplingEnd_lt_one (S.mesh.location m (e i))).add
      (memLp_const (Gibbs.primitiveMean F x r))
  have hh := hm.comp_measurePreserving (position_preserving S e r Ds main final N L hL)
  convert hh using 1
  funext sample
  simp only [Function.comp_apply, Pi.add_apply, SamplingFlowLp.centeredReply,
    SamplingFlowLp.sourceTime_eq S.samplingEnd_pos.le ⟨hi.1.le,hi.2.le⟩,
    SamplingFlowLp.sourcePath_eq hF hell hlo hup x hr S.samplingEnd_pos.le
      S.samplingEnd_lt_one ⟨hi.1.le,hi.2.le⟩,
    sub_add_cancel, reply, reference, path, SamplingGeometry.radius]

/-- Literal hres membership, discharged from original-data flow suppliers.
This does not assert a small quadrature-error budget. -/
theorem residual_memLp (L : PrimitiveLaws d)
    (hL : L.pointDraw = stdGaussian (Point d)) (i : Fin n) :
    let : MeasurableSpace (FullTape (d := d) S e r Ds main final N) := tapeSpace d _
    MemLp (SharedLayerRms.residual
      (fun j sample => x + (r*S.mesh.location m (e j)) • (show Point d from sample.2.1))
      (samplingMatrix S e r)
      (reply S e r Ds main final N hF hell hlo hup x hr)
      (reference S e r Ds main final N hF hell hlo hup x hr) i) 2
      (tapeLaw L (SamplingExecutable.build S e r Ds main final N).program) := by
  let : MeasurableSpace (FullTape (d := d) S e r Ds main final N) := tapeSpace d _
  have hinit := initial_error_memLp S e r Ds main final N hF hell hlo hup x hr L hL i
  have hs := memLp_finsetSum Finset.univ (fun j _ =>
    (reply_memLp S e r Ds main final N hF hell hlo hup x hr L hL j).const_smul
      (samplingMatrix S e r i j))
  apply (hinit.add hs).ae_eq
  filter_upwards with sample
  simp only [Pi.add_apply, Pi.smul_apply, SharedLayerRms.residual, initial]
  abel

end AcceleratedLogConcave.Oracle.PrivateSamplingFlowResidual
