import AcceleratedLogConcave.Oracle.MeanFinalBatchCoupling
import AcceleratedLogConcave.Oracle.DesignatedChildBatchJointTransfer

/-! Joint retained-Pi/reference law on the actual full source mean sample.
Only the correct coarse/raw projection is used for averaging; the complete
augmented past, original parent input, and original full tape remain retained. -/
noncomputable section
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open MeasureTheory ProbabilityTheory
namespace AcceleratedLogConcave.Oracle.MeanFinalBatchJointLaw
open Numerics.AffineGraph AffineLowering TapeLowering NoisyLayer SourceMeanExecutable
open TailOccurrenceCut TailCut CanonicalTapeLaw CanonicalTapeMeasurability PrivateCausalLayer
open MeanFinalBatchCoupling
variable {m n a h d : ℕ} (M : MeanGeometry m) (nodes : Fin n ≃ M.MeanNode)
  (anchors : Fin a ≃ M.Anchor) (seeds : Fin h ≃ Fin m × M.Kernel)
  (main : Fin n → ExecutableData) (final : Fin m → ExecutableData) (sampling : ExecutableData)
  (N : ℕ) (r Ds : ℝ) (hr : 0 < r) (hDs : 0 < Ds)
  (hmass : ∀ i, CovarianceSetup.shiftSq (final i).shiftVector ≤ Ds^2)
local notation "B" => data M nodes anchors seeds main final sampling N r Ds hr hDs hmass
local notation "cut" => batchCut M nodes anchors seeds main final sampling N r Ds hr hDs hmass
local notation "host" => SourceMeanExecutable.program M nodes anchors seeds main final sampling N
local instance canonicalTapeSpace (d : ℕ) (p : Prog c Γ τ) :
  MeasurableSpace (Tape d p) := tapeSpace d p
local instance : MeasurableSpace (Prefix d cut) := prefixSpace d cut
local instance : MeasurableSpace (Prefix d (afterBatch cut)) := prefixSpace d (afterBatch cut)
variable {A H : Type*} [MeasurableSpace A] [MeasurableSpace H]
  (G : Point d → Point d) (hG : Measurable G)
  (input : A → Inputs d (size (a := a) main final sampling))
  (hc : ∀ j, Measurable (fun a => (input a).coefficient j))
  (hx : Measurable (fun a => (input a).center))
  (hP : Measurable (fun a => (input a).momentum))
  (L : PrimitiveLaws d) (hL : L.pointDraw = stdGaussian (Point d))
  (J : DesignatedChildBatchCoupling.Lower L (data M nodes anchors seeds main final sampling N r Ds hr hDs hmass))
  (coarse : A × Prefix d (batchCut M nodes anchors seeds main final sampling N r Ds hr hDs hmass) → H)
  (hcoarse : Measurable coarse)
  (center : Fin m → H → Point d) (hcenter : ∀ i, Measurable (center i))
  (comparison : Fin m → A × Prefix d (batchCut M nodes anchors seeds main final sampling N r Ds hr hDs hmass) → Point d)
  (hcomparison : ∀ i, Measurable (comparison i))

/-- Concrete full-tape observation at the actual after-final-child cut. Pi
is read from the actual interpreter store via observation, not supplied. -/
def retainedPairs (z : (A × Tape d host) × (Fin m → Point d)) : H × (Fin m → Point d × Point d) :=
  let obs := observation M nodes anchors seeds main final sampling N r Ds hr hDs hmass G input
    coarse comparison (z.1.1,(split (afterBatch cut) z.1.2).1)
  (obs.1,fun i => ((obs.2 i).2.1,z.2 i))

/-- Exact final retained-pair kernel on the original full source sample.
The whole correction suffix law is derived from the cut, not assumed to
factor conditional on original P. The sole projected input law is the
chronological coarse/comparison/Pi inventory, as assembled and propagated. -/
theorem retained_pairs_law
    (oldLaw : Measure (A × Tape d host))
    (μ : Measure (A × Prefix d cut)) [IsProbabilityMeasure μ]
    (hsplit : oldLaw.map (CausalTailHistory.unpack cut) = μ.prod
      (tapeLaw L (.batch finalOrigin (DesignatedChildBatchCoupling.program B)
        (suffix M nodes anchors seeds main final sampling N))))
    (ν : Measure H) [IsProbabilityMeasure ν]
    (hprojection : (advancedLaw L cut μ).map
      (observation M nodes anchors seeds main final sampling N r Ds hr hDs hmass G input coarse comparison) =
        ν.prod (Measure.pi (DesignatedChildBatchCoupling.rawLaw L B))) :
    ((kernel M nodes anchors seeds main final sampling N r Ds hr hDs hmass
      G hG input hc hx hP L hL J coarse hcoarse center hcenter comparison hcomparison) ∘ₘ oldLaw).map
      (retainedPairs M nodes anchors seeds main final sampling N r Ds hr hDs hmass G input coarse comparison) =
      ν ⊗ₘ DesignatedChildBatchJointTransfer.averagedPairs L hL B J center hcenter := by
  let : ∀ i, IsProbabilityMeasure (tapeLaw L (DesignatedChildBatchCoupling.program B i)) :=
    fun i => tapeLaw_probability L _
  let : IsProbabilityMeasure (advancedLaw L cut μ) := by
    unfold advancedLaw
    infer_instance
  have hwhole := whole_suffix M nodes anchors seeds main final sampling N r Ds hr hDs hmass
    G hG input hc hx hP L hL J coarse hcoarse center hcenter comparison hcomparison oldLaw μ hsplit
  have hp := FreshChildBatchErrorTransfer.full_sample_projection_preserving L (afterBatch cut)
    _ _ hwhole
  let obs := observation M nodes anchors seeds main final sampling N r Ds hr hDs hmass
    G input coarse comparison
  have ho : Measurable obs := observation_measurable M nodes anchors seeds main final sampling N r Ds hr hDs hmass
    G hG input hc hx hP coarse hcoarse comparison hcomparison
  have hpair := DesignatedChildBatchJointTransfer.observed_coarse_pairs L hL B J center hcenter
    (advancedLaw L cut μ) ν obs ho hprojection
  have hm : Measurable (fun z : (A × Prefix d (afterBatch cut)) × (Fin m → Point d) =>
      ((obs z.1).1,fun i => (((obs z.1).2 i).2.1,z.2 i))) := by
    exact (ho.comp measurable_fst).fst.prodMk (Measurable.of_eval fun i =>
      (((measurable_pi_apply i).comp (ho.comp measurable_fst).snd).snd.fst.prodMk
        ((measurable_pi_apply i).comp measurable_snd)))
  have hfinal : MeasurePreserving
      (fun z : (A × Prefix d (afterBatch cut)) × (Fin m → Point d) =>
        ((obs z.1).1,fun i => (((obs z.1).2 i).2.1,z.2 i)))
      ((advancedLaw L cut μ) ⊗ₘ referenceConditional M nodes anchors seeds main final sampling N r Ds hr hDs hmass
        G hG input hc hx hP L hL J coarse hcoarse center hcenter comparison hcomparison)
      (ν ⊗ₘ DesignatedChildBatchJointTransfer.averagedPairs L hL B J center hcenter) :=
    ⟨hm,hpair⟩
  exact (hfinal.comp hp).map_eq

end AcceleratedLogConcave.Oracle.MeanFinalBatchJointLaw
