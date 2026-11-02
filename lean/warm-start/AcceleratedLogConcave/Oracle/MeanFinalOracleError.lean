import AcceleratedLogConcave.Oracle.MeanFinalIntegratedError
import AcceleratedLogConcave.Oracle.DesignatedChildBatchBenchmarkError
import AcceleratedLogConcave.Oracle.MeanBenchmarkMoments

/-! Quantitative lower-child error payments with executed oracle independent
of the scaled analytic potential, on the actual retained full source
mean tape. Each active-final benchmark uses its original stored Pi and literal
transformed final tape. The true iterate center is not identified with that
benchmark. The scale moment is proved from the actual mean benchmark law. -/
noncomputable section
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
open MeasureTheory ProbabilityTheory
namespace AcceleratedLogConcave.Oracle.MeanFinalOracleError
open Numerics Numerics.AffineGraph Numerics.MeanFlowLp
open AffineLowering TapeLowering NoisyLayer SourceMeanExecutable
open TailOccurrenceCut TailCut CanonicalTapeLaw CanonicalTapeMeasurability PrivateCausalLayer
open MeanFinalBatchCoupling MeanBenchmarkMoments
variable {D m n a h : ℕ} (d : MeanFlowLp.Data (Fin D) m) (nodes : Fin n ≃ d.G.MeanNode)
  (anchors : Fin a ≃ d.G.Anchor) (seeds : Fin h ≃ Fin m × d.G.Kernel)
  (main : Fin n → ExecutableData) (final : Fin m → ExecutableData) (sampling : ExecutableData)
  (N : ℕ) (Ds : ℝ) (hDs : 0 < Ds)
  (hmass : ∀ i, CovarianceSetup.shiftSq (final i).shiftVector ≤ Ds^2)
local notation "B" => data d.G nodes anchors seeds main final sampling N d.r Ds d.hr hDs hmass
local notation "cut" => batchCut d.G nodes anchors seeds main final sampling N d.r Ds d.hr hDs hmass
local notation "host" => SourceMeanExecutable.program d.G nodes anchors seeds main final sampling N
local notation "width" => RecursiveMeanPublicTable.finalWidth d.G.R d.sigma
variable (G : Point D → Point D) (hG : Measurable G)
local notation "hc" => (finalCenter_measurable d)
local instance canonicalTapeSpace (D : ℕ) (p : Prog c Γ τ) :
  MeasurableSpace (Tape D p) := tapeSpace D p
local instance : MeasurableSpace (Prefix D cut) := prefixSpace D cut
local instance : MeasurableSpace (Prefix D (afterBatch cut)) := prefixSpace D (afterBatch cut)
variable {A : Type*} [MeasurableSpace A]
  (input : A → Inputs D (size (a := a) main final sampling))
  (hcoeff : ∀ j, Measurable (fun a => (input a).coefficient j))
  (hx : Measurable (fun a => (input a).center))
  (hP : Measurable (fun a => (input a).momentum))
  (L : PrimitiveLaws D) (hL : L.pointDraw = stdGaussian (Point D))
  (J : DesignatedChildBatchCoupling.Lower L
    (data d.G nodes anchors seeds main final sampling N d.r Ds d.hr hDs hmass))
  (coarse : A × Prefix D (batchCut d.G nodes anchors seeds main final sampling N d.r Ds d.hr hDs hmass) → Seed d)
  (hcoarse : Measurable coarse)
  (comparison : Fin m → A × Prefix D (batchCut d.G nodes anchors seeds main final sampling N d.r Ds d.hr hDs hmass) → Point D)
  (hcomparison : ∀ i, Measurable (comparison i))
local notation "obs" => observation d.G nodes anchors seeds main final sampling N d.r Ds d.hr hDs hmass
  G input coarse comparison
local notation "ho" => observation_measurable d.G nodes anchors seeds main final sampling N d.r Ds d.hr hDs hmass
  G hG input hcoeff hx hP coarse hcoarse comparison hcomparison
local notation "K" => kernel d.G nodes anchors seeds main final sampling N d.r Ds d.hr hDs hmass
  G hG input hcoeff hx hP L hL J coarse hcoarse (finalCenter d) hc comparison hcomparison

/-- Literal transformed source evaluation at the ideal final benchmark, on
the exact full original tape/reference sample retained by the causal kernel. -/
def error (i : Fin m) (z : (A × Tape D host) × (Fin m → Point D)) : Point D :=
  DesignatedChildBatchBenchmarkError.sourceError B (finalCenter d) obs i G (finalMean d i) width
    ((z.1.1,(split (afterBatch cut) z.1.2).1),z.2)

/-- Actual rR radius, literal finalWidth, exact original potential and precision
payment; the scalar factor multiplies a proved benchmark scale moment. -/
def payment (δ q t : ℝ) : ℝ :=
  width * Real.rpow δ (q-t) * Real.sqrt (finalScaleSquareBudget d)

/-- Integrated child error from the LOWER full-seed coupling. No current-call
accuracy or absolute output moment is required. Only the actual chronological
coarse/comparison/Pi projection is used, preserving the entire original sample. -/
theorem error_payment (δ q t : ℝ) (hδ : 0 < δ)
    (oldLaw : Measure (A × Tape D host))
    (μ : Measure (A × Prefix D cut)) [IsProbabilityMeasure μ]
    (hsplit : oldLaw.map (CausalTailHistory.unpack cut) = μ.prod
      (tapeLaw L (.batch finalOrigin (DesignatedChildBatchCoupling.program B)
        (suffix d.G nodes anchors seeds main final sampling N))))
    (hprojection : (advancedLaw L cut μ).map obs =
      (seedMeasure d).prod (Measure.pi (DesignatedChildBatchCoupling.rawLaw L B)))
    (i : Fin m)
    (hshift : ChildAbsorption.QueryShift (final i).program (final i).enumeration
      (final i).coefficient (d.r*d.G.R) (final i).shiftVector)
    (hfiber : ∀ᵐ s ∂seedMeasure d,
      MemLp (DesignatedChildRunShift.lowerError (final i).program G (final i).coefficient
        (finalCenter d i s) (finalMean d i s) width) 2 (J.joint i (finalCenter d i s)))
    (hbound : ∀ᵐ s ∂seedMeasure d,
      (∫ z, ‖DesignatedChildRunShift.lowerError (final i).program G (final i).coefficient
        (finalCenter d i s) (finalMean d i s) width z‖^2 ∂J.joint i (finalCenter d i s)) ≤
        (width * Real.rpow δ (q-t) * Gibbs.primitiveScale d.F (finalCenter d i s))^2) :
    ∃ herr : MemLp (error d nodes anchors seeds main final sampling N Ds hDs hmass G input coarse comparison i) 2
        (K ∘ₘ oldLaw),
      ‖herr.toLp (error d nodes anchors seeds main final sampling N Ds hDs hmass G input coarse comparison i)‖ ≤
        payment d δ q t ∧
      (∫ z, ‖error d nodes anchors seeds main final sampling N Ds hDs hmass G input coarse comparison i z‖^2
        ∂K ∘ₘ oldLaw) ≤ (width * Real.rpow δ (q-t))^2 * finalScaleSquareBudget d := by
  let f := width * Real.rpow δ (q-t)
  let err := DesignatedChildBatchErrorTransfer.lowerError B (finalCenter d) i G (finalMean d i) width
  have hmeas : StronglyMeasurable err :=
    DesignatedChildBatchErrorTransfer.lowerError_stronglyMeasurable B (finalCenter d) hc
      i G hG (finalMean d i) (finalMean_measurable d i) width
  have hcost : Integrable (fun s : Seed d => (f*nodeScale d (.center d.G i) s)^2) (seedMeasure d) := by
    simpa only [mul_pow] using (node_scale_square_integrable d (.center d.G i)).const_mul (f^2)
  have hp := DesignatedChildBatchErrorTransfer.averaged_error_memLp_of_bound L B J (finalCenter d) hc
    (seedMeasure d) i err hmeas hfiber (fun s => f*nodeScale d (.center d.G i) s) hcost hbound
  let : ∀ j, IsProbabilityMeasure (tapeLaw L (DesignatedChildBatchCoupling.program B j)) :=
    fun j => tapeLaw_probability L _
  let : IsProbabilityMeasure (advancedLaw L cut μ) := by unfold advancedLaw; infer_instance
  let E := DesignatedChildBatchBenchmarkError.sourceError B (finalCenter d) obs i G (finalMean d i) width
  have hE : MemLp E 2 (DesignatedChildBatchErrorTransfer.observedLaw L hL B J
      (finalCenter d) hc (advancedLaw L cut μ) obs ho) :=
    DesignatedChildBatchBenchmarkError.source_error_memLp B (finalCenter d) obs L hL J hc
      (advancedLaw L cut μ) (seedMeasure d) ho hprojection i G (finalMean d i) width hshift hp.1
  have hEsq := DesignatedChildBatchBenchmarkError.source_error_square_integral B (finalCenter d) obs L hL J hc
    (advancedLaw L cut μ) (seedMeasure d) ho hprojection i G (finalMean d i) width hshift hp.1
  have hwhole := whole_suffix d.G nodes anchors seeds main final sampling N d.r Ds d.hr hDs hmass
    G hG input hcoeff hx hP L hL J coarse hcoarse (finalCenter d) hc comparison hcomparison oldLaw μ hsplit
  have hfull := FreshChildBatchErrorTransfer.full_sample_error_memLp L (afterBatch cut)
    (K ∘ₘ oldLaw) _ hwhole E hE
  have hfullsq := FreshChildBatchErrorTransfer.full_sample_error_square_integral L (afterBatch cut)
    (K ∘ₘ oldLaw) _ hwhole E hE
  have hierr := (memLp_two_iff_integrable_sq_norm hp.1.aestronglyMeasurable).mp hp.1
  have hbase : (∫ z, ‖E z‖^2 ∂DesignatedChildBatchErrorTransfer.observedLaw L hL B J
      (finalCenter d) hc (advancedLaw L cut μ) obs ho) ≤ f^2*finalScaleSquareBudget d := by
    rw [hEsq]
    have hh := hp.2
    rw [Measure.integral_compProd hierr] at hh
    apply hh.trans
    simp_rw [mul_pow]
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left (final_scale_square_integral_le d i) (sq_nonneg f)
  have hs : (∫ z, ‖error d nodes anchors seeds main final sampling N Ds hDs hmass G input coarse comparison i z‖^2
      ∂K ∘ₘ oldLaw) ≤ f^2*finalScaleSquareBudget d := hfullsq.trans_le hbase
  refine ⟨hfull,?_,hs⟩
  have hwidth : 0 ≤ width := (RecursiveExecutableDomain.mean_final_width_pos d.G d.sigma d.hsigma).le
  have hf : 0 ≤ f := mul_nonneg hwidth (Real.rpow_nonneg hδ.le _)
  have hb : 0 ≤ finalScaleSquareBudget d := by
    unfold finalScaleSquareBudget positionSquareBudget
    positivity
  apply FreshChildBatchErrorTransfer.norm_toLp_le_of_square_integral (K ∘ₘ oldLaw) _ hfull
    (payment d δ q t) (mul_nonneg hf (Real.sqrt_nonneg _))
  simpa only [payment,f,error,E,mul_pow,Real.sq_sqrt hb] using hs

end AcceleratedLogConcave.Oracle.MeanFinalOracleError
