import AcceleratedLogConcave.Kinetic.Corrector
import AcceleratedLogConcave.Kinetic.ReferenceChannel

/-!
# Corrector energy across an actual position-preserving collision

The channel is constructed from its actual coupling and marginals. Position
retention is a property of the two coordinate maps. The sole corrector estimate
assumed below is the explicit dormant W12 operator bound.
-/
noncomputable section
open MeasureTheory InnerProductSpace
open scoped ContDiff RealInnerProductSpace
namespace AcceleratedLogConcave.Kinetic.ConditionalContraction
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable (μ : Measure E) [IsProbabilityMeasure μ]
variable {Ω : Type*} [MeasurableSpace Ω] {η : Measure Ω}
  {p q : Ω → GaussianPhase E}
  (hp : MeasurePreserving p η (gaussianPhaseMeasure μ))
  (hq : MeasurePreserving q η (gaussianPhaseMeasure μ))
  (hpos : ∀ w, (p w).1.1 = (q w).1.1)
include hpos

omit [BorelSpace E] [IsProbabilityMeasure μ] in
private theorem position_pullbacks_eq (g : Lp ℝ 2 μ) :
    Lp.compMeasurePreservingₗᵢ ℝ q hq (positionEmbedding μ g) =
      Lp.compMeasurePreservingₗᵢ ℝ p hp (positionEmbedding μ g) := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_compMeasurePreserving (positionEmbedding μ g) hq,
    Lp.coeFn_compMeasurePreserving (positionEmbedding μ g) hp,
    hq.quasiMeasurePreserving.ae (positionEmbedding_coe μ g),
    hp.quasiMeasurePreserving.ae (positionEmbedding_coe μ g)] with w hqg hpg hqv hpv
  change Lp.compMeasurePreserving q hq (positionEmbedding μ g) w =
    Lp.compMeasurePreserving p hp (positionEmbedding μ g) w
  rw [hqg, hpg]
  change positionEmbedding μ g (q w) = positionEmbedding μ g (p w)
  rw [hqv, hpv, hpos]

omit [BorelSpace E] [IsProbabilityMeasure μ] in
/-- Geometric retention of position fixes every position observable. -/
theorem positionChannel_positionEmbedding (g : Lp ℝ 2 μ) :
    referenceChannel hp hq (positionEmbedding μ g) = positionEmbedding μ g := by
  unfold referenceChannel
  rw [ContinuousLinearMap.comp_apply]
  change (Lp.compMeasurePreservingₗᵢ ℝ p hp).toContinuousLinearMap.adjoint
    (Lp.compMeasurePreservingₗᵢ ℝ q hq (positionEmbedding μ g)) = _
  rw [position_pullbacks_eq μ hp hq hpos g]
  apply ext_inner_left ℝ
  intro f
  rw [ContinuousLinearMap.adjoint_inner_right]
  exact (Lp.compMeasurePreservingₗᵢ ℝ p hp).inner_map_map f (positionEmbedding μ g)

omit [BorelSpace E] [IsProbabilityMeasure μ] in
/-- The density adjoint fixes every position observable as well. -/
theorem positionChannel_adjoint_positionEmbedding (g : Lp ℝ 2 μ) :
    (referenceChannel hp hq).adjoint (positionEmbedding μ g) = positionEmbedding μ g := by
  rw [referenceChannel_adjoint]
  exact positionChannel_positionEmbedding μ hq hp (fun w => (hpos w).symm) g

omit [BorelSpace E] [IsProbabilityMeasure μ] in
/-- The actual channel fixes the position projection. -/
theorem positionChannel_positionProjection (f : Lp ℝ 2 (gaussianPhaseMeasure μ)) :
    referenceChannel hp hq (gaussianPositionProjection μ f) = gaussianPositionProjection μ f :=
  positionChannel_positionEmbedding μ hp hq hpos (gaussianAverage μ f)

omit [BorelSpace E] [IsProbabilityMeasure μ] in
theorem positionChannel_adjoint_positionProjection (f : Lp ℝ 2 (gaussianPhaseMeasure μ)) :
    (referenceChannel hp hq).adjoint (gaussianPositionProjection μ f) =
      gaussianPositionProjection μ f :=
  positionChannel_adjoint_positionEmbedding μ hp hq hpos (gaussianAverage μ f)

omit [BorelSpace E] [IsProbabilityMeasure μ] in
/-- The density collision preserves the macro component exactly. -/
theorem positionProjection_positionChannel_adjoint (f : Lp ℝ 2 (gaussianPhaseMeasure μ)) :
    gaussianPositionProjection μ ((referenceChannel hp hq).adjoint f) =
      gaussianPositionProjection μ f := by
  apply ext_inner_left ℝ
  intro g
  rw [← ContinuousLinearMap.adjoint_inner_left, gaussianPositionProjection_adjoint,
    ContinuousLinearMap.adjoint_inner_right,
    positionChannel_positionProjection μ hp hq hpos g,
    ← ContinuousLinearMap.adjoint_inner_left, gaussianPositionProjection_adjoint]

omit [BorelSpace E] [IsProbabilityMeasure μ] in
/-- The actual ordinary loss is exactly the loss in the micro component. -/
theorem positionChannel_micro_loss (f : Lp ℝ 2 (gaussianPhaseMeasure μ)) :
    ‖f - gaussianPositionProjection μ f‖ ^ 2 =
      ‖(referenceChannel hp hq).adjoint f -
        gaussianPositionProjection μ ((referenceChannel hp hq).adjoint f)‖ ^ 2 +
      (‖f‖ ^ 2 - ‖(referenceChannel hp hq).adjoint f‖ ^ 2) := by
  have hf := gaussianPositionProjection_norm_sq μ f
  have hqf := gaussianPositionProjection_norm_sq μ ((referenceChannel hp hq).adjoint f)
  rw [positionProjection_positionChannel_adjoint μ hp hq hpos f] at hqf ⊢
  linarith

section Corrector
variable (V : E → ℝ) (hV : ContDiff ℝ 2 V)
  (hI : Integrable (fun x => Real.exp (-V x))) (hμ : μ = volume.tilted (fun x => -V x))
  (m L : ℝ) (hm : 0 < m)
  (hlower : ∀ x a, m * ‖a‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x a a)
  (hupper : ∀ x a, fderiv ℝ (fderiv ℝ V) x a a ≤ L * ‖a‖ ^ 2)

/-- The source W12 premise, stated for the actual channel and the actual
Poisson/Gaussian corrector. It is not a contraction or current hypothesis. -/
def DormantW12 (C a : ℝ) : Prop :=
  ‖(referenceChannel hp hq - ContinuousLinearMap.id ℝ _).comp
    (gaussianCorrector μ V hV hI hμ m L hm hlower hupper).adjoint‖ ≤ C * a

/-- Exact cross-term change, derived from position retention and adjointness. -/
theorem positionChannel_corrector_change (f : Lp ℝ 2 (gaussianPhaseMeasure μ)) :
    inner ℝ (gaussianCorrector μ V hV hI hμ m L hm hlower hupper
      ((referenceChannel hp hq).adjoint f)) ((referenceChannel hp hq).adjoint f) -
    inner ℝ (gaussianCorrector μ V hV hI hμ m L hm hlower hupper f) f =
    inner ℝ (((referenceChannel hp hq - ContinuousLinearMap.id ℝ _).comp
      (gaussianCorrector μ V hV hI hμ m L hm hlower hupper).adjoint)
        (gaussianPositionProjection μ f)) (f - gaussianPositionProjection μ f) := by
  let A := gaussianCorrector μ V hV hI hμ m L hm hlower hupper
  let Q := referenceChannel hp hq
  let P := gaussianPositionProjection μ
  have hc (u : Lp ℝ 2 (gaussianPhaseMeasure μ)) : inner ℝ (A u) u = inner ℝ u (A.adjoint (P u)) := by
    have h := P.adjoint_inner_left u (A u)
    rw [gaussianPositionProjection_adjoint, positionProjection_gaussianCorrector] at h
    rw [h, ← A.adjoint_inner_right]
  have hmQ : P (Q.adjoint f) = P f := positionProjection_positionChannel_adjoint μ hp hq hpos f
  have hQm : Q.adjoint (P f) = P f := positionChannel_adjoint_positionProjection μ hp hq hpos f
  have hz : inner ℝ (Q (A.adjoint (P f)) - A.adjoint (P f)) (P f) = 0 := by
    rw [inner_sub_left, ← Q.adjoint_inner_right, hQm, sub_self]
  change inner ℝ (A (Q.adjoint f)) (Q.adjoint f) - inner ℝ (A f) f = _
  rw [hc, hc, hmQ, Q.adjoint_inner_left]
  change inner ℝ f (Q (A.adjoint (P f))) - inner ℝ f (A.adjoint (P f)) =
    inner ℝ (Q (A.adjoint (P f)) - A.adjoint (P f)) (f - P f)
  rw [inner_sub_right, hz, sub_zero, inner_sub_left, real_inner_comm f]
  rw [real_inner_comm f]

/-- The explicit W12 premise controls precisely the macro--micro corrector change. -/
theorem positionChannel_corrector_change_bound (C a : ℝ)
    (hW : DormantW12 μ hp hq V hV hI hμ m L hm hlower hupper C a)
    (f : Lp ℝ 2 (gaussianPhaseMeasure μ)) :
    |inner ℝ (gaussianCorrector μ V hV hI hμ m L hm hlower hupper
      ((referenceChannel hp hq).adjoint f)) ((referenceChannel hp hq).adjoint f) -
    inner ℝ (gaussianCorrector μ V hV hI hμ m L hm hlower hupper f) f| ≤
      C * a * ‖gaussianPositionProjection μ f‖ * ‖f - gaussianPositionProjection μ f‖ := by
  rw [positionChannel_corrector_change μ hp hq hpos V hV hI hμ m L hm hlower hupper]
  let B := (referenceChannel hp hq - ContinuousLinearMap.id ℝ _).comp
    (gaussianCorrector μ V hV hI hμ m L hm hlower hupper).adjoint
  have hb : ‖B (gaussianPositionProjection μ f)‖ ≤ C * a * ‖gaussianPositionProjection μ f‖ :=
    (B.le_opNorm _).trans (mul_le_mul_of_nonneg_right hW (norm_nonneg _))
  exact (abs_real_inner_le_norm _ _).trans
    (mul_le_mul_of_nonneg_right hb (norm_nonneg _))

/-- Actual dormant collision energy inequality. The negative term is its
ordinary L2 loss, and only the named W12 premise controls the corrector error. -/
theorem positionChannel_correctedEnergy_le (C a ε : ℝ) (hε : 0 ≤ ε)
    (hW : DormantW12 μ hp hq V hV hI hμ m L hm hlower hupper C a)
    (f : Lp ℝ 2 (gaussianPhaseMeasure μ)) :
    gaussianCorrectedEnergy μ V hV hI hμ m L hm hlower hupper ε
      ((referenceChannel hp hq).adjoint f) ≤
    gaussianCorrectedEnergy μ V hV hI hμ m L hm hlower hupper ε f -
      (1 / 2 : ℝ) * (‖f‖ ^ 2 - ‖(referenceChannel hp hq).adjoint f‖ ^ 2) +
      (C / 2) * ε * a * ‖f‖ ^ 2 := by
  have hchange := positionChannel_corrector_change_bound μ hp hq hpos V hV hI hμ m L hm
    hlower hupper C a hW f
  have hCa : 0 ≤ C * a := (norm_nonneg _).trans hW
  have hsplit := gaussianPositionProjection_norm_sq μ f
  have hMR : ‖gaussianPositionProjection μ f‖ * ‖f - gaussianPositionProjection μ f‖ ≤
      ‖f‖ ^ 2 / 2 := by
    nlinarith [sq_nonneg (‖gaussianPositionProjection μ f‖ - ‖f - gaussianPositionProjection μ f‖)]
  have hbound := mul_le_mul_of_nonneg_left hMR hCa
  have hu := (le_abs_self _).trans hchange
  have hscaled := mul_le_mul_of_nonneg_left hu hε
  have hscaled' := mul_le_mul_of_nonneg_left hbound hε
  unfold gaussianCorrectedEnergy
  nlinarith

end Corrector
end AcceleratedLogConcave.Kinetic.ConditionalContraction
