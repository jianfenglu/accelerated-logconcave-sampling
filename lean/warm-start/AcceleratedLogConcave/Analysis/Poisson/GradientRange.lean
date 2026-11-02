import AcceleratedLogConcave.Analysis.Poisson.Inverse

/-!
# The closed gradient range and its canonical projection

The vector variational solver identifies the canonical orthogonal projection
onto the closure of the actual weighted gradient range. Since every projected
vector is itself a genuine closed gradient, the range is already closed.
-/

noncomputable section
open MeasureTheory InnerProductSpace
open scoped ContDiff RealInnerProductSpace

namespace AcceleratedLogConcave.Analysis.Poisson
open WeightedGradient

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable (μ : Measure E) (V : E → ℝ)
  (hV : ContDiff ℝ 2 V) (hI : Integrable (fun x => Real.exp (-V x)))
  (hμ : μ = volume.tilted (fun x => -V x))

/-- The closure of the range of the genuine closed weighted gradient. -/
def weightedClosedGradientRange : Submodule ℝ (Lp E 2 μ) :=
  (closedGradient μ V (hV.of_le (by norm_num)) hI hμ).toFun.range.topologicalClosure

instance weightedClosedGradientRange_complete : CompleteSpace (weightedClosedGradientRange μ V hV hI hμ) := by
  unfold weightedClosedGradientRange
  infer_instance

/-- The canonical orthogonal projection onto the closed gradient range. -/
def canonicalWeightedGradientProjection : Lp E 2 μ →L[ℝ] Lp E 2 μ :=
  (weightedClosedGradientRange μ V hV hI hμ).starProjection

variable [IsProbabilityMeasure μ]
  (m L : ℝ) (hm : 0 < m)
  (hlower : ∀ x a, m * ‖a‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x a a)
  (hupper : ∀ x a, fderiv ℝ (fderiv ℝ V) x a a ≤ L * ‖a‖ ^ 2)

/-- The variational gradient map is the canonical orthogonal projection. -/
theorem weightedGradientProjection_eq_canonical :
    weightedGradientProjection μ V hV hI hμ m L hm hlower hupper =
      canonicalWeightedGradientProjection μ V hV hI hμ := by
  apply ContinuousLinearMap.ext
  intro f
  symm
  apply Submodule.eq_starProjection_of_mem_orthogonal
  · apply Submodule.le_topologicalClosure
    exact ⟨vectorPoissonSolution μ V hV hI hμ m L hm hlower hupper f, rfl⟩
  · change f - weightedGradientProjection μ V hV hI hμ m L hm hlower hupper f ∈
      (closedGradient μ V (hV.of_le (by norm_num)) hI hμ).toFun.range.topologicalClosureᗮ
    rw [Submodule.orthogonal_closure]
    intro w hw
    obtain ⟨v, rfl⟩ := hw
    rw [real_inner_comm, inner_sub_left, weightedGradientProjection_apply]
    exact sub_eq_zero.mpr ((vectorPoissonSolution_spec (μ := μ) (V := V) (hV := hV)
      (hI := hI) (hμ := hμ) (m := m) (L := L) (hm := hm)
      (hlower := hlower) (hupper := hupper) f).2 v).symm

include hm hlower hupper in
/-- Every member of the closure of the gradient range is an actual closed gradient. -/
theorem weightedClosedGradient_range_eq_closure :
    (closedGradient μ V (hV.of_le (by norm_num)) hI hμ).toFun.range =
      weightedClosedGradientRange μ V hV hI hμ := by
  apply le_antisymm (Submodule.le_topologicalClosure _)
  intro w hw
  have he : canonicalWeightedGradientProjection μ V hV hI hμ w = w :=
    Submodule.starProjection_eq_self_iff.mpr hw
  rw [← weightedGradientProjection_eq_canonical μ V hV hI hμ m L hm hlower hupper] at he
  exact ⟨vectorPoissonSolution μ V hV hI hμ m L hm hlower hupper w, he⟩

include hm hlower hupper in
/-- The actual weighted gradient has closed range, as a consequence of curvature. -/
theorem weightedClosedGradient_range_isClosed :
    IsClosed ((closedGradient μ V (hV.of_le (by norm_num)) hI hμ).toFun.range :
      Set (Lp E 2 μ)) := by
  rw [weightedClosedGradient_range_eq_closure μ V hV hI hμ m L hm hlower hupper]
  exact Submodule.isClosed_topologicalClosure _

end AcceleratedLogConcave.Analysis.Poisson
