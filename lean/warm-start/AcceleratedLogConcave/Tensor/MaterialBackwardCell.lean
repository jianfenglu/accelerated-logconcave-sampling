import AcceleratedLogConcave.Tensor.MaterialBackwardSharp
import AcceleratedLogConcave.Numerics.AffineQuadrature

noncomputable section
namespace AcceleratedLogConcave.Numerics.MeanResidualBridge
open MeanFlowLp AffineGraph AffineGraph.MeanGeometry Set
variable {D m : ℕ}

/-- Exact cellwise budget at the right endpoint, with no mesh simplification. -/
def materialBackwardCellBudget (d : MeanFlowLp.Data (Fin D) m)
    (c : d.G.backward.Cell) : ℝ :=
  materialBackwardDerivativeBudget d (m-1) / (1-(d.G.backward.right c)^2)^m

 theorem materialBackwardDerivativeBudget_nonneg (d : MeanFlowLp.Data (Fin D) m) (k : ℕ) :
    0 ≤ materialBackwardDerivativeBudget d k := by
  unfold materialBackwardDerivativeBudget
  have he := d.hell
  have hr := d.hr
  positivity

/-- The actual backward receiver satisfies the inherited cell regularity interface.
The index j supplies positive order; for m=0 the family is empty. -/
 theorem replacement_backwardMean_cellRegularity (d : MeanFlowLp.Data (Fin D) m)
    (U : H d → ℝ → H d)
    (hu : PrimitiveSpec (primitiveData d) (seedMeasure d) U) (j : Fin m) :
    AffineResidual.CellRegularity d.G.backward m
      ((curvesWithBackward d).backwardMean d.G U 0 d.r j)
      (materialBackwardCellBudget d) := by
  have hm : 1 ≤ m := by have hj := j.isLt; omega
  have hright (c : d.G.backward.Cell) : 0 < 1-(d.G.backward.right c)^2 := by
    apply Conditional.conditionalVariance_pos
    have h0 := d.G.backward.lo_le_left c
    have hl := d.G.backward.length_pos c
    dsimp [IntervalMesh.length] at hl
    linarith
    have hh := d.G.backward.right_le_hi c
    linarith [d.G.backwardEnd_lt_one]
  refine ⟨?_, ?_, ?_⟩
  · intro c
    exact div_nonneg (materialBackwardDerivativeBudget_nonneg d (m-1))
      (pow_nonneg (hright c).le _)
  · intro c t ht
    exact contDiffAt_replacement_backwardMean d U hu j m
      ⟨(d.G.backward.lo_le_left c).trans ht.1,
        ht.2.trans (d.G.backward.right_le_hi c)⟩
  · intro c t ht
    have hsource : t ∈ Icc 0 (backwardEnd d.G.R) :=
      ⟨(d.G.backward.lo_le_left c).trans ht.1,
        ht.2.trans (d.G.backward.right_le_hi c)⟩
    have hb := replacement_backwardMean_derivative_bound d U hu j (m-1) hsource
    rw [Nat.sub_add_cancel hm] at hb
    refine hb.trans ?_
    unfold materialBackwardCellBudget
    apply div_le_div_of_nonneg_left (materialBackwardDerivativeBudget_nonneg d (m-1))
      (pow_pos (hright c) m)
    apply pow_le_pow_left₀ (hright c).le
    nlinarith [hsource.1,ht.2]

end AcceleratedLogConcave.Numerics.MeanResidualBridge
