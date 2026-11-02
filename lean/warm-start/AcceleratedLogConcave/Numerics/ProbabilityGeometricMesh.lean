import AcceleratedLogConcave.Numerics.ProbabilityMeshBudget

/-! Generic probability schedule. Positivity and the half-step cap are explicit.
Only the numerical mesh is instantiated; the quantitative envelope is still supplied. -/
noncomputable section
open AcceleratedLogConcave.Numerics.AffineGraph
open AcceleratedLogConcave.Numerics.AffineGraph.MeanGeometry
set_option autoImplicit false
namespace AcceleratedLogConcave.Numerics

private theorem probability_count_pos {lo hi h₀ : ℝ}
    (hlt : lo < hi) (hhi : hi < 1) (hh : 0 < h₀) :
    0 < GeometricMesh.cellCount lo hi h₀ :=
  GeometricMesh.cellCount_pos hlt hhi hh

/-- Ceiling-balanced probability mesh on a positive-length probability interval. -/
def probabilityGeometricInterval (lo hi h₀ : ℝ) (hlt : lo < hi) (hhi : hi < 1) (hh : 0 < h₀) :
    IntervalMesh lo hi where
  cellsPred := GeometricMesh.cellCount lo hi h₀ - 1
  point := fun j => GeometricMesh.point lo hi h₀ j.val
  strictMono := by
    intro i j hij
    exact GeometricMesh.point_strictMono hlt hhi hh hij
  first := GeometricMesh.point_zero lo hi h₀
  last := by
    have hn := probability_count_pos hlt hhi hh
    change GeometricMesh.point lo hi h₀
      (GeometricMesh.cellCount lo hi h₀ - 1 + 1) = hi
    rw [Nat.sub_add_cancel hn]
    exact GeometricMesh.point_count hlt.le hhi hh

/-- Exact cell-count normalization, including the one-cell ceiling case. -/
theorem probabilityGeometricInterval_cellCount (lo hi h₀ : ℝ) (hlt : lo < hi) (hhi : hi < 1) (hh : 0 < h₀) :
    (probabilityGeometricInterval lo hi h₀ hlt hhi hh).cellsPred + 1 =
      GeometricMesh.cellCount lo hi h₀ :=
  Nat.sub_add_cancel (probability_count_pos hlt hhi hh)

/-- The prescribed geometric schedule discharges the named probability step premise. -/
theorem probabilityGeometricInterval_step (lo hi h₀ : ℝ) (hlt : lo < hi) (hhi : hi < 1) (hh : 0 < h₀) (hhalf : h₀ ≤ 1/2) (hlo : 0 ≤ lo)
    (c : (probabilityGeometricInterval lo hi h₀ hlt hhi hh).Cell) :
    (probabilityGeometricInterval lo hi h₀ hlt hhi hh).length c ≤
      2*h₀*(1-((probabilityGeometricInterval lo hi h₀ hlt hhi hh).right c)^2) := by
  let c' : Fin (GeometricMesh.cellCount lo hi h₀) :=
    ⟨c.val, by rw [← probabilityGeometricInterval_cellCount lo hi h₀ hlt hhi hh]; exact c.isLt⟩
  exact GeometricMesh.cellLength_le_two_mul_one_sub_right_sq
    hlo hlt hhi hh hhalf c'


end AcceleratedLogConcave.Numerics
