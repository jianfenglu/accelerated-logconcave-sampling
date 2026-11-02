import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Order.Interval.Set.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-! geometry of the enlarged slab. The reference time b stays
strictly inside the construction interval, as does the requested open
neighborhood of the original closed source interval. -/
noncomputable section
open Set
namespace AcceleratedLogConcave.Analysis.PositiveVarianceSlab

def left (b : ℝ) : ℝ := (b - 1) / 2
def right (b : ℝ) : ℝ := (b + 1) / 2
def radius (b : ℝ) : ℝ := (1 - b) / 4
def varianceFloor (b : ℝ) : ℝ := 1 - (right b) ^ 2

theorem geometry {b : ℝ} (hb0 : 0 ≤ b) (hb1 : b < 1) :
    -1 < left b ∧ left b < -radius b ∧ -radius b < 0 ∧
      b < b + radius b ∧ b + radius b < right b ∧ right b < 1 := by
  dsimp [left, right, radius]
  constructor <;> try linarith
  constructor <;> try linarith
  constructor <;> try linarith
  constructor <;> try linarith
  constructor <;> linarith

theorem source_subset {b : ℝ} (_hb0 : 0 ≤ b) (hb1 : b < 1) :
    Icc 0 b ⊆ Ioo (left b) (right b) := by
  intro t ht
  dsimp [left, right]
  constructor <;> linarith [ht.1, ht.2]

theorem neighborhood_subset {b : ℝ} (_hb0 : 0 ≤ b) (hb1 : b < 1) :
    Ioo (-radius b) (b + radius b) ⊆ Ioo (left b) (right b) := by
  intro t ht
  dsimp [left, right, radius] at *
  constructor <;> linarith [ht.1, ht.2]

theorem construction_subset {b : ℝ} (hb0 : 0 ≤ b) (hb1 : b < 1) :
    Icc (left b) (right b) ⊆ Ioo (-1) 1 := by
  intro t ht
  dsimp [left, right] at *
  constructor <;> linarith [ht.1, ht.2]

theorem varianceFloor_pos {b : ℝ} (hb0 : 0 ≤ b) (hb1 : b < 1) :
    0 < varianceFloor b := by
  have hc : 0 ≤ right b := by dsimp [right]; positivity
  have hc1 : right b < 1 := by dsimp [right]; linarith
  dsimp [varianceFloor]
  nlinarith [mul_pos (sub_pos.mpr hc1) (show 0 < 1 + right b by linarith)]

theorem abs_time_le_right {b t : ℝ} (hb0 : 0 ≤ b)
    (ht : t ∈ Icc (left b) (right b)) : |t| ≤ right b := by
  rw [abs_le]
  dsimp [left, right] at *
  constructor <;> linarith [ht.1, ht.2]

theorem variance_mem {b t : ℝ} (hb0 : 0 ≤ b)
    (ht : t ∈ Icc (left b) (right b)) :
    1 - t ^ 2 ∈ Icc (varianceFloor b) 1 := by
  have habs := abs_time_le_right hb0 ht
  have hs : t ^ 2 ≤ (right b) ^ 2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg t) habs 2
  dsimp [varianceFloor]
  exact ⟨by linarith, by nlinarith [sq_nonneg t]⟩

theorem precision_mem {b t : ℝ} (hb0 : 0 ≤ b) (hb1 : b < 1)
    (ht : t ∈ Icc (left b) (right b)) :
    (2 * (1 - t ^ 2))⁻¹ ∈ Icc ((2 : ℝ)⁻¹) ((2 * varianceFloor b)⁻¹) := by
  have hv := variance_mem hb0 ht
  have hv0 := varianceFloor_pos hb0 hb1
  have hvt : 0 < 1 - t ^ 2 := hv0.trans_le hv.1
  constructor
  · apply (inv_le_inv₀ (by norm_num) (by positivity)).mpr
    linarith [hv.2]
  · apply (inv_le_inv₀ (by positivity) (by positivity)).mpr
    linarith [hv.1]

theorem abs_timeRatio_le {b t : ℝ} (hb0 : 0 ≤ b) (hb1 : b < 1)
    (ht : t ∈ Icc (left b) (right b)) :
    |t / (1 - t ^ 2)| ≤ right b * (varianceFloor b)⁻¹ := by
  have hv := variance_mem hb0 ht
  have hv0 := varianceFloor_pos hb0 hb1
  have hvt : 0 < 1 - t ^ 2 := hv0.trans_le hv.1
  have hinv : (1 - t ^ 2)⁻¹ ≤ (varianceFloor b)⁻¹ :=
    (inv_le_inv₀ hvt hv0).mpr hv.1
  rw [div_eq_mul_inv, abs_mul, abs_of_pos (inv_pos.mpr hvt)]
  exact mul_le_mul (abs_time_le_right hb0 ht) hinv
    (inv_nonneg.mpr hvt.le) (by dsimp [right]; positivity)

end AcceleratedLogConcave.Analysis.PositiveVarianceSlab
