import AcceleratedLogConcave.Numerics.ReciprocalQuadrature
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Order.Interval.Set.Union
import Mathlib.Order.Interval.Set.Disjoint
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum

/-!
# Ceiling-balanced probability meshes

The mesh chooses ceil(T/h0) equal logarithmic steps, where
T = log(1-a) - log(1-b).

Zero/short intervals and exact ceiling boundaries are explicit. Physical cells
feed the frozen Gauss-Legendre and reciprocal-quadrature interfaces. The kernel
mass theorem derives its first-cell premise from the source parameter guards.
The right-endpoint-square bound is exported for separate downstream error work;
no singular-kernel RMS estimate or compiler theorem is asserted here.
-/

/- Foundation -/
noncomputable section

namespace AcceleratedLogConcave.Numerics.GeometricMesh

def logSpan (a b : ℝ) : ℝ := Real.log (1 - a) - Real.log (1 - b)

def cellCount (a b h₀ : ℝ) : ℕ := Nat.ceil (logSpan a b / h₀)

def logStep (a b h₀ : ℝ) : ℝ := logSpan a b / (cellCount a b h₀ : ℝ)

def point (a b h₀ : ℝ) (j : ℕ) : ℝ :=
  1 - (1 - a) * Real.exp (-(j : ℝ) * logStep a b h₀)

def mesh (a b h₀ : ℝ) : Fin (cellCount a b h₀ + 1) → ℝ :=
  fun j ↦ point a b h₀ j.val

def cellLength (a b h₀ : ℝ) (c : Fin (cellCount a b h₀)) : ℝ :=
  point a b h₀ (c.val + 1) - point a b h₀ c.val

variable {a b h₀ : ℝ}

theorem logSpan_nonneg (hab : a ≤ b) (hb : b < 1) : 0 ≤ logSpan a b := by
  exact sub_nonneg.mpr (Real.log_le_log (sub_pos.mpr hb) (sub_le_sub_left hab 1))

theorem logSpan_pos (hab : a < b) (hb : b < 1) : 0 < logSpan a b := by
  exact sub_pos.mpr (Real.log_lt_log (sub_pos.mpr hb) (sub_lt_sub_left hab 1))

theorem cellCount_pos (hab : a < b) (hb : b < 1) (hh : 0 < h₀) :
    0 < cellCount a b h₀ := by
  exact Nat.one_le_ceil_iff.mpr (div_pos (logSpan_pos hab hb) hh)

theorem logStep_pos (hab : a < b) (hb : b < 1) (hh : 0 < h₀) :
    0 < logStep a b h₀ := by
  exact div_pos (logSpan_pos hab hb) (Nat.cast_pos.mpr (cellCount_pos hab hb hh))

theorem logStep_le (hab : a < b) (hb : b < 1) (hh : 0 < h₀) :
    logStep a b h₀ ≤ h₀ := by
  have hn : (0 : ℝ) < cellCount a b h₀ := Nat.cast_pos.mpr (cellCount_pos hab hb hh)
  have hceil : logSpan a b / h₀ ≤ (cellCount a b h₀ : ℝ) := Nat.le_ceil _
  apply (div_le_iff₀ hn).mpr
  simpa only [mul_comm] using (div_le_iff₀ hh).mp hceil

theorem logStep_lower (hab : a < b) (hb : b < 1) (hh : 0 < h₀)
    (hT : h₀ ≤ logSpan a b) : h₀ / 2 ≤ logStep a b h₀ := by
  have hn : (0 : ℝ) < cellCount a b h₀ := Nat.cast_pos.mpr (cellCount_pos hab hb hh)
  have hceil : (cellCount a b h₀ : ℝ) < logSpan a b / h₀ + 1 :=
    Nat.ceil_lt_add_one (div_nonneg (logSpan_pos hab hb).le hh.le)
  have hmul := mul_lt_mul_of_pos_right hceil hh
  rw [add_mul, div_mul_cancel₀ _ hh.ne', one_mul] at hmul
  apply (le_div_iff₀ hn).mpr
  nlinarith

@[simp] theorem point_zero (a b h₀ : ℝ) : point a b h₀ 0 = a := by
  simp [point]

theorem point_count (hab : a ≤ b) (hb : b < 1) (hh : 0 < h₀) :
    point a b h₀ (cellCount a b h₀) = b := by
  rcases hab.eq_or_lt with rfl | hab
  · simp [point, logStep, cellCount, logSpan]
  have hn : (cellCount a b h₀ : ℝ) ≠ 0 :=
    (Nat.cast_pos.mpr (cellCount_pos hab hb hh)).ne'
  have he : -(cellCount a b h₀ : ℝ) * logStep a b h₀ = -logSpan a b := by
    dsimp [logStep]
    field_simp
  have ha : 0 < 1 - a := sub_pos.mpr (hab.trans hb)
  rw [point, he,
    show -logSpan a b = Real.log (1 - b) - Real.log (1 - a) by
      dsimp [logSpan]; ring,
    Real.exp_sub, Real.exp_log (sub_pos.mpr hb), Real.exp_log ha]
  field_simp
  ring

theorem point_strictMono (hab : a < b) (hb : b < 1) (hh : 0 < h₀) :
    StrictMono (point a b h₀) := by
  intro i j hij
  have hijR : (i : ℝ) < j := Nat.cast_lt.mpr hij
  have he : -(j : ℝ) * logStep a b h₀ < -(i : ℝ) * logStep a b h₀ :=
    mul_lt_mul_of_pos_right (neg_lt_neg hijR) (logStep_pos hab hb hh)
  exact sub_lt_sub_left
    (mul_lt_mul_of_pos_left (Real.exp_lt_exp.mpr he) (sub_pos.mpr (hab.trans hb))) 1

theorem point_lt_one (ha : a < 1) (j : ℕ) : point a b h₀ j < 1 := by
  exact sub_lt_self 1 (mul_pos (sub_pos.mpr ha) (Real.exp_pos _))

theorem mesh_strictMono (hab : a < b) (hb : b < 1) (hh : 0 < h₀) :
    StrictMono (mesh a b h₀) := by
  intro i j hij
  exact point_strictMono hab hb hh hij

/-- The logarithmic coordinate is exactly affine in the natural index. -/
theorem log_one_sub_point (ha : a < 1) (j : ℕ) :
    Real.log (1 - point a b h₀ j) =
      Real.log (1 - a) - (j : ℝ) * logStep a b h₀ := by
  have he : 1 - point a b h₀ j =
      (1 - a) * Real.exp (-(j : ℝ) * logStep a b h₀) := by
    dsimp [point]
    ring
  rw [he, Real.log_mul (sub_pos.mpr ha).ne' (Real.exp_ne_zero _), Real.log_exp]
  ring

end AcceleratedLogConcave.Numerics.GeometricMesh

/- Geometry -/
open scoped BigOperators
namespace AcceleratedLogConcave.Numerics.GeometricMesh

private theorem one_sub_exp_neg_lower {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    x / 2 ≤ 1 - Real.exp (-x) := by
  have hden : 0 < 1 + x := by linarith
  have he : Real.exp (-x) ≤ 1 / (1 + x) := by
    rw [Real.exp_neg, ← one_div]
    exact one_div_le_one_div_of_le hden (by simpa [add_comm] using Real.add_one_le_exp x)
  calc
    x / 2 ≤ x / (1 + x) :=
      div_le_div_of_nonneg_left hx hden (by linarith)
    _ = 1 - 1 / (1 + x) := by field_simp; ring
    _ ≤ 1 - Real.exp (-x) := by linarith

variable {a b h₀ : ℝ}

/-- Physical widths are geometric in the residual probability coordinate. -/
theorem point_succ_sub_point (a b h₀ : ℝ) (j : ℕ) :
    point a b h₀ (j + 1) - point a b h₀ j =
      (1 - point a b h₀ j) * (1 - Real.exp (-logStep a b h₀)) := by
  have he : -((j + 1 : ℕ) : ℝ) * logStep a b h₀ =
      -(j : ℝ) * logStep a b h₀ + -logStep a b h₀ := by
    push_cast
    ring
  simp only [point, he, Real.exp_add]
  ring

theorem cellLength_eq (c : Fin (cellCount a b h₀)) :
    cellLength a b h₀ c =
      (1 - point a b h₀ c.val) * (1 - Real.exp (-logStep a b h₀)) :=
  point_succ_sub_point a b h₀ c.val

theorem cellLength_pos (hab : a < b) (hb : b < 1) (hh : 0 < h₀)
    (c : Fin (cellCount a b h₀)) : 0 < cellLength a b h₀ c :=
  sub_pos.mpr (point_strictMono hab hb hh (Nat.lt_succ_self c.val))

theorem point_mem_Icc_of_lt (hab : a < b) (hb : b < 1) (hh : 0 < h₀)
    {j : ℕ} (hj : j ≤ cellCount a b h₀) : point a b h₀ j ∈ Set.Icc a b := by
  constructor
  · simpa only [point_zero] using (point_strictMono hab hb hh).monotone (Nat.zero_le j)
  · simpa only [point_count hab.le hb hh] using
      (point_strictMono hab hb hh).monotone hj

theorem cellLength_le_left (hab : a < b) (hb : b < 1) (hh : 0 < h₀)
    (c : Fin (cellCount a b h₀)) :
    cellLength a b h₀ c ≤ h₀ * (1 - point a b h₀ c.val) := by
  rw [cellLength_eq, mul_comm h₀]
  apply mul_le_mul_of_nonneg_left _ (sub_nonneg.mpr (point_lt_one (hab.trans hb) _).le)
  have he := Real.one_sub_le_exp_neg (logStep a b h₀)
  have hd := logStep_le hab hb hh
  linarith

/-- Uniform physical-cell upper bound at the right endpoint. -/
theorem cellLength_le_right (hab : a < b) (hb : b < 1) (hh : 0 < h₀)
    (hh_half : h₀ ≤ 1 / 2) (c : Fin (cellCount a b h₀)) :
    cellLength a b h₀ c ≤ 2 * h₀ * (1 - point a b h₀ (c.val + 1)) := by
  have hl := cellLength_le_left hab hb hh c
  have hres : 0 ≤ 1 - point a b h₀ c.val :=
    sub_nonneg.mpr (point_lt_one (hab.trans hb) _).le
  have hhalf : cellLength a b h₀ c ≤ (1 / 2 : ℝ) * (1 - point a b h₀ c.val) :=
    hl.trans (mul_le_mul_of_nonneg_right hh_half hres)
  have hrel : 1 - point a b h₀ c.val ≤
      2 * (1 - point a b h₀ (c.val + 1)) := by
    dsimp [cellLength] at hhalf
    linarith
  calc
    cellLength a b h₀ c ≤ h₀ * (1 - point a b h₀ c.val) := hl
    _ ≤ h₀ * (2 * (1 - point a b h₀ (c.val + 1))) :=
      mul_le_mul_of_nonneg_left hrel hh.le
    _ = 2 * h₀ * (1 - point a b h₀ (c.val + 1)) := by ring

/-- The exact right-endpoint factor used by the downstream singular-kernel estimate. -/
theorem cellLength_le_two_mul_one_sub_right_sq
    (ha : 0 ≤ a) (hab : a < b) (hb : b < 1) (hh : 0 < h₀)
    (hh_half : h₀ ≤ 1 / 2) (c : Fin (cellCount a b h₀)) :
    cellLength a b h₀ c ≤ 2 * h₀ * (1 - (point a b h₀ (c.val + 1))^2) := by
  have hr := point_mem_Icc_of_lt hab hb hh (Nat.succ_le_iff.mpr c.isLt)
  have hp : 0 ≤ point a b h₀ (c.val + 1) := ha.trans hr.1
  have hp1 : point a b h₀ (c.val + 1) ≤ 1 := hr.2.trans hb.le
  have hs : 1 - point a b h₀ (c.val + 1) ≤
      1 - (point a b h₀ (c.val + 1))^2 := by
    nlinarith [mul_nonneg hp (sub_nonneg.mpr hp1)]
  exact (cellLength_le_right hab hb hh hh_half c).trans
    (mul_le_mul_of_nonneg_left hs (by positivity))

theorem cellLength_le_two_mul_one_sub_sq
    (ha : 0 ≤ a) (hab : a < b) (hb : b < 1) (hh : 0 < h₀)
    (hh_half : h₀ ≤ 1 / 2) (c : Fin (cellCount a b h₀)) {ρ : ℝ}
    (hρ : ρ ∈ Set.Icc (point a b h₀ c.val) (point a b h₀ (c.val + 1))) :
    cellLength a b h₀ c ≤ 2 * h₀ * (1 - ρ^2) := by
  have hl := point_mem_Icc_of_lt hab hb hh c.isLt.le
  have hρ0 : 0 ≤ ρ := le_trans (ha.trans hl.1) hρ.1
  have hs : ρ^2 ≤ (point a b h₀ (c.val + 1))^2 :=
    pow_le_pow_left₀ hρ0 hρ.2 2
  exact (cellLength_le_two_mul_one_sub_right_sq ha hab hb hh hh_half c).trans
    (mul_le_mul_of_nonneg_left (sub_le_sub_left hs 1) (by positivity))

/-- The first-cell lower bound retains the residual factor for a general start. -/
theorem firstCell_lower (hab : a < b) (hb : b < 1) (hh : 0 < h₀)
    (hh_half : h₀ ≤ 1 / 2) (hT : h₀ ≤ logSpan a b) :
    (1 - a) * h₀ / 4 ≤ point a b h₀ 1 - point a b h₀ 0 := by
  have hd := logStep_lower hab hb hh hT
  have he := one_sub_exp_neg_lower (logStep_pos hab hb hh).le
    ((logStep_le hab hb hh).trans (by linarith : h₀ ≤ 1))
  rw [show (1 : ℕ) = 0 + 1 from rfl, point_succ_sub_point, point_zero]
  have ha : 0 ≤ 1 - a := sub_nonneg.mpr (hab.trans hb).le
  calc
    (1 - a) * h₀ / 4 = (1 - a) * (h₀ / 4) := by ring
    _ ≤ (1 - a) * (logStep a b h₀ / 2) :=
      mul_le_mul_of_nonneg_left (by linarith) ha
    _ ≤ (1 - a) * (1 - Real.exp (-logStep a b h₀)) :=
      mul_le_mul_of_nonneg_left he ha

end AcceleratedLogConcave.Numerics.GeometricMesh

/- Coverage -/
/-!
Finite coverage and exact inventory for the constructed logarithmic mesh.
The inventory counts indexed evaluation locations, including endpoints. It does
not identify coincident physical locations or count calls to an oracle.
-/

noncomputable section

open scoped BigOperators
open Set MeasureTheory

namespace AcceleratedLogConcave.Numerics.GeometricMesh

variable {a b h₀ : ℝ}

@[simp] theorem logSpan_self (a : ℝ) : logSpan a a = 0 := by
  simp [logSpan]

@[simp] theorem cellCount_self (a h₀ : ℝ) : cellCount a a h₀ = 0 := by
  simp [cellCount]

@[simp] theorem logStep_self (a h₀ : ℝ) : logStep a a h₀ = 0 := by
  simp [logStep]

@[simp] theorem point_self (a h₀ : ℝ) (j : ℕ) : point a a h₀ j = a := by
  simp [point]

theorem point_monotone (hab : a ≤ b) (hb : b < 1) (hh : 0 < h₀) :
    Monotone (point a b h₀) := by
  rcases hab.eq_or_lt with rfl | hab
  · intro i j _
    simp
  · exact (point_strictMono hab hb hh).monotone

theorem point_mem_Icc (hab : a ≤ b) (hb : b < 1) (hh : 0 < h₀)
    {j : ℕ} (hj : j ≤ cellCount a b h₀) : point a b h₀ j ∈ Icc a b := by
  have hm := point_monotone hab hb hh
  constructor
  · simpa only [point_zero] using hm (Nat.zero_le j)
  · simpa only [point_count hab hb hh] using hm hj

/-- The half-open cells cover exactly the physical interval, also for `a = b`. -/
theorem iUnion_cells (hab : a ≤ b) (hb : b < 1) (hh : 0 < h₀) :
    (⋃ j ∈ Finset.range (cellCount a b h₀),
      Ioc (point a b h₀ j) (point a b h₀ (j + 1))) = Ioc a b := by
  apply subset_antisymm
  · intro x hx
    rcases mem_iUnion.mp hx with ⟨j, hx⟩
    rcases mem_iUnion.mp hx with ⟨hj, hx⟩
    have hjN := Finset.mem_range.mp hj
    exact ⟨(point_mem_Icc hab hb hh (Nat.le_of_lt hjN)).1.trans_lt hx.1,
      hx.2.trans (point_mem_Icc hab hb hh (Nat.succ_le_of_lt hjN)).2⟩
  · simpa only [point_zero, point_count hab hb hh] using
      Ioc_subset_biUnion_Ioc (cellCount a b h₀) (point a b h₀)

theorem iUnion_fin_cells (hab : a ≤ b) (hb : b < 1) (hh : 0 < h₀) :
    (⋃ c : Fin (cellCount a b h₀),
      Ioc (point a b h₀ c.val) (point a b h₀ (c.val + 1))) = Ioc a b := by
  rw [← iUnion_cells hab hb hh]
  ext x
  simp only [mem_iUnion, Finset.mem_range]
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨c.val, c.isLt, hc⟩
  · rintro ⟨j, hj, hx⟩
    exact ⟨⟨j, hj⟩, hx⟩

/-- Touching boundaries belong only to the cell on their left. -/
theorem cells_pairwise_disjoint (hab : a ≤ b) (hb : b < 1) (hh : 0 < h₀) :
    Pairwise (fun c d : Fin (cellCount a b h₀) ↦
      Disjoint (Ioc (point a b h₀ c.val) (point a b h₀ (c.val + 1)))
        (Ioc (point a b h₀ d.val) (point a b h₀ (d.val + 1)))) := by
  intro c d hcd
  rcases lt_or_gt_of_ne hcd with hcd | hdc
  · exact Ioc_disjoint_Ioc_of_le
      (point_monotone hab hb hh (Nat.succ_le_of_lt hcd))
  · exact (Ioc_disjoint_Ioc_of_le
      (point_monotone hab hb hh (Nat.succ_le_of_lt hdc))).symm

theorem existsUnique_cell (hab : a ≤ b) (hb : b < 1) (hh : 0 < h₀)
    {x : ℝ} (hx : x ∈ Ioc a b) :
    ∃! c : Fin (cellCount a b h₀),
      x ∈ Ioc (point a b h₀ c.val) (point a b h₀ (c.val + 1)) := by
  rw [← iUnion_fin_cells hab hb hh] at hx
  obtain ⟨c, hc⟩ := mem_iUnion.mp hx
  refine ⟨c, hc, ?_⟩
  intro d hd
  by_contra hdc
  exact Set.disjoint_left.mp (cells_pairwise_disjoint hab hb hh hdc) hd hc

theorem sum_cellLength (hab : a ≤ b) (hb : b < 1) (hh : 0 < h₀) :
    ∑ c : Fin (cellCount a b h₀), cellLength a b h₀ c = b - a := by
  simp only [cellLength]
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ ↦
    point a b h₀ (j + 1) - point a b h₀ j), Finset.sum_range_sub,
    point_count hab hb hh, point_zero]

theorem sum_prefix_lengths (k : ℕ) :
    (∑ j ∈ Finset.range k, (point a b h₀ (j + 1) - point a b h₀ j)) =
      point a b h₀ k - a := by
  rw [Finset.sum_range_sub, point_zero]

theorem cellCount_eq_zero_iff (hab : a ≤ b) (hb : b < 1) (hh : 0 < h₀) :
    cellCount a b h₀ = 0 ↔ a = b := by
  constructor
  · intro hc
    by_contra hn
    have hp := cellCount_pos (lt_of_le_of_ne hab hn) hb hh
    omega
  · rintro rfl
    simp

/-- Short positive logarithmic intervals have exactly one cell. -/
theorem cellCount_eq_one_of_short (hab : a < b) (hb : b < 1) (hh : 0 < h₀)
    (hT : logSpan a b ≤ h₀) : cellCount a b h₀ = 1 := by
  apply (Nat.ceil_eq_iff (by decide : (1 : ℕ) ≠ 0)).mpr
  constructor
  · simpa only [Nat.sub_self, Nat.cast_zero] using
      div_pos (logSpan_pos hab hb) hh
  · simpa only [Nat.cast_one] using (div_le_one hh).mpr hT

theorem logStep_eq_span_of_short (hab : a < b) (hb : b < 1) (hh : 0 < h₀)
    (hT : logSpan a b ≤ h₀) : logStep a b h₀ = logSpan a b := by
  simp [logStep, cellCount_eq_one_of_short hab hb hh hT]

/-- Exact integer quotients are charged exactly, including the zero quotient. -/
theorem cellCount_of_logSpan_eq_mul (hh : 0 < h₀) (k : ℕ)
    (hT : logSpan a b = (k : ℝ) * h₀) : cellCount a b h₀ = k := by
  simp [cellCount, hT, hh.ne']

theorem logStep_of_logSpan_eq_mul (hh : 0 < h₀) {k : ℕ} (hk : k ≠ 0)
    (hT : logSpan a b = (k : ℝ) * h₀) : logStep a b h₀ = h₀ := by
  rw [logStep, cellCount_of_logSpan_eq_mul hh k hT, hT]
  exact mul_div_cancel_left₀ h₀ (Nat.cast_ne_zero.mpr hk)

theorem cellCount_lt_span_div_add_one (hab : a ≤ b) (hb : b < 1) (hh : 0 < h₀) :
    (cellCount a b h₀ : ℝ) < logSpan a b / h₀ + 1 := by
  exact Nat.ceil_lt_add_one (div_nonneg (logSpan_nonneg hab hb) hh.le)

theorem cellCount_le_span_div_add_one (hab : a ≤ b) (hb : b < 1) (hh : 0 < h₀) :
    (cellCount a b h₀ : ℝ) ≤ logSpan a b / h₀ + 1 :=
  (cellCount_lt_span_div_add_one hab hb hh).le

/-- Indexed cell-node pairs; this does not deduplicate physical locations. -/
theorem card_cell_node_indices (a b h₀ : ℝ) (n : ℕ) :
    Fintype.card (Fin (cellCount a b h₀) × Fin n) = cellCount a b h₀ * n := by
  simp

theorem card_endpoint_indices (a b h₀ : ℝ) :
    Fintype.card (Fin (cellCount a b h₀ + 1)) = cellCount a b h₀ + 1 := by
  simp

/-- Separate node and endpoint charges retain their possible coincidences. -/
theorem card_evaluation_indices (a b h₀ : ℝ) (n : ℕ) :
    Fintype.card ((Fin (cellCount a b h₀) × Fin n) ⊕
      Fin (cellCount a b h₀ + 1)) =
      cellCount a b h₀ * n + (cellCount a b h₀ + 1) := by
  simp

theorem node_inventory_le (hab : a ≤ b) (hb : b < 1) (hh : 0 < h₀) (n : ℕ) :
    ((cellCount a b h₀ * n : ℕ) : ℝ) ≤
      (logSpan a b / h₀ + 1) * (n : ℝ) := by
  push_cast
  exact mul_le_mul_of_nonneg_right (cellCount_le_span_div_add_one hab hb hh)
    (Nat.cast_nonneg n)

/-- The endpoint `+1` is preserved after the ceiling charge. -/
theorem evaluation_inventory_le (hab : a ≤ b) (hb : b < 1) (hh : 0 < h₀) (n : ℕ) :
    ((cellCount a b h₀ * n + (cellCount a b h₀ + 1) : ℕ) : ℝ) ≤
      (logSpan a b / h₀ + 1) * ((n : ℝ) + 1) + 1 := by
  have hn := mul_le_mul_of_nonneg_right
    (cellCount_le_span_div_add_one hab hb hh) (by positivity : 0 ≤ (n : ℝ) + 1)
  push_cast
  nlinarith

/-- Any choice of bounded-kernel partial rows, one per mesh cell, has total
absolute mass at most the full physical horizon. Completed cells use `u = 0`,
`v = 1`; inactive cells may use `u = v`. Reversed limits are allowed. -/
theorem sum_abs_cell_partialRows_le (hab : a ≤ b) (hb : b < 1) (hh : 0 < h₀)
    (n : ℕ) (hn : 0 < n)
    (u v : Fin (cellCount a b h₀) → ℝ)
    (hu : ∀ c, u c ∈ Icc (0 : ℝ) 1) (hv : ∀ c, v c ∈ Icc (0 : ℝ) 1)
    (k : Fin (cellCount a b h₀) → ℝ → ℝ)
    (hk : ∀ c, AEStronglyMeasurable (k c) (volume.restrict
      (uIoc (point a b h₀ c.val + cellLength a b h₀ c * u c)
        (point a b h₀ c.val + cellLength a b h₀ c * v c))))
    (hbound : ∀ c, ∀ᵐ y ∂volume.restrict
      (uIoc (point a b h₀ c.val + cellLength a b h₀ c * u c)
        (point a b h₀ c.val + cellLength a b h₀ c * v c)), |k c y| ≤ 1) :
    (∑ c : Fin (cellCount a b h₀), ∑ i : Fin n,
      |GaussLegendre.partialRow n (point a b h₀ c.val) (cellLength a b h₀ c)
        (u c) (v c) (k c) i|) ≤ b - a := by
  rcases hab.eq_or_lt with rfl | hab
  · simp
  calc
    _ ≤ ∑ c : Fin (cellCount a b h₀), cellLength a b h₀ c := by
      apply Finset.sum_le_sum
      intro c _
      exact GaussLegendre.sum_abs_partialRow_le_length n hn
        (point a b h₀ c.val) (cellLength a b h₀ c) (u c) (v c)
        (sub_pos.mpr (point_strictMono hab hb hh (Nat.lt_succ_self c.val)))
        (hu c) (hv c) (k c) (hk c) (hbound c)
    _ = b - a := sum_cellLength hab.le hb hh

end AcceleratedLogConcave.Numerics.GeometricMesh

/- Kernel -/
/-!
The actual logarithmic kernel mesh ending at `sqrt (1 - R^2)`, and the
coefficient mass bound for its physical Gauss–Legendre cells. The positive
guards exclude the totalized `log 0` endpoint. This module proves no RMS estimate.
-/

noncomputable section

open scoped BigOperators

namespace AcceleratedLogConcave.Numerics.GeometricMesh

open ReciprocalQuadrature

theorem kernel_endpoint_bounds {R : ℝ} (hR : 0 < R) (hRupper : R ≤ 1 / 2) :
    1 / 2 ≤ Real.sqrt (1 - R ^ 2) ∧ Real.sqrt (1 - R ^ 2) < 1 := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    nlinarith
  · apply (Real.sqrt_lt' (by norm_num : (0 : ℝ) < 1)).mpr
    nlinarith [sq_pos_of_pos hR]

theorem kernel_logSpan_lower {R h₀ : ℝ} (hR : 0 < R) (hRupper : R ≤ 1 / 2)
    (hhupper : h₀ ≤ 1 / 2) :
    h₀ ≤ logSpan 0 (Real.sqrt (1 - R ^ 2)) := by
  obtain ⟨hblo, hbhi⟩ := kernel_endpoint_bounds hR hRupper
  have hlog := Real.log_le_sub_one_of_pos (sub_pos.mpr hbhi)
  simp only [logSpan, sub_zero, Real.log_one, zero_sub]
  linarith

theorem kernel_cellCount_pos {R h₀ : ℝ} (hR : 0 < R) (hRupper : R ≤ 1 / 2)
    (hh : 0 < h₀) : 0 < cellCount 0 (Real.sqrt (1 - R ^ 2)) h₀ := by
  obtain ⟨hblo, hbhi⟩ := kernel_endpoint_bounds hR hRupper
  exact cellCount_pos (by linarith) hbhi hh

/-- The natural-index mesh in the finite shape required by reciprocal quadrature. -/
def kernelMesh (R h₀ : ℝ) :
    Fin ((cellCount 0 (Real.sqrt (1 - R ^ 2)) h₀ - 1) + 2) → ℝ :=
  fun j ↦ point 0 (Real.sqrt (1 - R ^ 2)) h₀ j.val

@[simp] theorem kernelMesh_zero (R h₀ : ℝ) : kernelMesh R h₀ 0 = 0 := by
  simp [kernelMesh]

theorem kernelMesh_strictMono {R h₀ : ℝ} (hR : 0 < R) (hRupper : R ≤ 1 / 2)
    (hh : 0 < h₀) : StrictMono (kernelMesh R h₀) := by
  obtain ⟨hblo, hbhi⟩ := kernel_endpoint_bounds hR hRupper
  intro i j hij
  exact point_strictMono (by linarith) hbhi hh hij

theorem kernelMesh_horizon {R h₀ : ℝ} (hR : 0 < R) (hRupper : R ≤ 1 / 2)
    (hh : 0 < h₀) :
    meshHorizon (kernelMesh R h₀) = Real.sqrt (1 - R ^ 2) := by
  obtain ⟨hblo, hbhi⟩ := kernel_endpoint_bounds hR hRupper
  have hn := kernel_cellCount_pos hR hRupper hh
  have hlast : cellCount 0 (Real.sqrt (1 - R ^ 2)) h₀ - 1 + 1 =
      cellCount 0 (Real.sqrt (1 - R ^ 2)) h₀ := by omega
  simp only [meshHorizon, kernelMesh, Fin.val_last, hlast]
  exact point_count (by linarith) hbhi hh

theorem kernelMesh_cellLength_pos {R h₀ : ℝ} (hR : 0 < R)
    (hRupper : R ≤ 1 / 2) (hh : 0 < h₀)
    (c : Fin ((cellCount 0 (Real.sqrt (1 - R ^ 2)) h₀ - 1) + 1)) :
    0 < meshCellLength (kernelMesh R h₀) c := by
  exact sub_pos.mpr (kernelMesh_strictMono hR hRupper hh c.castSucc_lt_succ)

/-- Every later physical cell uses the telescoping reciprocal difference. -/
theorem kernel_laterCell_mass_le (n : ℕ) {R h₀ : ℝ} (hR : 0 < R)
    (hRupper : R ≤ 1 / 2) (hh : 0 < h₀)
    (c : Fin (cellCount 0 (Real.sqrt (1 - R ^ 2)) h₀ - 1)) :
    reciprocalCellMass n (meshCellLeft (kernelMesh R h₀) c.succ)
      (meshCellLength (kernelMesh R h₀) c.succ) ≤
      1 / meshCellLeft (kernelMesh R h₀) c.succ -
        1 / kernelMesh R h₀ c.succ.succ := by
  have hleft : 0 < meshCellLeft (kernelMesh R h₀) c.succ := by
    calc
      0 = kernelMesh R h₀ 0 := (kernelMesh_zero R h₀).symm
      _ < meshCellLeft (kernelMesh R h₀) c.succ := by
        apply kernelMesh_strictMono hR hRupper hh
        change (0 : ℕ) < c.val + 1
        omega
  have h := reciprocalCellMass_le_reciprocal_difference n
    (meshCellLeft (kernelMesh R h₀) c.succ)
    (meshCellLength (kernelMesh R h₀) c.succ) hleft
    (kernelMesh_cellLength_pos hR hRupper hh c.succ)
  simpa only [meshCellLeft, meshCellLength, add_sub_cancel] using h

theorem kernelMesh_firstCell_lower {R h₀ : ℝ} (hR : 0 < R)
    (hRupper : R ≤ 1 / 2) (hh : 0 < h₀) (hhupper : h₀ ≤ 1 / 2) :
    h₀ / 4 ≤ meshCellLength (kernelMesh R h₀) 0 := by
  obtain ⟨hblo, hbhi⟩ := kernel_endpoint_bounds hR hRupper
  have hfirst := firstCell_lower (by linarith : (0 : ℝ) < Real.sqrt (1 - R ^ 2))
    hbhi hh hhupper (kernel_logSpan_lower hR hRupper hhupper)
  simpa only [meshCellLength, kernelMesh, Fin.val_succ, Fin.val_castSucc,
    Fin.val_zero, zero_add, sub_zero, one_mul] using hfirst

/-- The source's full signed coefficient mass on the actual physical kernel mesh. -/
theorem kernel_coefficient_mass_le (n : ℕ) (hn : 2 ≤ n) {R h₀ : ℝ}
    (hR : 0 < R) (hRupper : R ≤ 1 / 2) (hh : 0 < h₀) (hhupper : h₀ ≤ 1 / 2) :
    (∑ z, |kernelValueCoefficient n (kernelMesh R h₀) z|) ≤
      40 * (n : ℝ) ^ 2 / h₀ := by
  exact sum_abs_kernelValueCoefficient_le n hn (kernelMesh R h₀)
    (kernelMesh_strictMono hR hRupper hh) (kernelMesh_zero R h₀) h₀ hh
    (kernelMesh_firstCell_lower hR hRupper hh hhupper)

/-- Exact count of kernel value locations: cell-interior nodes and the origin. -/
theorem kernelValueIndex_card (n : ℕ) {R h₀ : ℝ} (hR : 0 < R)
    (hRupper : R ≤ 1 / 2) (hh : 0 < h₀) :
    Fintype.card (Option
      (Fin ((cellCount 0 (Real.sqrt (1 - R ^ 2)) h₀ - 1) + 1) × Fin n)) =
      cellCount 0 (Real.sqrt (1 - R ^ 2)) h₀ * n + 1 := by
  have hn := kernel_cellCount_pos hR hRupper hh
  have hlast : cellCount 0 (Real.sqrt (1 - R ^ 2)) h₀ - 1 + 1 =
      cellCount 0 (Real.sqrt (1 - R ^ 2)) h₀ := by omega
  simp only [Fintype.card_option, Fintype.card_prod, Fintype.card_fin, hlast]

/-- The ceiling and the extra origin are both charged in the kernel row count. -/
theorem kernelValueIndex_card_le (n : ℕ) {R h₀ : ℝ} (hR : 0 < R)
    (hRupper : R ≤ 1 / 2) (hh : 0 < h₀) :
    (Fintype.card (Option
      (Fin ((cellCount 0 (Real.sqrt (1 - R ^ 2)) h₀ - 1) + 1) × Fin n)) : ℝ) ≤
      (logSpan 0 (Real.sqrt (1 - R ^ 2)) / h₀ + 1) * (n : ℝ) + 1 := by
  rw [kernelValueIndex_card n hR hRupper hh]
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_one]
  have hbhi := (kernel_endpoint_bounds hR hRupper).2
  have hcount : (cellCount 0 (Real.sqrt (1 - R ^ 2)) h₀ : ℝ) <
      logSpan 0 (Real.sqrt (1 - R ^ 2)) / h₀ + 1 :=
    Nat.ceil_lt_add_one
      (div_nonneg (logSpan_nonneg (Real.sqrt_nonneg _) hbhi) hh.le)
  have hmul := mul_le_mul_of_nonneg_right hcount.le (Nat.cast_nonneg n)
  linarith

end AcceleratedLogConcave.Numerics.GeometricMesh
