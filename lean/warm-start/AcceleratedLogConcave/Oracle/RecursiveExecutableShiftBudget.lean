import AcceleratedLogConcave.Oracle.RecursiveExecutableShift

/-! The original source support-height budget pays the actual recursive shift
bound. The explicit absolute constant merely enlarges the source work base;
no stronger precision-dependent or full-rank shift budget is introduced. -/
noncomputable section
namespace AcceleratedLogConcave.Oracle.RecursiveExecutable
open ChildAbsorption Precision Numerics.AffineGraph TapeLowering CovarianceSetup
variable {layers n ns inventory Hs : ℕ} {K Ds : ℝ}

/-- One explicit admissible enlargement of the manuscript's local inventory base. -/
def sourceShiftBase (layers inventory : ℕ) : ℝ :=
  100 * ((layers:ℝ)+2) * ((inventory:ℝ)+1)

theorem shiftBase_le_sourceShiftBase (hcount : n+ns ≤ inventory) :
    shiftBase layers n ns ≤ sourceShiftBase layers inventory := by
  have hc : (n:ℝ)+(ns:ℝ) ≤ inventory := by exact_mod_cast hcount
  have hN : (0:ℝ) ≤ layers := Nat.cast_nonneg _
  have hn : (0:ℝ) ≤ n := Nat.cast_nonneg _
  have hs : (0:ℝ) ≤ ns := Nat.cast_nonneg _
  have hi : (0:ℝ) ≤ inventory := Nat.cast_nonneg _
  have hm := mul_le_mul_of_nonneg_left hc (show (0:ℝ) ≤ layers+1 by positivity)
  unfold shiftBase sourceShiftBase
  push_cast
  nlinarith

/-- Quarter-precision support depth is paid by the source's padded height. -/
theorem quarterRank_le_source_height (hK : (1/2:ℝ) < K)
    (hHs : 8*K+4 ≤ (Hs:ℝ)) : precisionRank (1/4) K ≤ Hs := by
  unfold precisionRank
  apply Nat.ceil_le.mpr
  have h : (K-(1/2:ℝ))/(1/4) = 4*K-2 := by ring
  rw [h]
  linarith

/-- The manuscript's `B^(Hs+1) ≤ Ds` pays the actual finite shift-mass budget. -/
theorem source_shift_budget (hcount : n+ns ≤ inventory) (hK : (1/2:ℝ) < K)
    (hHs : 8*K+4 ≤ (Hs:ℝ))
    (hbudget : sourceShiftBase layers inventory ^ (Hs+1) ≤ Ds) :
    shiftBase layers n ns ^ precisionRank (1/4) K ≤ Ds^2 := by
  have hC := shiftBase_ge_one layers n ns
  have hCB := shiftBase_le_sourceShiftBase (layers := layers) hcount
  have hB : 1 ≤ sourceShiftBase layers inventory := hC.trans hCB
  have hRank : precisionRank (1/4) K ≤ Hs+1 :=
    (quarterRank_le_source_height hK hHs).trans (Nat.le_succ Hs)
  have hm : shiftBase layers n ns ^ precisionRank (1/4) K ≤ Ds := by
    exact ((pow_le_pow_left₀ (by linarith) hCB _).trans
      (pow_le_pow_right₀ hB hRank)).trans hbudget
  have hDs : 1 ≤ Ds := (one_le_pow₀ hB).trans hbudget
  nlinarith

/-- The actual all-precision mean shift under the manuscript support-height budget. -/
theorem source_mean_queryShift_and_mass
    (M : MeanGeometry m) (nodes : Fin n ≃ M.MeanNode)
    (anchors : Fin a ≃ M.Anchor) (seeds : Fin h ≃ Fin m × M.Kernel)
    (mesh : IntervalMesh 0 (samplingEnd (M.R/backwardEnd M.R)))
    (snodes : Fin ns ≃ mesh.Source m)
    (Ds δ t w : ℝ) (layers : ℕ) (ht : 0 < t) (htq : t ≤ 1/4)
    (K scale : ℝ) (hDs : 0 < Ds) (hpsi : M.psi ≤ M.R^4)
    (inventory Hs : ℕ) (hcount : n+ns ≤ inventory) (hK : (1/2:ℝ) < K)
    (hHs : 8*K+4 ≤ (Hs:ℝ))
    (hbudget : sourceShiftBase layers inventory ^ (Hs+1) ≤ Ds)
    (r σ q : ℝ) (hr : 0 < r) (hqK : q ≤ K) :
    let data := mean M nodes anchors seeds Ds δ t w ht htq layers mesh snodes scale r σ q
    QueryShift data.program data.enumeration data.coefficient r data.shiftVector ∧
      shiftSq data.shiftVector ≤ shiftBase layers n ns ^ precisionRank (1/4) q :=
  mean_queryShift_and_mass M nodes anchors seeds mesh snodes Ds δ t w layers ht htq
    K scale hDs hpsi (source_shift_budget hcount hK hHs hbudget) r σ q hr hqK

end AcceleratedLogConcave.Oracle.RecursiveExecutable
