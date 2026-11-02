import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.RCLike

noncomputable section
open Set Metric Function
open scoped Topology ContDiff
namespace AcceleratedLogConcave.Conditional.Transport

/-- A globally smooth time map agrees with time on the chosen compact
interval and takes every real argument strictly inside `(-1,1)`. -/
theorem exists_smooth_timeClamp {a b : ℝ} (hab : a ≤ b) (ha : -1 < a) (hb : b < 1) :
    ∃ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ ∧ (∀ t, -1 < ψ t ∧ ψ t < 1) ∧
      EqOn ψ id (Icc a b) := by
  let c := max |a| |b|
  have hc : 0 ≤ c := (abs_nonneg a).trans (le_max_left _ _)
  have hc' : c < 1 := by
    apply max_lt_iff.mpr
    exact ⟨abs_lt.mpr ⟨ha,hab.trans_lt hb⟩,abs_lt.mpr ⟨ha.trans_le hab,hb⟩⟩
  let χ : ContDiffBump (0:ℝ) :=
    {rIn := (c+1)/2, rOut := (c+3)/4, rIn_pos := by linarith,
      rIn_lt_rOut := by linarith}
  refine ⟨fun t => χ t*t,χ.contDiff.mul contDiff_id,fun t => ?_,fun t ht => ?_⟩
  · by_cases hz : χ t = 0
    · simp only [hz,zero_mul]; norm_num
    · have hmem : t ∈ ball (0:ℝ) χ.rOut := by
        rw [← χ.support_eq]
        exact hz
      have ht : |t| < (c+3)/4 := by simpa only [mem_ball,dist_zero_right,Real.norm_eq_abs] using hmem
      have hh : |χ t*t| ≤ |t| := by
        rw [abs_mul,abs_of_nonneg χ.nonneg]
        simpa only [one_mul] using mul_le_mul_of_nonneg_right χ.le_one (abs_nonneg t)
      exact abs_lt.mp (hh.trans_lt (by linarith))
  · have ht' : |t| ≤ c := by
      apply abs_le.mpr
      have haa : -c ≤ a := by dsimp [c]; linarith [neg_le_abs a,le_max_left |a| |b|]
      have hbb : b ≤ c := (le_abs_self b).trans (le_max_right _ _)
      exact ⟨haa.trans ht.1,ht.2.trans hbb⟩
    have hχ : χ t = 1 := χ.one_of_mem_closedBall (by
      simp only [mem_closedBall_zero_iff,Real.norm_eq_abs]
      change |t| ≤ (c+1)/2
      linarith)
    simp only [hχ,one_mul,id_eq]

end AcceleratedLogConcave.Conditional.Transport
