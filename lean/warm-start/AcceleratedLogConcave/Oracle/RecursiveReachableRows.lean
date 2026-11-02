import AcceleratedLogConcave.Oracle.RecursiveReachableSize

/-! Actual matrix-row smallness at occurrence-reachable mean states, from a
root size certificate and explicit static schedule caps. The backward partition
identity and half-step cap are independent geometric premises. -/
noncomputable section
open scoped BigOperators
set_option autoImplicit false
namespace AcceleratedLogConcave.Oracle.RecursiveCall
open RecursiveSize Precision Numerics.AffineGraph
variable {m n ns : ℕ} {C : Source m n ns} {p₀ p : State} {d j : ℕ}

/-- The actual geometric first-width theorem is used by the existing row
supplier. No row bound or first-width conclusion is assumed here. -/
theorem Source.matrix_row_le_source_bound (C : Source m n ns)
    (hm : 2 ≤ m) (r σ : ℝ) (hr : 0 ≤ r) (hσ : 0 < σ)
    (hδ : 0 < C.δ) (hδ1 : C.δ ≤ 1) (ht : 0 ≤ C.t)
    (hpsi : C.M.psi = C.δ^(4*C.t)) (hhalf : C.δ^C.w ≤ 1/2)
    (hback : C.M.backward = actualKernelInterval C.M.R (C.δ^C.w)
      C.M.R_pos C.M.R_le_half (Real.rpow_pos_of_pos hδ C.w)) (i : C.M.MeanNode) :
    (∑ u, |C.M.matrix r σ i u|) ≤ SourceMeanExecutable.rowBound (m := m) r σ C.δ C.t C.w := by
  have hpsi1 : C.M.psi ≤ 1 := by
    rw [hpsi]
    exact Real.rpow_le_one hδ.le hδ1 (by positivity)
  rw [source_rowBound_eq _ _ _ _ _ hδ]
  simpa only [hpsi] using C.M.sum_abs_matrix_le_actual hm r σ hr hσ hpsi1
    (C.δ^C.w) (Real.rpow_pos_of_pos hδ C.w) hhalf hback i

section Reachable
variable (hp : Path C p₀ p d j) (L B : ℝ)
  (hroot : SizeBound L C.δ 1 1 p₀.radius p₀.width)
  (hm : 2 ≤ m) (hL : 0 ≤ L) (hr : 0 < p₀.radius) (hσ : 0 < p₀.width)
  (hDs : 0 < C.Ds) (hδ : 0 < C.δ) (hδ1 : C.δ ≤ 1)
  (ht : 0 < C.t) (ht60 : C.t ≤ 1/60) (hw : 0 ≤ C.w) (hwt : C.w ≤ C.t) (hB : 1 ≤ B)
  (hR : C.M.R = C.δ ^ C.t) (hDsBound : C.Ds ≤ C.δ ^ (-C.t))
  (hn : Real.sqrt n ≤ B*C.δ ^ (-C.w)) (hns : Real.sqrt ns ≤ B*C.δ ^ (-C.w))
  (hcost : 10*C.t*(precisionRank (1/4) p₀.precision : ℝ) ≤ 1/2)
  (hres : C.δ ≤ (520*(m:ℝ)^5*(stepFactor m B)^(precisionRank C.t p₀.precision))^(-12:ℝ))
  (hpsi : C.M.psi = C.δ^(4*C.t)) (hhalf : C.δ^C.w ≤ 1/2)
  (hback : C.M.backward = actualKernelInterval C.M.R (C.δ^C.w)
    C.M.R_pos C.M.R_le_half (Real.rpow_pos_of_pos hδ C.w))
include hp hroot hm hL hr hσ hDs hδ hδ1 ht ht60 hw hwt hB hR hDsBound hn hns
  hcost hres hpsi hhalf hback

/-- Every actual endpoint row is paid by root caps, with the factor 2L
retained. Positive endpoint width is derived along the path. -/
theorem Path.actual_rows_small :
    (∀ i : C.M.MeanNode, 2*L*(∑ u, |C.M.matrix p.radius p.width i u|) ≤ C.δ^((1:ℝ)/3)) ∧
    2*L*p.radius^2 ≤ C.δ^((1:ℝ)/3) := by
  have hs := hp.scalar_smallness L B hroot hm hL hr hσ hDs hδ hδ1 ht ht60 hw hwt hB
    hR hDsBound hn hns hcost hres
  have hpos := hp.positive (by omega) hDs hδ hr hσ
  refine ⟨fun i => ?_, hs.2⟩
  exact (mul_le_mul_of_nonneg_left
    (C.matrix_row_le_source_bound hm p.radius p.width hpos.1.le hpos.2 hδ hδ1 ht.le
      hpsi hhalf hback i) (mul_nonneg (by norm_num) hL)).trans hs.1

/-- Reindex onto the literal finite matrix supplied to the executable main table. -/
theorem Path.indexed_rows_small :
    (∀ i : Fin n, 2*L*(∑ u : Fin n, |C.M.matrix p.radius p.width (C.nodes i) (C.nodes u)|) ≤
      C.δ^((1:ℝ)/3)) ∧ 2*L*p.radius^2 ≤ C.δ^((1:ℝ)/3) := by
  have hs := hp.actual_rows_small L B hroot hm hL hr hσ hDs hδ hδ1 ht ht60 hw hwt hB
    hR hDsBound hn hns hcost hres hpsi hhalf hback
  refine ⟨fun i => ?_, hs.2⟩
  rw [C.nodes.sum_comp (fun u => |C.M.matrix p.radius p.width (C.nodes i) u|)]
  exact hs.1 (C.nodes i)
end Reachable

end AcceleratedLogConcave.Oracle.RecursiveCall
