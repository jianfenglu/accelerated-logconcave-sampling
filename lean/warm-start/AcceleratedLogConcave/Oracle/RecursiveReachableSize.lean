import AcceleratedLogConcave.Oracle.RecursiveCallPathSize

/-! Root-capped sufficient size and scalar row envelopes for actual occurrence
paths. These estimates do not cover unused finite-envelope parameter families. -/
noncomputable section
set_option autoImplicit false
namespace AcceleratedLogConcave.Oracle.RecursiveCall
open RecursiveSize Precision Numerics.AffineGraph
variable {m n ns : ℕ} {C : Source m n ns} {p₀ p : State} {d j : ℕ}

/-- Exact relation between the executable scalar row bound and the affine
denominator. It also holds for zero width under total division. -/
theorem source_rowBound_eq {m : ℕ} (r σ δ t w : ℝ) (hδ : 0 < δ) :
    SourceMeanExecutable.rowBound (m := m) r σ δ t w =
      256*(m:ℝ)^5*r/(σ*δ^(4*t)*δ^w)+4*r^2 := by
  have he : δ ^ (-4*t-w) = (δ^(4*t)*δ^w)⁻¹ := by
    rw [← Real.rpow_add hδ, ← Real.rpow_neg hδ.le]
    congr 1
    ring
  unfold SourceMeanExecutable.rowBound
  simp only [Real.rpow_eq_pow]
  rw [he]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

section RootCaps
variable (hp : Path C p₀ p d j) (L B : ℝ)
  (hroot : SizeBound L C.δ 1 1 p₀.radius p₀.width)
  (hm : 0 < m) (hL : 0 ≤ L) (hr : 0 < p₀.radius) (hσ : 0 < p₀.width)
  (hDs : 0 < C.Ds) (hδ : 0 < C.δ) (hδ1 : C.δ ≤ 1)
  (ht : 0 < C.t) (htq : C.t ≤ 1/4) (hw : 0 ≤ C.w) (hwt : C.w ≤ C.t) (hB : 1 ≤ B)
  (hR : C.M.R = C.δ ^ C.t) (hDsBound : C.Ds ≤ C.δ ^ (-C.t))
  (hn : Real.sqrt n ≤ B*C.δ ^ (-C.w)) (hns : Real.sqrt ns ≤ B*C.δ ^ (-C.w))
include hp hroot hm hL hr hσ hDs hδ hδ1 ht htq hw hwt hB hR hDsBound hn hns

/-- Both endpoint counts are bounded by root ranks, and C is at least one.
The endpoint estimate is derived from the root certificate, not assumed. -/
theorem Path.root_cap_size :
    SizeBound L C.δ (1-10*C.t*(precisionRank (1/4) p₀.precision : ℝ))
      ((stepFactor m B)^(precisionRank C.t p₀.precision)) p.radius p.width := by
  have hs := hp.root_size_bound L B hroot hm hL hr hσ hDs hδ hδ1 hw hwt hB hR hDsBound hn hns
  have hd := hp.depth_rank_le ht htq
  have hj := hp.cost_rank_le ht.le
  have hdepth : d ≤ precisionRank C.t p₀.precision := by omega
  have hcost : j ≤ precisionRank (1/4) p₀.precision := by omega
  have hC : 1 ≤ stepFactor m B := le_trans (by norm_num) (stepFactor_ge_three m B (by linarith))
  apply hs.mono hδ hδ1 (pow_nonneg (by linarith : 0 ≤ stepFactor m B) _)
  · have hc : (j:ℝ) ≤ (precisionRank (1/4) p₀.precision : ℝ) := by exact_mod_cast hcost
    nlinarith
  · exact pow_le_pow_right₀ hC hdepth

/-- Explicit root-dependent eta bound, valid without imposing a small-resolution
threshold. It is a finite envelope, not a uniform stability constant. -/
theorem Path.root_cap_row_envelope :
    L*SourceMeanExecutable.rowBound (m := m) p.radius p.width C.δ C.t C.w ≤
      (rowFactor m*(stepFactor m B)^(precisionRank C.t p₀.precision))*
        C.δ^(1-10*C.t*(precisionRank (1/4) p₀.precision : ℝ)-4*C.t-C.w) := by
  have hs := hp.root_cap_size L B hroot hm hL hr hσ hDs hδ hδ1 ht htq hw hwt hB hR hDsBound hn hns
  exact scaled_rowBound_le hs hδ hδ1
    (pow_nonneg (le_trans (by norm_num) (stepFactor_ge_three m B (by linarith))) _)
    ht.le hw
end RootCaps

/-- Sufficient root caps pay both the actual source row envelope and the
sampling radius-square envelope. The geometric mesh certificate is still separate. -/
theorem Path.scalar_smallness (hp : Path C p₀ p d j) (L B : ℝ)
    (hroot : SizeBound L C.δ 1 1 p₀.radius p₀.width)
    (hm : 2 ≤ m) (hL : 0 ≤ L) (hr : 0 < p₀.radius) (hσ : 0 < p₀.width)
    (hDs : 0 < C.Ds) (hδ : 0 < C.δ) (hδ1 : C.δ ≤ 1)
    (ht : 0 < C.t) (ht60 : C.t ≤ 1/60) (hw : 0 ≤ C.w) (hwt : C.w ≤ C.t) (hB : 1 ≤ B)
    (hR : C.M.R = C.δ ^ C.t) (hDsBound : C.Ds ≤ C.δ ^ (-C.t))
    (hn : Real.sqrt n ≤ B*C.δ ^ (-C.w)) (hns : Real.sqrt ns ≤ B*C.δ ^ (-C.w))
    (hcost : 10*C.t*(precisionRank (1/4) p₀.precision : ℝ) ≤ 1/2)
    (hres : C.δ ≤ (520*(m:ℝ)^5*(stepFactor m B)^(precisionRank C.t p₀.precision))^(-12:ℝ)) :
    2*L*SourceMeanExecutable.rowBound (m := m) p.radius p.width C.δ C.t C.w ≤ C.δ^((1:ℝ)/3) ∧
    2*L*p.radius^2 ≤ C.δ^((1:ℝ)/3) := by
  have hm0 : 0 < m := by omega
  have hs := hp.root_cap_size L B hroot hm0 hL hr hσ hDs hδ hδ1 ht (by linarith)
    hw hwt hB hR hDsBound hn hns
  have hpos := hp.positive hm0 hDs hδ hr hσ
  have hb : 1/2 ≤ 1-10*C.t*(precisionRank (1/4) p₀.precision : ℝ) := by linarith
  have hC : 1 ≤ stepFactor m B := le_trans (by norm_num) (stepFactor_ge_three m B (by linarith))
  have hS : 1 ≤ (stepFactor m B)^(precisionRank C.t p₀.precision) := one_le_pow₀ hC
  constructor
  · rw [source_rowBound_eq _ _ _ _ _ hδ]
    exact affine_mean_envelope_le_rpow_third hm hδ hδ1 hw hwt ht60 hb hS hpos.2
      hs.1 (by simpa only [mul_div_assoc] using hs.2) hres
  · exact affine_sampling_envelope_le_rpow_third hm hδ hδ1 hw hwt ht60 hb hS hs.1 hres

end AcceleratedLogConcave.Oracle.RecursiveCall
