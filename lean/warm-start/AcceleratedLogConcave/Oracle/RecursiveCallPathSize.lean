import AcceleratedLogConcave.Oracle.RecursiveCallPath
import AcceleratedLogConcave.Oracle.RecursiveSizePropagation

/-! Sufficient source-schedule size accounting along actual call paths.
Every edge pays one factor C; only the three quarter-cost tags lose 10t in
the exponent. This is not a uniform stability or schedule-closure theorem. -/
noncomputable section
set_option autoImplicit false
namespace AcceleratedLogConcave.Oracle.RecursiveCall
open RecursiveSize Precision
variable {m n ns : ℕ} {C : Source m n ns}

theorem Edge.size_bound {p c : State} {o : Occurrence C.layers n ns m}
    (he : Edge C p o c) (lam b s B : ℝ)
    (h : SizeBound lam C.δ b s p.radius p.width)
    (hlam : 0 ≤ lam) (hs : 0 ≤ s) (hr : 0 < p.radius) (hσ : 0 < p.width)
    (hDs : 0 < C.Ds) (hδ : 0 < C.δ) (hδ1 : C.δ ≤ 1)
    (hw : 0 ≤ C.w) (hwt : C.w ≤ C.t) (hB : 1 ≤ B)
    (hR : C.M.R = C.δ ^ C.t) (hDsBound : C.Ds ≤ C.δ ^ (-C.t))
    (hn : Real.sqrt n ≤ B * C.δ ^ (-C.w))
    (hns : Real.sqrt ns ≤ B * C.δ ^ (-C.w)) :
    SizeBound lam C.δ (b - 10*C.t*(o.cost : ℝ)) (stepFactor m B*s) c.radius c.width := by
  have hh := source_children_size C.M C.nodes C.S C.snodes
    lam C.δ b s p.radius p.width C.Ds C.t C.w B h hlam hs hr hσ hDs hδ hδ1 hw hwt hB
    hR rfl hDsBound hn hns
  rcases he with ⟨_, rfl⟩
  rcases o with (⟨k, i⟩ | i) | (⟨k, i⟩ | i)
  all_goals simp only [Occurrence.cost, Nat.cast_one, Nat.cast_zero, mul_one, mul_zero,
    sub_zero, Source.child]
  · exact hh.2.2.1 i
  · exact hh.2.2.2 i
  · exact hh.1 i
  · exact hh.2.1.mono hδ hδ1 (mul_nonneg (by norm_num) hs) le_rfl
      (mul_le_mul_of_nonneg_right (stepFactor_ge_three m B (by linarith)) hs)

/-- General initial exponent and amplitude. All intermediate positive domains
are derived from the root and the actual width suppliers. -/
theorem Path.size_bound {p₀ p : State} {d j : ℕ} (hp : Path C p₀ p d j)
    (lam b₀ s₀ B : ℝ) (hroot : SizeBound lam C.δ b₀ s₀ p₀.radius p₀.width)
    (hm : 0 < m) (hlam : 0 ≤ lam) (hs₀ : 0 ≤ s₀)
    (hr : 0 < p₀.radius) (hσ : 0 < p₀.width) (hDs : 0 < C.Ds)
    (hδ : 0 < C.δ) (hδ1 : C.δ ≤ 1) (hw : 0 ≤ C.w) (hwt : C.w ≤ C.t) (hB : 1 ≤ B)
    (hR : C.M.R = C.δ ^ C.t) (hDsBound : C.Ds ≤ C.δ ^ (-C.t))
    (hn : Real.sqrt n ≤ B * C.δ ^ (-C.w))
    (hns : Real.sqrt ns ≤ B * C.δ ^ (-C.w)) :
    SizeBound lam C.δ (b₀ - 10*C.t*(j : ℝ)) ((stepFactor m B)^d*s₀) p.radius p.width := by
  have hC : 0 ≤ stepFactor m B := le_trans (by norm_num) (stepFactor_ge_three m B (by linarith))
  induction hp with
  | refl => simpa using hroot
  | @snoc p c d j hp o he ih =>
      have hpos := hp.positive hm hDs hδ hr hσ
      have hh := he.size_bound lam (b₀ - 10*C.t*(j : ℝ)) ((stepFactor m B)^d*s₀) B ih
        hlam (mul_nonneg (pow_nonneg hC _) hs₀) hpos.1 hpos.2
        hDs hδ hδ1 hw hwt hB hR hDsBound hn hns
      convert hh using 1
      · push_cast
        ring
      · rw [pow_succ]
        ring

/-- The requested root certificate, without a supplied descendant estimate. -/
theorem Path.root_size_bound {p₀ p : State} {d j : ℕ} (hp : Path C p₀ p d j)
    (lam B : ℝ) (hroot : SizeBound lam C.δ 1 1 p₀.radius p₀.width)
    (hm : 0 < m) (hlam : 0 ≤ lam) (hr : 0 < p₀.radius) (hσ : 0 < p₀.width)
    (hDs : 0 < C.Ds) (hδ : 0 < C.δ) (hδ1 : C.δ ≤ 1)
    (hw : 0 ≤ C.w) (hwt : C.w ≤ C.t) (hB : 1 ≤ B)
    (hR : C.M.R = C.δ ^ C.t) (hDsBound : C.Ds ≤ C.δ ^ (-C.t))
    (hn : Real.sqrt n ≤ B * C.δ ^ (-C.w))
    (hns : Real.sqrt ns ≤ B * C.δ ^ (-C.w)) :
    SizeBound lam C.δ (1 - 10*C.t*(j : ℝ)) ((stepFactor m B)^d) p.radius p.width := by
  simpa using hp.size_bound lam 1 1 B hroot hm hlam (by norm_num) hr hσ hDs
    hδ hδ1 hw hwt hB hR hDsBound hn hns

/-- Joint finite certificate. Positive widths, both rank charges and size are
proved; no uniform stability constant or descendant smallness is inferred. -/
theorem Path.certificate {p₀ p : State} {d j : ℕ} (hp : Path C p₀ p d j)
    (lam B : ℝ) (hroot : SizeBound lam C.δ 1 1 p₀.radius p₀.width)
    (hm : 0 < m) (hlam : 0 ≤ lam) (hr : 0 < p₀.radius) (hσ : 0 < p₀.width)
    (hDs : 0 < C.Ds) (hδ : 0 < C.δ) (hδ1 : C.δ ≤ 1)
    (ht : 0 < C.t) (htq : C.t ≤ 1/4) (hw : 0 ≤ C.w) (hwt : C.w ≤ C.t) (hB : 1 ≤ B)
    (hR : C.M.R = C.δ ^ C.t) (hDsBound : C.Ds ≤ C.δ ^ (-C.t))
    (hn : Real.sqrt n ≤ B * C.δ ^ (-C.w))
    (hns : Real.sqrt ns ≤ B * C.δ ^ (-C.w)) :
    j ≤ d ∧
    p.precision = p₀.precision - (j : ℝ)/4 - ((d-j : ℕ) : ℝ)*C.t ∧
    d + precisionRank C.t p.precision ≤ precisionRank C.t p₀.precision ∧
    j + precisionRank (1/4) p.precision ≤ precisionRank (1/4) p₀.precision ∧
    (0 < p.radius ∧ 0 < p.width) ∧
    SizeBound lam C.δ (1 - 10*C.t*(j : ℝ)) ((stepFactor m B)^d) p.radius p.width :=
  ⟨hp.cost_le_depth, hp.precision_eq, hp.depth_rank_le ht htq, hp.cost_rank_le ht.le,
    hp.positive hm hDs hδ hr hσ,
    hp.root_size_bound lam B hroot hm hlam hr hσ hDs hδ hδ1 hw hwt hB hR hDsBound hn hns⟩

end AcceleratedLogConcave.Oracle.RecursiveCall
