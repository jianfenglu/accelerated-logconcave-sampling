import AcceleratedLogConcave.Oracle.Precision
import Mathlib.Tactic.NormNum

/-!
# Decreasing source-call ranks and source height caps

The explicit mean/sampling ranks decrease on the allowed scalar source edges.
These proofs concern the source index relation, not a constructed call graph or
the already structurally total finite-program interpreter. Full-work edges keep
every supplier. The separate support relation applies to actual recursive shifts
only after their nonzero coefficients are proved to have the supported roles.

The caps bound rank and hence the number of edges in a call chain, not its number
of nodes, local instruction count, tape length, or total work. No center, oracle,
tape, probability law, or success event occurs in these scalar statements.
-/

namespace AcceleratedLogConcave.Oracle.Precision

/-- The source scalar conditions imply the smaller step needed to pay an
explicit private sampling wrapper in the full-work rank. -/
theorem source_step_bounds {K w t : ℝ}
    (hK : 2 ≤ K) (hw : 0 < w) (hwt : w < t)
    (hsmall : 40 * (K + 2) * t < (1 / 4 : ℝ)) :
    0 < t ∧ t < (1 / 8 : ℝ) := by
  have ht : 0 < t := lt_trans hw hwt
  constructor
  · exact ht
  · nlinarith [mul_nonneg (show 0 ≤ K - 2 by linarith) ht.le]

/-- A nonterminal mean has rank at least two; its terminal private wrapper has
rank one rather than zero. -/
theorem meanFullRank_two_le {t q : ℝ} (ht : 0 < t)
    (hq : (1 / 2 : ℝ) < q) : 2 ≤ meanFullRank t q := by
  have hp := (precisionRank_pos_iff ht).2 hq
  have hnt : ¬ terminal q := not_le_of_gt hq
  simp only [meanFullRank, ite_eq_right hnt]
  omega

theorem meanFullRank_mono {t : ℝ} (ht : 0 < t) :
    Monotone (meanFullRank t) := by
  intro q q' hqq'
  by_cases hq : terminal q
  · simp only [meanFullRank, ite_eq_left hq]
    exact Nat.zero_le _
  · have hq' : ¬ terminal q' := by
      intro h
      exact hq (le_trans hqq' h)
    simp only [meanFullRank, ite_eq_right hq, ite_eq_right hq']
    exact Nat.add_le_add_right (precisionRank_mono ht hqq') 1

theorem fullRank_mean_mono {t : ℝ} (ht : 0 < t) :
    Monotone (fun q => fullRank t (.mean q)) :=
  meanFullRank_mono ht

theorem fullRank_sampling_mono {t : ℝ} (ht : 0 < t) :
    Monotone (fun q => fullRank t (.sampling q)) := by
  intro q q' hqq'
  exact Nat.add_le_add_right (meanFullRank_mono ht hqq') 1

/-- Every allowed executed role decreases full rank, including active-final
suppliers and the private sampling wrapper itself. -/
theorem CallEdge.fullRank_lt {t : ℝ} {role : EdgeRole}
    {child parent : CallIndex} (ht : 0 < t) (ht8 : t ≤ (1 / 8 : ℝ))
    (hedge : CallEdge t role child parent) :
    fullRank t child < fullRank t parent := by
  cases hedge with
  | @activeFinal q hq =>
      have hnt : ¬ terminal q := not_le_of_gt hq
      by_cases hc : terminal (q - t)
      · simp only [fullRank, meanFullRank, ite_eq_left hc, ite_eq_right hnt]
        omega
      · have hd := precisionRank_drop ht hq (le_refl (q - t))
        simp only [fullRank, meanFullRank, ite_eq_right hc, ite_eq_right hnt]
        omega
  | @mainLayer q hq =>
      have hnt : ¬ terminal q := not_le_of_gt hq
      by_cases hc : terminal (q - (1 / 4 : ℝ))
      · simp only [fullRank, meanFullRank, ite_eq_left hc, ite_eq_right hnt]
        omega
      · have hd := precisionRank_drop ht hq
          (show q - (1 / 4 : ℝ) ≤ q - t by linarith)
        simp only [fullRank, meanFullRank, ite_eq_right hc, ite_eq_right hnt]
        omega
  | @privateAnchor q hq =>
      have hnt : ¬ terminal q := not_le_of_gt hq
      by_cases hc : terminal (q - (1 / 4 : ℝ))
      · have hp := meanFullRank_two_le ht hq
        simp only [fullRank, meanFullRank, ite_eq_left hc, ite_eq_right hnt] at hp ⊢
        omega
      · have hchild : (1 / 2 : ℝ) < q - 1 / 4 := lt_of_not_ge hc
        have hd := precisionRank_drop_units 2 ht hchild
          (show q - (1 / 4 : ℝ) + (2 : ℝ) * t ≤ q by linarith)
        simp only [fullRank, meanFullRank, ite_eq_right hc, ite_eq_right hnt]
        omega
  | samplingSupplier alpha =>
      simp only [fullRank]
      omega

theorem WorkChild.rank_lt {t : ℝ} {child parent : CallIndex}
    (ht : 0 < t) (ht8 : t ≤ (1 / 8 : ℝ))
    (hedge : WorkChild t child parent) :
    fullRank t child < fullRank t parent := by
  obtain ⟨role, hedge⟩ := hedge
  exact hedge.fullRank_lt ht ht8

theorem workChild_wellFounded {t : ℝ}
    (ht : 0 < t) (ht8 : t ≤ (1 / 8 : ℝ)) :
    WellFounded (WorkChild t) := by
  apply Subrelation.wf (r := InvImage (· < ·) (fullRank t))
  · intro child parent hedge
    exact hedge.rank_lt ht ht8
  · exact InvImage.wf _ Nat.lt_wfRel.wf

/-- The root is nonterminal; its extra two units are the mean padding and the
public sampling wrapper. Positivity of `t` is needed for decrease, not this identity. -/
theorem public_fullRank_eq {K t : ℝ} (hK : (1 / 2 : ℝ) < K) :
    fullRank t (.sampling K) =
      2 + Nat.ceil ((K - (1 / 2 : ℝ)) / t) := by
  have hnt : ¬ terminal K := not_le_of_gt hK
  simp only [fullRank, meanFullRank, ite_eq_right hnt, precisionRank]
  omega

theorem public_fullRank_le {K t : ℝ} {H : ℕ} (hK : (1 / 2 : ℝ) < K)
    (hH : 2 + Nat.ceil ((K - (1 / 2 : ℝ)) / t) ≤ H) :
    fullRank t (.sampling K) ≤ H := by
  rw [public_fullRank_eq hK]
  exact hH

/-- Global cap for any mean precision below the public root. -/
theorem mean_fullRank_le {q K t : ℝ} {H : ℕ}
    (ht : 0 < t) (hK : (1 / 2 : ℝ) < K) (hq : q ≤ K)
    (hH : 2 + Nat.ceil ((K - (1 / 2 : ℝ)) / t) ≤ H) :
    fullRank t (.mean q) ≤ H := by
  have hm := meanFullRank_mono ht hq
  have hr := public_fullRank_le (t := t) hK hH
  simp only [fullRank] at hr ⊢
  omega

/-- Global cap includes private or public finite sampling wrappers. -/
theorem sampling_fullRank_le {q K t : ℝ} {H : ℕ}
    (ht : 0 < t) (hK : (1 / 2 : ℝ) < K) (hq : q ≤ K)
    (hH : 2 + Nat.ceil ((K - (1 / 2 : ℝ)) / t) ≤ H) :
    fullRank t (.sampling q) ≤ H :=
  le_trans (fullRank_sampling_mono ht hq) (public_fullRank_le hK hH)

theorem meanSupportRank_mono : Monotone meanSupportRank := by
  intro q q' hqq'
  apply Nat.mul_le_mul_left 2
  apply Nat.ceil_mono
  linarith

theorem supportRank_mean_mono : Monotone (fun q => supportRank (.mean q)) :=
  meanSupportRank_mono

theorem supportRank_sampling_mono : Monotone (fun q => supportRank (.sampling q)) := by
  intro q q' hqq'
  exact Nat.add_le_add_right (meanSupportRank_mono hqq') 1

/-- A nonterminal quarter step pays two support units, including an overshoot
past the terminal cutoff. -/
theorem meanSupportRank_quarter {q : ℝ} (hq : (1 / 2 : ℝ) < q) :
    meanSupportRank (q - 1 / 4) + 2 = meanSupportRank q := by
  have hp : 1 ≤ Nat.ceil (4 * (q - (1 / 2 : ℝ))) :=
    Nat.one_le_ceil_iff.2 (by linarith)
  have heq : 4 * (q - 1 / 4 - (1 / 2 : ℝ)) =
      4 * (q - 1 / 2) - 1 := by ring
  simp only [meanSupportRank, heq, Nat.ceil_sub_one]
  omega

/-- Potential support edges decrease without any restriction on `t`. Actual
nonzero recursive shifts must separately be shown to use these supported roles. -/
theorem SupportChild.rank_lt {t : ℝ} {child parent : CallIndex}
    (hedge : SupportChild t child parent) :
    supportRank child < supportRank parent := by
  obtain ⟨role, hrole, hedge⟩ := hedge
  cases hedge with
  | activeFinal hq => exact False.elim (hrole rfl)
  | mainLayer hq =>
      have hd := meanSupportRank_quarter hq
      simp only [supportRank]
      omega
  | privateAnchor hq =>
      have hd := meanSupportRank_quarter hq
      simp only [supportRank]
      omega
  | samplingSupplier alpha =>
      simp only [supportRank]
      omega

theorem supportChild_wellFounded (t : ℝ) :
    WellFounded (SupportChild t) := by
  apply Subrelation.wf (r := InvImage (· < ·) supportRank)
  · intro child parent hedge
    exact hedge.rank_lt
  · exact InvImage.wf _ Nat.lt_wfRel.wf

/-- A sharper scalar cap implies the manuscript's deliberately padded support
height. This remains a rank bound, not a shift-norm estimate. -/
theorem public_supportRank_lt {K : ℝ} (hK : (1 / 2 : ℝ) < K) :
    (supportRank (.sampling K) : ℝ) < 8 * K - 1 := by
  have hc := Nat.ceil_lt_add_one (show 0 ≤ 4 * (K - (1 / 2 : ℝ)) by linarith)
  simp only [supportRank, meanSupportRank, Nat.cast_add, Nat.cast_mul,
    Nat.cast_ofNat, Nat.cast_one]
  linarith

theorem public_supportRank_le {K : ℝ} {Hs : ℕ} (hK : (1 / 2 : ℝ) < K)
    (hHs : 8 * K + 4 ≤ (Hs : ℝ)) :
    supportRank (.sampling K) ≤ Hs := by
  have hc := public_supportRank_lt hK
  exact_mod_cast (show (supportRank (.sampling K) : ℝ) ≤ (Hs : ℝ) by linarith)

theorem mean_supportRank_le {q K : ℝ} {Hs : ℕ}
    (hK : (1 / 2 : ℝ) < K) (hq : q ≤ K)
    (hHs : 8 * K + 4 ≤ (Hs : ℝ)) : supportRank (.mean q) ≤ Hs := by
  have hm := meanSupportRank_mono hq
  have hr := public_supportRank_le hK hHs
  simp only [supportRank] at hr ⊢
  omega

theorem sampling_supportRank_le {q K : ℝ} {Hs : ℕ}
    (hK : (1 / 2 : ℝ) < K) (hq : q ≤ K)
    (hHs : 8 * K + 4 ≤ (Hs : ℝ)) : supportRank (.sampling q) ≤ Hs :=
  le_trans (supportRank_sampling_mono hq) (public_supportRank_le hK hHs)

private theorem decreasing_chain_bound (r : ℕ → ℕ) (n : ℕ) :
    (∀ i, i < n → r (i + 1) < r i) → n + r n ≤ r 0 := by
  induction n with
  | zero =>
      intro _
      simp
  | succ n ih =>
      intro hstep
      have hp := ih (fun i hi => hstep i (Nat.lt_succ_of_lt hi))
      have hl := hstep n (Nat.lt_succ_self n)
      omega

/-- A finite prefix of allowed work calls consumes at least one full-rank unit
per edge. The sequence has `n + 1` vertices; this is not a vertex-count bound. -/
theorem work_chain_rank_add_le {t : ℝ} (ht : 0 < t)
    (ht8 : t ≤ (1 / 8 : ℝ)) (x : ℕ → CallIndex) (n : ℕ)
    (hstep : ∀ i, i < n → WorkChild t (x (i + 1)) (x i)) :
    n + fullRank t (x n) ≤ fullRank t (x 0) := by
  apply decreasing_chain_bound (fun i => fullRank t (x i)) n
  intro i hi
  exact (hstep i hi).rank_lt ht ht8

/-- Bounds only the number of edges in an abstract finite call chain. Combine
with a source rank cap for `x 0` to obtain `n ≤ H`; no graph is constructed. -/
theorem work_chain_edges_le {t : ℝ} (ht : 0 < t)
    (ht8 : t ≤ (1 / 8 : ℝ)) (x : ℕ → CallIndex) (n : ℕ)
    (hstep : ∀ i, i < n → WorkChild t (x (i + 1)) (x i)) :
    n ≤ fullRank t (x 0) := by
  have h := work_chain_rank_add_le ht ht8 x n hstep
  omega

/-- This finite-chain bound concerns potential supported roles. Its application
to an actual shift still requires the nonzero-coefficient correspondence. -/
theorem support_chain_rank_add_le {t : ℝ} (x : ℕ → CallIndex) (n : ℕ)
    (hstep : ∀ i, i < n → SupportChild t (x (i + 1)) (x i)) :
    n + supportRank (x n) ≤ supportRank (x 0) := by
  apply decreasing_chain_bound (fun i => supportRank (x i)) n
  intro i hi
  exact (hstep i hi).rank_lt

/-- Counts edges rather than vertices, with no claim about total work or shifts. -/
theorem support_chain_edges_le {t : ℝ} (x : ℕ → CallIndex) (n : ℕ)
    (hstep : ∀ i, i < n → SupportChild t (x (i + 1)) (x i)) :
    n ≤ supportRank (x 0) := by
  have h := support_chain_rank_add_le x n hstep
  omega

end AcceleratedLogConcave.Oracle.Precision
