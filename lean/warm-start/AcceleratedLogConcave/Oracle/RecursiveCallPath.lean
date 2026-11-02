import AcceleratedLogConcave.Oracle.RecursiveCallOccurrence

/-! Finite paths through actual occurrence-tagged source calls. Total depth and
quarter-cost depth are separate, including when the active-final drop equals 1/4.
Ranks use ceilings and allow the last call to overshoot the terminal cutoff. -/
noncomputable section
set_option autoImplicit false
namespace AcceleratedLogConcave.Oracle.RecursiveCall
open Precision
variable {m n ns : ℕ} {C : Source m n ns}

/-- Counts are accumulated from tags; an active-final call costs zero quarter charges. -/
inductive Path (C : Source m n ns) : State → State → ℕ → ℕ → Prop
  | refl (p : State) : Path C p p 0 0
  | snoc {p₀ p c : State} {d j : ℕ} (path : Path C p₀ p d j)
      (o : Occurrence C.layers n ns m) (edge : Edge C p o c) :
      Path C p₀ c (d + 1) (j + o.cost)

theorem Edge.rank_drop {p c : State} {o : Occurrence C.layers n ns m}
    (h : Edge C p o c) (ht : 0 < C.t) (htq : C.t ≤ 1/4) :
    precisionRank C.t c.precision + 1 ≤ precisionRank C.t p.precision := by
  apply precisionRank_drop ht h.1
  rw [h.precision_eq]
  rcases o with (⟨k, i⟩ | i) | (⟨k, i⟩ | i) <;>
    simp only [Occurrence.cost, Nat.cast_one, Nat.cast_zero] <;> linarith

theorem Edge.cost_rank_drop {p c : State} {o : Occurrence C.layers n ns m}
    (h : Edge C p o c) (ht : 0 ≤ C.t) :
    o.cost + precisionRank (1/4) c.precision ≤ precisionRank (1/4) p.precision := by
  have hq := h.1
  rcases h with ⟨_, rfl⟩
  rcases o with (⟨k, i⟩ | i) | (⟨k, i⟩ | i)
  all_goals simp only [Occurrence.cost, Source.child, zero_add]
  · have hd := precisionRank_drop (step := (1/4 : ℝ)) (by norm_num) hq le_rfl
    omega
  · have hd := precisionRank_drop (step := (1/4 : ℝ)) (by norm_num) hq le_rfl
    omega
  · have hd := precisionRank_drop (step := (1/4 : ℝ)) (by norm_num) hq le_rfl
    omega
  · exact precisionRank_mono (by norm_num) (sub_le_self _ ht)

theorem Path.cost_le_depth {p₀ p : State} {d j : ℕ} (h : Path C p₀ p d j) : j ≤ d := by
  induction h with
  | refl => omega
  | snoc h o he ih => have hc := o.cost_le_one; omega

theorem Path.precision_eq_real {p₀ p : State} {d j : ℕ} (h : Path C p₀ p d j) :
    p.precision = p₀.precision - (j : ℝ)/4 - ((d : ℝ) - (j : ℝ))*C.t := by
  induction h with
  | refl => simp
  | snoc h o he ih => rw [he.precision_eq, ih]; push_cast; ring

/-- Exact charge accounting, with a natural count of the active-final calls. -/
theorem Path.precision_eq {p₀ p : State} {d j : ℕ} (h : Path C p₀ p d j) :
    p.precision = p₀.precision - (j : ℝ)/4 - ((d - j : ℕ) : ℝ)*C.t := by
  rw [Nat.cast_sub h.cost_le_depth]
  exact h.precision_eq_real

theorem Path.depth_rank_le {p₀ p : State} {d j : ℕ} (h : Path C p₀ p d j)
    (ht : 0 < C.t) (htq : C.t ≤ 1/4) :
    d + precisionRank C.t p.precision ≤ precisionRank C.t p₀.precision := by
  induction h with
  | refl => simp
  | snoc h o he ih => have hd := he.rank_drop ht htq; omega

theorem Path.cost_rank_le {p₀ p : State} {d j : ℕ} (h : Path C p₀ p d j)
    (ht : 0 ≤ C.t) :
    j + precisionRank (1/4) p.precision ≤ precisionRank (1/4) p₀.precision := by
  induction h with
  | refl => simp
  | snoc h o he ih => have hd := he.cost_rank_drop ht; omega

/-- The ceiling is necessary: the final quarter call can cross the cutoff. -/
theorem Path.cost_le_ceil {p₀ p : State} {d j : ℕ} (h : Path C p₀ p d j)
    (ht : 0 ≤ C.t) : j ≤ Nat.ceil (4 * (p₀.precision - 1/2)) := by
  have hb := h.cost_rank_le ht
  have he : precisionRank (1/4) p₀.precision = Nat.ceil (4 * (p₀.precision - 1/2)) := by
    unfold precisionRank
    congr 1
    ring
  rw [he] at hb
  omega

theorem Path.terminal_root {p₀ p : State} {d j : ℕ} (h : Path C p₀ p d j)
    (ht : 0 < C.t) (htq : C.t ≤ 1/4) (hq : p₀.precision ≤ 1/2) : d = 0 ∧ j = 0 := by
  have hr : precisionRank C.t p₀.precision = 0 := (precisionRank_zero_iff ht).2 hq
  have hd := h.depth_rank_le ht htq
  have hj := h.cost_le_depth
  omega

theorem Path.positive {p₀ p : State} {d j : ℕ} (h : Path C p₀ p d j)
    (hm : 0 < m) (hDs : 0 < C.Ds) (hδ : 0 < C.δ)
    (hr : 0 < p₀.radius) (hσ : 0 < p₀.width) : 0 < p.radius ∧ 0 < p.width := by
  induction h with
  | refl => exact ⟨hr, hσ⟩
  | snoc h o he ih => exact he.positive hm hDs hδ ih.1 ih.2

end AcceleratedLogConcave.Oracle.RecursiveCall
