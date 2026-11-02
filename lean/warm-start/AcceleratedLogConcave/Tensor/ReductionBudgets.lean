import AcceleratedLogConcave.Tensor.AdjointReduction
import AcceleratedLogConcave.Tensor.Expressions

/-!
# Structural reduction budgets

These budgets concern the existing structural scheduler only. They neither
supply a coordinate-network interpretation nor count distinct routing records.
Labels are lists: repeated labels contribute with their full multiplicity.
-/

open scoped NNReal

namespace AcceleratedLogConcave.Tensor.AdjointReduction

variable {Name Label E : Type*} {σ : CoefficientSignature Name}

namespace Pending

/-- Formula size including outside derivatives; a score is a differentiated Hessian. -/
def sizeBudget : Pending σ Label E → ℕ
  | .formula e J => e.size + J.length
  | .score _ J _ => J.length + 1

/-- Outside labels plus the still-unexpanded derivative and adjoint operations. -/
def labelBudget : Pending σ Label E → ℕ
  | .formula e J => J.length + e.weightedOperationCount
  | .score _ J _ => J.length

/-- A nonempty score group of length `k` has Hessian smoothing weight `k - 1`.
The subtraction is in naturals before casting. -/
def smoothingBudget : Pending σ Label E → ℝ≥0
  | .formula e J => e.weight + J.length
  | .score _ J _ => (J.length - 1 : ℕ)

@[simp] theorem sizeBudget_decorate (i : Label) (p : Pending σ Label E) :
    (p.decorate i).sizeBudget = p.sizeBudget + 1 := by
  cases p <;> simp [decorate, sizeBudget, add_assoc, add_comm, add_left_comm]

@[simp] theorem labelBudget_decorate (i : Label) (p : Pending σ Label E) :
    (p.decorate i).labelBudget = p.labelBudget + 1 := by
  cases p <;> simp [decorate, labelBudget, add_assoc, add_comm, add_left_comm]

@[simp] theorem smoothingBudget_decorate (i : Label) (p : Pending σ Label E) :
    (p.decorate i).smoothingBudget = p.smoothingBudget + 1 := by
  cases p with
  | formula e J => simp [decorate, smoothingBudget, Nat.cast_add, add_assoc]
  | score v J hJ =>
    have hpos : 0 < J.length := List.length_pos_iff.mpr hJ
    have hlen : J.length - 1 + 1 = J.length := by omega
    simp only [decorate, smoothingBudget, List.length_cons, Nat.add_sub_cancel]
    exact_mod_cast hlen.symm

end Pending

def forestSize (s : List (Pending σ Label E)) : ℕ := (s.map Pending.sizeBudget).sum

def forestLabels (s : List (Pending σ Label E)) : ℕ := (s.map Pending.labelBudget).sum

def forestSmoothing (s : List (Pending σ Label E)) : ℝ≥0 :=
  (s.map Pending.smoothingBudget).sum

/-- Score routes conserve the length of the original list, without deduplication. -/
theorem scoreRoute_length (J : List Label) (A B : List Label)
    (h : (A, B) ∈ scoreRoutes J) : A.length + B.length = J.length := by
  exact route_length J (A, B) (by rw [routes_eq]; exact List.mem_cons_of_mem _ h)

/-- Correlated exact changes: respectively a preserving step, contraction,
or a score-producing step. This is only a numerical classification; it does
not reconstruct the erased origin of a scheduler occurrence. -/
theorem step_budget_cases {s t : List (Pending σ Label E)} (h : Step t s) :
    (forestSize t = forestSize s ∧ forestLabels t = forestLabels s ∧
      forestSmoothing t = forestSmoothing s) ∨
    (forestSize t + 1 = forestSize s ∧ forestLabels t = forestLabels s ∧
      forestSmoothing t = forestSmoothing s) ∨
    (forestSize t = forestSize s ∧ forestLabels t + 1 = forestLabels s ∧
      forestSmoothing t + 2 = forestSmoothing s) := by
  cases h with
  | permute =>
    left
    simp [forestSize, forestLabels, forestSmoothing, Pending.sizeBudget,
      Pending.labelBudget, Pending.smoothingBudget, Expr.size,
      Expr.weightedOperationCount, Expr.weight]
  | derivative =>
    left
    simp only [forestSize, forestLabels, forestSmoothing, List.map_append,
      List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil,
      Pending.sizeBudget, Pending.labelBudget, Pending.smoothingBudget,
      Expr.size, Expr.weightedOperationCount, Expr.weight,
      List.length_append, List.length_cons, List.length_nil]
    refine ⟨by omega, by omega, ?_⟩
    push_cast
    ring
  | contract e f i j J A B route before after =>
    have hr : A.length + B.length = J.length := route_length J (A, B) route
    have hrw : (A.length : ℝ≥0) + B.length = J.length := by exact_mod_cast hr
    right; left
    simp only [forestSize, forestLabels, forestSmoothing, List.map_append,
      List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil,
      Pending.sizeBudget, Pending.labelBudget, Pending.smoothingBudget,
      Expr.size, Expr.weightedOperationCount, Expr.weight]
    refine ⟨by omega, by omega, ?_⟩
    linear_combination hrw
  | score e i v J A B route before after =>
    have hr := scoreRoute_length J A B route
    have hp : 0 < A.length := List.length_pos_iff.mpr
      (scoreRoutes_left_ne_nil J (A, B) route)
    have hrw : ((A.length - 1 : ℕ) : ℝ≥0) + B.length + 1 = J.length := by
      exact_mod_cast (show A.length - 1 + B.length + 1 = J.length by omega)
    right; right
    simp only [forestSize, forestLabels, forestSmoothing, List.map_append,
      List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil,
      Pending.sizeBudget, Pending.labelBudget, Pending.smoothingBudget,
      Expr.size, Expr.weightedOperationCount, Expr.weight]
    refine ⟨by omega, by omega, ?_⟩
    linear_combination hrw
  | ibpAfter | ibpBefore =>
    left
    simp only [forestSize, forestLabels, forestSmoothing, List.map_append,
      List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil]
    rw [Pending.sizeBudget_decorate, Pending.labelBudget_decorate,
      Pending.smoothingBudget_decorate]
    simp only [Pending.sizeBudget, Pending.labelBudget, Pending.smoothingBudget,
      Expr.size, Expr.weightedOperationCount, Expr.weight]
    exact ⟨by omega, by omega, by ring⟩

/-- Every step either preserves size or drops exactly one unit. -/
theorem step_size_exact {s t : List (Pending σ Label E)} (h : Step t s) :
    forestSize t = forestSize s ∨ forestSize t + 1 = forestSize s := by
  rcases step_budget_cases h with hp | hc | hq
  · exact Or.inl hp.1
  · exact Or.inr hc.1
  · exact Or.inl hq.1

/-- Every step either preserves the label budget or drops exactly one unit. -/
theorem step_labels_exact {s t : List (Pending σ Label E)} (h : Step t s) :
    forestLabels t = forestLabels s ∨ forestLabels t + 1 = forestLabels s := by
  rcases step_budget_cases h with hp | hc | hq
  · exact Or.inl hp.2.1
  · exact Or.inl hc.2.1
  · exact Or.inr hq.2.1

/-- Every step either preserves smoothing weight or drops exactly two units. -/
theorem step_smoothing_exact {s t : List (Pending σ Label E)} (h : Step t s) :
    forestSmoothing t = forestSmoothing s ∨
      forestSmoothing t + 2 = forestSmoothing s := by
  rcases step_budget_cases h with hp | hc | hq
  · exact Or.inl hp.2.2
  · exact Or.inl hc.2.2
  · exact Or.inr hq.2.2

/-- Exact cumulative losses along an arbitrary finite reduction. The natural
numbers `c` and `q` record the contraction and score losses numerically; no
injective routing-record encoding is asserted. -/
theorem steps_budget_losses {n : ℕ} {s t : List (Pending σ Label E)}
    (h : Steps n s t) :
    ∃ c q : ℕ, c + q ≤ n ∧ forestSize t + c = forestSize s ∧
      forestLabels t + q = forestLabels s ∧
      forestSmoothing t + 2 * (q : ℝ≥0) = forestSmoothing s := by
  induction h with
  | zero s => exact ⟨0, 0, by simp⟩
  | succ first rest ih =>
    obtain ⟨c, q, hn, hs, hl, hw⟩ := ih
    rcases step_budget_cases first with ⟨hfs, hfl, hfw⟩ |
      ⟨hfs, hfl, hfw⟩ | ⟨hfs, hfl, hfw⟩
    · exact ⟨c, q, by omega, by omega, by omega, hw.trans hfw⟩
    · exact ⟨c + 1, q, by omega, by omega, by omega, hw.trans hfw⟩
    · refine ⟨c, q + 1, by omega, by omega, by omega, ?_⟩
      push_cast
      linear_combination hw + hfw

/-- The three budgets are nonincreasing for every concrete step. -/
theorem step_budgets_le {s t : List (Pending σ Label E)} (h : Step t s) :
    forestSize t ≤ forestSize s ∧ forestLabels t ≤ forestLabels s ∧
      forestSmoothing t ≤ forestSmoothing s := by
  refine ⟨?_, ?_, ?_⟩
  · rcases step_size_exact h with he | he <;> omega
  · rcases step_labels_exact h with he | he <;> omega
  · rcases step_smoothing_exact h with he | he
    · exact le_of_eq he
    · rw [← he]; exact le_add_of_nonneg_right (by positivity)

/-- All budgets are nonincreasing along the existing `Steps` relation. -/
theorem steps_budgets_le {n : ℕ} {s t : List (Pending σ Label E)} (h : Steps n s t) :
    forestSize t ≤ forestSize s ∧ forestLabels t ≤ forestLabels s ∧
      forestSmoothing t ≤ forestSmoothing s := by
  induction h with
  | zero => exact ⟨le_rfl, le_rfl, le_rfl⟩
  | succ first rest ih =>
    obtain ⟨hs, hl, hw⟩ := step_budgets_le first
    exact ⟨ih.1.trans hs, ih.2.1.trans hl, ih.2.2.trans hw⟩

/-- Every expression starts from coefficients of size at least two. -/
theorem expression_size_two_le {r : ℕ} (e : Expr σ r) : 2 ≤ e.size := by
  induction e with
  | coefficient c => exact (σ.two_le_arity c).trans (σ.arity_le_size c)
  | permute p e ih => exact ih
  | contract e f i j ih₁ ih₂ => simp only [Expr.size]; omega
  | derivative e ih => simp only [Expr.size]; omega
  | adjoint i e ih => simp only [Expr.size]; omega

theorem weightedOperationCount_le_size {r : ℕ} (e : Expr σ r) :
    e.weightedOperationCount ≤ e.size := by
  induction e <;> simp_all [Expr.weightedOperationCount, Expr.size]; omega

namespace Pending

theorem sizeBudget_two_le (p : Pending σ Label E) : 2 ≤ p.sizeBudget := by
  cases p with
  | formula e J => have := expression_size_two_le e; simp only [sizeBudget]; omega
  | score v J hJ =>
    have := List.length_pos_iff.mpr hJ
    simp only [sizeBudget]; omega

theorem labelBudget_le_sizeBudget (p : Pending σ Label E) :
    p.labelBudget ≤ p.sizeBudget := by
  cases p with
  | formula e J =>
    have := weightedOperationCount_le_size e
    simp only [labelBudget, sizeBudget]; omega
  | score => simp [labelBudget, sizeBudget]

/-- The actual number of attached labels, with repetitions counted. -/
def labelLength : Pending σ Label E → ℕ
  | .formula _ J => J.length
  | .score _ J _ => J.length

theorem terminal_labelBudget (p : Pending σ Label E) (h : p.Terminal) :
    p.labelBudget = p.labelLength := by
  cases p with
  | score => rfl
  | formula e J => cases e <;> simp_all [Terminal, labelBudget, labelLength,
      Expr.weightedOperationCount]

end Pending

theorem twice_length_le_forestSize (s : List (Pending σ Label E)) :
    2 * s.length ≤ forestSize s := by
  induction s with
  | nil => simp [forestSize]
  | cons p s ih =>
    have := p.sizeBudget_two_le
    simp only [List.length_cons, forestSize, List.map_cons, List.sum_cons] at *
    omega

theorem forestLabels_le_forestSize (s : List (Pending σ Label E)) :
    forestLabels s ≤ forestSize s := by
  induction s with
  | nil => simp [forestLabels, forestSize]
  | cons p s ih =>
    have := p.labelBudget_le_sizeBudget
    simp only [forestLabels, forestSize, List.map_cons, List.sum_cons] at *
    omega

/-- The usual initial two copies may carry different lists of equal length. -/
def initialTwoCopies {r : ℕ} (e : Expr σ r) (J K : List Label) :
    List (Pending σ Label E) := [.formula e J, .formula e K]

/-- Write `N = e.size + j`. All reachable forests, including terminal ones,
have at most `N` occurrences, total size and labels at most `2*N`, and smoothing
weight at most twice the initial decorated weight. -/
theorem initialTwoCopies_budgets {r n j : ℕ} (e : Expr σ r) (J K : List Label)
    (hJ : J.length = j) (hK : K.length = j)
    {t : List (Pending σ Label E)} (h : Steps n (initialTwoCopies e J K) t) :
    t.length ≤ e.size + j ∧ forestSize t ≤ 2 * (e.size + j) ∧
      forestLabels t ≤ 2 * (j + e.weightedOperationCount) ∧
      forestLabels t ≤ 2 * (e.size + j) ∧
      forestSmoothing t ≤ 2 * (e.weight + (j : ℝ≥0)) := by
  obtain ⟨hs, hl, hw⟩ := steps_budgets_le h
  simp only [initialTwoCopies, forestSize, forestLabels, forestSmoothing,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Pending.sizeBudget,
    Pending.labelBudget, Pending.smoothingBudget, hJ, hK, add_zero] at hs hl hw
  change forestSize t ≤ e.size + j + (e.size + j) at hs
  change forestLabels t ≤ j + e.weightedOperationCount + (j + e.weightedOperationCount) at hl
  change forestSmoothing t ≤ e.weight + (j : ℝ≥0) + (e.weight + (j : ℝ≥0)) at hw
  have hn := twice_length_le_forestSize t
  have hm := forestLabels_le_forestSize t
  refine ⟨by omega, by omega, by omega, by omega, ?_⟩
  simpa only [two_mul] using hw

/-- At a terminal forest the label budget is the literal sum of attached label
lengths. This includes repeated labels and every occurrence. -/
theorem terminal_labels_eq (t : List (Pending σ Label E))
    (ht : ∀ p ∈ t, p.Terminal) :
    forestLabels t = (t.map Pending.labelLength).sum := by
  unfold forestLabels
  congr 1
  apply List.map_congr_left
  intro p hp
  exact p.terminal_labelBudget (ht p hp)

/-- Existence of a terminal reduction with all two-copy budgets, without an
assumption that a terminal state or reduction certificate is supplied. -/
theorem exists_terminal_twoCopies [Nonempty Label] {r j : ℕ}
    (e : Expr σ r) (J K : List Label) (hJ : J.length = j) (hK : K.length = j) :
    ∃ (n : ℕ) (t : List (Pending σ Label E)), Steps n (initialTwoCopies e J K) t ∧
      (∀ p ∈ t, p.Terminal) ∧ n = 2 * syntaxRank e ∧
      t.length ≤ e.size + j ∧ forestSize t ≤ 2 * (e.size + j) ∧
      (t.map Pending.labelLength).sum ≤ 2 * (j + e.weightedOperationCount) ∧
      forestSmoothing t ≤ 2 * (e.weight + (j : ℝ≥0)) := by
  obtain ⟨n, t, hs, ht, hn⟩ := exists_terminal (initialTwoCopies (E := E) e J K)
    (by simp [initialTwoCopies])
  obtain ⟨hlen, hsize, hlabels, _, hweight⟩ := initialTwoCopies_budgets e J K hJ hK hs
  refine ⟨n, t, hs, ht, ?_, hlen, hsize, ?_, hweight⟩
  · simpa [initialTwoCopies, forestRank, Pending.rank, two_mul] using hn
  · rw [← terminal_labels_eq t ht]; exact hlabels

end AcceleratedLogConcave.Tensor.AdjointReduction
