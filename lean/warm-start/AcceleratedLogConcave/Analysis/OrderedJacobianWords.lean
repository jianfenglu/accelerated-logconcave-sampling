import AcceleratedLogConcave.Analysis.FiniteDerivativeLadder
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.Ring

/-!
# Ordered words for B' = B C
-/
noncomputable section
set_option autoImplicit false
namespace AcceleratedLogConcave.Analysis.OrderedJacobianWords

abbrev Word := List ℕ

def order (w : Word) : ℕ := (w.map (· + 1)).sum

/-- One ordinary product rule on the C factors, keeping every position. -/
def differentiate : Word → List Word
  | [] => []
  | j :: w => ((j + 1) :: w) :: (differentiate w).map (List.cons j)

/-- Differentiating B inserts C on the LEFT of the old ordered product. -/
def step (w : Word) : List Word := (0 :: w) :: differentiate w

def words : ℕ → List Word
  | 0 => [[]]
  | n + 1 => (words n).flatMap step

@[simp] theorem order_nil : order [] = 0 := rfl
@[simp] theorem order_cons (j : ℕ) (w : Word) :
    order (j :: w) = j + 1 + order w := by simp [order]

theorem length_le_order (w : Word) : w.length ≤ order w := by
  induction w with
  | nil => simp
  | cons j w ih => simp only [List.length_cons, order_cons]; omega

theorem differentiate_length (w : Word) : (differentiate w).length = w.length := by
  induction w with
  | nil => rfl
  | cons j w ih => simp [differentiate, ih]

theorem step_length (w : Word) : (step w).length = w.length + 1 := by
  simp [step, differentiate_length]

theorem order_of_mem_differentiate {w v : Word} (h : v ∈ differentiate w) :
    order v = order w + 1 := by
  induction w generalizing v with
  | nil => simp [differentiate] at h
  | cons j w ih =>
    simp only [differentiate, List.mem_cons, List.mem_map] at h
    rcases h with rfl | ⟨u, hu, rfl⟩
    · simp only [order_cons]; omega
    · simp only [order_cons]; have := ih hu; omega

theorem order_of_mem_step {w v : Word} (h : v ∈ step w) :
    order v = order w + 1 := by
  rcases List.mem_cons.mp h with rfl | h
  · simp [Nat.add_comm]
  · exact order_of_mem_differentiate h

theorem order_of_mem_words {n : ℕ} {w : Word} (h : w ∈ words n) : order w = n := by
  induction n generalizing w with
  | zero =>
    have hw : w = [] := by simpa [words] using h
    subst w
    rfl
  | succ n ih =>
    obtain ⟨v, hv, hw⟩ := List.mem_flatMap.mp h
    rw [order_of_mem_step hw, ih hv]

/-- Every term at positive order has at least one C factor. -/
theorem nonempty_of_mem_words {n : ℕ} {w : Word} (hn : 0 < n) (h : w ∈ words n) :
    w ≠ [] := by
  intro hw
  subst w
  have := order_of_mem_words h
  simp at this
  omega

private theorem length_flatMap_le (l : List Word) (n : ℕ)
    (h : ∀ w ∈ l, w.length ≤ n) : (l.flatMap step).length ≤ l.length * (n + 1) := by
  induction l with
  | nil => simp
  | cons w l ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons, step_length]
    have h₁ := h w (by simp)
    have h₂ := ih (fun v hv => h v (by simp [hv]))
    calc
      w.length + 1 + (l.flatMap step).length ≤ (n + 1) + l.length * (n + 1) :=
        Nat.add_le_add (Nat.add_le_add_right h₁ 1) h₂
      _ = (l.length + 1) * (n + 1) := by ring

/-- Coefficient mass counts repeated words separately. No dimension enters. -/
theorem coefficient_mass_le_factorial (n : ℕ) : (words n).length ≤ n.factorial := by
  induction n with
  | zero => simp [words]
  | succ n ih =>
    calc
      (words (n+1)).length ≤ (words n).length * (n+1) :=
        length_flatMap_le (words n) n (fun w hw => (length_le_order w).trans_eq (order_of_mem_words hw))
      _ ≤ n.factorial * (n+1) := Nat.mul_le_mul_right _ ih
      _ = (n+1).factorial := by rw [Nat.factorial_succ, Nat.mul_comm]

/-- The sum of allocated material derivative orders plus the number of factors. -/
theorem order_eq_sum_add_length (w : Word) : order w = w.sum + w.length := by
  induction w with
  | nil => rfl
  | cons j w ih => simp only [order_cons, List.sum_cons, List.length_cons]; omega

/-- Sum of per-factor sizes 2+3j and a-1 contraction nodes is exactly 3n-1. -/
theorem expression_size_budget {n : ℕ} {w : Word} (hn : 0 < n) (h : w ∈ words n) :
    (w.map (fun j => 2 + 3*j)).sum + (w.length - 1) = 3*n - 1 := by
  have he : (w.map (fun j => 2 + 3*j)).sum = 2*w.length + 3*w.sum := by
    clear h hn n
    induction w with
    | nil => simp
    | cons j w ih => simp only [List.map_cons, List.sum_cons, List.length_cons]; rw [ih]; ring
  have ho := order_of_mem_words h
  rw [order_eq_sum_add_length] at ho
  have hp : 0 < w.length := List.length_pos_iff.mpr (nonempty_of_mem_words hn h)
  rw [he]
  omega

/-- Whole-expression weight has exponent at most 2(n-1), not a product of
separate moment estimates. -/
theorem expression_weight_budget {n : ℕ} {w : Word} (hn : 0 < n) (h : w ∈ words n) :
    2*w.sum ≤ 2*(n-1) := by
  have ho := order_of_mem_words h
  rw [order_eq_sum_add_length] at ho
  have hp : 0 < w.length := List.length_pos_iff.mpr (nonempty_of_mem_words hn h)
  omega


section Interpretation
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]

/-- Ordered product, not a commutative monomial. -/
def evaluate (C : ℕ → ℝ → A) (w : Word) (t : ℝ) : A :=
  (w.map (fun j => C j t)).prod

def evaluateSum (C : ℕ → ℝ → A) (ws : List Word) (t : ℝ) : A :=
  (ws.map (fun w => evaluate C w t)).sum

omit [NormedAlgebra ℝ A] in
@[simp] theorem evaluate_nil (C : ℕ → ℝ → A) (t : ℝ) : evaluate C [] t = 1 := rfl
omit [NormedAlgebra ℝ A] in
@[simp] theorem evaluate_cons (C : ℕ → ℝ → A) (j : ℕ) (w : Word) (t : ℝ) :
    evaluate C (j :: w) t = C j t * evaluate C w t := rfl

omit [NormedAlgebra ℝ A] in
private theorem evaluateSum_prepend (C : ℕ → ℝ → A) (j : ℕ) (ws : List Word) (t : ℝ) :
    evaluateSum C (ws.map (List.cons j)) t = C j t * evaluateSum C ws t := by
  simp only [evaluateSum, List.map_map, Function.comp_def, evaluate_cons]
  exact List.sum_map_mul_left _ _ _

theorem hasDerivAt_evaluate (C : ℕ → ℝ → A) (w : Word) {t : ℝ}
    (hC : ∀ j ∈ w, HasDerivAt (C j) (C (j+1) t) t) :
    HasDerivAt (evaluate C w) (evaluateSum C (differentiate w) t) t := by
  induction w with
  | nil =>
    change HasDerivAt (fun _ : ℝ => (1 : A)) 0 t
    exact hasDerivAt_const t (1 : A)
  | cons j w ih =>
    have hj := hC j (by simp)
    have hw := ih (fun k hk => hC k (by simp [hk]))
    have he : evaluateSum C (differentiate (j :: w)) t =
        C (j+1) t * evaluate C w t + C j t * evaluateSum C (differentiate w) t := by
      change _ + evaluateSum C ((differentiate w).map (List.cons j)) t = _
      simp only [evaluate_cons, evaluateSum_prepend]
    rw [he]
    exact hj.mul hw

/-- A single complete product rule, including the noncommuting left factor B. -/
theorem hasDerivAt_left_evaluate (B : ℝ → A) (C : ℕ → ℝ → A) (w : Word) {t : ℝ}
    (hB : HasDerivAt B (B t * C 0 t) t)
    (hC : ∀ j ∈ w, HasDerivAt (C j) (C (j+1) t) t) :
    HasDerivAt (fun u => B u * evaluate C w u) (B t * evaluateSum C (step w) t) t := by
  have he : B t * evaluateSum C (step w) t =
      (B t * C 0 t) * evaluate C w t + B t * evaluateSum C (differentiate w) t := by
    change B t * (evaluate C (0 :: w) t + evaluateSum C (differentiate w) t) = _
    rw [evaluate_cons, mul_add, mul_assoc]
  rw [he]
  exact hB.mul (hasDerivAt_evaluate C w hC)

/-- The literal sum of all words obeys the consecutive derivative recurrence. -/
theorem hasDerivAt_left_evaluateSum (B : ℝ → A) (C : ℕ → ℝ → A) (ws : List Word) {t : ℝ}
    (hB : HasDerivAt B (B t * C 0 t) t)
    (hC : ∀ w ∈ ws, ∀ j ∈ w, HasDerivAt (C j) (C (j+1) t) t) :
    HasDerivAt (fun u => B u * evaluateSum C ws u)
      (B t * evaluateSum C (ws.flatMap step) t) t := by
  induction ws with
  | nil => simpa [evaluateSum] using (hasDerivAt_const t (0 : A))
  | cons w ws ih =>
    have hw := hasDerivAt_left_evaluate B C w hB (hC w (by simp))
    have hs := ih (fun v hv => hC v (by simp [hv]))
    convert hw.add hs using 1 <;>
      simp only [List.flatMap_cons, evaluateSum, List.map_append, List.sum_append,
        List.map_cons, List.sum_cons, mul_add]
    funext u
    rfl

private theorem entry_lt_order {w : Word} {j : ℕ} (h : j ∈ w) : j < order w := by
  induction w with
  | nil => simp at h
  | cons k w ih =>
    rcases List.mem_cons.mp h with rfl | hj
    · simp only [order_cons]; omega
    · have := ih hj; simp only [order_cons]; omega

/-- Exact ordinary derivative formula from a FINITE C-jet ladder on an open
set. No commutativity and no derivative above the requested order is assumed.
Together with coefficient_mass_le_factorial, this supplies the manuscript's
ordered-word expansion and its explicit coefficient budget. -/
theorem iteratedDeriv_eq_words (n : ℕ) (B : ℝ → A) (C : ℕ → ℝ → A)
    {s : Set ℝ} (hs : IsOpen s)
    (hB : ∀ t ∈ s, HasDerivAt B (B t * C 0 t) t)
    (hC : ∀ j < n, ∀ t ∈ s, HasDerivAt (C j) (C (j+1) t) t)
    {t : ℝ} (ht : t ∈ s) :
    iteratedDeriv n B t = B t * evaluateSum C (words n) t := by
  have hl := Analysis.iteratedDeriv_eq_of_finite_ladder n
    (fun k u => B u * evaluateSum C (words k) u) hs
    (fun k hk u hu => hasDerivAt_left_evaluateSum B C (words k) (hB u hu)
      (fun w hw j hj => hC j (by
        have he := entry_lt_order hj
        rw [order_of_mem_words hw] at he
        omega) u hu)) ht
  simpa only [words, evaluateSum, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, evaluate_nil, add_zero, mul_one] using hl

end Interpretation

end AcceleratedLogConcave.Analysis.OrderedJacobianWords
