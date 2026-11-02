import AcceleratedLogConcave.Tensor.ReductionExpansion
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Choose.Basic

/-! Numeric bounds for literal reachable forests and literal terminal branch positions.
No analytic, network, integrability, or norm assumptions occur in this module. -/

open scoped NNReal
namespace AcceleratedLogConcave.Tensor.AdjointReduction
variable {Name Label E : Type*} {σ : CoefficientSignature Name}

/-- The coefficient-budget factor, with every forest occurrence retained. -/
noncomputable def budgetProduct (R : ℝ) (t : List (Pending σ Label E)) : ℝ :=
  (t.map (fun p => (2 : ℝ) ^ p.sizeBudget * (p.sizeBudget.factorial : ℝ) *
    R ^ (-(p.smoothingBudget : ℝ)))).prod

private theorem factorial_product_le (a b : ℕ) :
    (a.factorial : ℝ) * b.factorial ≤ (a + b).factorial := by
  exact_mod_cast Nat.le_of_dvd (Nat.factorial_pos (a+b))
    (Nat.factorial_mul_factorial_dvd_factorial_add a b)

/-- Aggregation uses only positivity of R, not terminality or reachability. -/
theorem budgetProduct_le_aggregate (R : ℝ) (hR : 0 < R)
    (t : List (Pending σ Label E)) :
    budgetProduct R t ≤ (2 : ℝ) ^ forestSize t * (forestSize t).factorial *
      R ^ (-(forestSmoothing t : ℝ)) := by
  induction t with
  | nil => simp [budgetProduct, forestSize, forestSmoothing]
  | cons p t ih =>
    have hf := factorial_product_le p.sizeBudget (forestSize t)
    have hfac : 0 ≤ (2 : ℝ) ^ p.sizeBudget * (p.sizeBudget.factorial : ℝ) *
        R ^ (-(p.smoothingBudget : ℝ)) := by positivity
    calc
      budgetProduct R (p :: t) =
          ((2 : ℝ) ^ p.sizeBudget * (p.sizeBudget.factorial : ℝ) *
          R ^ (-(p.smoothingBudget : ℝ))) * budgetProduct R t := by
            simp [budgetProduct]
      _ ≤ ((2 : ℝ) ^ p.sizeBudget * (p.sizeBudget.factorial : ℝ) *
          R ^ (-(p.smoothingBudget : ℝ))) *
          ((2 : ℝ) ^ forestSize t * (forestSize t).factorial *
          R ^ (-(forestSmoothing t : ℝ))) := mul_le_mul_of_nonneg_left ih hfac
      _ = (2 : ℝ) ^ (p.sizeBudget + forestSize t) *
          ((p.sizeBudget.factorial : ℝ) * (forestSize t).factorial) *
          R ^ (-((p.smoothingBudget : ℝ) + (forestSmoothing t : ℝ))) := by
            rw [pow_add, neg_add, Real.rpow_add hR]
            ring
      _ ≤ (2 : ℝ) ^ (p.sizeBudget + forestSize t) *
          (p.sizeBudget + forestSize t).factorial *
          R ^ (-((p.smoothingBudget : ℝ) + (forestSmoothing t : ℝ))) := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hf (by positivity)) (by positivity)
      _ = _ := by simp [forestSize, forestSmoothing]

/-- The exact two-copy numeric factor; no terminality hypothesis is needed. -/
theorem budgetProduct_twoCopies_le {r n j : ℕ} (e : Expr σ r)
    (J K : List Label) (hJ : J.length = j) (hK : K.length = j)
    {t : List (Pending σ Label E)} (h : Steps n (initialTwoCopies e J K) t)
    (R : ℝ) (hR : 0 < R) (hR1 : R ≤ 1) :
    budgetProduct R t ≤ (2 : ℝ) ^ (2 * (e.size + j)) *
      (2 * (e.size + j)).factorial * R ^ (-(2 * ((e.weight : ℝ) + (j : ℝ)))) := by
  obtain ⟨_, hs, _, _, hw⟩ := initialTwoCopies_budgets e J K hJ hK h
  have hw' : (forestSmoothing t : ℝ) ≤ 2 * ((e.weight : ℝ) + (j : ℝ)) := by
    exact_mod_cast hw
  have hp : (2 : ℝ) ^ forestSize t ≤ (2 : ℝ) ^ (2 * (e.size + j)) := by
    exact pow_le_pow_right₀ (by norm_num) hs
  have hf : ((forestSize t).factorial : ℝ) ≤ (2 * (e.size + j)).factorial := by
    exact_mod_cast Nat.factorial_le hs
  have hr := Real.rpow_le_rpow_of_exponent_ge hR hR1 (neg_le_neg hw')
  exact (budgetProduct_le_aggregate R hR t).trans
    (mul_le_mul (mul_le_mul hp hf (by positivity) (by positivity))
      hr (by positivity) (by positivity))

namespace ReductionRecords

/-- Every actual canonical branch inherits the reachable-forest bound after arbitrary
origin erasure, including repeated equal label values and score values. -/
theorem terminalBranch_budgetProduct_le {r : ℕ} (e : Expr σ r) (j : ℕ)
    (v : OriginValues Label E) (R : ℝ) (hR : 0 < R) (hR1 : R ≤ 1)
    (run : List Event × List (TaggedPending σ))
    (hr : run ∈ terminalBranches (initialTwoFormulas e e j j)
      (initialTwoFormulas_support_nodup e e j j)
      (initialTwoFormulas_inventory_nodup e e j j)) :
    budgetProduct R (eraseForest v run.2) ≤ (2 : ℝ) ^ (2 * (e.size + j)) *
      (2 * (e.size + j)).factorial * R ^ (-(2 * ((e.weight : ℝ) + (j : ℝ)))) := by
  have ht := ((ExpansionTree.build (initialTwoFormulas e e j j)
    (initialTwoFormulas_support_nodup e e j j)
    (initialTwoFormulas_inventory_nodup e e j j)).branch_sound run hr).1.erase v
  have ht' : Steps run.1.length
      (initialTwoCopies e ((initialLabels 0 j).map v.label)
        ((initialLabels 1 j).map v.label)) (eraseForest v run.2) := by
    simpa [eraseForest, initialTwoFormulas, initialTwoCopies, TaggedPending.erase] using ht
  exact budgetProduct_twoCopies_le e _ _ (by simp [initialLabels])
    (by simp [initialLabels]) ht' R hR hR1

/-- The literal sum over terminal branch list positions, not a set of endpoints. -/
theorem terminalBranches_budgetProduct_sum_le {r : ℕ} (e : Expr σ r) (j : ℕ)
    (v : OriginValues Label E) (R : ℝ) (hR : 0 < R) (hR1 : R ≤ 1) :
    ((terminalBranches (initialTwoFormulas e e j j)
      (initialTwoFormulas_support_nodup e e j j)
      (initialTwoFormulas_inventory_nodup e e j j)).map
      (fun run => budgetProduct R (eraseForest v run.2))).sum ≤
    ((2 * (e.size + j) : ℕ) : ℝ) ^ (2 * (e.size + j)) *
      ((2 : ℝ) ^ (2 * (e.size + j)) * (2 * (e.size + j)).factorial *
        R ^ (-(2 * ((e.weight : ℝ) + (j : ℝ))))) := by
  let branches := terminalBranches (initialTwoFormulas e e j j)
    (initialTwoFormulas_support_nodup e e j j)
    (initialTwoFormulas_inventory_nodup e e j j)
  let B : ℝ := (2 : ℝ) ^ (2 * (e.size + j)) * (2 * (e.size + j)).factorial *
    R ^ (-(2 * ((e.weight : ℝ) + (j : ℝ))))
  have hsum : (branches.map (fun run => budgetProduct R (eraseForest v run.2))).sum ≤
      (branches.length : ℝ) * B := by
    have hh := List.sum_le_length_nsmul
      (branches.map (fun run => budgetProduct R (eraseForest v run.2))) B
      (by
        intro x hx
        obtain ⟨run, hr, rfl⟩ := List.mem_map.mp hx
        exact terminalBranch_budgetProduct_le e j v R hR hR1 run hr)
    simpa using hh
  have hc : (branches.length : ℝ) ≤
      ((2 * (e.size + j) : ℕ) : ℝ) ^ (2 * (e.size + j)) := by
    exact_mod_cast terminalBranches_twoCopy_le_size_power e j
  exact hsum.trans (mul_le_mul_of_nonneg_right hc (by dsimp [B]; positivity))

end ReductionRecords
end AcceleratedLogConcave.Tensor.AdjointReduction
