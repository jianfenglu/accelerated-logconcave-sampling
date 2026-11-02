import AcceleratedLogConcave.Tensor.TerminalBudgetBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Choose.Basic

/-! Numeric bounds for literal reachable forests and literal terminal branch positions.
No analytic, network, integrability, or norm assumptions occur in this module. -/

open scoped NNReal
namespace AcceleratedLogConcave.Tensor.AdjointReduction.PhaseBudget
variable {Name Label E : Type*} {σ : CoefficientSignature Name}

/-- The coefficient-budget factor, with every forest occurrence retained. -/
noncomputable def budgetProduct (c R : ℝ) (t : List (Pending σ Label E)) : ℝ :=
  (t.map (fun p => c ^ p.sizeBudget * (p.sizeBudget.factorial : ℝ) *
    R ^ (-(p.smoothingBudget : ℝ)))).prod

private theorem factorial_product_le (a b : ℕ) :
    (a.factorial : ℝ) * b.factorial ≤ (a + b).factorial := by
  exact_mod_cast Nat.le_of_dvd (Nat.factorial_pos (a+b))
    (Nat.factorial_mul_factorial_dvd_factorial_add a b)

/-- Aggregation uses only positivity of R, not terminality or reachability. -/
theorem budgetProduct_le_aggregate (c R : ℝ) (hc : 1 ≤ c) (hR : 0 < R)
    (t : List (Pending σ Label E)) :
    budgetProduct c R t ≤ c ^ forestSize t * (forestSize t).factorial *
      R ^ (-(forestSmoothing t : ℝ)) := by
  induction t with
  | nil => simp [budgetProduct, forestSize, forestSmoothing]
  | cons p t ih =>
    have hf := factorial_product_le p.sizeBudget (forestSize t)
    have hfac : 0 ≤ c ^ p.sizeBudget * (p.sizeBudget.factorial : ℝ) *
        R ^ (-(p.smoothingBudget : ℝ)) := by positivity
    calc
      budgetProduct c R (p :: t) =
          (c ^ p.sizeBudget * (p.sizeBudget.factorial : ℝ) *
          R ^ (-(p.smoothingBudget : ℝ))) * budgetProduct c R t := by
            simp [budgetProduct]
      _ ≤ (c ^ p.sizeBudget * (p.sizeBudget.factorial : ℝ) *
          R ^ (-(p.smoothingBudget : ℝ))) *
          (c ^ forestSize t * (forestSize t).factorial *
          R ^ (-(forestSmoothing t : ℝ))) := mul_le_mul_of_nonneg_left ih hfac
      _ = c ^ (p.sizeBudget + forestSize t) *
          ((p.sizeBudget.factorial : ℝ) * (forestSize t).factorial) *
          R ^ (-((p.smoothingBudget : ℝ) + (forestSmoothing t : ℝ))) := by
            rw [pow_add, neg_add, Real.rpow_add hR]
            ring
      _ ≤ c ^ (p.sizeBudget + forestSize t) *
          (p.sizeBudget + forestSize t).factorial *
          R ^ (-((p.smoothingBudget : ℝ) + (forestSmoothing t : ℝ))) := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hf (by positivity)) (by positivity)
      _ = _ := by simp [forestSize, forestSmoothing]

/-- The exact two-copy numeric factor; no terminality hypothesis is needed. -/
theorem budgetProduct_twoCopies_le {r n j : ℕ} (e : Expr σ r)
    (J K : List Label) (hJ : J.length = j) (hK : K.length = j)
    {t : List (Pending σ Label E)} (h : Steps n (initialTwoCopies e J K) t)
    (c R : ℝ) (hc : 1 ≤ c) (hR : 0 < R) (hR1 : R ≤ 1) :
    budgetProduct c R t ≤ c ^ (2 * (e.size + j)) *
      (2 * (e.size + j)).factorial * R ^ (-(2 * ((e.weight : ℝ) + (j : ℝ)))) := by
  obtain ⟨_, hs, _, _, hw⟩ := initialTwoCopies_budgets e J K hJ hK h
  have hw' : (forestSmoothing t : ℝ) ≤ 2 * ((e.weight : ℝ) + (j : ℝ)) := by
    exact_mod_cast hw
  have hp : c ^ forestSize t ≤ c ^ (2 * (e.size + j)) := by
    exact pow_le_pow_right₀ hc hs
  have hf : ((forestSize t).factorial : ℝ) ≤ (2 * (e.size + j)).factorial := by
    exact_mod_cast Nat.factorial_le hs
  have hr := Real.rpow_le_rpow_of_exponent_ge hR hR1 (neg_le_neg hw')
  exact (budgetProduct_le_aggregate c R hc hR t).trans
    (mul_le_mul (mul_le_mul hp hf (by positivity) (by positivity))
      hr (by positivity) (by positivity))

open ReductionRecords
namespace ReductionRecords

/-- Every actual canonical branch inherits the reachable-forest bound after arbitrary
origin erasure, including repeated equal label values and score values. -/
theorem terminalBranch_budgetProduct_le {r : ℕ} (e : Expr σ r) (j : ℕ)
    (v : OriginValues Label E) (c R : ℝ) (hc : 1 ≤ c) (hR : 0 < R) (hR1 : R ≤ 1)
    (run : List Event × List (TaggedPending σ))
    (hr : run ∈ terminalBranches (initialTwoFormulas e e j j)
      (initialTwoFormulas_support_nodup e e j j)
      (initialTwoFormulas_inventory_nodup e e j j)) :
    budgetProduct c R (eraseForest v run.2) ≤ c ^ (2 * (e.size + j)) *
      (2 * (e.size + j)).factorial * R ^ (-(2 * ((e.weight : ℝ) + (j : ℝ)))) := by
  have ht := ((ExpansionTree.build (initialTwoFormulas e e j j)
    (initialTwoFormulas_support_nodup e e j j)
    (initialTwoFormulas_inventory_nodup e e j j)).branch_sound run hr).1.erase v
  have ht' : Steps run.1.length
      (initialTwoCopies e ((initialLabels 0 j).map v.label)
        ((initialLabels 1 j).map v.label)) (eraseForest v run.2) := by
    simpa [eraseForest, initialTwoFormulas, initialTwoCopies, TaggedPending.erase] using ht
  exact budgetProduct_twoCopies_le e _ _ (by simp [initialLabels])
    (by simp [initialLabels]) ht' c R hc hR hR1

/-- The literal sum over terminal branch list positions, not a set of endpoints. -/
theorem terminalBranches_budgetProduct_sum_le {r : ℕ} (e : Expr σ r) (j : ℕ)
    (v : OriginValues Label E) (c R : ℝ) (hc : 1 ≤ c) (hR : 0 < R) (hR1 : R ≤ 1) :
    ((terminalBranches (initialTwoFormulas e e j j)
      (initialTwoFormulas_support_nodup e e j j)
      (initialTwoFormulas_inventory_nodup e e j j)).map
      (fun run => budgetProduct c R (eraseForest v run.2))).sum ≤
    ((2 * (e.size + j) : ℕ) : ℝ) ^ (2 * (e.size + j)) *
      (c ^ (2 * (e.size + j)) * (2 * (e.size + j)).factorial *
        R ^ (-(2 * ((e.weight : ℝ) + (j : ℝ))))) := by
  let branches := terminalBranches (initialTwoFormulas e e j j)
    (initialTwoFormulas_support_nodup e e j j)
    (initialTwoFormulas_inventory_nodup e e j j)
  let B : ℝ := c ^ (2 * (e.size + j)) * (2 * (e.size + j)).factorial *
    R ^ (-(2 * ((e.weight : ℝ) + (j : ℝ))))
  have hsum : (branches.map (fun run => budgetProduct c R (eraseForest v run.2))).sum ≤
      (branches.length : ℝ) * B := by
    have hh := List.sum_le_length_nsmul
      (branches.map (fun run => budgetProduct c R (eraseForest v run.2))) B
      (by
        intro x hx
        obtain ⟨run, hr, rfl⟩ := List.mem_map.mp hx
        exact terminalBranch_budgetProduct_le e j v c R hc hR hR1 run hr)
    simpa using hh
  have hc : (branches.length : ℝ) ≤
      ((2 * (e.size + j) : ℕ) : ℝ) ^ (2 * (e.size + j)) := by
    exact_mod_cast terminalBranches_twoCopy_le_size_power e j
  exact hsum.trans (mul_le_mul_of_nonneg_right hc (by dsimp [B]; positivity))

end ReductionRecords
end AcceleratedLogConcave.Tensor.AdjointReduction.PhaseBudget

namespace AcceleratedLogConcave.Tensor.AdjointReduction.PhaseBudget

/-- Explicit universal majorant requested for the phase expression theorem. -/
noncomputable def Q (c : ℝ) (n : ℕ) : ℝ :=
  ((16*(n+1) : ℕ) : ℝ)^(16*(n+1)) * c^(16*(n+1)) *
    ((16*(n+1)).factorial : ℝ)

theorem Q_nonneg {c : ℝ} (hc : 0 ≤ c) (n : ℕ) : 0 ≤ Q c n := by
  unfold Q
  positivity

/-- The literal two-copy expansion bound fits the announced larger majorant.
This is a numerical theorem, not an expression moment assumption. -/
theorem twoCopy_numeric_le_Q {c : ℝ} (hc : 1 ≤ c) (n : ℕ) :
    ((2*n : ℕ) : ℝ)^(2*n) * c^(2*n) * ((2*n).factorial : ℝ) ≤ Q c n := by
  have hN : 2*n ≤ 16*(n+1) := by omega
  have hbase : ((2*n : ℕ) : ℝ) ≤ ((16*(n+1) : ℕ) : ℝ) := by exact_mod_cast hN
  have hlarge : (1 : ℝ) ≤ ((16*(n+1) : ℕ) : ℝ) := by
    exact_mod_cast (show 1 ≤ 16*(n+1) by omega)
  have hp := (pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ ((2*n : ℕ) : ℝ))
    hbase (2*n)).trans (pow_le_pow_right₀ hlarge hN)
  have hc' := pow_le_pow_right₀ hc hN
  have hf : ((2*n).factorial : ℝ) ≤ ((16*(n+1)).factorial : ℝ) := by
    exact_mod_cast Nat.factorial_le hN
  exact mul_le_mul (mul_le_mul hp hc' (by positivity) (by positivity)) hf
    (by positivity) (by positivity)
end AcceleratedLogConcave.Tensor.AdjointReduction.PhaseBudget
