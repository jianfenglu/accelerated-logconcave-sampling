import AcceleratedLogConcave.Analysis.OrderedSpatialComposition
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!

-/
noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical
namespace AcceleratedLogConcave.Tensor.FlowInduction
open AcceleratedLogConcave.Analysis.SpatialPartition

def primitiveConstant (n : ℕ) : ℝ := (n.factorial : ℝ) * Real.sqrt 2 ^ (n+1)
def growthConstant : ℝ := Real.exp (1/4)

def properPartitions (n : ℕ) (hn : 0 < n) : Finset (OrderedFinpartition n) :=
  Finset.univ.erase (OrderedFinpartition.oneBlock n hn)

private def orderStep (n : ℕ) (prev : ∀ j, j < n → ℝ) : ℝ :=
  if hn : 2 ≤ n then
    growthConstant * ∑ c ∈ (properPartitions n (by omega)).attach,
      primitiveConstant c.val.length * ∏ i,
        prev (c.val.partSize i)
          (spatialForcing_support n (by omega) c.val c.property i).2
  else growthConstant

/-- Defined by well-founded recursion, with positive strictly smaller branches. -/
def orderConstant : ℕ → ℝ := Nat.lt_wfRel.wf.fix orderStep

def forcingConstant (n : ℕ) (hn : 0 < n) : ℝ :=
  ∑ c ∈ properPartitions n hn,
    primitiveConstant c.length * ∏ i, orderConstant (c.partSize i)

 theorem orderConstant_small {n : ℕ} (hn : n < 2) :
    orderConstant n = growthConstant := by
  rw [orderConstant, WellFounded.fix_eq]
  simp [orderStep, show ¬ 2 ≤ n by omega]

 theorem orderConstant_recurrence {n : ℕ} (hn : 2 ≤ n) :
    orderConstant n = growthConstant * forcingConstant n (by omega) := by
  rw [orderConstant, WellFounded.fix_eq]
  simp only [orderStep, dite_eq_left hn]
  change growthConstant * (∑ c ∈ (properPartitions n (by omega)).attach,
    primitiveConstant c.val.length * ∏ i, orderConstant (c.val.partSize i)) = _
  rw [Finset.sum_attach _ (fun c : OrderedFinpartition n =>
    primitiveConstant c.length * ∏ i, orderConstant (c.partSize i))]
  rfl

 theorem primitiveConstant_nonneg (n : ℕ) : 0 ≤ primitiveConstant n := by
  exact mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (Real.sqrt_nonneg _) _)

 theorem orderConstant_nonneg (n : ℕ) : 0 ≤ orderConstant n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : 2 ≤ n
    · rw [orderConstant_recurrence hn]
      apply mul_nonneg (le_of_lt (Real.exp_pos _))
      apply Finset.sum_nonneg
      intro c hc
      apply mul_nonneg (primitiveConstant_nonneg _)
      apply Finset.prod_nonneg
      intro i _
      exact ih _ (spatialForcing_support n (by omega) c hc i).2
    · rw [orderConstant_small (by omega)]
      exact le_of_lt (Real.exp_pos _)

 theorem forcingConstant_nonneg (n : ℕ) (hn : 0 < n) :
    0 ≤ forcingConstant n hn := by
  apply Finset.sum_nonneg
  intro c _
  exact mul_nonneg (primitiveConstant_nonneg _)
    (Finset.prod_nonneg (fun i _ => orderConstant_nonneg _))

/-- Exact exponent count, including multiplicities of labeled blocks. -/
 theorem partition_exponent {n : ℕ} (hn : 0 < n) (c : OrderedFinpartition n) :
    (c.length - 1) + (∑ i, (c.partSize i - 1)) = n - 1 := by
  have hp : ∑ i, ((c.partSize i - 1) + 1) = n := by
    calc
      _ = ∑ i, c.partSize i := Finset.sum_congr rfl
        (fun i _ => Nat.sub_add_cancel (c.partSize_pos i))
      _ = n := OrderedFinpartition.sum_partSize c
  rw [Finset.sum_add_distrib] at hp
  have hp' : (∑ i, (c.partSize i - 1)) + c.length = n := by simpa using hp
  have hl := c.length_pos hn
  omega

/-- A local elementary product identity avoids reliance on a guessed pow-product API. -/
 theorem prod_powers {I : Type*} [DecidableEq I] (s : Finset I)
    (H : ℝ) (p : I → ℕ) : ∏ i ∈ s, H ^ p i = H ^ (∑ i ∈ s, p i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp [ha, ih, pow_add]

 theorem partition_weight {n : ℕ} (hn : 0 < n) (c : OrderedFinpartition n)
    (α t H : ℝ) :
    (α*t*primitiveConstant c.length*H^(c.length-1)) *
      (∏ i, H^(c.partSize i-1)*orderConstant (c.partSize i)) =
    α*t*H^(n-1) * (primitiveConstant c.length * ∏ i, orderConstant (c.partSize i)) := by
  rw [Finset.prod_mul_distrib, prod_powers]
  have hp := partition_exponent hn c
  calc
    _ = α*t*(H^(c.length-1)*H^(∑ i, (c.partSize i-1))) *
        (primitiveConstant c.length * ∏ i, orderConstant (c.partSize i)) := by ring
    _ = _ := by rw [← pow_add, hp]

 theorem forcing_weight (n : ℕ) (hn : 0 < n) (α t H : ℝ) :
    (∑ c ∈ properPartitions n hn,
      (α*t*primitiveConstant c.length*H^(c.length-1)) *
        ∏ i, H^(c.partSize i-1)*orderConstant (c.partSize i)) =
      α*t*H^(n-1)*forcingConstant n hn := by
  simp_rw [partition_weight hn]
  rw [← Finset.mul_sum]
  rfl

 theorem exp_sub_one_le {A : ℝ} (hA : 0 ≤ A) (hA' : A ≤ 1/4) :
    Real.exp A - 1 ≤ A * growthConstant := by
  have hl := Real.add_one_le_exp (-A)
  have hm := mul_le_mul_of_nonneg_left hl (le_of_lt (Real.exp_pos A))
  have he : Real.exp A * Real.exp (-A) = 1 := by rw [← Real.exp_add]; simp
  rw [he] at hm
  have hfirst : Real.exp A - 1 ≤ A * Real.exp A := by nlinarith
  exact hfirst.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hA') hA)

end AcceleratedLogConcave.Tensor.FlowInduction
