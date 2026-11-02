import AcceleratedLogConcave.Tensor.FlowOrderConstants

/-!

-/
noncomputable section
set_option autoImplicit false
open scoped Classical BigOperators
namespace AcceleratedLogConcave.Tensor.InverseFlow
open FlowInduction

private def inverseOrderStep (n : ℕ) (prev : ∀ j, j < n → ℝ) : ℝ :=
  if n = 0 then growthConstant else
    growthConstant * ∑ s ∈ (Finset.range n).attach,
      (n.choose s.val : ℝ) * prev s.val (Finset.mem_range.mp s.property) *
        orderConstant (n-s.val+1)

def inverseOrderConstant : ℕ → ℝ := Nat.lt_wfRel.wf.fix inverseOrderStep

 theorem inverseOrderConstant_zero : inverseOrderConstant 0 = growthConstant := by
  rw [inverseOrderConstant,WellFounded.fix_eq]
  simp [inverseOrderStep]

 theorem inverseOrderConstant_recurrence {n : ℕ} (hn : 0 < n) :
    inverseOrderConstant n = growthConstant * ∑ s ∈ Finset.range n,
      (n.choose s : ℝ) * inverseOrderConstant s * orderConstant (n-s+1) := by
  rw [inverseOrderConstant,WellFounded.fix_eq]
  simp only [inverseOrderStep,ite_eq_right (Nat.ne_of_gt hn)]
  change growthConstant * (∑ s ∈ (Finset.range n).attach,
    (n.choose s.val : ℝ) * inverseOrderConstant s.val * orderConstant (n-s.val+1)) = _
  rw [Finset.sum_attach _ (fun s : ℕ =>
    (n.choose s : ℝ) * inverseOrderConstant s * orderConstant (n-s+1))]
  rfl

 theorem inverseOrderConstant_nonneg (n : ℕ) : 0 ≤ inverseOrderConstant n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n = 0
    · subst n
      rw [inverseOrderConstant_zero]
      exact (Real.exp_pos _).le
    · rw [inverseOrderConstant_recurrence (Nat.pos_of_ne_zero hn)]
      apply mul_nonneg (Real.exp_pos _).le
      apply Finset.sum_nonneg
      intro s hs
      exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (ih s (Finset.mem_range.mp hs)))
        (orderConstant_nonneg _)

/-- Exactly the spatial powers in the B_s J_(n-s) B_0 path.
This is a multiplication identity, not cancellation of H or of the clock. -/
theorem inverse_weight (A H Q C R : ℝ) {n s : ℕ} (hs : s ≤ n) :
    ((H^s*Q)*(A*H^(n-s)*C))*R = A*H^n*(Q*C*R) := by
  have hp : H^s*H^(n-s) = H^n := by
    have he : s+(n-s)=n := by omega
    rw [← pow_add,he]
  calc
    _ = A*(H^s*H^(n-s))*(Q*C*R) := by ring
    _ = _ := by rw [hp]
end AcceleratedLogConcave.Tensor.InverseFlow
