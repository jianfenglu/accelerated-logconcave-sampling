import AcceleratedLogConcave.Tensor.CanonicalMaximumPartition

/-!

-/
noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical
namespace AcceleratedLogConcave.Tensor.FlowInduction

abbrev SizedAssignment {n k : ℕ} (j : Fin k → ℕ) :=
  {f : Fin n → Fin k // ∀ i, Fintype.card {x : Fin n // f x = i} = j i}

/-- A compatible labeling itself certifies every fiber size. -/
theorem compatibleLabeling_sizes {n k : ℕ} {j : Fin k → ℕ} {f : Fin n → Fin k}
    (e : CompatibleLabeling j f) (i : Fin k) :
    Fintype.card {x : Fin n // f x = i} = j i := by
  simpa using (Fintype.card_congr (labelingFiberEquiv e i)).symm

/-- Restricting the assignment index to its exact size stratum loses no labelings. -/
def sizedLabelingEquiv {n k : ℕ} (j : Fin k → ℕ) :
    (Σ f : SizedAssignment (n := n) j, CompatibleLabeling j f.val) ≃
      (Σ f : Fin n → Fin k, CompatibleLabeling j f) where
  toFun x := ⟨x.1.val, x.2⟩
  invFun x := ⟨⟨x.1, compatibleLabeling_sizes x.2⟩, x.2⟩
  left_inv x := by cases x; rfl
  right_inv x := by cases x; rfl

/-- Division-free cardinality identity. No positive-size assumption is necessary:
zero segments are harmless here, and will be excluded for surjections. -/
theorem sizedAssignment_card_mul {n k : ℕ} (j : Fin k → ℕ)
    (hsum : (∑ i, j i) = n) :
    Fintype.card (SizedAssignment (n := n) j) * (∏ i, (j i).factorial) = n.factorial := by
  have h := Fintype.card_congr (sizedLabelingEquiv (n := n) j)
  rw [Fintype.card_sigma, Fintype.card_sigma] at h
  calc
    _ = ∑ f : SizedAssignment (n := n) j, ∏ i, (j i).factorial := by simp
    _ = ∑ f : SizedAssignment (n := n) j, Fintype.card (CompatibleLabeling j f.val) := by
      apply Finset.sum_congr rfl
      intro f _
      exact (compatibleLabeling_card j f.val f.property).symm
    _ = ∑ f : Fin n → Fin k, Fintype.card (CompatibleLabeling j f) := h
    _ = n.factorial := compatibleLabeling_total j hsum

/-- Real-valued multinomial count, after proving positivity of the denominator. -/
theorem sizedAssignment_card_real {n k : ℕ} (j : Fin k → ℕ)
    (hsum : (∑ i, j i) = n) :
    (Fintype.card (SizedAssignment (n := n) j) : ℝ) =
      (n.factorial : ℝ) / ∏ i, ((j i).factorial : ℝ) := by
  have hd : (∏ i, ((j i).factorial : ℝ)) ≠ 0 := by positivity
  apply (eq_div_iff hd).mpr
  exact_mod_cast sizedAssignment_card_mul j hsum

/-- The exact weighted contribution of one freely labeled size stratum. -/
theorem sizedAssignment_weighted {n k : ℕ} (j : Fin k → ℕ)
    (hsum : (∑ i, j i) = n) (w : ℕ → ℝ) :
    (∑ _f : SizedAssignment (n := n) j, ∏ i, w (j i)) =
      ((n.factorial : ℝ) / ∏ i, ((j i).factorial : ℝ)) * ∏ i, w (j i) := by
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [sizedAssignment_card_real j hsum]

/-- Positive sizes force surjectivity; no empty block is silently admitted. -/
theorem sizedAssignment_surjective {n k : ℕ} {j : Fin k → ℕ}
    (hj : ∀ i, 0 < j i) (f : SizedAssignment (n := n) j) :
    Function.Surjective f.val := by
  intro i
  have hc : 0 < Fintype.card {x : Fin n // f.val x = i} := by rw [f.property i]; exact hj i
  obtain ⟨x⟩ := Fintype.card_pos_iff.mp hc
  exact ⟨x.val, x.property⟩

/-- Conversely, every actual surjection has positive fiber sizes. -/
theorem surjection_fiber_card_pos {n k : ℕ} (f : LabeledSurjection n k) (i : Fin k) :
    0 < Fintype.card {x : Fin n // f.val x = i} := by
  obtain ⟨x,hx⟩ := f.property i
  exact Fintype.card_pos_iff.mpr ⟨⟨x,hx⟩⟩

theorem assignment_fiber_card_sum {n k : ℕ} (f : Fin n → Fin k) :
    (∑ i, Fintype.card {x : Fin n // f x = i}) = n := by
  simpa only [Fintype.card_sigma, Fintype.card_fin] using
    Fintype.card_congr (Equiv.sigmaFiberEquiv f)

end AcceleratedLogConcave.Tensor.FlowInduction
