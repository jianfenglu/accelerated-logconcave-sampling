import AcceleratedLogConcave.Tensor.ActualNormalizedRecurrence
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!

-/
noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical
namespace AcceleratedLogConcave.Tensor.FlowInduction

abbrev BoundedPositiveProfile (N k : ℕ) :=
  Σ d : Fin (N+2), PositiveSizeProfile d.val k

/-- For arity at least two, every entry at degree at most N+1 is at most N. -/
def boundedProfileBox {N k : ℕ} (hk : 2 ≤ k) (x : BoundedPositiveProfile N k) :
    Fin k → Fin N := fun i => ⟨(x.2.val i).val - 1, by
  have hp := x.2.property.1 i
  have hd : (∑ a, (x.2.val a).val) ≤ N+1 := by rw [x.2.property.2]; omega
  have he := growth_tuple_entry_le_previous hk (fun a => (x.2.val a).val)
    x.2.property.1 hd i
  omega⟩

@[simp] theorem boundedProfileBox_entry {N k : ℕ} (hk : 2 ≤ k)
    (x : BoundedPositiveProfile N k) (i : Fin k) :
    (boundedProfileBox hk x i).val + 1 = (x.2.val i).val := by
  have hp := x.2.property.1 i
  change (x.2.val i).val - 1 + 1 = _
  omega

/-- Degree is determined by the tuple sum, so no duplicate tuple appears
when the finite sums over all degrees are collected. -/
theorem boundedProfileBox_injective {N k : ℕ} (hk : 2 ≤ k) :
    Function.Injective (boundedProfileBox (N := N) hk) := by
  rintro ⟨d,j⟩ ⟨e,l⟩ h
  have hv (i : Fin k) : (j.val i).val = (l.val i).val := by
    have hi := congrArg (fun p : Fin k → Fin N => (p i).val + 1) h
    simpa only [boundedProfileBox_entry] using hi
  have hd : d = e := by
    apply Fin.ext
    rw [← j.property.2, ← l.property.2]
    exact Finset.sum_congr rfl (fun i _ => hv i)
  subst e
  have hj : j = l := by
    apply Subtype.ext
    funext i
    exact Fin.ext (hv i)
  subst l
  rfl

/-- All degree contributions at one arity cost at most one full box mass.
No induction hypothesis or mass bound is used. -/
theorem boundedPositiveProfile_mass_le (N k : ℕ) (hk : 2 ≤ k) :
    (∑ x : BoundedPositiveProfile N k,
      (∏ i, normalizedOrder ((x.2.val i).val)) * (1/32 : ℝ) ^ x.1.val) ≤
      orderMass N ^ k := by
  rw [← growth_tuple_box N k]
  apply Finset.sum_le_sum_of_injOn (boundedProfileBox hk)
  · intro a _ b _ h
    exact boundedProfileBox_injective hk h
  · exact Finset.subset_univ _
  · intro x _
    apply le_of_eq
    simp_rw [boundedProfileBox_entry]
    rw [growth_tuple_radius, x.2.property.2]
  · intro p _ _
    exact Finset.prod_nonneg (fun i _ =>
      mul_nonneg (normalizedOrder_nonneg _) (pow_nonneg (by norm_num) _))

end AcceleratedLogConcave.Tensor.FlowInduction
