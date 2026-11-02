import AcceleratedLogConcave.Tensor.SplitNorm

/-! Dimension-free zero padding, independently in each tensor slot.
The proof uses the actual rectangular Euclidean operator norm, including empty
index types. No positive dimension or nonempty split assumption is needed. -/
noncomputable section
open scoped BigOperators
namespace AcceleratedLogConcave.Tensor
open WithLp

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq J]

/-- Literal zero extension along a finite coordinate injection. -/
def coordinatePad (e : I ↪ J) (f : I → ℝ) (j : J) : ℝ :=
  ∑ i, if e i = j then f i else 0

lemma coordinatePad_pairing (e : I ↪ J) (f : I → ℝ) (g : J → ℝ) :
    (∑ j, g j * coordinatePad e f j) = ∑ i, g (e i) * f i := by
  simp only [coordinatePad, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp [mul_ite, eq_comm]

lemma coordinate_restrict_energy_le (e : I ↪ J) (g : J → ℝ) :
    (∑ i, (g (e i))^2) ≤ ∑ j, (g j)^2 := by
  calc
    _ = ∑ j ∈ Finset.univ.image e, (g j)^2 := by
      rw [Finset.sum_image]
      intro a _ b _ h
      exact e.injective h
    _ ≤ ∑ j, (g j)^2 :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (by
        intro j _ _
        exact sq_nonneg _)

variable {Slot : Type*} [Fintype Slot] [DecidableEq Slot] {d N : ℕ}

/-- Each slot may use its own injection, e.g. a different phase-space block. -/
def assignmentEmbedding (e : Slot → (Fin d ↪ Fin N)) :
    (Slot → Fin d) ↪ (Slot → Fin N) where
  toFun a i := e i (a i)
  inj' a b h := by
    funext i
    exact (e i).injective (congrFun h i)

/-- Tensor zero extension, not a tensor norm hypothesis. -/
def coordinatePadCoeff (e : Slot → (Fin d ↪ Fin N)) (T : Coeff Slot d) :
    Coeff Slot N := toLp 2 (coordinatePad (assignmentEmbedding e) T)

lemma split_pairing_as_assignment_sum (D : ℕ) (S : Finset Slot) (T : Coeff Slot D)
    (u : LeftAssignment D S → ℝ) (v : RightAssignment D S → ℝ) :
    (∑ r, ∑ c, u r * unfoldEquiv D S T r c * v c) =
      ∑ a, (u ((assignmentEquiv D S a).1) * v ((assignmentEquiv D S a).2)) * T a := by
  change (∑ r, ∑ c, u r * T ((assignmentEquiv D S).symm (r,c)) * v c) = _
  rw [← Fintype.sum_prod_type (f := fun p : LeftAssignment D S × RightAssignment D S =>
    u p.1 * T ((assignmentEquiv D S).symm p) * v p.2)]
  rw [← (assignmentEquiv D S).sum_comp]
  apply Finset.sum_congr rfl
  intro a _
  simp only [Equiv.symm_apply_apply]
  ring

lemma coordinatePadCoeff_pairing (e : Slot → (Fin d ↪ Fin N)) (S : Finset Slot)
    (T : Coeff Slot d) (u : LeftAssignment N S → ℝ) (v : RightAssignment N S → ℝ) :
    (∑ r, ∑ c, u r * unfoldEquiv N S (coordinatePadCoeff e T) r c * v c) =
      ∑ r, ∑ c, u (fun i => e i (r i)) * unfoldEquiv d S T r c *
        v (fun i => e i (c i)) := by
  rw [split_pairing_as_assignment_sum, split_pairing_as_assignment_sum]
  change (∑ a, _ * coordinatePad (assignmentEmbedding e) T a) = _
  rw [coordinatePad_pairing]
  rfl

/-- No dimension loss under independent zero padding of every tensor slot. -/
theorem splitNorm_coordinatePadCoeff_le (e : Slot → (Fin d ↪ Fin N))
    (S : Finset Slot) (T : Coeff Slot d) :
    splitNorm N S (coordinatePadCoeff e T) ≤ splitNorm d S T := by
  apply (splitNorm_le_iff_bilinear_sq N S _ _ (norm_nonneg _)).2
  intro u v
  rw [coordinatePadCoeff_pairing]
  have h := (splitNorm_le_iff_bilinear_sq d S T _ (norm_nonneg _)).1 (le_refl _)
    (fun r => u (fun i => e i (r i))) (fun c => v (fun i => e i (c i)))
  apply h.trans
  have hu := coordinate_restrict_energy_le
    (assignmentEmbedding (fun i : S => e i)) u
  have hv := coordinate_restrict_energy_le
    (assignmentEmbedding (fun i : {i : Slot // i ∉ S} => e i)) v
  change (∑ i : LeftAssignment d S, (u (fun j => e j (i j)))^2) ≤ _ at hu
  change (∑ i : RightAssignment d S, (v (fun j => e j (i j)))^2) ≤ _ at hv
  gcongr
  · exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  · exact mul_nonneg (sq_nonneg _) (Finset.sum_nonneg (fun _ _ => sq_nonneg _))

/-- For two independently embedded blocks the triangle factor is explicit. -/
theorem splitNorm_coordinatePadCoeff_add_le (e f : Slot → (Fin d ↪ Fin N))
    (S : Finset Slot) (T U : Coeff Slot d) :
    splitNorm N S (coordinatePadCoeff e T + coordinatePadCoeff f U) ≤
      splitNorm d S T + splitNorm d S U :=
  (splitNorm_add_le N S _ _).trans
    (add_le_add (splitNorm_coordinatePadCoeff_le e S T)
      (splitNorm_coordinatePadCoeff_le f S U))

end AcceleratedLogConcave.Tensor
