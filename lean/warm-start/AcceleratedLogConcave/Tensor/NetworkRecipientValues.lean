import AcceleratedLogConcave.Tensor.NetworkRecipientSlots

noncomputable section
open scoped Classical
namespace AcceleratedLogConcave.Tensor.Ordered.Graph
variable {n D : ℕ} {Edge : Type*} [Fintype Edge] (g : Graph n Edge)
    (p q : Fin (n+1)) (hne : p ≠ q)

private theorem cast_family_apply {g h : Graph n Edge} (eq : g = h)
    (T : g.Tensors D) (v : Fin (n+1)) (a : h.Slot v → Fin D) :
    (eq ▸ T) v a = T v (a ∘ ((eq ▸ Equiv.refl (g.Slot v)) : g.Slot v ≃ h.Slot v)) := by
  subst h
  rfl

/-- The source factor is evaluated at the actual fresh coordinate and old ports. -/
theorem recipientPairFamily_source_apply (T : g.Tensors D)
    (A : Fin D → Coeff (g.Slot p) D) (B : Fin D → Coeff (g.Slot q) D)
    (a : (g.recipientGraph p q hne).Slot p → Fin D) :
    g.recipientPairFamily p q hne T A B p a =
      A (a (g.recipientSourcePorts p q hne (.inr ())))
        (fun u => a (g.recipientSourcePorts p q hne (.inl u))) := by
  unfold recipientPairFamily recipientSourcePorts
  split_ifs with h
  · let he : g.addOrderedEdge p q h = g.recipientGraph p q hne := by simp [recipientGraph, h]
    change (he ▸ g.addedPairFamily p q h T A B) p a = _
    rw [cast_family_apply, addedPairFamily_source]
    simp only [dite_eq_left h]
    rfl
  · let he : g.addOrderedEdge q p (by omega) = g.recipientGraph p q hne := by simp [recipientGraph, h]
    change (he ▸ g.addedPairFamily q p (by omega) T B A) p a = _
    rw [cast_family_apply, addedPairFamily_target]
    simp only [dite_eq_right h]
    rfl

/-- The recipient factor uses the same joining coordinate, regardless of orientation. -/
theorem recipientPairFamily_target_apply (T : g.Tensors D)
    (A : Fin D → Coeff (g.Slot p) D) (B : Fin D → Coeff (g.Slot q) D)
    (a : (g.recipientGraph p q hne).Slot q → Fin D) :
    g.recipientPairFamily p q hne T A B q a =
      B (a (g.recipientTargetPorts p q hne (.inr ())))
        (fun u => a (g.recipientTargetPorts p q hne (.inl u))) := by
  unfold recipientPairFamily recipientTargetPorts
  split_ifs with h
  · let he : g.addOrderedEdge p q h = g.recipientGraph p q hne := by simp [recipientGraph, h]
    change (he ▸ g.addedPairFamily p q h T A B) q a = _
    rw [cast_family_apply, addedPairFamily_target]
    simp only [dite_eq_left h]
    rfl
  · let he : g.addOrderedEdge q p (by omega) = g.recipientGraph p q hne := by simp [recipientGraph, h]
    change (he ▸ g.addedPairFamily q p (by omega) T B A) q a = _
    rw [cast_family_apply, addedPairFamily_source]
    simp only [dite_eq_right h]
    rfl

 theorem recipientPairFamily_other_apply (T : g.Tensors D)
    (A : Fin D → Coeff (g.Slot p) D) (B : Fin D → Coeff (g.Slot q) D)
    (v : Fin (n+1)) (hvp : v ≠ p) (hvq : v ≠ q)
    (a : (g.recipientGraph p q hne).Slot v → Fin D) :
    g.recipientPairFamily p q hne T A B v a =
      T v (fun u => a (g.recipientOtherPorts p q hne v hvp hvq u)) := by
  unfold recipientPairFamily recipientOtherPorts
  split_ifs with h
  · let he : g.addOrderedEdge p q h = g.recipientGraph p q hne := by simp [recipientGraph, h]
    change (he ▸ g.addedPairFamily p q h T A B) v a = _
    rw [cast_family_apply, addedPairFamily_other g p q h T A B v hvp hvq]
    simp only [dite_eq_left h]
    rfl
  · let he : g.addOrderedEdge q p (by omega) = g.recipientGraph p q hne := by simp [recipientGraph, h]
    change (he ▸ g.addedPairFamily q p (by omega) T B A) v a = _
    rw [cast_family_apply, addedPairFamily_other g q p _ T B A v hvq hvp]
    simp only [dite_eq_right h]
    rfl

/-- The old source factor is discarded by the actual principal replacement. -/
theorem recipientPairFamily_replaceTensorAt_source (T : g.Tensors D)
    (U : Coeff (g.Slot p) D)
    (A : Fin D → Coeff (g.Slot p) D) (B : Fin D → Coeff (g.Slot q) D) :
    g.recipientPairFamily p q hne (g.replaceTensorAt p T U) A B =
      g.recipientPairFamily p q hne T A B := by
  funext v
  ext a
  by_cases hp : v = p
  · subst v
    rw [recipientPairFamily_source_apply, recipientPairFamily_source_apply]
  by_cases hq : v = q
  · subst v
    rw [recipientPairFamily_target_apply, recipientPairFamily_target_apply]
  rw [recipientPairFamily_other_apply g p q hne _ _ _ v hp hq,
    recipientPairFamily_other_apply g p q hne _ _ _ v hp hq]
  rw [replaceTensorAt_other g p T U v hp]

 theorem principalRecipientFamily_replaceTensorAt_source
    (T : EuclideanSpace ℝ (Fin D) → g.Tensors D)
    (U : EuclideanSpace ℝ (Fin D) → Coeff (g.Slot p) D)
    (A : EuclideanSpace ℝ (Fin D) → Fin D → Coeff (g.Slot p) D)
    (x : EuclideanSpace ℝ (Fin D)) :
    g.principalRecipientFamily p q hne (fun y => g.replaceTensorAt p (T y) (U y)) A x =
      g.principalRecipientFamily p q hne T A x := by
  unfold principalRecipientFamily
  have hderiv : g.recipientDerivativeTensor q (fun y => g.replaceTensorAt p (T y) (U y)) x =
      g.recipientDerivativeTensor q T x := by
    funext k
    ext a
    simp [recipientDerivativeTensor, hne.symm]
  rw [hderiv, recipientPairFamily_replaceTensorAt_source]

end AcceleratedLogConcave.Tensor.Ordered.Graph
