import AcceleratedLogConcave.Tensor.NetworkOccurrenceSplit

/-! Exact list-position bookkeeping when one syntax occurrence becomes two. -/
noncomputable section
namespace AcceleratedLogConcave.Tensor.Ordered.Graph
variable {α : Type*}

def forestParentIndex (before after : List α) (parent : α) :
    Fin (before ++ [parent] ++ after).length := ⟨before.length, by simp⟩

theorem forestSplit_length (before after : List α) (parent left right : α) :
    (before ++ [left,right] ++ after).length = (before ++ [parent] ++ after).length + 1 := by
  simp
  omega

 theorem forestSplit_get_left (before after : List α) (parent left right : α) :
    (before ++ [left,right] ++ after).get
      (Fin.cast (forestSplit_length before after parent left right).symm
        (forestParentIndex before after parent).castSucc) = left := by
  simp [forestParentIndex]

 theorem forestSplit_get_right (before after : List α) (parent left right : α) :
    (before ++ [left,right] ++ after).get
      (Fin.cast (forestSplit_length before after parent left right).symm
        (forestParentIndex before after parent).succ) = right := by
  simp [forestParentIndex]

 theorem forestSplit_get_other (before after : List α) (parent left right : α)
    (v : Fin (before ++ [parent] ++ after).length)
    (hv : v ≠ forestParentIndex before after parent) :
    (before ++ [left,right] ++ after).get
      (Fin.cast (forestSplit_length before after parent left right).symm
        ((forestParentIndex before after parent).succ.succAbove v)) =
      (before ++ [parent] ++ after).get v := by
  have hne : v.val ≠ before.length := by
    intro h
    exact hv (Fin.ext h)
  rcases lt_or_gt_of_ne hne with h | h
  · rw [Fin.succAbove_succ_of_le _ _ (by exact Nat.le_of_lt h)]
    simp [h]
  · rw [Fin.succAbove_succ_of_lt _ _ (by exact h)]
    have h₁ : ¬ v.val + 1 < before.length + 2 := by omega
    have h₂ : ¬ v.val < before.length + 1 := by omega
    have h₃ : ¬ v.val + 1 < before.length := by omega
    simp only [List.get_eq_getElem, Fin.val_cast, Fin.val_succ, List.getElem_append,
      List.length_append, List.length_cons, List.length_nil,
      h₁, h₂, h₃, Nat.not_lt.mpr h.le, dite_false]
    congr 1; omega

/-- A stable forest split is compatible with either physical child order. -/
theorem forestSplit_occurrence {n : ℕ} (before after : List α) (parent left right : α)
    (e : Fin (before ++ [parent] ++ after).length ≃ Fin n) (b : Bool)
    (P : Fin n → α) (Q : Fin (n+1) → α)
    (hP : ∀ v, P (e v) = (before ++ [parent] ++ after).get v)
    (hleft : Q (if b then (e (forestParentIndex before after parent)).succ
      else (e (forestParentIndex before after parent)).castSucc) = left)
    (hright : Q (if b then (e (forestParentIndex before after parent)).castSucc
      else (e (forestParentIndex before after parent)).succ) = right)
    (hother : ∀ v, v ≠ forestParentIndex before after parent →
      Q ((e (forestParentIndex before after parent)).succ.succAbove (e v)) = P (e v)) :
    ∀ u, Q (splitOccurrenceEquiv e (forestParentIndex before after parent) b
      (Fin.cast (forestSplit_length before after parent left right) u)) =
      (before ++ [left,right] ++ after).get u := by
  intro u
  let p := forestParentIndex before after parent
  let k := Fin.cast (forestSplit_length before after parent left right) u
  have hu : u = Fin.cast (forestSplit_length before after parent left right).symm k := by rfl
  by_cases hr : k = p.succ
  · rw [hu]
    change Q (splitOccurrenceEquiv e p b k) = _
    rw [hr, splitOccurrenceEquiv_right, hright]
    exact (forestSplit_get_right before after parent left right).symm
  obtain ⟨v, hv⟩ := Fin.exists_succAbove_eq hr
  by_cases hp : v = p
  · subst v
    have hk : k = p.castSucc := hv.symm.trans (Fin.succAbove_succ_self p)
    rw [hu]
    change Q (splitOccurrenceEquiv e p b k) = _
    rw [hk, splitOccurrenceEquiv_left, hleft]
    exact (forestSplit_get_left before after parent left right).symm
  · rw [hu]
    change Q (splitOccurrenceEquiv e p b k) = _
    rw [← hv, splitOccurrenceEquiv_other e p v hp b, hother v hp, hP v]
    exact (forestSplit_get_other before after parent left right v hp).symm

end AcceleratedLogConcave.Tensor.Ordered.Graph
