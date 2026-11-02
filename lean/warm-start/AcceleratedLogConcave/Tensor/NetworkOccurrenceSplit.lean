import AcceleratedLogConcave.Tensor.NetworkSyntaxState

/-! Stable syntax child order and independently chosen graph child orientation. -/
noncomputable section
open scoped Classical
namespace AcceleratedLogConcave.Tensor.Ordered.Graph

 def splitOccurrenceEquiv {m n : ℕ} (e : Fin m ≃ Fin n) (p : Fin m) (b : Bool) :
    Fin (m+1) ≃ Fin (n+1) :=
  (finSuccEquiv' p.succ).trans ((Equiv.optionCongr e).trans
    (finSuccEquiv' (if b then (e p).castSucc else (e p).succ)).symm)

 theorem splitOccurrenceEquiv_right {m n : ℕ} (e : Fin m ≃ Fin n) (p : Fin m) (b : Bool) :
    splitOccurrenceEquiv e p b p.succ = if b then (e p).castSucc else (e p).succ := by
  simp [splitOccurrenceEquiv]

 theorem splitOccurrenceEquiv_left {m n : ℕ} (e : Fin m ≃ Fin n) (p : Fin m) (b : Bool) :
    splitOccurrenceEquiv e p b p.castSucc = if b then (e p).succ else (e p).castSucc := by
  have hp : finSuccEquiv' p.succ p.castSucc = some p := by
    rw [← Fin.succAbove_succ_self p]
    exact finSuccEquiv'_succAbove _ _
  cases b <;> simp only [splitOccurrenceEquiv, Equiv.trans_apply, hp,
    Equiv.optionCongr_apply, Option.map_some, Bool.false_eq_true, ↓reduceIte,
    finSuccEquiv'_symm_some, Fin.succAbove_succ_self, Fin.succAbove_castSucc_self]

 theorem splitOccurrenceEquiv_other {m n : ℕ} (e : Fin m ≃ Fin n) (p v : Fin m)
    (hv : v ≠ p) (b : Bool) :
    splitOccurrenceEquiv e p b (p.succ.succAbove v) = (e p).succ.succAbove (e v) := by
  simp only [splitOccurrenceEquiv, Equiv.trans_apply, finSuccEquiv'_succAbove,
    Equiv.optionCongr_apply, Option.map_some, finSuccEquiv'_symm_some]
  cases b
  · rfl
  · have hne : e v ≠ e p := fun h => hv (e.injective h)
    change (e p).castSucc.succAbove (e v) = (e p).succ.succAbove (e v)
    rcases lt_or_gt_of_ne hne with h | h
    · rw [Fin.succAbove_castSucc_of_lt _ _ h, Fin.succAbove_succ_of_le _ _ h.le]
    · rw [Fin.succAbove_castSucc_of_le _ _ h.le, Fin.succAbove_succ_of_lt _ _ h]

end AcceleratedLogConcave.Tensor.Ordered.Graph
