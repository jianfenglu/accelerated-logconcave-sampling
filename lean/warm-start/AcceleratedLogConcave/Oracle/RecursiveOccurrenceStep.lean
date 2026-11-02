import AcceleratedLogConcave.Oracle.RecursiveExecutableOccurrenceStability
import AcceleratedLogConcave.Oracle.RecursiveCallOccurrence

/-! Stability of one actual nonterminal source call from its occurrence inventory.
Main-child hypotheses are extracted only when a layer exists. At zero layers,
the existing final-only endpoint applies and the row parameter is arbitrary. -/
noncomputable section
set_option autoImplicit false
namespace AcceleratedLogConcave.Oracle.RecursiveCall
open Numerics.AffineGraph RecursiveExecutable FixedTapeStability
open scoped BigOperators

variable {d m n ns a h : ℕ} (C : Source m n ns)
    (anchors : Fin a ≃ C.M.Anchor) (seeds : Fin h ≃ Fin m × C.M.Kernel)
    (ht : 0 < C.t) (htq : C.t ≤ 1/4) (scale : ℝ)

local notation "E" => meanCore C.M C.nodes anchors seeds C.S C.snodes
  C.Ds C.δ C.t C.w C.layers ht htq scale

/-- A common child bound over actual occurrences suffices. Row nonnegativity
and the row certificate are required only when the main loop is nonempty. -/
theorem childStable_occurrence_step (p : State) (hq : 1/2 < p.precision)
    (G : Point d → Point d) (κ A : ℝ)
    (hm : 0 < m) (hr : 0 ≤ p.radius) (hκ : 0 ≤ κ) (hpsi : C.M.psi ≤ C.M.R^4)
    (hchildren : ∀ o : Occurrence C.layers n ns m,
      ChildStable (E (C.child p o).radius (C.child p o).width (C.child p o).precision).program
        (E (C.child p o).radius (C.child p o).width (C.child p o).precision).coefficient G κ)
    (hA : 0 < C.layers → 0 ≤ A)
    (hrow : 0 < C.layers → ∀ i : C.M.MeanNode,
      ∑ j, |C.M.matrix p.radius p.width i j| ≤ A) :
    ChildStable (E p.radius p.width p.precision).program
      (E p.radius p.width p.precision).coefficient G
      (meanGrowth C.layers κ κ p.radius (backwardEnd C.M.R) A) := by
  rcases Nat.eq_zero_or_pos C.layers with hz | hpos
  · rw [hz]
    apply meanCore_childStable_zero_growth C.M C.nodes anchors seeds C.S C.snodes
      C.Ds C.δ C.t C.w ht htq scale p.radius p.width p.precision
      hq G κ κ A hm hm hr hκ hκ hpsi
    · intro i
      have hi := hchildren (Occurrence.activeFinal i)
      dsimp only [Source.child, Occurrence.activeFinal] at hi
      rw [hz] at hi
      exact hi
    · intro i
      have hi := hchildren (Occurrence.samplingFinal i)
      dsimp only [Source.child, Occurrence.samplingFinal] at hi
      rw [hz] at hi
      exact hi
  · let k : Fin C.layers := ⟨0, hpos⟩
    apply meanCore_childStable_step C.M C.nodes anchors seeds C.S C.snodes
      C.Ds C.δ C.t C.w C.layers ht htq scale p.radius p.width p.precision
      hq G κ κ A hm hm hr hκ hκ (hA hpos) hpsi
    · intro i
      exact hchildren (Occurrence.meanMain k i)
    · intro i
      exact hchildren (Occurrence.activeFinal i)
    · intro i
      exact hchildren (Occurrence.samplingMain k i)
    · intro i
      exact hchildren (Occurrence.samplingFinal i)
    · exact hrow hpos

end AcceleratedLogConcave.Oracle.RecursiveCall
