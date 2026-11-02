import AcceleratedLogConcave.Oracle.NoisyLayer

/-! Pure direct rows extracted from the actual mean graph's anchor coefficients.
No gradient, random draw, or evaluator certificate occurs in these rows. -/
noncomputable section
namespace AcceleratedLogConcave.Oracle.PrefixDirect
open AffineLowering NoisyLayer
open AcceleratedLogConcave.Numerics.AffineGraph
open scoped BigOperators

/-- Enumerated literal coefficients; the enumeration retains every anchor. -/
def table (M : MeanGeometry m) (nodes : Fin n ≃ M.MeanNode)
    (anchors : Fin a ≃ M.Anchor) (r σ : ℝ) : Fin (n*a) → ℝ :=
  fun k => M.centerForm r σ (nodes (finProdFinEquiv.symm k).1)
    (.inl (anchors (finProdFinEquiv.symm k).2))

def slot (j : Fin n) (k : Fin a) : Fin (n*a) := finProdFinEquiv (j,k)

abbrev row (slots : Fin (n*a) → Fin C) (x : Ref Γ .point)
    (anchor : Fin a → Ref Γ .point) (j : Fin n) : Prog C Γ .point :=
  affineRow [] x (List.ofFn fun k => (slots (slot j k), anchor k))

theorem run_row (M : MeanGeometry m) (nodes : Fin n ≃ M.MeanNode)
    (anchors : Fin a ≃ M.Anchor) (r σ : ℝ)
    (slots : Fin (n*a) → Fin C) (x : Ref Γ .point)
    (anchor : Fin a → Ref Γ .point)
    (G : Point d → Point d) (input : Inputs d C) (env : Env d Γ)
    (y0 g0 : Point d) (ζ : Fin m → M.Kernel → Point d)
    (htable : input.coefficient ∘ slots = table M nodes anchors r σ)
    (hanchor : ∀ k, storedPoint env (anchor k) = M.anchorValues y0 g0 ζ (anchors k))
    (j : Fin n) (tape : Tape d (row slots x anchor j)) :
    run (row slots x anchor j) G input env tape =
      pointResult (M.direct r σ (storedPoint env x) y0 g0 ζ (nodes j)) [] := by
  rw [run_affineRow_ofFn]
  have hs (k : Fin a) : input.coefficient (slots (slot j k)) =
      M.centerForm r σ (nodes j) (.inl (anchors k)) := by
    simpa [table, slot] using congrFun htable (slot j k)
  simp only [hs, hanchor, MeanGeometry.direct]
  congr 2
  exact anchors.sum_comp (fun k => M.centerForm r σ (nodes j) (.inl k) •
    M.anchorValues y0 g0 ζ k)

theorem syntaxCount_row (kind : EventKind) (slots : Fin (n*a) → Fin C)
    (x : Ref Γ .point) (anchor : Fin a → Ref Γ .point) (j : Fin n) :
    syntaxCount kind (row slots x anchor j) = 0 :=
  syntaxCount_affineRow kind [] x _

end AcceleratedLogConcave.Oracle.PrefixDirect
