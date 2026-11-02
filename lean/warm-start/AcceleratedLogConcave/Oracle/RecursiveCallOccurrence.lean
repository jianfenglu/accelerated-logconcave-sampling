import AcceleratedLogConcave.Oracle.RecursiveExecutableWork
import AcceleratedLogConcave.Oracle.RecursiveExecutableDomain

/-! Occurrences of mean-to-mean calls in the actual source constructor.
The private sampler is flattened to its main and final mean calls. A layer
index records an occurrence, even when different occurrences have equal scalar
parameters. No tape alignment or probabilistic interpretation is asserted. -/
noncomputable section
open scoped BigOperators
set_option autoImplicit false
namespace AcceleratedLogConcave.Oracle.RecursiveCall
open Numerics.AffineGraph RecursiveMeanPublicTable
variable {m n ns : ℕ}

/-- Static source parameters; this record contains no analytic certificates. -/
structure Source (m n ns : ℕ) where
  M : MeanGeometry m
  nodes : Fin n ≃ M.MeanNode
  mesh : IntervalMesh 0 (samplingEnd (M.R / backwardEnd M.R))
  snodes : Fin ns ≃ mesh.Source m
  Ds : ℝ
  δ : ℝ
  t : ℝ
  w : ℝ
  layers : ℕ

abbrev Source.S (C : Source m n ns) := RecursiveExecutable.privateGeometry C.M C.mesh

structure State where
  radius : ℝ
  width : ℝ
  precision : ℝ

/-- The two main families carry an actual layer index. Finals survive at zero layers. -/
abbrev Occurrence (layers n ns m : ℕ) :=
  ((Fin layers × Fin ns) ⊕ Fin ns) ⊕ ((Fin layers × Fin n) ⊕ Fin m)

namespace Occurrence
variable {layers : ℕ}
def samplingMain (k : Fin layers) (i : Fin ns) : Occurrence layers n ns m :=
  .inl (.inl (k, i))
def samplingFinal (i : Fin ns) : Occurrence layers n ns m := .inl (.inr i)
def meanMain (k : Fin layers) (i : Fin n) : Occurrence layers n ns m := .inr (.inl (k, i))
def activeFinal (i : Fin m) : Occurrence layers n ns m := .inr (.inr i)

/-- Cost is determined by the occurrence tag, not by the numerical precision drop. -/
def cost : Occurrence layers n ns m → ℕ
  | .inr (.inr _) => 0
  | _ => 1

theorem cost_le_one (o : Occurrence layers n ns m) : cost o ≤ 1 := by
  rcases o with (⟨k, i⟩ | i) | (⟨k, i⟩ | i) <;> simp [cost]

theorem zero_layers (o : Occurrence 0 n ns m) :
    (∃ i, o = samplingFinal i) ∨ (∃ i, o = activeFinal i) := by
  rcases o with (⟨k, i⟩ | i) | (⟨k, i⟩ | i)
  · exact Fin.elim0 k
  · exact Or.inl ⟨i, rfl⟩
  · exact Fin.elim0 k
  · exact Or.inr ⟨i, rfl⟩
end Occurrence

/-- Literal scalar arguments of the four recursive `meanCore` families. -/
def Source.child (C : Source m n ns) (p : State) : Occurrence C.layers n ns m → State
  | .inl (.inl (_, i)) =>
      ⟨C.S.radius p.radius (C.snodes i),
        mainWidth ns p.radius C.S.R C.Ds (p.radius ^ 2), p.precision - 1/4⟩
  | .inl (.inr i) =>
      ⟨C.S.radius p.radius (C.snodes i),
        SourceExecutableTables.samplingFinalWidth C.S p.radius, p.precision - 1/4⟩
  | .inr (.inl (_, i)) =>
      ⟨C.M.radius p.radius (C.nodes i),
        mainWidth n p.radius C.M.R C.Ds
          (SourceMeanExecutable.rowBound (m := m) p.radius p.width C.δ C.t C.w),
        p.precision - 1/4⟩
  | .inr (.inr _) =>
      ⟨p.radius * C.M.R, finalWidth C.M.R p.width, p.precision - C.t⟩

/-- A source call is available only when the parent actually selects its nonterminal branch. -/
def Edge (C : Source m n ns) (p : State) (o : Occurrence C.layers n ns m) (c : State) : Prop :=
  1/2 < p.precision ∧ c = C.child p o

theorem no_edge_of_terminal (C : Source m n ns) {p c : State}
    (hq : p.precision ≤ 1/2) (o : Occurrence C.layers n ns m) : ¬ Edge C p o c := by
  intro h
  exact (not_lt_of_ge hq) h.1

theorem Edge.precision_eq {C : Source m n ns} {p c : State}
    {o : Occurrence C.layers n ns m} (h : Edge C p o c) :
    c.precision = p.precision - (o.cost : ℝ)/4 - (1 - (o.cost : ℝ))*C.t := by
  rcases h with ⟨_, rfl⟩
  rcases o with (⟨k, i⟩ | i) | (⟨k, i⟩ | i) <;> simp [Source.child, Occurrence.cost]

theorem Edge.positive {C : Source m n ns} {p c : State}
    {o : Occurrence C.layers n ns m} (h : Edge C p o c)
    (hm : 0 < m) (hDs : 0 < C.Ds) (hδ : 0 < C.δ)
    (hr : 0 < p.radius) (hσ : 0 < p.width) : 0 < c.radius ∧ 0 < c.width := by
  rcases h with ⟨_, rfl⟩
  rcases o with (⟨k, i⟩ | i) | (⟨k, i⟩ | i)
  · exact ⟨C.S.radius_pos _ hr _, RecursiveExecutableDomain.sampling_main_width_pos
      C.S C.snodes _ _ hm hr hDs⟩
  · exact ⟨C.S.radius_pos _ hr _, RecursiveExecutableDomain.sampling_final_width_pos C.S _ hr⟩
  · exact ⟨C.M.radius_pos _ hr _, RecursiveExecutableDomain.mean_main_width_pos
      C.M C.nodes _ _ _ _ _ _ hr hσ hDs hδ⟩
  · exact ⟨mul_pos hr C.M.R_pos, RecursiveExecutableDomain.mean_final_width_pos C.M _ hσ⟩

/-- The occurrence inventory is certified against the published exact query
recurrence of the actual constructor. It does not identify tapes or environments. -/
theorem queries_eq_sum_occurrences (C : Source m n ns) {a h : ℕ}
    (anchors : Fin a ≃ C.M.Anchor) (seeds : Fin h ≃ Fin m × C.M.Kernel)
    (ht : 0 < C.t) (htq : C.t ≤ 1/4) (scale : ℝ) (p : State) (hq : 1/2 < p.precision) :
    queryCount (RecursiveExecutable.meanCore C.M C.nodes anchors seeds C.S C.snodes
      C.Ds C.δ C.t C.w C.layers ht htq scale p.radius p.width p.precision).program =
    ∑ o : Occurrence C.layers n ns m,
      queryCount (RecursiveExecutable.meanCore C.M C.nodes anchors seeds C.S C.snodes
        C.Ds C.δ C.t C.w C.layers ht htq scale (C.child p o).radius
        (C.child p o).width (C.child p o).precision).program := by
  rw [RecursiveExecutable.queries_nonterminal C.M C.nodes anchors seeds C.S C.snodes
    C.Ds C.δ C.t C.w C.layers ht htq scale p.radius p.width p.precision hq]
  simp only [Occurrence, Fintype.sum_sum_type, Fintype.sum_prod_type, Source.child]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  simp only [Nat.cast_id, add_assoc]
  rfl

end AcceleratedLogConcave.Oracle.RecursiveCall
