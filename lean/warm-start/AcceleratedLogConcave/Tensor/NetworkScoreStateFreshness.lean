import AcceleratedLogConcave.Tensor.NetworkSyntaxState

noncomputable section
open scoped Classical
namespace AcceleratedLogConcave.Tensor.Ordered.Graph
open AdjointReduction ReductionRecords
variable {Name : Type*} {σ : CoefficientSignature Name} {r : ℕ}
variable (node : NodeAddress) (E : Expr σ (r+2)) (i : Fin (r+2))
    (J : List LabelOrigin) (before after : List (TaggedPending σ))

/-- Reservation inventory excludes the current adjoint wire from every old derivative label. -/
theorem adjoint_ibp_not_attached
    (hinv : (originInventory (before ++ [.formula node (.adjoint i E) J] ++ after)).Nodup) :
    .ibp node ∉ attachedOrigins (before ++ [.formula node (.adjoint i E) J] ++ after) := by
  have hd := (Multiset.nodup_add.mp hinv).2.2
  have hf : .ibp node ∈ forestFutureOrigins (before ++ [.formula node (.adjoint i E) J] ++ after) := by
    simp [forestFutureOrigins,List.map_append,List.sum_append,TaggedPending.futureOrigins,futureOrigins]
  intro ha
  exact (Multiset.disjoint_left.mp hd) (by simpa using ha) hf

/-- Support uniqueness also excludes a previously retained score output at this node. -/
theorem adjoint_score_not_mem
    (hs : (forestSupport (before ++ [.formula node (.adjoint i E) J] ++ after)).Nodup)
    (K : List LabelOrigin) (hK : K ≠ []) :
    .score node K hK ∉ before ++ [.formula node (.adjoint i E) J] ++ after := by
  have hsp : (forestSupport before ++
      (expressionSupport node (.adjoint i E) ++ forestSupport after)).Nodup := by
    simpa [forestSupport,TaggedPending.support,List.append_assoc] using hs
  have hm : OccurrenceTag.score node ∈ expressionSupport node (.adjoint i E) := by simp
  intro hp
  rcases List.mem_append.mp hp with hp | hp
  · rcases List.mem_append.mp hp with hp | hp
    · have hb : OccurrenceTag.score node ∈ forestSupport before :=
        List.mem_flatMap.mpr ⟨_,hp,by simp [TaggedPending.support]⟩
      exact (List.nodup_append.mp hsp).2.2 _ hb _
        (List.mem_append_left _ hm) rfl
    · simp at hp
  · have ha : OccurrenceTag.score node ∈ forestSupport after :=
      List.mem_flatMap.mpr ⟨_,hp,by simp [TaggedPending.support]⟩
    exact (List.nodup_append.mp (List.nodup_append.mp hsp).2.1).2.2 _ hm _ ha rfl

/-- Shared freshness theorem for both actual score and principal-IBP state updates.
It uses canonical support and reservation inventory, not injective numeric labels. -/
theorem adjoint_pendingPortOrigin_ne
    (hs : (forestSupport (before ++ [.formula node (.adjoint i E) J] ++ after)).Nodup)
    (hinv : (originInventory (before ++ [.formula node (.adjoint i E) J] ++ after)).Nodup)
    (p : TaggedPending σ) (hp : p ∈ before ++ [.formula node (.adjoint i E) J] ++ after)
    (u : pendingPorts p) (o : LabelOrigin) (hu : pendingPortOrigin p u = some o) :
    o ≠ .ibp node := by
  have hl : .ibp node ∉ p.labels := by
    intro h
    exact adjoint_ibp_not_attached node E i J before after hinv
      (List.mem_flatMap.mpr ⟨p,hp,h⟩)
  cases p with
  | formula a F K =>
    cases u with
    | inr v => cases hu
    | inl v =>
      have he : o = K.get v := Option.some.inj hu.symm
      intro hn
      apply hl
      change .ibp node ∈ K
      rw [←hn,he]
      exact List.get_mem K v
  | score a K hK =>
    cases u with
    | inl v =>
      have he : o = K.get v := Option.some.inj hu.symm
      intro hn
      apply hl
      change .ibp node ∈ K
      rw [←hn,he]
      exact List.get_mem K v
    | inr v =>
      have he : o = .ibp a := Option.some.inj hu.symm
      intro hn
      have ha : a = node := LabelOrigin.ibp.inj (he.symm.trans hn)
      subst a
      exact adjoint_score_not_mem node E i J before after hs K hK hp

namespace SyntaxState
/-- The graph occurrence bijection transfers the canonical freshness invariant. -/
theorem adjoint_origin_fresh
    (S : SyntaxState (before ++ [.formula node (.adjoint i E) J] ++ after))
    (hs : (forestSupport (before ++ [.formula node (.adjoint i E) J] ++ after)).Nodup)
    (hinv : (originInventory (before ++ [.formula node (.adjoint i E) J] ++ after)).Nodup)
    (v : Fin (S.n+1)) (u : pendingPorts (S.pending v)) (o : LabelOrigin)
    (hu : pendingPortOrigin (S.pending v) u = some o) : o ≠ .ibp node := by
  apply adjoint_pendingPortOrigin_ne node E i J before after hs hinv (S.pending v) _ u o hu
  have he := S.occurrence_spec (S.occurrence.symm v)
  simp only [Equiv.apply_symm_apply] at he
  rw [he]
  exact List.get_mem _ _
end SyntaxState
end AcceleratedLogConcave.Tensor.Ordered.Graph
