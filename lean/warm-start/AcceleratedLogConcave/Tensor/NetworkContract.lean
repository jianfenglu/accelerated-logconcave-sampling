import AcceleratedLogConcave.Tensor.NetworkReplacement
import AcceleratedLogConcave.Tensor.CoordinateReduction

/-! Literal child tensors for an actual cross-contraction network rewrite. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators Classical
namespace AcceleratedLogConcave.Tensor.Ordered.Graph
variable {n D : ℕ} {Edge : Type*} [Fintype Edge]
variable (g : Graph n Edge) (p : Fin (n+1)) (part : g.Slot p → Bool)
  (hI : ∃ q : g.InPort p, part (.inl q) = false)
  (hO : ∃ q : g.OutPort p, part (.inr q) = true)

def inheritedChildSlot (b : Bool) (s : g.Slot p) (hs : part s = b) :
    (g.replaceVertex p part).Slot (splitVertex p p b) :=
  match s with
  | .inl q => .inl (g.replaceInChildEmbedding p part hI b ⟨q,hs⟩)
  | .inr q => .inr (g.replaceOutChildEmbedding p part hO b ⟨q,hs⟩)

def joiningChildSlot : (b : Bool) → (g.replaceVertex p part).Slot (splitVertex p p b)
  | false => .inr ⟨some none, by simp [outgoing, replaceVertex]⟩
  | true => .inl ⟨some none, by simp [incoming, replaceVertex]⟩

omit [Fintype Edge] in
theorem inheritedChildSlot_value (b : Bool) (s : g.Slot p) (hs : part s = b)
    (c : Option Edge → Fin D) (k : Fin D) :
    Sum.elim (fun q => extendAssignment c k q.val) (fun q => extendAssignment c k q.val)
      (g.inheritedChildSlot p part hI hO b s hs) =
    Sum.elim (fun q : g.InPort p => c q.val) (fun q : g.OutPort p => c q.val) s := by
  cases s <;> simp [inheritedChildSlot, replaceInChildEmbedding, replaceOutChildEmbedding]

/-- An operand is evaluated using its inherited old slots and the fresh joining slot. -/
def contractChildTensor {r : ℕ} (b : Bool) (A : Coeff (Fin (r+2)) D)
    (i : Fin (r+2)) (a : Fin (r+1) → g.Slot p) (ha : ∀ u, part (a u) = b) :
    Coeff ((g.replaceVertex p part).Slot (splitVertex p p b)) D :=
  WithLp.toLp 2 (fun x => A (Fin.insertNth i (x (g.joiningChildSlot p part b))
    (fun u => x (g.inheritedChildSlot p part hI hO b (a u) (ha u)))))

theorem contractChildTensor_value {r : ℕ} (b : Bool) (A : Coeff (Fin (r+2)) D)
    (i : Fin (r+2)) (a : Fin (r+1) → g.Slot p) (ha : ∀ u, part (a u) = b)
    (c : Option Edge → Fin D) (k : Fin D) :
    g.contractChildTensor p part hI hO b A i a ha (Sum.elim
      (fun q => extendAssignment c k q.val) (fun q => extendAssignment c k q.val)) =
    A (Fin.insertNth i k (fun u => Sum.elim
      (fun q : g.InPort p => c q.val) (fun q : g.OutPort p => c q.val) (a u))) := by
  unfold contractChildTensor
  apply congrArg (fun x => A x)
  congr 1
  · cases b <;> rfl
  · funext u
    exact g.inheritedChildSlot_value p part hI hO b (a u) (ha u) c k

/-- The parent contraction identity is derived from actual child tensors, not assumed. -/
theorem crossContract_children_value {r s : ℕ}
    (A : Coeff (Fin (r+2)) D) (B : Coeff (Fin (s+2)) D)
    (i : Fin (r+2)) (j : Fin (s+2)) (e : g.Slot p ≃ Fin (r+s+2))
    (la : Fin (r+1) → g.Slot p) (ra : Fin (s+1) → g.Slot p)
    (hla : ∀ u, part (la u) = false) (hra : ∀ u, part (ra u) = true)
    (hel : ∀ u, e (la u) = Fin.cast (by omega : (r+1)+(s+1)=r+s+2) (Fin.castAdd (s+1) u))
    (her : ∀ u, e (ra u) = Fin.cast (by omega : (r+1)+(s+1)=r+s+2) (Fin.natAdd (r+1) u))
    (c : Option Edge → Fin D) :
    crossContract D A B i j (fun z => Sum.elim
      (fun q : g.InPort p => c q.val) (fun q : g.OutPort p => c q.val) (e.symm z)) =
    ∑ k : Fin D,
      g.contractChildTensor p part hI hO false A i la hla (Sum.elim
        (fun q => extendAssignment c k q.val) (fun q => extendAssignment c k q.val)) *
      g.contractChildTensor p part hI hO true B j ra hra (Sum.elim
        (fun q => extendAssignment c k q.val) (fun q => extendAssignment c k q.val)) := by
  simp only [contractChildTensor_value]
  simp only [crossContract, WithLp.ofLp_toLp]
  apply Finset.sum_congr rfl
  intro k _
  apply congrArg₂ (fun x y : ℝ => x*y)
  · apply congrArg (fun z => A z)
    congr 1
    funext u
    rw [← hel u, e.symm_apply_apply]
  · apply congrArg (fun z => B z)
    congr 1
    funext u
    rw [← her u, e.symm_apply_apply]

/-- The literal expression evaluator supplies the parent; no tensor identification is assumed. -/
theorem evaluate_contract_children_value {Name : Type*} {σ : CoefficientSignature Name}
    {r s : ℕ} (ρ : CoefficientEnvironment σ D) (H : EuclideanSpace ℝ (Fin D) → ℝ)
    (E : Expr σ (r+2)) (F : Expr σ (s+2)) (x : EuclideanSpace ℝ (Fin D))
    (i : Fin (r+2)) (j : Fin (s+2)) (e : g.Slot p ≃ Fin (r+s+2))
    (la : Fin (r+1) → g.Slot p) (ra : Fin (s+1) → g.Slot p)
    (hla : ∀ u, part (la u) = false) (hra : ∀ u, part (ra u) = true)
    (hel : ∀ u, e (la u) = Fin.cast (by omega : (r+1)+(s+1)=r+s+2) (Fin.castAdd (s+1) u))
    (her : ∀ u, e (ra u) = Fin.cast (by omega : (r+1)+(s+1)=r+s+2) (Fin.natAdd (r+1) u))
    (c : Option Edge → Fin D) :
    Expr.evaluate ρ H (.contract E F i j) x (fun z => Sum.elim
      (fun q : g.InPort p => c q.val) (fun q : g.OutPort p => c q.val) (e.symm z)) =
    ∑ k : Fin D,
      g.contractChildTensor p part hI hO false (Expr.evaluate ρ H E x) i la hla (Sum.elim
        (fun q => extendAssignment c k q.val) (fun q => extendAssignment c k q.val)) *
      g.contractChildTensor p part hI hO true (Expr.evaluate ρ H F x) j ra hra (Sum.elim
        (fun q => extendAssignment c k q.val) (fun q => extendAssignment c k q.val)) := by
  exact g.crossContract_children_value p part hI hO (Expr.evaluate ρ H E x)
    (Expr.evaluate ρ H F x) i j e la ra hla hra hel her c

end AcceleratedLogConcave.Tensor.Ordered.Graph
