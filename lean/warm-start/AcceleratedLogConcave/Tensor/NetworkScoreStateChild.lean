import AcceleratedLogConcave.Tensor.NetworkScoreStateSlots
import AcceleratedLogConcave.Tensor.NetworkContractChildSyntax

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Classical
namespace AcceleratedLogConcave.Tensor.Ordered.Graph
open AdjointReduction CoordinateReduction ReductionRecords
variable {Name : Type*} {σ : CoefficientSignature Name}
variable {n : ℕ} {Edge : Type*} (g : Graph n Edge) (p : Fin (n+1))
    (part : g.Slot p → Bool)
    (hi : ∃ q : g.InPort p, part (.inl q) = false)
    (ho : ∃ q : g.OutPort p, part (.inr q) = true)

def scoreChildSyntax {j : ℕ} (J : List LabelOrigin) (hJ : J.length = j)
    (A : List (Fin j)) (hA : A ≠ []) (node : NodeAddress) (b : Bool)
    (selected : Fin A.length ≃ {z : g.Slot p // part z = b}) :
    (g.replaceVertex p part).SyntaxAt (σ := σ) (splitVertex p p b) :=
  ⟨.score node (A.map (fun u => J.get (Fin.cast hJ.symm u))) (by simpa using hA),
    (g.scoreChildEquiv p part hi ho b selected).symm.trans
      (Equiv.sumCongr (finCongr (List.length_map _).symm) (Equiv.refl Unit))⟩

def scoreOriginWire (node : NodeAddress) (wire : LabelOrigin → Option Edge)
    (o : LabelOrigin) : Option (Option Edge) :=
  if o = .ibp node then some none else oldWire (wire o)

theorem scoreChildSyntax_origin {j : ℕ} (J : List LabelOrigin) (hJ : J.length = j)
    (A : List (Fin j)) (hA : A ≠ []) (node : NodeAddress) (b : Bool)
    (selected : Fin A.length ≃ {z : g.Slot p // part z = b})
    (wire : LabelOrigin → Option Edge)
    (hfresh : ∀ u, J.get (Fin.cast hJ.symm (A.get u)) ≠ .ibp node)
    (hwire : ∀ u, Sum.elim Subtype.val Subtype.val (selected u).val =
      wire (J.get (Fin.cast hJ.symm (A.get u)))) :
    let Q := g.scoreChildSyntax p part hi ho J hJ A hA node b selected (σ := σ)
    ∀ u o, pendingPortOrigin Q.1 u = some o →
      Sum.elim Subtype.val Subtype.val (Q.2.symm u) = scoreOriginWire node wire o := by
  dsimp only
  intro u o hu
  change Fin (A.map (fun v => J.get (Fin.cast hJ.symm v))).length ⊕ Unit at u
  cases u with
  | inl v =>
    have hv : o = J.get (Fin.cast hJ.symm (A.get (Fin.cast (List.length_map _) v))) := by
      simpa [pendingPortOrigin,scoreChildSyntax] using hu.symm
    subst o
    change Sum.elim Subtype.val Subtype.val
      (g.scoreChildEquiv p part hi ho b selected (.inl (Fin.cast (List.length_map _) v))) = _
    rw [scoreChildEquiv_derivative,inheritedChildSlot_wire,hwire]
    simp only [scoreOriginWire,ite_eq_right (hfresh _)]
  | inr v =>
    have hv : o = .ibp node := Option.some.inj hu.symm
    subst o
    cases v
    change Sum.elim Subtype.val Subtype.val
      (g.scoreChildEquiv p part hi ho b selected (.inr ())) = _
    rw [scoreChildEquiv_joining]
    cases b <;> simp [scoreOriginWire,joiningChildSlot]

variable {D : ℕ}

def scorePortTensor {k a : ℕ} {Edges : Type*} [Fintype Edges] (h : Graph k Edges) (v : Fin (k+1))
    (H : EuclideanSpace ℝ (Fin D) → ℝ) (e : h.Slot v ≃ (Fin a ⊕ Unit))
    (x : EuclideanSpace ℝ (Fin D)) : Coeff (h.Slot v) D :=
  WithLp.toLp 2 (fun c => partialAlong
    (fun u => coordinateDirection D (c (e.symm (.inl u)))) (List.finRange a)
    (dir (coordinateDirection D (c (e.symm (.inr ())))) H) x)

theorem scorePortTensor_cast {k a a' : ℕ} {Edges : Type*} [Fintype Edges] (h : Graph k Edges) (v : Fin (k+1))
    (H : EuclideanSpace ℝ (Fin D) → ℝ) (e : h.Slot v ≃ (Fin a ⊕ Unit))
    (ha : a=a') (x : EuclideanSpace ℝ (Fin D)) :
    scorePortTensor h v H (e.trans (Equiv.sumCongr (finCongr ha) (Equiv.refl Unit))) x =
      scorePortTensor h v H e x := by subst a'; rfl

theorem scoreChildSyntax_tensor {j : ℕ} [Fintype Edge]
    (J : List LabelOrigin) (hJ : J.length = j)
    (A : List (Fin j)) (hA : A ≠ []) (node : NodeAddress) (b : Bool)
    (selected : Fin A.length ≃ {z : g.Slot p // part z = b})
    (ρ : CoefficientEnvironment σ D) (H : EuclideanSpace ℝ (Fin D) → ℝ)
    (x : EuclideanSpace ℝ (Fin D)) :
    let Q := g.scoreChildSyntax p part hi ho J hJ A hA node b selected (σ := σ)
    (g.replaceVertex p part).pendingTensor (splitVertex p p b) ρ H Q.1 Q.2 x =
      scorePortTensor (g.replaceVertex p part) (splitVertex p p b) H
        (g.scoreChildEquiv p part hi ho b selected).symm x := by
  exact scorePortTensor_cast _ _ H _ _ x

end AcceleratedLogConcave.Tensor.Ordered.Graph
