import AcceleratedLogConcave.Tensor.NetworkSyntaxPermutation
import AcceleratedLogConcave.Tensor.NetworkIBPDerivativeValue

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
open scoped Classical BigOperators
namespace AcceleratedLogConcave.Tensor.Ordered.Graph
open AdjointReduction CoordinateReduction ReductionRecords
variable {Name : Type*} {σ : CoefficientSignature Name}

/-- The last output becomes the final derivative port; all old ports retain order. -/
def derivativePortEquiv (j r : ℕ) : (Fin (j+1) ⊕ Fin r) ≃ (Fin j ⊕ Fin (r+1)) where
  toFun := Sum.elim (Fin.lastCases (.inr (Fin.last r)) (fun i => .inl i))
    (fun i => .inr i.castSucc)
  invFun := Sum.elim (fun i => .inl i.castSucc)
    (Fin.lastCases (.inl (Fin.last j)) (fun i => .inr i))
  left_inv := by
    intro u
    cases u with
    | inl i => refine Fin.lastCases ?_ (fun k => ?_) i <;> simp
    | inr i => simp
  right_inv := by
    intro u
    cases u with
    | inl i => simp
    | inr i => refine Fin.lastCases ?_ (fun k => ?_) i <;> simp

@[simp] theorem derivativePortEquiv_old (j r : ℕ) (i : Fin j) :
    derivativePortEquiv j r (.inl i.castSucc) = .inl i := by
  simp [derivativePortEquiv]
@[simp] theorem derivativePortEquiv_fresh (j r : ℕ) :
    derivativePortEquiv j r (.inl (Fin.last j)) = .inr (Fin.last r) := by
  simp [derivativePortEquiv]
@[simp] theorem derivativePortEquiv_output (j r : ℕ) (i : Fin r) :
    derivativePortEquiv j r (.inr i) = .inr i.castSucc := rfl

/-- Tail version of the positional derivative list identity. -/
theorem partialAlong_finRange_last {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (j : ℕ) (d : Fin (j+1) → V) (F : V → ℝ) :
    partialAlong d (List.finRange (j+1)) F =
      partialAlong (fun i : Fin j => d i.castSucc) (List.finRange j)
        (dir (d (Fin.last j)) F) := by
  have hr : List.finRange (j+1) =
      (List.finRange j).map Fin.castSucc ++ [Fin.last j] := by
    apply List.ext_get
    · simp
    · intro n hn hm
      by_cases h : n < j
      · simp [List.getElem_append, h]
      · have he : n = j := by simp only [List.length_finRange] at hn; omega
        subst n
        simp
        rfl
  rw [hr, partialAlong_append, partialAlong_map_directions]
  rfl

/-- Literal tensor identity. No smoothness or semantic equality assumption is needed. -/
theorem decoratedSectionTensor_derivative {D n j r : ℕ} {Edge : Type*} [Fintype Edge]
    (g : Graph n Edge) (v : Fin (n+1))
    (ρ : CoefficientEnvironment σ D) (H : EuclideanSpace ℝ (Fin D) → ℝ)
    (E : Expr σ r) (e : g.Slot v ≃ (Fin j ⊕ Fin (r+1)))
    (x : EuclideanSpace ℝ (Fin D)) :
    g.decoratedSectionTensor v ρ H E (e.trans (derivativePortEquiv j r).symm) x =
      g.decoratedSectionTensor v ρ H (.derivative E) e x := by
  ext a
  change partialAlong (fun u => coordinateDirection D
    (a (e.symm (derivativePortEquiv j r (.inl u))))) (List.finRange (j+1))
    (sectionValue ρ H E (fun u => a (e.symm (derivativePortEquiv j r (.inr u))))) x = _
  rw [partialAlong_finRange_last]
  simp only [derivativePortEquiv_old, derivativePortEquiv_fresh, derivativePortEquiv_output]
  rfl



/-- Construct syntax and its port equivalence together, avoiding dependent casts
between independently simplified syntax indices. -/
def eraseDerivativeData (a : NodeAddress) (p : TaggedPending σ) :
    Σ q : TaggedPending σ, pendingPorts q ≃ pendingPorts p := by
  cases p with
  | score b J h => exact ⟨.score b J h, Equiv.refl _⟩
  | formula b E J =>
    cases E with
    | derivative E =>
      exact if a = b then
        ⟨.formula (b.child false) E (J ++ [.derivative a]),
          (Equiv.sumCongr (finCongr (by simp)) (Equiv.refl _)).trans
            (derivativePortEquiv J.length _)⟩
        else ⟨.formula b (.derivative E) J, Equiv.refl _⟩
    | coefficient c => exact ⟨.formula b (.coefficient c) J, Equiv.refl _⟩
    | contract E F i k => exact ⟨.formula b (.contract E F i k) J, Equiv.refl _⟩
    | permute q E => exact ⟨.formula b (.permute q E) J, Equiv.refl _⟩
    | adjoint i E => exact ⟨.formula b (.adjoint i E) J, Equiv.refl _⟩

def eraseDerivative (a : NodeAddress) (p : TaggedPending σ) : TaggedPending σ :=
  (eraseDerivativeData a p).1

def eraseDerivativePorts (a : NodeAddress) (p : TaggedPending σ) :
    pendingPorts (eraseDerivative a p) ≃ pendingPorts p := (eraseDerivativeData a p).2

theorem eraseDerivative_eq_self_of_tag_ne (a : NodeAddress) (p : TaggedPending σ)
    (hp : p.tag ≠ .formula a) : eraseDerivative a p = p := by
  cases p with
  | score b J h => rfl
  | formula b E J =>
    cases E with
    | derivative E =>
      have hab : a ≠ b := by intro h; subst b; exact hp rfl
      simp only [eraseDerivative, eraseDerivativeData, ite_eq_right hab]
    | coefficient c => rfl
    | contract E F i k => rfl
    | permute q E => rfl
    | adjoint i E => rfl

private theorem map_eraseDerivative_fixed (a : NodeAddress) (s : List (TaggedPending σ))
    (h : ∀ p ∈ s, p.tag ≠ .formula a) : s.map (eraseDerivative a) = s := by
  induction s with
  | nil => rfl
  | cons p s ih =>
    rw [List.map_cons, eraseDerivative_eq_self_of_tag_ne a p (h p (by simp))]
    rw [ih (by intro q hq; exact h q (by simp [hq]))]

theorem map_eraseDerivative_canonical {r : ℕ} (a : NodeAddress)
    (E : Expr σ r) (J : List LabelOrigin) (before after : List (TaggedPending σ))
    (h : ∀ p ∈ before ++ after, p.tag ≠ .formula a) :
    (before ++ [TaggedPending.formula a (.derivative E) J] ++ after).map (eraseDerivative a) =
      before ++ [TaggedPending.formula (a.child false) E (J ++ [.derivative a])] ++ after := by
  rw [List.map_append, List.map_append]
  rw [map_eraseDerivative_fixed a before (by intro p hp; exact h p (by simp [hp]))]
  rw [map_eraseDerivative_fixed a after (by intro p hp; exact h p (by simp [hp]))]
  simp [eraseDerivative, eraseDerivativeData]

theorem decoratedSectionTensor_cast_labels {D n j k r : ℕ} {Edge : Type*}
    [Fintype Edge] (g : Graph n Edge) (v : Fin (n+1))
    (ρ : CoefficientEnvironment σ D) (H : EuclideanSpace ℝ (Fin D) → ℝ)
    (E : Expr σ r) (e : g.Slot v ≃ (Fin j ⊕ Fin r)) (h : j = k)
    (x : EuclideanSpace ℝ (Fin D)) :
    g.decoratedSectionTensor v ρ H E
      (e.trans (Equiv.sumCongr (finCongr h) (Equiv.refl _))) x =
        g.decoratedSectionTensor v ρ H E e x := by
  subst k
  rfl

theorem pendingTensor_eraseDerivative {D n : ℕ} {Edge : Type*} [Fintype Edge]
    (g : Graph n Edge) (v : Fin (n+1))
    (ρ : CoefficientEnvironment σ D) (H : EuclideanSpace ℝ (Fin D) → ℝ)
    (a : NodeAddress) (p : TaggedPending σ) (e : g.Slot v ≃ pendingPorts p)
    (x : EuclideanSpace ℝ (Fin D)) :
    g.pendingTensor v ρ H (eraseDerivative a p)
      (e.trans (eraseDerivativePorts a p).symm) x = g.pendingTensor v ρ H p e x := by
  cases p with
  | score b J h => rfl
  | formula b E J =>
    cases E with
    | derivative E =>
      by_cases h : a = b
      · subst b
        dsimp only [eraseDerivativePorts, eraseDerivative, eraseDerivativeData]
        rw [ite_eq_left rfl]
        change g.decoratedSectionTensor v ρ H E
          ((e.trans (derivativePortEquiv J.length _).symm).trans
            (Equiv.sumCongr (finCongr (show J.length+1 = (J ++ [LabelOrigin.derivative a]).length by simp))
              (Equiv.refl _))) x = _
        rw [decoratedSectionTensor_cast_labels]
        exact decoratedSectionTensor_derivative g v ρ H E e x
      · dsimp only [eraseDerivativePorts, eraseDerivative, eraseDerivativeData]
        rw [ite_eq_right h]
        rfl

    | coefficient c => rfl
    | contract E F i k => rfl
    | permute q E => rfl
    | adjoint i E => rfl


/-- The physical coordinate consumed by a derivative redex, if this is that redex. -/
def derivativeOutput (a : NodeAddress) (p : TaggedPending σ) : Option (pendingPorts p) := by
  cases p with
  | score b J h => exact none
  | formula b E J =>
    cases E with
    | derivative E => exact if a = b then some (.inr (Fin.last _)) else none
    | coefficient c => exact none
    | contract E F i k => exact none
    | permute q E => exact none
    | adjoint i E => exact none

theorem derivativeOutput_tag (a : NodeAddress) (p : TaggedPending σ)
    (u : pendingPorts p) (h : derivativeOutput a p = some u) : p.tag = .formula a := by
  cases p with
  | score b J hJ => cases h
  | formula b E J =>
    cases E <;> try { cases h }
    rename_i E
    by_cases hab : a = b
    · subst b; rfl
    · simp [derivativeOutput, hab] at h

/-- Every new labelled port is either an old labelled port, or precisely the
last output moved to the appended derivative label. -/
theorem eraseDerivative_origin_cases (a : NodeAddress) (p : TaggedPending σ)
    (u : pendingPorts (eraseDerivative a p)) (o : LabelOrigin)
    (h : pendingPortOrigin (eraseDerivative a p) u = some o) :
    pendingPortOrigin p ((eraseDerivativePorts a p).toFun u) = some o ∨
      (o = .derivative a ∧ derivativeOutput a p = some ((eraseDerivativePorts a p).toFun u)) := by
  cases p with
  | score b J hJ => exact Or.inl h
  | formula b E J =>
    cases E with
    | derivative E =>
      by_cases hab : a = b
      · subst b
        revert h u
        dsimp only [eraseDerivative, eraseDerivativePorts, eraseDerivativeData]
        rw [ite_eq_left rfl]
        intro u h
        change (Fin (J ++ [LabelOrigin.derivative a]).length ⊕ _) at u
        obtain ⟨u, rfl⟩ := (Equiv.sumCongr
          (finCongr (show J.length+1 = (J ++ [LabelOrigin.derivative a]).length by simp))
          (Equiv.refl _)).surjective u
        cases u with
        | inr k => cases h
        | inl k =>
          revert h
          refine Fin.lastCases ?_ (fun i => ?_) k
          · intro h
            right
            have ho : LabelOrigin.derivative a = o := by simpa [pendingPortOrigin] using h
            subst o
            simp [derivativeOutput, derivativePortEquiv, pendingPorts]
          · intro h
            left
            simpa [pendingPortOrigin, derivativePortEquiv, pendingPorts, List.getElem_append,
              i.isLt] using h
      · revert h u
        dsimp only [eraseDerivative, eraseDerivativePorts, eraseDerivativeData]
        rw [ite_eq_right hab]
        intro u h
        exact Or.inl h
    | coefficient c => exact Or.inl h
    | contract E F i k => exact Or.inl h
    | permute q E => exact Or.inl h
    | adjoint i E => exact Or.inl h

end AcceleratedLogConcave.Tensor.Ordered.Graph
