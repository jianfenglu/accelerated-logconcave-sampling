import AcceleratedLogConcave.Tensor.NetworkLinearity

/-! Literal evaluation when a fresh coordinate wire joins two existing occurrences. -/
noncomputable section
open MeasureTheory
open scoped Classical BigOperators
namespace AcceleratedLogConcave.Tensor.Ordered.Graph
variable {n D : ℕ} {Edge : Type*} [Fintype Edge]
variable (g : Graph n Edge) (p q : Fin (n+1)) (hpq : p < q)

omit [Fintype Edge] in
def addedOldSlot (v : Fin (n+1)) : g.Slot v → (g.addOrderedEdge p q hpq).Slot v
  | .inl a => .inl (g.addEdgeInEmbedding p q hpq v a)
  | .inr a => .inr (g.addEdgeOutEmbedding p q hpq v a)

omit [Fintype Edge] in
def addedSourceSlot : (g.addOrderedEdge p q hpq).Slot p :=
  .inr ⟨some none, rfl⟩

omit [Fintype Edge] in
def addedTargetSlot : (g.addOrderedEdge p q hpq).Slot q :=
  .inl ⟨some none, rfl⟩

omit [Fintype Edge] in
theorem addedOldSlot_value (v : Fin (n+1)) (a : g.Slot v)
    (c : Option Edge → Fin D) (k : Fin D) :
    Sum.elim (fun s => extendAssignment c k s.val) (fun s => extendAssignment c k s.val)
      (g.addedOldSlot p q hpq v a) =
      Sum.elim (fun s : g.InPort v => c s.val) (fun s : g.OutPort v => c s.val) a := by
  cases a with
  | inl a => exact extendAssignment_oldWire c k a.val
  | inr a => exact extendAssignment_oldWire c k a.val

def addedPullbackFamily (T : g.Tensors D) : (g.addOrderedEdge p q hpq).Tensors D :=
  fun v => WithLp.toLp 2 (fun a => T v (a ∘ g.addedOldSlot p q hpq v))

def addedSourceTensor (A : Fin D → Coeff (g.Slot p) D) :
    Coeff ((g.addOrderedEdge p q hpq).Slot p) D :=
  WithLp.toLp 2 (fun a => A (a (g.addedSourceSlot p q hpq)) (a ∘ g.addedOldSlot p q hpq p))

def addedTargetTensor (B : Fin D → Coeff (g.Slot q) D) :
    Coeff ((g.addOrderedEdge p q hpq).Slot q) D :=
  WithLp.toLp 2 (fun a => B (a (g.addedTargetSlot p q hpq)) (a ∘ g.addedOldSlot p q hpq q))

/-- The actual family changes exactly the two incident occurrences. -/
def addedPairFamily (T : g.Tensors D) (A : Fin D → Coeff (g.Slot p) D)
    (B : Fin D → Coeff (g.Slot q) D) : (g.addOrderedEdge p q hpq).Tensors D :=
  (g.addOrderedEdge p q hpq).replaceTensorAt q
    ((g.addOrderedEdge p q hpq).replaceTensorAt p (g.addedPullbackFamily p q hpq T)
      (g.addedSourceTensor p q hpq A)) (g.addedTargetTensor p q hpq B)

theorem addedPairFamily_source (T : g.Tensors D) (A : Fin D → Coeff (g.Slot p) D)
    (B : Fin D → Coeff (g.Slot q) D) :
    g.addedPairFamily p q hpq T A B p = g.addedSourceTensor p q hpq A := by
  simp [addedPairFamily, ne_of_lt hpq]

theorem addedPairFamily_target (T : g.Tensors D) (A : Fin D → Coeff (g.Slot p) D)
    (B : Fin D → Coeff (g.Slot q) D) :
    g.addedPairFamily p q hpq T A B q = g.addedTargetTensor p q hpq B := by
  simp [addedPairFamily]

theorem addedPairFamily_other (T : g.Tensors D) (A : Fin D → Coeff (g.Slot p) D)
    (B : Fin D → Coeff (g.Slot q) D) (v : Fin (n+1)) (hvp : v ≠ p) (hvq : v ≠ q) :
    g.addedPairFamily p q hpq T A B v = g.addedPullbackFamily p q hpq T v := by
  simp [addedPairFamily, hvp, hvq]

/-- The full new-edge coordinate sum is exactly the old assignments plus one fresh index. -/
theorem coordinateEval_addOrderedEdge (U : (g.addOrderedEdge p q hpq).Tensors D) :
    (g.addOrderedEdge p q hpq).coordinateEval D U =
      ∑ c : (Option Edge → Fin D), ∑ k : Fin D,
        ∏ v, (g.addOrderedEdge p q hpq).wireValue U (extendAssignment c k) v := by
  let e := assignmentExtensionEquiv (Edge := Edge) (D := D)
  have he : (∑ b : Wire (Edge := Option Edge) → Fin D, ∏ v, U v (Sum.elim
      (fun s : (g.addOrderedEdge p q hpq).InPort v => b s.val)
      (fun s : (g.addOrderedEdge p q hpq).OutPort v => b s.val))) =
      ∑ ck : (Wire (Edge := Edge) → Fin D) × Fin D,
        ∏ v, (g.addOrderedEdge p q hpq).wireValue U (extendAssignment ck.1 ck.2) v := by
    apply Fintype.sum_equiv e.symm
    intro b
    simp only [wireValue]
    congr 1
    ext v
    apply congrArg (fun z => U v z)
    funext s
    cases s <;> exact (congrFun (e.apply_symm_apply b) _).symm
  have he' : (g.addOrderedEdge p q hpq).coordinateEval D U =
      ∑ ck : (Wire (Edge := Edge) → Fin D) × Fin D,
        ∏ v, (g.addOrderedEdge p q hpq).wireValue U (extendAssignment ck.1 ck.2) v := by
    convert he using 1
    unfold coordinateEval
    apply Finset.sum_congr
    · ext b; simp
    · intro b _; rfl
  rw [he', Fintype.sum_prod_type]

 theorem addedPairFamily_source_value (T : g.Tensors D) (A : Fin D → Coeff (g.Slot p) D)
    (B : Fin D → Coeff (g.Slot q) D) (c : Option Edge → Fin D) (k : Fin D) :
    (g.addOrderedEdge p q hpq).wireValue (g.addedPairFamily p q hpq T A B) (extendAssignment c k) p =
    A k (Sum.elim (fun s : g.InPort p => c s.val) (fun s : g.OutPort p => c s.val)) := by
  unfold wireValue
  rw [addedPairFamily_source]
  change A k _ = _
  apply congrArg (fun z => A k z)
  funext a
  exact g.addedOldSlot_value p q hpq p a c k

 theorem addedPairFamily_target_value (T : g.Tensors D) (A : Fin D → Coeff (g.Slot p) D)
    (B : Fin D → Coeff (g.Slot q) D) (c : Option Edge → Fin D) (k : Fin D) :
    (g.addOrderedEdge p q hpq).wireValue (g.addedPairFamily p q hpq T A B) (extendAssignment c k) q =
    B k (Sum.elim (fun s : g.InPort q => c s.val) (fun s : g.OutPort q => c s.val)) := by
  unfold wireValue
  rw [addedPairFamily_target]
  change B k _ = _
  apply congrArg (fun z => B k z)
  funext a
  exact g.addedOldSlot_value p q hpq q a c k

 theorem addedPairFamily_other_value (T : g.Tensors D) (A : Fin D → Coeff (g.Slot p) D)
    (B : Fin D → Coeff (g.Slot q) D) (c : Option Edge → Fin D) (k : Fin D)
    (v : Fin (n+1)) (hvp : v ≠ p) (hvq : v ≠ q) :
    (g.addOrderedEdge p q hpq).wireValue (g.addedPairFamily p q hpq T A B) (extendAssignment c k) v =
    g.wireValue T c v := by
  unfold wireValue
  rw [addedPairFamily_other g p q hpq T A B v hvp hvq]
  change T v _ = _
  apply congrArg (fun z => T v z)
  funext a
  exact g.addedOldSlot_value p q hpq v a c k

/-- The new graph evaluates exactly the two selected coordinate fields against every
unchanged occurrence. This is the algebraic network side of principal IBP. -/
theorem coordinateEval_addedPairFamily (T : g.Tensors D)
    (A : Fin D → Coeff (g.Slot p) D) (B : Fin D → Coeff (g.Slot q) D) :
    (g.addOrderedEdge p q hpq).coordinateEval D (g.addedPairFamily p q hpq T A B) =
      ∑ c : (Option Edge → Fin D), ∑ k : Fin D,
        A k (Sum.elim (fun s : g.InPort p => c s.val) (fun s : g.OutPort p => c s.val)) *
        B k (Sum.elim (fun s : g.InPort q => c s.val) (fun s : g.OutPort q => c s.val)) *
        ∏ v ∈ (Finset.univ.erase p).erase q, g.wireValue T c v := by
  rw [g.coordinateEval_addOrderedEdge p q hpq]
  apply Finset.sum_congr rfl
  intro c _
  apply Finset.sum_congr rfl
  intro k _
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ p)]
  rw [← Finset.mul_prod_erase _ _ (show q ∈ Finset.univ.erase p from by simp [ne_of_gt hpq])]
  rw [g.addedPairFamily_source_value p q hpq, g.addedPairFamily_target_value p q hpq, ← mul_assoc]
  congr 1
  apply Finset.prod_congr rfl
  intro v hv
  exact g.addedPairFamily_other_value p q hpq T A B c k v
    (Finset.mem_erase.mp (Finset.mem_erase.mp hv).2).1 (Finset.mem_erase.mp hv).1


/-- A selected recipient may occur on either side of the adjoint occurrence.
No reordering of the syntax forest is imposed. -/
theorem exists_addedPair_network (hg : g.Admissible) (hne : p ≠ q)
    (T : g.Tensors D) (A : Fin D → Coeff (g.Slot p) D) (B : Fin D → Coeff (g.Slot q) D) :
    ∃ (lo hi : Fin (n+1)) (h : lo < hi) (U : (g.addOrderedEdge lo hi h).Tensors D),
      (lo = p ∧ hi = q ∨ lo = q ∧ hi = p) ∧
      (g.addOrderedEdge lo hi h).Admissible ∧
      (g.addOrderedEdge lo hi h).coordinateEval D U =
        ∑ c : (Option Edge → Fin D), ∑ k : Fin D,
          A k (Sum.elim (fun s : g.InPort p => c s.val) (fun s : g.OutPort p => c s.val)) *
          B k (Sum.elim (fun s : g.InPort q => c s.val) (fun s : g.OutPort q => c s.val)) *
          ∏ v ∈ (Finset.univ.erase p).erase q, g.wireValue T c v := by
  rcases lt_or_gt_of_ne hne with h | h
  · exact ⟨p,q,h,g.addedPairFamily p q h T A B,Or.inl ⟨rfl,rfl⟩,
      g.addOrderedEdge_admissible hg p q h,g.coordinateEval_addedPairFamily p q h T A B⟩
  · refine ⟨q,p,h,g.addedPairFamily q p h T B A,Or.inr ⟨rfl,rfl⟩,
      g.addOrderedEdge_admissible hg q p h,?_⟩
    rw [g.coordinateEval_addedPairFamily q p h]
    apply Finset.sum_congr rfl
    intro c _
    apply Finset.sum_congr rfl
    intro k _
    rw [Finset.erase_right_comm]
    ring

/-- Finite-coordinate integration of the literal added-edge family. Analytic
integrability is required only for the actual two-field product terms. -/
theorem integral_coordinateEval_addedPairFamily {X : Type*} [MeasurableSpace X]
    (μ : MeasureTheory.Measure X) (T : X → g.Tensors D)
    (A : X → Fin D → Coeff (g.Slot p) D) (B : X → Fin D → Coeff (g.Slot q) D)
    (hterms : ∀ c : (Option Edge → Fin D), ∀ k : Fin D,
      MeasureTheory.Integrable (fun x =>
        A x k (Sum.elim (fun s : g.InPort p => c s.val) (fun s : g.OutPort p => c s.val)) *
        B x k (Sum.elim (fun s : g.InPort q => c s.val) (fun s : g.OutPort q => c s.val)) *
        ∏ v ∈ (Finset.univ.erase p).erase q, g.wireValue (T x) c v) μ) :
    (∫ x, (g.addOrderedEdge p q hpq).coordinateEval D (g.addedPairFamily p q hpq (T x) (A x) (B x)) ∂μ) =
      ∑ c : (Option Edge → Fin D), ∑ k : Fin D, ∫ x,
        A x k (Sum.elim (fun s : g.InPort p => c s.val) (fun s : g.OutPort p => c s.val)) *
        B x k (Sum.elim (fun s : g.InPort q => c s.val) (fun s : g.OutPort q => c s.val)) *
        ∏ v ∈ (Finset.univ.erase p).erase q, g.wireValue (T x) c v ∂μ := by
  simp_rw [g.coordinateEval_addedPairFamily p q hpq]
  rw [MeasureTheory.integral_finsetSum _ (fun c _ =>
    MeasureTheory.integrable_finsetSum _ (fun k _ => hterms c k))]
  apply Finset.sum_congr rfl
  intro c _
  exact MeasureTheory.integral_finsetSum _ (fun k _ => hterms c k)

end AcceleratedLogConcave.Tensor.Ordered.Graph
