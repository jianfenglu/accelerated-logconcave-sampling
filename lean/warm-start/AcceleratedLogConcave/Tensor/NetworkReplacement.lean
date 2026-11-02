import AcceleratedLogConcave.Tensor.OrderedContraction

/-! Exact finite coordinate-sum semantics of replacing one ordered occurrence.
The local tensor contraction premise is separate from the proved global equality. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators Classical
namespace AcceleratedLogConcave.Tensor.Ordered.Graph
variable {n D : ℕ} {Edge : Type*}

/-- Old labeled wires retain their coordinates; only the new joining wire is fresh. -/
def extendAssignment (a : Option Edge → Fin D) (k : Fin D) : Option (Option Edge) → Fin D
  | none => a none
  | some none => k
  | some (some e) => a (some e)

@[simp] theorem extendAssignment_oldWire (a : Option Edge → Fin D) (k : Fin D)
    (w : Option Edge) : extendAssignment a k (oldWire w) = a w := by cases w <;> rfl

/-- A coordinate on the refined graph is exactly an old assignment and one fresh coordinate. -/
def assignmentExtensionEquiv :
    ((Option Edge → Fin D) × Fin D) ≃ (Option (Option Edge) → Fin D) where
  toFun p := extendAssignment p.1 p.2
  invFun b := (fun w => b (oldWire w), b (some none))
  left_inv p := by
    apply Prod.ext
    · funext w
      exact extendAssignment_oldWire p.1 p.2 w
    · rfl
  right_inv b := by funext w; cases w with
    | none => rfl
    | some w => cases w <;> rfl

variable [Fintype Edge]

/-- Literal tensor factor in the original global coordinate sum. -/
def wireValue (g : Graph n Edge) (T : g.Tensors D) (a : Option Edge → Fin D)
    (v : Fin (n+1)) : ℝ :=
  T v (Sum.elim (fun p : g.InPort v => a p.val) (fun p : g.OutPort v => a p.val))

omit [Fintype Edge] in
lemma splitVertex_false_eq_succAbove (p v : Fin (n+1)) :
    splitVertex p v false = p.succ.succAbove v := by
  apply Fin.ext
  simp only [splitVertex, Fin.succAbove, Bool.false_eq_true, ↓reduceIte]
  split_ifs <;> simp_all only [Fin.lt_def, Fin.val_succ, Fin.val_castSucc] <;> omega

omit [Fintype Edge] in
/-- Product factorization preserves occurrence multiplicity, not just distinct tensor values. -/
lemma prod_splitVertex (p : Fin (n+1)) (B : Fin (n+2) → ℝ) :
    (∏ v, B v) = B p.castSucc * B p.succ *
      ∏ v ∈ Finset.univ.erase p, B (splitVertex p v false) := by
  rw [Fin.prod_univ_succAbove B p.succ]
  simp_rw [← splitVertex_false_eq_succAbove]
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ p)]
  simp only [splitVertex_parent_false]
  ring

/-- The unchanged occurrence tensor transported along the literal inherited ports. -/
def replacementOtherTensor (g : Graph n Edge) (p : Fin (n+1))
    (part : g.Slot p → Bool) (T : g.Tensors D) (v : Fin (n+1)) (hv : v ≠ p) :
    Coeff ((g.replaceVertex p part).Slot (splitVertex p v false)) D :=
  WithLp.toLp 2 (fun b => T v (Sum.elim
    (fun q => b (.inl (g.replaceInOtherEmbedding p v part hv q)))
    (fun q => b (.inr (g.replaceOutOtherEmbedding p v part hv q)))))

theorem replacementOtherTensor_wireValue (g : Graph n Edge) (p : Fin (n+1))
    (part : g.Slot p → Bool) (T : g.Tensors D) (v : Fin (n+1)) (hv : v ≠ p)
    (a : Option Edge → Fin D) (k : Fin D) :
    g.replacementOtherTensor p part T v hv (Sum.elim
      (fun q => extendAssignment a k q.val) (fun q => extendAssignment a k q.val)) =
        g.wireValue T a v := by
  unfold replacementOtherTensor wireValue
  apply congrArg (fun b => T v b)
  funext q
  cases q <;> simp [replaceInOtherEmbedding, replaceOutOtherEmbedding]

/-- Replacing a local contracted tensor by its two children preserves the entire
closed coordinate contraction, including all old wire labels and the one cut coordinate.
`hother` is literal unchanged-occurrence semantics and `hparent` is the one local
contraction; no global equality or norm bound is assumed. -/
theorem coordinateEval_replaceVertex (g : Graph n Edge) (p : Fin (n+1))
    (part : g.Slot p → Bool) (T : g.Tensors D)
    (U : (g.replaceVertex p part).Tensors D)
    (hother : ∀ a k v, v ≠ p →
      (g.replaceVertex p part).wireValue U (extendAssignment a k) (splitVertex p v false) =
        g.wireValue T a v)
    (hparent : ∀ a, g.wireValue T a p = ∑ k : Fin D,
      (g.replaceVertex p part).wireValue U (extendAssignment a k) p.castSucc *
      (g.replaceVertex p part).wireValue U (extendAssignment a k) p.succ) :
    g.coordinateEval D T = (g.replaceVertex p part).coordinateEval D U := by
  classical
  unfold wireValue at hother hparent
  let e := assignmentExtensionEquiv (Edge := Edge) (D := D)
  have he : (∑ b : Wire (Edge := Option Edge) → Fin D, ∏ v, (U v) (Sum.elim
      (fun q : (g.replaceVertex p part).InPort v => b q.val)
      (fun q : (g.replaceVertex p part).OutPort v => b q.val))) =
      ∑ ak : (Wire (Edge := Edge) → Fin D) × Fin D, ∏ v,
        (g.replaceVertex p part).wireValue U (extendAssignment ak.1 ak.2) v := by
    apply Fintype.sum_equiv e.symm
    intro b
    simp only [wireValue]
    congr 1
    ext v
    apply congrArg (fun z => (U v) z)
    funext s
    cases s <;> exact (congrFun (e.apply_symm_apply b) _).symm
  have he' : (g.replaceVertex p part).coordinateEval D U =
      ∑ ak : (Wire (Edge := Edge) → Fin D) × Fin D, ∏ v,
        (g.replaceVertex p part).wireValue U (extendAssignment ak.1 ak.2) v := by
    convert he using 1
    unfold coordinateEval
    apply Finset.sum_congr
    · ext b; simp
    · intro b _; rfl
  rw [he']
  unfold coordinateEval
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ p), hparent]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k _
  rw [prod_splitVertex p]
  congr 1
  apply Finset.prod_congr rfl
  intro v hv
  exact (hother a k v (Finset.mem_erase.mp hv).1).symm

end AcceleratedLogConcave.Tensor.Ordered.Graph
