import AcceleratedLogConcave.Tensor.OrderedContraction

/-!
# A single tree edge in grouped Hilbert unfoldings

The coordinate groups may contain any number of tensor slots. In particular,
an empty slot group is represented by its one-element assignment type, not by
a zero-dimensional identity. The core estimate also permits empty coordinate
types, hence includes coordinate dimension zero.

The last theorem is the canonical four-group form of the single-edge lemma.
It is not yet a universal arbitrary-slot reindexing wrapper, a Faà di Bruno
supplier, an ODE majorant, or a transported Stein coefficient bound.
-/

noncomputable section
open scoped BigOperators Classical
namespace AcceleratedLogConcave.Tensor.SingleEdge

section Matrix
variable {I J K L W : Type*}
  [Fintype I] [Fintype J] [Fintype K] [Fintype L] [Fintype W]
  [DecidableEq I] [DecidableEq J] [DecidableEq K]
  [DecidableEq L] [DecidableEq W]

/-- Contract exactly one coordinate between two tensors, with arbitrary
grouped external row and column coordinates. -/
def crossed (A : Matrix (I × W) J ℝ) (B : Matrix K (W × L) ℝ) :
    Matrix (I × K) (J × L) ℝ :=
  fun p q => ∑ w, A (p.1,w) q.1 * B p.2 (w,q.2)

omit [DecidableEq J] [DecidableEq K] [DecidableEq W] in
/-- The first orientation, A before B. Identities act on bypass Hilbert
coordinates, so the energy constant has no dimension factor. -/
theorem crossed_energy (A : Matrix (I × W) J ℝ)
    (B : Matrix K (W × L) ℝ) {CA CB : ℝ}
    (hA : EnergyBound A CA) (hB : EnergyBound B CB)
    (hCA : 0 ≤ CA) (hCB : 0 ≤ CB) :
    EnergyBound (crossed A B) (CB * CA) := by
  let Astep : Matrix ((I × W) × L) (J × L) ℝ :=
    fun p q => A p.1 q.1 * if p.2 = q.2 then 1 else 0
  let Bstep : Matrix (I × K) ((I × W) × L) ℝ :=
    fun p q => (if p.1 = q.1.1 then 1 else 0) * B p.2 (q.1.2,q.2)
  have hAs : EnergyBound Astep CA := by
    have h := hA.kronecker (bound_identity (I := L)) hCA
    have heA : Matrix.kronecker A (fun i j : L => if i = j then (1 : ℝ) else 0) =
        Astep := by
      funext p q
      rfl
    rw [heA, mul_one] at h
    exact h
  have hBs : EnergyBound Bstep CB := by
    have h := ((bound_identity (I := I)).kronecker hB (by norm_num : (0:ℝ) ≤ 1)).reindex
      (Equiv.refl (I × K)) (Equiv.prodAssoc I W L)
    have heB : (fun (p : I × K) (q : (I × W) × L) =>
        Matrix.kronecker (fun i j : I => if i = j then (1 : ℝ) else 0) B
          ((Equiv.refl (I × K)) p) ((Equiv.prodAssoc I W L) q)) = Bstep := by
      funext p q
      rfl
    rw [heB, one_mul] at h
    exact h
  have he : (fun p q => ∑ u, Bstep p u * Astep u q) = crossed A B := by
    funext p q
    simp [Astep, Bstep, crossed, Fintype.sum_prod_type, mul_ite, ite_mul,
      mul_comm]
  have h := hBs.comp hAs hCB
  rw [he] at h
  exact h

omit [DecidableEq K] in
/-- Genuine rectangular Euclidean operator norm, not a directional norm. -/
theorem crossed_norm_le (A : Matrix (I × W) J ℝ)
    (B : Matrix K (W × L) ℝ) :
    ‖matrixCLMEquiv (crossed A B)‖ ≤
      ‖matrixCLMEquiv A‖ * ‖matrixCLMEquiv B‖ := by
  apply opNorm_le_of_energyBound _ _ (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  have h := crossed_energy A B (energyBound_opNorm A) (energyBound_opNorm B)
    (sq_nonneg _) (sq_nonneg _)
  convert h using 1
  ring

/-- The reverse orientation, B before A, with the same external grouping. -/
def crossedReverse (A : Matrix I (W × J) ℝ) (B : Matrix (K × W) L ℝ) :
    Matrix (I × K) (J × L) ℝ :=
  fun p q => ∑ w, A p.1 (w,q.1) * B (p.2,w) q.2

omit [DecidableEq I] in
theorem crossedReverse_norm_le (A : Matrix I (W × J) ℝ)
    (B : Matrix (K × W) L ℝ) :
    ‖matrixCLMEquiv (crossedReverse A B)‖ ≤
      ‖matrixCLMEquiv A‖ * ‖matrixCLMEquiv B‖ := by
  have he := matrixCLM_reindex_norm (crossed B A)
    (Equiv.prodComm I K) (Equiv.prodComm J L)
  have hc : (fun p q => crossed B A
      ((Equiv.prodComm I K) p) ((Equiv.prodComm J L) q)) = crossedReverse A B := by
    funext p q
    change (∑ w, B (p.2, w) q.2 * A p.1 (w, q.1)) =
      ∑ w, A p.1 (w, q.1) * B (p.2, w) q.2
    apply Finset.sum_congr rfl
    intro w _
    exact mul_comm _ _
  rw [hc] at he
  rw [he]
  simpa only [mul_comm] using crossed_norm_le B A

end Matrix

section Tensor
variable {AL AR BL BR : Type*}
  [Fintype AL] [Fintype AR] [Fintype BL] [Fintype BR]
  [DecidableEq AL] [DecidableEq AR] [DecidableEq BL] [DecidableEq BR]
  (D : ℕ)

/-- An actual assignment equivalence; the edge is one Unit slot. -/
def leftEdgeAssignments :
    ((AL → Fin D) × Fin D) ≃ ((AL ⊕ Unit) → Fin D) where
  toFun p := Sum.elim p.1 (fun _ => p.2)
  invFun f := (fun a => f (.inl a), f (.inr ()))
  left_inv p := by cases p; rfl
  right_inv f := by
    funext s
    cases s with
    | inl a => rfl
    | inr u => cases u; rfl

def edgeRightAssignments :
    (Fin D × (BR → Fin D)) ≃ ((Unit ⊕ BR) → Fin D) where
  toFun p := Sum.elim (fun _ => p.1) p.2
  invFun f := (f (.inl ()), fun b => f (.inr b))
  left_inv p := by cases p; rfl
  right_inv f := by
    funext s
    cases s with
    | inl u => cases u; rfl
    | inr b => rfl

def leftMatrix (A : Coeff (AR ⊕ (AL ⊕ Unit)) D) :
    Matrix ((AL → Fin D) × Fin D) (AR → Fin D) ℝ :=
  fun p q => A (Sum.elim q (leftEdgeAssignments D p))

def rightMatrix (B : Coeff ((Unit ⊕ BR) ⊕ BL) D) :
    Matrix (BL → Fin D) (Fin D × (BR → Fin D)) ℝ :=
  fun p q => B (Sum.elim (edgeRightAssignments D q) p)

theorem leftMatrix_norm (A : Coeff (AR ⊕ (AL ⊕ Unit)) D) :
    ‖matrixCLMEquiv (leftMatrix D A)‖ = splitNorm D outputSlots A := by
  have h := matrixCLM_reindex_norm
    (fun (p : (AL ⊕ Unit) → Fin D) (q : AR → Fin D) => A (Sum.elim q p))
    (leftEdgeAssignments D) (Equiv.refl (AR → Fin D))
  change ‖matrixCLMEquiv (leftMatrix D A)‖ = _ at h
  exact h.trans (sum_unfold_norm D A)

theorem rightMatrix_norm (B : Coeff ((Unit ⊕ BR) ⊕ BL) D) :
    ‖matrixCLMEquiv (rightMatrix D B)‖ = splitNorm D outputSlots B := by
  have h := matrixCLM_reindex_norm
    (fun (p : BL → Fin D) (q : (Unit ⊕ BR) → Fin D) => B (Sum.elim q p))
    (Equiv.refl (BL → Fin D)) (edgeRightAssignments D)
  change ‖matrixCLMEquiv (rightMatrix D B)‖ = _ at h
  exact h.trans (sum_unfold_norm D B)

/-- Literal coefficient sum. Its retained slots are AR, BR, AL, BL; no
distinguished output is discarded. The requested unfolding groups AL with BL
and AR with BR, including any output slot placed in one of these groups. -/
def contract (A : Coeff (AR ⊕ (AL ⊕ Unit)) D)
    (B : Coeff ((Unit ⊕ BR) ⊕ BL) D) :
    Coeff ((AR ⊕ BR) ⊕ (AL ⊕ BL)) D :=
  WithLp.toLp 2 (fun a => ∑ w : Fin D,
    A (Sum.elim (fun i => a (.inl (.inl i)))
      (Sum.elim (fun i => a (.inr (.inl i))) (fun _ => w))) *
    B (Sum.elim (Sum.elim (fun _ => w) (fun i => a (.inl (.inr i))))
      (fun i => a (.inr (.inr i)))))

theorem contract_unfolding_norm (A : Coeff (AR ⊕ (AL ⊕ Unit)) D)
    (B : Coeff ((Unit ⊕ BR) ⊕ BL) D) :
    ‖matrixCLMEquiv (crossed (leftMatrix D A) (rightMatrix D B))‖ =
      splitNorm D outputSlots (contract D A B) := by
  have h := matrixCLM_reindex_norm
    (fun (p : (AL ⊕ BL) → Fin D) (q : (AR ⊕ BR) → Fin D) =>
      contract D A B (Sum.elim q p))
    (Equiv.sumArrowEquivProdArrow AL BL (Fin D)).symm
    (Equiv.sumArrowEquivProdArrow AR BR (Fin D)).symm
  change ‖matrixCLMEquiv (crossed (leftMatrix D A) (rightMatrix D B))‖ = _ at h
  exact h.trans (sum_unfold_norm D (contract D A B))

/-- The canonical grouped single-edge split estimate. Even AL or BR empty is
allowed: their assignment spaces have dimension one, not a dimension loss. -/
theorem contract_splitNorm_le (A : Coeff (AR ⊕ (AL ⊕ Unit)) D)
    (B : Coeff ((Unit ⊕ BR) ⊕ BL) D) :
    splitNorm D outputSlots (contract D A B) ≤
      splitNorm D outputSlots A * splitNorm D outputSlots B := by
  rw [← contract_unfolding_norm D A B, ← leftMatrix_norm D A, ← rightMatrix_norm D B]
  exact crossed_norm_le _ _

/-- When AR and BL contain external slots, both primitive unfoldings are
proper, so primitive all-proper-split bounds supply the hypotheses directly.
The opposite order is covered by crossedReverse_norm_le after regrouping. -/
theorem contract_splitNorm_le_of_allSplits [Nonempty AR] [Nonempty BL]
    (A : Coeff (AR ⊕ (AL ⊕ Unit)) D) (B : Coeff ((Unit ⊕ BR) ⊕ BL) D)
    {CA CB : ℝ} (hCA : 0 ≤ CA) (_hCB : 0 ≤ CB)
    (hA : ∀ S, NontrivialSplit S → splitNorm D S A ≤ CA)
    (hB : ∀ S, NontrivialSplit S → splitNorm D S B ≤ CB) :
    splitNorm D outputSlots (contract D A B) ≤ CA * CB := by
  apply (contract_splitNorm_le D A B).trans
  exact mul_le_mul (hA _ outputSlots_nontrivial) (hB _ outputSlots_nontrivial)
    (splitNorm_nonneg D _ B) hCA

end Tensor
end AcceleratedLogConcave.Tensor.SingleEdge
