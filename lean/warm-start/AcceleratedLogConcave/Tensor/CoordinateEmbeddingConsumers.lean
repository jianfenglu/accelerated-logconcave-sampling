import AcceleratedLogConcave.Tensor.CoordinateEmbedding
import Mathlib.Data.Fin.Embedding

/-! Focused consumers: zero dimension, output multiplicity, mixed phase blocks,
and an explicit two-block budget. These are algebraic adapters, not assertions
that any analytic derivative tensor has the requisite source bound. -/
noncomputable section
namespace AcceleratedLogConcave.Tensor

variable {I J : Type*} [Fintype I] [DecidableEq I] [DecidableEq J]

 theorem coordinatePad_at_image (e : I ↪ J) (f : I → ℝ) (i : I) :
    coordinatePad e f (e i) = f i := by
  simp only [coordinatePad, e.injective.eq_iff]
  simp

omit [DecidableEq I] in
 theorem coordinatePad_off_image (e : I ↪ J) (f : I → ℝ) (j : J)
    (hj : j ∉ Set.range e) : coordinatePad e f j = 0 := by
  apply Finset.sum_eq_zero
  intro i _
  split_ifs with h
  · exact False.elim (hj ⟨i, h⟩)
  · rfl

variable {Slot : Type*} [Fintype Slot] [DecidableEq Slot] {d : ℕ}

 theorem coordinatePadCoeff_at_image {N : ℕ} (e : Slot → (Fin d ↪ Fin N))
    (T : Coeff Slot d) (a : Slot → Fin d) :
    coordinatePadCoeff e T (fun i => e i (a i)) = T a :=
  coordinatePad_at_image (assignmentEmbedding e) T a

 theorem coordinatePadCoeff_off_image {N : ℕ} (e : Slot → (Fin d ↪ Fin N))
    (T : Coeff Slot d) (b : Slot → Fin N)
    (hb : b ∉ Set.range (assignmentEmbedding e)) :
    coordinatePadCoeff e T b = 0 :=
  coordinatePad_off_image (assignmentEmbedding e) T b hb

/-- Place each slot in either physical coordinate block of phase space. -/
def phaseBlockEmbedding (second : Slot → Bool) : Slot → (Fin d ↪ Fin (d+d)) :=
  fun i => if second i then Fin.natAddEmb d else Fin.castAddEmb d

 theorem phaseBlock_splitNorm_le (second : Slot → Bool) (S : Finset Slot)
    (T : Coeff Slot d) :
    splitNorm (d+d) S (coordinatePadCoeff (phaseBlockEmbedding second) T) ≤
      splitNorm d S T :=
  splitNorm_coordinatePadCoeff_le _ _ _

 theorem phaseBlock_two_budget (second₁ second₂ : Slot → Bool) (S : Finset Slot)
    (T U : Coeff Slot d) (C : ℝ)
    (hT : splitNorm d S T ≤ C) (hU : splitNorm d S U ≤ C) :
    splitNorm (d+d) S
      (coordinatePadCoeff (phaseBlockEmbedding second₁) T +
       coordinatePadCoeff (phaseBlockEmbedding second₂) U) ≤ 2*C := by
  calc
    _ ≤ splitNorm d S T + splitNorm d S U := splitNorm_coordinatePadCoeff_add_le _ _ _ _ _
    _ ≤ C+C := add_le_add hT hU
    _ = 2*C := by ring

/-- No division by physical dimension is used, even when every coordinate set is empty. -/
example (second : Slot → Bool) (S : Finset Slot) (T : Coeff Slot 0) :
    splitNorm (0+0) S (coordinatePadCoeff (phaseBlockEmbedding second) T) ≤
      splitNorm 0 S T := phaseBlock_splitNorm_le second S T

/-- Arbitrarily many output slots require no special one-output assumption. -/
example (n m : ℕ) (second : (Fin n ⊕ Fin m) → Bool)
    (S : Finset (Fin n ⊕ Fin m)) (T : Coeff (Fin n ⊕ Fin m) d) :
    splitNorm (d+d) S (coordinatePadCoeff (phaseBlockEmbedding second) T) ≤
      splitNorm d S T := phaseBlock_splitNorm_le second S T

end AcceleratedLogConcave.Tensor
