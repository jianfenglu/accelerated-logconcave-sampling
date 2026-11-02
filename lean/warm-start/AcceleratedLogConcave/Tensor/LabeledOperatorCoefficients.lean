import AcceleratedLogConcave.Tensor.LabeledOperatorLeibniz
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!

-/
noncomputable section
open scoped BigOperators ContDiff
namespace LabeledOperatorLeibniz
abbrev Space (D : ℕ) := EuclideanSpace ℝ (Fin D)
abbrev basis (D : ℕ) := EuclideanSpace.basisFun (Fin D) ℝ

private theorem basis_comp {D : ℕ} (L R : Space D →L[ℝ] Space D) (i o : Fin D) :
    inner ℝ (basis D o) ((L.comp R) (basis D i)) =
      ∑ w : Fin D, inner ℝ (basis D o) (L (basis D w)) *
        inner ℝ (basis D w) (R (basis D i)) := by
  have h := congrArg L ((basis D).sum_repr' (R (basis D i)))
  change inner ℝ (basis D o) (L (R (basis D i))) = _
  rw [← h]
  simp only [map_sum, map_smul, inner_sum, inner_smul_right]
  apply Finset.sum_congr rfl
  intro w _
  exact mul_comm _ _

/-- Complete subset-labeled product rule with all n derivative labels and
both ordinary operator indices retained. Each internal coordinate w is summed
once per SUBSET, including coincident coordinate labels in different slots. -/
theorem iteratedFDeriv_comp_coefficient {D : ℕ}
    (B H : Space D → (Space D →L[ℝ] Space D))
    (hB : ContDiff ℝ ∞ B) (hH : ContDiff ℝ ∞ H)
    (n : ℕ) (y : Space D) (a : Fin n → Fin D) (i o : Fin D) :
    inner ℝ (basis D o)
      ((iteratedFDeriv ℝ n (fun z => (B z).comp (H z)) y
        (fun j => basis D (a j))) (basis D i)) =
      ∑ S : Finset (Fin n), ∑ w : Fin D,
        inner ℝ (basis D o)
          ((iteratedFDeriv ℝ (leftCount ((subsetEquiv n).symm S)) B y
            (fun j => basis D (a (subsetLeftEmb S j)))) (basis D w)) *
        inner ℝ (basis D w)
          ((iteratedFDeriv ℝ (rightCount ((subsetEquiv n).symm S)) H y
            (fun j => basis D (a (subsetRightEmb S j)))) (basis D i)) := by
  let L : (Space D →L[ℝ] Space D) →L[ℝ] ℝ :=
    (innerSL ℝ (basis D o)).comp
      (ContinuousLinearMap.apply ℝ (Space D) (basis D i))
  have h := congrArg L
    (iteratedFDeriv_comp_subsets B H hB hH n y (fun j => basis D (a j)))
  simp only [map_sum] at h
  refine h.trans ?_
  apply Finset.sum_congr rfl
  intro S _
  exact basis_comp _ _ i o

/-- The operator equality itself is meaningful at physical D=0 and includes
n=0. No Nonempty(Fin D) assumption was needed for the general formula. -/
theorem physical_dimension_zero
    (B H : Space 0 → (Space 0 →L[ℝ] Space 0))
    (hB : ContDiff ℝ ∞ B) (hH : ContDiff ℝ ∞ H)
    (n : ℕ) (y : Space 0) (v : Fin n → Space 0) :
    iteratedFDeriv ℝ n (fun z => (B z).comp (H z)) y v =
      ∑ s : Split n, term B H s y v :=
  iteratedFDeriv_comp_split B H hB hH n y v

end LabeledOperatorLeibniz
