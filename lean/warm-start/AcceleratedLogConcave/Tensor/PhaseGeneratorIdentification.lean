import AcceleratedLogConcave.Tensor.PhaseExpressionGrammar
import AcceleratedLogConcave.Tensor.CoordinateReduction
import AcceleratedLogConcave.Tensor.SkewCoordinateGenerator

/-!
NEW reconstruction, 2026-10-22. Not recovered historical source.
Literal generator identification for the corrected ordered grammar: slot 0 is
observable output and slot 1 is the differentiated/contracted input. These are
pointwise calculus identities; they introduce no measure, moment or bound premise.
-/
noncomputable section
open scoped ContDiff
namespace AcceleratedLogConcave.Tensor.PhaseGeneratorIdentification
open AdjointReduction CoordinateReduction PhaseExpression
variable {D : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin D)

def transportEntry (ρ : CoefficientEnvironment signature D) (i j : Fin D) : E → ℝ :=
  fun x => ρ .transport x ![i,j]

theorem insert_first_pair (i a : Fin D) :
    Fin.insertNth (0 : Fin 2) i ![a] = ![i,a] := by
  ext k
  fin_cases k <;> simp

theorem leftAssignment_pair (i a j : Fin D) :
    leftAssignment (r := 0) (s := 0) 1 ![i,a] j = ![i,j] := by
  ext k
  fin_cases k <;> simp [leftAssignment, Fin.insertNth, Fin.succAboveCases]

theorem rightAssignment_pair (i a j : Fin D) :
    rightAssignment (r := 0) (s := 0) 1 ![i,a] j = ![a,j] := by
  ext k
  fin_cases k <;> simp [rightAssignment, Fin.insertNth, Fin.succAboveCases]

/-- The derivative node appends the direction, preserving observable output. -/
theorem derivative_section_pair (ρ : CoefficientEnvironment signature D) (H : E → ℝ)
    (e : Expr signature 1) (a j : Fin D) :
    sectionValue ρ H (.derivative e) ![a,j] =
      dir (coordinateDirection D j) (sectionValue ρ H e ![a]) := by
  rw [section_derivative]
  have ha : (![a,j] : Fin 2 → Fin D) ∘ Fin.castSucc = ![a] := by
    ext k
    fin_cases k
    rfl
  rw [ha]
  rfl

/-- No skew premise is required to identify the literal adjoint expression.
Skewness is used later, precisely when identifying this generator with velocity. -/
theorem next_section_eq_generator (ρ : CoefficientEnvironment signature D) (H : E → ℝ)
    (hρ : ∀ c a, ContDiff ℝ ∞ (fun x => ρ c x a)) (hH : ContDiff ℝ ∞ H)
    (e : Expr signature 1) (a : Fin D) :
    sectionValue ρ H (next e) ![a] = fun x =>
      SkewCoordinateGenerator.generator (coordinateDirection D) (transportEntry ρ) H
        (sectionValue ρ H e ![a]) x := by
  unfold next
  rw [section_adjoint]
  have hs (i : Fin D) :
      sectionValue ρ H (.contract B (.derivative e) 1 1) (Fin.insertNth 0 i ![a]) =
      fun x => ∑ j, transportEntry ρ i j x *
        dir (coordinateDirection D j) (sectionValue ρ H e ![a]) x := by
    rw [insert_first_pair, section_contract]
    funext x
    apply Finset.sum_congr rfl
    intro j _
    rw [leftAssignment_pair, rightAssignment_pair, derivative_section_pair]
    rfl
  funext x
  unfold adjointField adjointComponent
  simp_rw [hs]
  have hp (i j : Fin D) : Differentiable ℝ
      (fun x => transportEntry ρ i j x *
        dir (coordinateDirection D j) (sectionValue ρ H e ![a]) x) :=
    ((hρ .transport ![i,j]).differentiable (by simp)).mul
      ((contDiff_dir (contDiff_section ρ H hρ hH e ![a])
        (coordinateDirection D j)).differentiable (by simp))
  simp_rw [dir_sum Finset.univ _ _ (fun j _ => hp _ j)]
  simp only [SkewCoordinateGenerator.generator, Finset.sum_neg_distrib,
    Finset.mul_sum, Finset.sum_add_distrib]
end AcceleratedLogConcave.Tensor.PhaseGeneratorIdentification
