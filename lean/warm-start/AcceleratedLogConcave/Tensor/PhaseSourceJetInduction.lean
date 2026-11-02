import AcceleratedLogConcave.Tensor.PhaseGeneratorIdentification
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-! Source-jet induction from literal gradient coefficients and the actual ODE.
The gradient and velocity identities below are explicit interfaces to be
proved for the original source data, not substitutes for stationary bounds. -/
noncomputable section
open scoped ContDiff
namespace AcceleratedLogConcave.Tensor.PhaseSourceJetInduction
open AdjointReduction CoordinateReduction PhaseExpression PhaseGeneratorIdentification
variable {D : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin D)

theorem first_section_eq_generator (ρ : CoefficientEnvironment signature D) (H ψ : E → ℝ)
    (hρ : ∀ c a, ContDiff ℝ ∞ (fun x => ρ c x a)) (hψ : ContDiff ℝ ∞ ψ)
    (f : Expr signature 2) (a : Fin D)
    (hgradient : ∀ j, sectionValue ρ H f ![a,j] = dir (coordinateDirection D j) ψ) :
    sectionValue ρ H (first f) ![a] = fun x =>
      SkewCoordinateGenerator.generator (coordinateDirection D) (transportEntry ρ) H ψ x := by
  unfold first
  rw [section_adjoint]
  have hs (i : Fin D) :
      sectionValue ρ H (.contract B f 1 1) (Fin.insertNth 0 i ![a]) =
      fun x => ∑ j, transportEntry ρ i j x * dir (coordinateDirection D j) ψ x := by
    rw [insert_first_pair,section_contract]
    funext x
    apply Finset.sum_congr rfl
    intro j _
    rw [leftAssignment_pair,rightAssignment_pair]
    change sectionValue ρ H B ![i,j] x * sectionValue ρ H f ![a,j] x = _
    rw [hgradient]
    rfl
  funext x
  unfold adjointField adjointComponent
  simp_rw [hs]
  have hp (i j : Fin D) : Differentiable ℝ
      (fun x => transportEntry ρ i j x * dir (coordinateDirection D j) ψ x) :=
    ((hρ .transport ![i,j]).differentiable (by simp)).mul
      ((contDiff_dir hψ (coordinateDirection D j)).differentiable (by simp))
  simp_rw [dir_sum Finset.univ _ _ (fun j _ => hp _ j)]
  simp only [SkewCoordinateGenerator.generator,Finset.sum_neg_distrib,
    Finset.mul_sum,Finset.sum_add_distrib]

theorem hasDerivAt_section_along (ρ : CoefficientEnvironment signature D) (H : E → ℝ)
    (hρ : ∀ c a, ContDiff ℝ ∞ (fun x => ρ c x a)) (hH : ContDiff ℝ ∞ H)
    (hskew : ∀ x i j, transportEntry ρ i j x = -transportEntry ρ j i x)
    (e : Expr signature 1) (a : Fin D) {Z : ℝ → E} {α t : ℝ}
    (hZ : HasDerivAt Z (α • SkewCoordinateGenerator.velocity
      (coordinateDirection D) (transportEntry ρ) H (Z t)) t) :
    HasDerivAt (fun u => sectionValue ρ H e ![a] (Z u))
      (α * sectionValue ρ H (next e) ![a] (Z t)) t := by
  have h := SkewCoordinateGenerator.hasDerivAt_along_generator
    (coordinateDirection D) (transportEntry ρ) H (sectionValue ρ H e ![a])
    (fun i j => (hρ .transport ![i,j]).differentiable (by simp)) hskew
    (contDiff_section ρ H hρ hH e ![a]) hZ
  rw [next_section_eq_generator ρ H hρ hH e a]
  exact h

/-- Every positive source derivative equals the corresponding connected grammar
jet. This induction retains the whole expression, rather than bounding products. -/
theorem iteratedDeriv_eq_jet (ρ : CoefficientEnvironment signature D) (H ψ : E → ℝ)
    (hρ : ∀ c a, ContDiff ℝ ∞ (fun x => ρ c x a)) (hH : ContDiff ℝ ∞ H)
    (hψ : ContDiff ℝ ∞ ψ)
    (hskew : ∀ x i j, transportEntry ρ i j x = -transportEntry ρ j i x)
    (f : Expr signature 2) (a : Fin D)
    (hgradient : ∀ j, sectionValue ρ H f ![a,j] = dir (coordinateDirection D j) ψ)
    (Z : ℝ → E) (α : ℝ)
    (hZ : ∀ t, HasDerivAt Z (α • SkewCoordinateGenerator.velocity
      (coordinateDirection D) (transportEntry ρ) H (Z t)) t) (k : ℕ) :
    iteratedDeriv (k+1) (fun t => ψ (Z t)) =
      fun t => α^(k+1) * sectionValue ρ H (jet f k) ![a] (Z t) := by
  induction k with
  | zero =>
    funext t
    rw [iteratedDeriv_one]
    have h := SkewCoordinateGenerator.hasDerivAt_along_generator
      (coordinateDirection D) (transportEntry ρ) H ψ
      (fun i j => (hρ .transport ![i,j]).differentiable (by simp)) hskew hψ (hZ t)
    simpa only [jet,Nat.zero_add,pow_one,first_section_eq_generator ρ H ψ hρ hψ f a hgradient]
      using h.deriv
  | succ k ih =>
    rw [iteratedDeriv_succ,ih]
    funext t
    have h := (hasDerivAt_section_along ρ H hρ hH hskew (jet f k) a (hZ t)).const_mul
      (α^(k+1))
    simpa only [jet,pow_succ,mul_assoc] using h.deriv

end AcceleratedLogConcave.Tensor.PhaseSourceJetInduction
