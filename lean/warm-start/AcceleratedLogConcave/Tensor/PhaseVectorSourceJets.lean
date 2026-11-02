import AcceleratedLogConcave.Tensor.PhaseVectorSource

/-! Whole-vector source jets retain a single phase RMS estimate. Taking an
independent scalar moment estimate for every coordinate would lose dimension. -/
noncomputable section
open scoped ContDiff
namespace AcceleratedLogConcave.Tensor.PhaseSourceJetInduction
open AdjointReduction CoordinateReduction PhaseExpression PhaseGeneratorIdentification
variable {D : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin D)

theorem hasDerivAt_sourceVector_along (ρ : CoefficientEnvironment signature D)
    (H : E → ℝ) (Ψ : E → E)
    (hρ : ∀ c a, ContDiff ℝ ∞ (fun x => ρ c x a))
    (hΨ : ∀ i, ContDiff ℝ ∞ (fun x => Ψ x i))
    (hskew : ∀ x i j, transportEntry ρ i j x = -transportEntry ρ j i x)
    (f : Expr signature 2)
    (hgradient : ∀ i j, sectionValue ρ H f ![i,j] =
      dir (coordinateDirection D j) (fun x => Ψ x i))
    {Z : ℝ → E} {α t : ℝ}
    (hZ : HasDerivAt Z (α • SkewCoordinateGenerator.velocity
      (coordinateDirection D) (transportEntry ρ) H (Z t)) t) :
    HasDerivAt (fun u => Ψ (Z u)) (α • vectorSection ρ H (first f) (Z t)) t := by
  have hi (i : Fin D) : HasDerivAt (fun u => Ψ (Z u) i)
      (α * sectionValue ρ H (first f) ![i] (Z t)) t := by
    have h := SkewCoordinateGenerator.hasDerivAt_along_generator
      (coordinateDirection D) (transportEntry ρ) H (fun x => Ψ x i)
      (fun j k => (hρ .transport ![j,k]).differentiable (by simp)) hskew (hΨ i) hZ
    simpa only [first_section_eq_generator ρ H (fun x => Ψ x i) hρ (hΨ i) f i
      (hgradient i)] using h
  have hp := hasDerivAt_pi.mpr hi
  have h := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin D => ℝ)).symm.hasFDerivAt.comp_hasDerivAt t hp
  convert h using 1
  · funext u
    ext i
    rfl
  · ext i
    rfl

theorem iteratedDeriv_sourceVector_eq_jet (ρ : CoefficientEnvironment signature D)
    (H : E → ℝ) (Ψ : E → E)
    (hρ : ∀ c a, ContDiff ℝ ∞ (fun x => ρ c x a)) (hH : ContDiff ℝ ∞ H)
    (hΨ : ∀ i, ContDiff ℝ ∞ (fun x => Ψ x i))
    (hskew : ∀ x i j, transportEntry ρ i j x = -transportEntry ρ j i x)
    (f : Expr signature 2)
    (hgradient : ∀ i j, sectionValue ρ H f ![i,j] =
      dir (coordinateDirection D j) (fun x => Ψ x i))
    (Z : ℝ → E) (α : ℝ)
    (hZ : ∀ t, HasDerivAt Z (α • SkewCoordinateGenerator.velocity
      (coordinateDirection D) (transportEntry ρ) H (Z t)) t) (k : ℕ) :
    iteratedDeriv (k+1) (fun t => Ψ (Z t)) =
      fun t => α^(k+1) • vectorSection ρ H (jet f k) (Z t) := by
  induction k with
  | zero =>
    funext t
    rw [iteratedDeriv_one]
    simpa only [jet,Nat.zero_add,pow_one] using
      (hasDerivAt_sourceVector_along ρ H Ψ hρ hΨ hskew f hgradient (hZ t)).deriv
  | succ k ih =>
    rw [iteratedDeriv_succ,ih]
    funext t
    have h := (hasDerivAt_vectorSection_along ρ H hρ hH hskew (jet f k) (hZ t)).const_smul
      (α^(k+1))
    have hd := h.deriv
    change deriv (fun u => α^(k+1) • vectorSection ρ H (jet f k) (Z u)) t = _ at hd
    simpa only [jet,pow_succ,smul_smul] using hd
end AcceleratedLogConcave.Tensor.PhaseSourceJetInduction
