import AcceleratedLogConcave.Conditional.ScaledJetPolynomial

/-! The full original-data coefficient environment for qualitative adjoint
reduction. No integrability or polynomial-growth certificates are hypotheses.
This is not the sharp second-moment bound. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory WithLp
open scoped ContDiff NNReal Classical BigOperators
namespace AcceleratedLogConcave.Tensor.ActualCoefficientIntegrability
open Conditional Conditional.ScaledJetPolynomial PolynomialClosure AdjointReduction CoordinateReduction
open Analysis.PositiveVarianceSlab

/-- `inl n` denotes J_(n+1); `inr ()` denotes the actual Hessian S. -/
abbrev Name := ℕ ⊕ Unit

abbrev signature : CoefficientSignature Name where
  arity := Sum.elim (fun n => n+2) (fun _ => 2)
  size := Sum.elim (fun n => n+2) (fun _ => 2)
  weight := Sum.elim (fun n => (n : ℝ≥0)) (fun _ => 0)
  two_le_arity := by intro c; cases c <;> simp
  arity_le_size := by intro c; exact le_refl _

variable {D : ℕ}

def coefficientEnvironment (F : (EuclideanSpace ℝ (Fin D)) → ℝ) (x : (EuclideanSpace ℝ (Fin D))) (ell r t : ℝ) :
    CoefficientEnvironment signature D
  | Sum.inl n, y => toLp 2 (fun a : Fin (n+2) → Fin D =>
      (ell*r*((n+1).factorial:ℝ))⁻¹ * inner ℝ (coordinateDirection D (a 0))
        (scaledJet (n+1) F x r t y (fun i => coordinateDirection D (a i.succ))))
  | Sum.inr _, y => toLp 2 (fun a : Fin 2 → Fin D =>
      dir (coordinateDirection D (a 0)) (dir (coordinateDirection D (a 1))
        (interpolationPotential F x r t)) y)

variable {F : (EuclideanSpace ℝ (Fin D)) → ℝ} (hF : ContDiff ℝ 2 F) {ell b : ℝ}
  (hlo : ∀ z w, 0 ≤ fderiv ℝ (fderiv ℝ F) z w w)
  (hhi : ∀ z w, fderiv ℝ (fderiv ℝ F) z w w ≤ ell*‖w‖^2)
  (hb0 : 0 ≤ b) (hb1 : b < 1) (x : (EuclideanSpace ℝ (Fin D))) (r : ℝ) {t : ℝ}
  (ht : t ∈ Set.Icc (left b) (right b))

include hF hlo hhi hb0 hb1 ht x

theorem coefficient_polynomialJets (c : Name) (a : Fin (signature.arity c) → Fin D) :
    HasPolynomialJets (fun y => coefficientEnvironment F x ell r t c y a) := by
  cases c with
  | inl n =>
    change Fin (n+2) → Fin D at a
    exact normalized_scaledJet_coordinate_polynomialJets (n+1) hF hlo hhi hb0 hb1 x r ht
      (fun i => coordinateDirection D (a i.succ)) (coordinateDirection D (a 0))
  | inr u =>
    change Fin 2 → Fin D at a
    exact hessian_coordinate_polynomialJets hF hlo hhi hb0 hb1 x r ht
      (coordinateDirection D (a 0)) (coordinateDirection D (a 1))

theorem coefficient_contDiff (c : Name) (a : Fin (signature.arity c) → Fin D) :
    ContDiff ℝ ∞ (fun y => coefficientEnvironment F x ell r t c y a) := by
  have ht' := construction_subset hb0 hb1 ht
  cases c with
  | inl n =>
    change Fin (n+2) → Fin D at a
    have hc : ContDiff ℝ ∞ (fun y : (EuclideanSpace ℝ (Fin D)) => (t,y)) := contDiff_const.prodMk contDiff_id
    have hh := (contDiffOn_scaledJet (n+1) hF hlo hhi x r).comp
      hc.contDiffOn (s := Set.univ) (fun _ _ => ht')
    have hs : ContDiff ℝ ∞ (scaledJet (n+1) F x r t) := contDiffOn_univ.mp hh
    exact contDiff_const.mul ((innerSL ℝ (coordinateDirection D (a 0))).contDiff.comp
      ((tensorEvaluation (n+1) (fun i => coordinateDirection D (a i.succ))).contDiff.comp hs))
  | inr u =>
    change Fin 2 → Fin D at a
    exact contDiff_dir (contDiff_dir (contDiff_interpolationPotential hF hlo hhi x r ht'.1 ht'.2) _) _

theorem section_polynomialJets {s : ℕ} (e : Expr signature s) (a : Fin s → Fin D) :
    HasPolynomialJets (sectionValue (coefficientEnvironment F x ell r t)
      (interpolationPotential F x r t) e a) := by
  have ht' := construction_subset hb0 hb1 ht
  exact section_hasPolynomialJets _ _
    (coefficient_contDiff hF hlo hhi hb0 hb1 x r ht)
    (contDiff_interpolationPotential hF hlo hhi x r ht'.1 ht'.2)
    (coefficient_polynomialJets hF hlo hhi hb0 hb1 x r ht)
    (score_direction_polynomialJets hF hlo hhi hb0 hb1 x r ht) e a

/-- Every decorated coordinate of every actual coefficient expression has all
moments under the original interpolation law, including probability time zero. -/
theorem integral_section_pow {s : ℕ} (e : Expr signature s) (a : Fin s → Fin D)
    (J : List (EuclideanSpace ℝ (Fin D))) (q : ℕ) :
    Integrable (fun y => (partialAlong id J
      (sectionValue (coefficientEnvironment F x ell r t)
        (interpolationPotential F x r t) e a) y)^q)
      (interpolationLaw F x r t) := by
  have ht' := construction_subset hb0 hb1 ht
  exact interpolation_integrable_section_pow (coefficientEnvironment F x ell r t)
    (interpolationPotential F x r t)
    (coefficient_contDiff hF hlo hhi hb0 hb1 x r ht)
    (contDiff_interpolationPotential hF hlo hhi x r ht'.1 ht'.2)
    (coefficient_polynomialJets hF hlo hhi hb0 hb1 x r ht)
    (score_direction_polynomialJets hF hlo hhi hb0 hb1 x r ht)
    hF hlo x r t e a J q

/-- Complete local decorated-adjoint reduction for arbitrary products of
actual coefficient expressions. No extra growth or integrability assumptions. -/
theorem integral_decorated_adjoint {Label K : Type*} [Fintype K] [DecidableEq K]
    (d : Label → (EuclideanSpace ℝ (Fin D))) (J : List Label) (v : (EuclideanSpace ℝ (Fin D)))
    {s : ℕ} (e : Expr signature s) (a : Fin s → Fin D)
    (sizes : K → ℕ) (es : ∀ k, Expr signature (sizes k))
    (slots : ∀ k, Fin (sizes k) → Fin D) :
    let H := interpolationPotential F x r t
    let env := coefficientEnvironment F x ell r t
    let f := sectionValue env H e a
    let g := fun k => sectionValue env H (es k) (slots k)
    (∫ y, partialAlong d J (adjointComponent H v f) y * ∏ k, g k y
      ∂interpolationLaw F x r t) =
    (∑ k, ∫ y, partialAlong d J f y * dir v (g k) y *
      ∏ j ∈ Finset.univ.erase k, g j y ∂interpolationLaw F x r t) +
    ((scoreRoutes J).map (fun p => ∫ y, partialAlong d p.1 (dir v H) y *
      partialAlong d p.2 f y * ∏ k, g k y ∂interpolationLaw F x r t)).sum := by
  dsimp only
  have ht' := construction_subset hb0 hb1 ht
  have hs := coefficient_contDiff hF hlo hhi hb0 hb1 x r ht
  have hH := contDiff_interpolationPotential hF hlo hhi x r ht'.1 ht'.2
  exact interpolation_integral_decorated_adjoint hF hlo hhi x r ht'.1 ht'.2 d J _ v _
    (contDiff_section _ _ hs hH e a)
    (fun k => contDiff_section _ _ hs hH (es k) (slots k))
    (score_direction_polynomialJets hF hlo hhi hb0 hb1 x r ht v)
    (section_polynomialJets hF hlo hhi hb0 hb1 x r ht e a)
    (fun k => section_polynomialJets hF hlo hhi hb0 hb1 x r ht (es k) (slots k))

end AcceleratedLogConcave.Tensor.ActualCoefficientIntegrability
