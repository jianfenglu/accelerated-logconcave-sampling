import AcceleratedLogConcave.Tensor.NetworkPrincipalIBP
import AcceleratedLogConcave.Tensor.ActualCoefficientIntegrability

/-! Original-law principal network IBP with analytic premises discharged from
literal decorated-expression coordinates. -/
noncomputable section
open MeasureTheory
open scoped Classical BigOperators ContDiff
namespace AcceleratedLogConcave.Tensor.Ordered.Graph
open AdjointReduction CoordinateReduction PolynomialClosure
open ActualCoefficientIntegrability Conditional Conditional.ScaledJetPolynomial
open Analysis.PositiveVarianceSlab
variable {D n : ℕ} {Edge : Type*} [Fintype Edge]

/-- A literal syntactic representation, not a growth or integration certificate. -/
def ActualDecoratedCoordinate (F : EuclideanSpace ℝ (Fin D) → ℝ)
    (x : EuclideanSpace ℝ (Fin D)) (ell r t : ℝ)
    (f : EuclideanSpace ℝ (Fin D) → ℝ) : Prop :=
  ∃ (s : ℕ) (e : Expr signature s) (a : Fin s → Fin D) (J : List (EuclideanSpace ℝ (Fin D))),
    f = partialAlong id J (sectionValue (coefficientEnvironment F x ell r t)
      (interpolationPotential F x r t) e a)

private theorem polynomialJets_partialAlong {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} (hf : HasPolynomialJets f) (J : List E) :
    HasPolynomialJets (partialAlong id J f) := by
  induction J with
  | nil => exact hf
  | cons v J ih => exact ih.direction v

variable {F : EuclideanSpace ℝ (Fin D) → ℝ} (hF : ContDiff ℝ 2 F) {ell b : ℝ}
  (hlo : ∀ z w, 0 ≤ fderiv ℝ (fderiv ℝ F) z w w)
  (hhi : ∀ z w, fderiv ℝ (fderiv ℝ F) z w w ≤ ell*‖w‖^2)
  (hb0 : 0 ≤ b) (hb1 : b < 1) (x : EuclideanSpace ℝ (Fin D)) (r : ℝ) {t : ℝ}
  (ht : t ∈ Set.Icc (left b) (right b))

include hF hlo hhi hb0 hb1 ht

 theorem ActualDecoratedCoordinate.contDiff {f : EuclideanSpace ℝ (Fin D) → ℝ}
    (hf : ActualDecoratedCoordinate F x ell r t f) : ContDiff ℝ ∞ f := by
  obtain ⟨s,e,a,J,rfl⟩ := hf
  have ht' := construction_subset hb0 hb1 ht
  exact contDiff_partialAlong id J (contDiff_section _ _
    (coefficient_contDiff hF hlo hhi hb0 hb1 x r ht)
    (contDiff_interpolationPotential hF hlo hhi x r ht'.1 ht'.2) e a)

 theorem ActualDecoratedCoordinate.polynomialJets {f : EuclideanSpace ℝ (Fin D) → ℝ}
    (hf : ActualDecoratedCoordinate F x ell r t f) : HasPolynomialJets f := by
  obtain ⟨s,e,a,J,rfl⟩ := hf
  exact polynomialJets_partialAlong (section_polynomialJets hF hlo hhi hb0 hb1 x r ht e a) J

/-- Every analytic IBP obligation follows from original Gibbs assumptions.
Only literal coordinate representations and the literal parent adjoint identity remain. -/
theorem integral_actual_adjoint_network (g : Graph n Edge) (p : Fin (n+1))
    (T : EuclideanSpace ℝ (Fin D) → g.Tensors D)
    (A : EuclideanSpace ℝ (Fin D) → Fin D → Coeff (g.Slot p) D)
    (hA : ∀ k a, ActualDecoratedCoordinate F x ell r t (fun y => A y k a))
    (hT : ∀ v, v ≠ p → ∀ a, ActualDecoratedCoordinate F x ell r t (fun y => T y v a))
    (hparent : ∀ y, T y p = g.adjointCoordinateTensor p (interpolationPotential F x r t) A y) :
    (∫ y, g.coordinateEval D (T y) ∂interpolationLaw F x r t) =
      ∑ q : {v : Fin (n+1) // v ≠ p}, ∫ y,
        (g.recipientGraph p q.val (Ne.symm q.property)).coordinateEval D
          (g.principalRecipientFamily p q.val (Ne.symm q.property) T A y)
        ∂interpolationLaw F x r t := by
  let := interpolationLaw_isProbabilityMeasure hF hlo x r t
  have ht' := construction_subset hb0 hb1 ht
  have hH := contDiff_interpolationPotential hF hlo hhi x r ht'.1 ht'.2
  have has := fun k a => ActualDecoratedCoordinate.contDiff hF hlo hhi hb0 hb1 x r ht (hA k a)
  have hts (v : Fin (n+1)) (a : g.Slot v → Fin D) :
      ContDiff ℝ ∞ (fun y => T y v a) := by
    by_cases hv : v = p
    · subst v
      have he : (fun y => T y p a) = (fun y => adjointField
          (interpolationPotential F x r t) (coordinateDirection D) (fun k z => A z k a) y) := by
        funext y
        exact congrArg (fun z : Coeff (g.Slot p) D => z a) (hparent y)
      rw [he]
      unfold adjointField adjointComponent
      apply ContDiff.sum
      intro k _
      exact (contDiff_dir (has k a) _).neg.add ((contDiff_dir hH _).mul (has k a))
    · exact ActualDecoratedCoordinate.contDiff hF hlo hhi hb0 hb1 x r ht (hT v hv a)
  have hap := fun k a => ActualDecoratedCoordinate.polynomialJets hF hlo hhi hb0 hb1 x r ht (hA k a)
  have htp := fun v hv a => ActualDecoratedCoordinate.polynomialJets hF hlo hhi hb0 hb1 x r ht (hT v hv a)
  have hi (c : Option Edge → Fin D) (k : Fin D) :=
    productIntegrability_of_polynomialJets
      (interpolationLaw_integrable_norm_pow hF hlo x r t)
      (fun _ : Unit => (0 : EuclideanSpace ℝ (Fin D))) []
      (interpolationPotential F x r t)
      (fun y => A y k (Sum.elim (fun s : g.InPort p => c s.val) (fun s : g.OutPort p => c s.val)))
      (coordinateDirection D k)
      (fun q : {v : Fin (n+1) // v ≠ p} => fun y => g.wireValue (T y) c q.val)
      hH (has k _) (fun q => hts q.val _)
      (score_direction_polynomialJets hF hlo hhi hb0 hb1 x r ht (coordinateDirection D k))
      (hap k _) (fun q => htp q.val q.property _)
  rw [interpolationLaw_eq_tilted hF hlo x r ht'.1 ht'.2] at hi ⊢
  exact g.integral_adjoint_network p _ hH
    (integrable_exp_neg_interpolationPotential hF hlo x r ht'.1 ht'.2)
    T A has (fun v a => (hts v a).differentiable (by simp)) hparent hi
end AcceleratedLogConcave.Tensor.Ordered.Graph
