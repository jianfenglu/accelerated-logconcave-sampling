import AcceleratedLogConcave.Tensor.PhaseSourceJetInduction

/-!
NEW reconstruction, 2026-10-22. Not recovered historical source.
The whole vector is an isometric reindexing of a rank-one coefficient tensor.
Consequently the lift spends no additional dimension factor. No integrability
or source moment assumptions enter this pointwise differential interface.
-/
noncomputable section
open scoped ContDiff
namespace AcceleratedLogConcave.Tensor.PhaseSourceJetInduction
open AdjointReduction CoordinateReduction PhaseExpression PhaseGeneratorIdentification
variable {D : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin D)

def rankOneAssignmentEquiv : (Fin 1 → Fin D) ≃ Fin D where
  toFun a := a 0
  invFun i := ![i]
  left_inv a := by
    funext k
    fin_cases k
    rfl
  right_inv i := rfl

def rankOneVectorEquiv : Coeff (Fin 1) D ≃ₗᵢ[ℝ] E :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ rankOneAssignmentEquiv

def vectorSection (ρ : CoefficientEnvironment signature D) (H : E → ℝ)
    (e : Expr signature 1) (x : E) : E :=
  rankOneVectorEquiv (Expr.evaluate ρ H e x)

@[simp] theorem vectorSection_apply (ρ : CoefficientEnvironment signature D) (H : E → ℝ)
    (e : Expr signature 1) (x : E) (i : Fin D) :
    vectorSection ρ H e x i = sectionValue ρ H e ![i] x := rfl

@[simp] theorem norm_vectorSection (ρ : CoefficientEnvironment signature D) (H : E → ℝ)
    (e : Expr signature 1) (x : E) :
    ‖vectorSection ρ H e x‖ = ‖Expr.evaluate ρ H e x‖ :=
  rankOneVectorEquiv.norm_map _

theorem hasDerivAt_vectorSection_along (ρ : CoefficientEnvironment signature D) (H : E → ℝ)
    (hρ : ∀ c a, ContDiff ℝ ∞ (fun x => ρ c x a)) (hH : ContDiff ℝ ∞ H)
    (hskew : ∀ x i j, transportEntry ρ i j x = -transportEntry ρ j i x)
    (e : Expr signature 1) {Z : ℝ → E} {α t : ℝ}
    (hZ : HasDerivAt Z (α • SkewCoordinateGenerator.velocity
      (coordinateDirection D) (transportEntry ρ) H (Z t)) t) :
    HasDerivAt (fun u => vectorSection ρ H e (Z u))
      (α • vectorSection ρ H (next e) (Z t)) t := by
  have hi (i : Fin D) := hasDerivAt_section_along ρ H hρ hH hskew e i hZ
  have hp := hasDerivAt_pi.mpr hi
  have h := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin D => ℝ)).symm.hasFDerivAt.comp_hasDerivAt t hp
  convert h using 1
  · funext u
    ext i
    rfl
  · ext i
    rfl
end AcceleratedLogConcave.Tensor.PhaseSourceJetInduction
