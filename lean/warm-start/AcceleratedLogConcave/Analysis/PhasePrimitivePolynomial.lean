import AcceleratedLogConcave.Analysis.CoordinatePolynomialJets
import AcceleratedLogConcave.Analysis.PhaseCoefficientEntryBound
import AcceleratedLogConcave.Tensor.PhasePrimitiveBudgets
import AcceleratedLogConcave.Tensor.PhaseExpressionGrammar

/-! The genuine primitive split bounds imply the qualitative coefficient
jet tails required by the Gibbs engine. No extra tail hypothesis is necessary. -/
noncomputable section
open scoped ContDiff
namespace AcceleratedLogConcave.Tensor.Ordered.Graph
open AdjointReduction PolynomialClosure PhaseExpression
variable {D : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin D)

private theorem partialAlong_comp {I J : Type*} (d : I → E) (g : J → I)
    (l : List J) (f : E → ℝ) :
    partialAlong (d ∘ g) l f = partialAlong d (l.map g) f := by
  induction l with
  | nil => rfl
  | cons i l ih => simp only [partialAlong,List.map_cons,Function.comp_apply,ih]

theorem PhasePrimitiveBudgets.coefficient_coordinateJets
    {ρ : CoefficientEnvironment signature D} {H : E → ℝ} {C R : ℝ}
    (h : PhasePrimitiveBudgets ρ H C R) (c : Primitive) (u : Fin 2 → Fin D) :
    CoordinatePolynomialJets (fun x => ρ c x u) := by
  apply coordinatePolynomialJets_of_bounded
  intro J
  let a : Fin J.length ⊕ Fin 2 → Fin D := Sum.elim J.get u
  let S : Finset (Fin J.length ⊕ Fin 2) := {.inr 0}
  have hS : NontrivialSplit S := by
    constructor
    · exact ⟨.inr 0,by simp [S]⟩
    · exact ⟨.inr 1,by simp [S]⟩
  have he (x : E) : phaseCoefficientJet ρ c J.length x a =
      partialAlong (coordinateDirection D) J (fun y => ρ c y u) x := by
    change partialAlong (coordinateDirection D ∘ J.get) (List.finRange J.length)
      (fun y => ρ c y u) x = _
    rw [partialAlong_comp,List.map_get_finRange]
  refine ⟨C^(2+J.length) * ((2+J.length).factorial : ℝ) *
    R^(-((signature.weight c : ℝ)+(J.length : ℝ))),?_⟩
  intro x
  rw [Real.norm_eq_abs,← he]
  exact (abs_coefficient_le_splitNorm _ S a).trans (h.coefficient c J.length x S hS)

theorem PhasePrimitiveBudgets.coefficient_polynomialJets
    {ρ : CoefficientEnvironment signature D} {H : E → ℝ} {C R : ℝ}
    (h : PhasePrimitiveBudgets ρ H C R)
    (hs : ∀ c u, ContDiff ℝ ∞ (fun x => ρ c x u)) :
    ∀ c u, HasPolynomialJets (fun x => ρ c x u) := by
  intro c u
  exact (h.coefficient_coordinateJets c u).toPolynomialJets (hs c u)
end AcceleratedLogConcave.Tensor.Ordered.Graph
