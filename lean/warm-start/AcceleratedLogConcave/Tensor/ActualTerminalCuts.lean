import AcceleratedLogConcave.Tensor.RankTwoCuts
import AcceleratedLogConcave.Tensor.ActualCoefficientAssembly

/-!

-/
noncomputable section
set_option autoImplicit false
open scoped ContDiff Classical
namespace AcceleratedLogConcave.Tensor.ActualCoefficient
open Conditional Conditional.Transport.SpatialFlow
open AcceleratedLogConcave.Analysis.SpatialVariation
variable {D : ℕ}

 theorem actualY_terminal_eq_id (d : PositiveVarianceFlowData (Space D)) :
    (actualY d d.b : Space D → Space D) = id := by
  funext z
  exact backward_spatial_terminal d.hF d.hell d.hlo d.hhi d.x
    d.hr d.hb0 d.hb1 ([] : List (Space D)) z

 theorem actualJetCoeff_terminal_one_eq (d : PositiveVarianceFlowData (Space D))
    (y : Space D) :
    actualJetCoeff d 1 y d.b = rankTwoCoeff (ContinuousLinearMap.id ℝ (Space D)) := by
  change vectorCoeff (iteratedFDeriv ℝ 1 (actualY d d.b) y) = _
  rw [actualY_terminal_eq_id,vectorCoeff_one_eq_rankTwo,fderiv_id]

 theorem actualJetCoeff_terminal_one_le (d : PositiveVarianceFlowData (Space D))
    (y : Space D) (S : Finset (Fin 1 ⊕ Unit)) (hS : NontrivialSplit S) :
    splitNorm D S (actualJetCoeff d 1 y d.b) ≤ 1 := by
  rw [actualJetCoeff_terminal_one_eq]
  apply (rankTwo_splitNorm_le _ S hS).trans
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro v
  simp

 theorem actualJetCoeff_terminal_ge_two_zero (d : PositiveVarianceFlowData (Space D))
    (n : ℕ) (hn : 2 ≤ n) (y : Space D) : actualJetCoeff d n y d.b = 0 := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le' hn
  ext a
  change inner ℝ (basis D (a (.inr ())))
    (iteratedFDeriv ℝ (k+2) (actualY d d.b) y
      (fun j => basis D (a (.inl j)))) = 0
  rw [actualY_terminal_eq_id,← along_ofFn_eq_iteratedFDeriv contDiff_id]
  rw [List.ofFn_succ,List.ofFn_succ,along_id_at_least_two]
  simp

 theorem actualJetCoeff_terminal_ge_two_eq_zero (d : PositiveVarianceFlowData (Space D))
    (n : ℕ) (hn : 2 ≤ n) (y : Space D) (S : Finset (Fin n ⊕ Unit)) :
    splitNorm D S (actualJetCoeff d n y d.b) = 0 := by
  rw [actualJetCoeff_terminal_ge_two_zero d n hn y,splitNorm_zero]

/-- At dimension zero the first terminal cut norm is ZERO, not one. -/
 theorem actualJetCoeff_terminal_dim_zero (d : PositiveVarianceFlowData (Space 0))
    (n : ℕ) (y : Space 0) (S : Finset (Fin n ⊕ Unit)) :
    splitNorm 0 S (actualJetCoeff d n y d.b) = 0 := by
  have hz : actualJetCoeff d n y d.b = 0 := by
    ext a
    exact Fin.elim0 (a (.inr ()))
  rw [hz,splitNorm_zero]

end AcceleratedLogConcave.Tensor.ActualCoefficient
