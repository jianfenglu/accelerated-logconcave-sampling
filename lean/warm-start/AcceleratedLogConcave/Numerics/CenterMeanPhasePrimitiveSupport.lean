import AcceleratedLogConcave.Numerics.CenterMeanPhaseCalculus
import AcceleratedLogConcave.Numerics.CenterMeanPhaseCoefficients
import AcceleratedLogConcave.Tensor.CoordinateEmbeddingConsumers
import AcceleratedLogConcave.Tensor.PhasePrimitiveBudgets
import AcceleratedLogConcave.Analysis.AngleDirectionalScaling

/-! NEW reconstruction; source only, not compiler validated.
Only the dependencies actually used by the surviving transport tensor proof.
No primitive budget, moment hypothesis, or Regularity assertion is introduced. -/
noncomputable section
namespace AcceleratedLogConcave.Numerics.CenterMeanSecondJetSource
open Tensor Tensor.CoordinateReduction
variable {D : ℕ}

/-- Exchange exactly the terminal row and column. Derivative slots stay fixed. -/
def centerGradientSlotSwap (j : ℕ) : (Fin j ⊕ Fin 2) ≃ (Fin j ⊕ Fin 2) :=
  Equiv.sumCongr (Equiv.refl _) (Equiv.swap 0 1)

theorem phasePosition_coordinate_castAdd (i : Fin D) :
    phasePosition (coordinateDirection (D+D) (Fin.castAdd D i)) =
      coordinateDirection D i := by
  have hb (N : ℕ) (k : Fin N) : coordinateDirection N k =
      EuclideanSpace.basisFun (Fin N) ℝ k := by
    simp [EuclideanSpace.basisFun_apply, coordinateDirection, EuclideanSpace.single]
  simp only [hb]
  exact phasePosition_position_basis i

theorem phasePosition_coordinate_natAdd (i : Fin D) :
    phasePosition (coordinateDirection (D+D) (Fin.natAdd D i)) = 0 := by
  have hb (N : ℕ) (k : Fin N) : coordinateDirection N k =
      EuclideanSpace.basisFun (Fin N) ℝ k := by
    simp [EuclideanSpace.basisFun_apply, coordinateDirection, EuclideanSpace.single]
  simp only [hb]
  exact phasePosition_momentum_basis i

end AcceleratedLogConcave.Numerics.CenterMeanSecondJetSource
