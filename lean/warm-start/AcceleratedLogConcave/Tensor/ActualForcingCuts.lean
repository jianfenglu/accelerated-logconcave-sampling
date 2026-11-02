import AcceleratedLogConcave.Tensor.VectorPartitionCuts
import AcceleratedLogConcave.Conditional.Transport.ActualFlowVolterra

/-!

-/
noncomputable section
open scoped BigOperators Classical
namespace AcceleratedLogConcave.Tensor.ActualPartitionTree
open EdgeClosure ActualCoefficient
open AcceleratedLogConcave.Conditional
open AcceleratedLogConcave.Conditional.Transport.SpatialFlow
open AcceleratedLogConcave.Analysis.SpatialPartition

 theorem actual_forcing_allProper {D : ℕ}
    (d : PositiveVarianceFlowData (Space D)) (n : ℕ) (hn : 0 < n)
    (s : ℝ) (y : Space D) (A P : ℕ → ℝ)
    (hA : ∀ k, 0 ≤ A k) (hP : ∀ k, 0 ≤ P k)
    (hroot : ∀ k, 2 ≤ k → k ≤ n →
      AllProper D (vectorCoeff (iteratedFDeriv ℝ k
        (probabilityVelocity d.F d.x d.r s) (actualY d s y))) (A k))
    (hbranch : ∀ j, 1 ≤ j → j < n →
      AllProper D (vectorCoeff (iteratedFDeriv ℝ j (actualY d s) y)) (P j)) :
    AllProper D (vectorCoeff (spatialForcing
      (probabilityVelocity d.F d.x d.r s) (actualY d s) y n hn))
      (∑ c ∈ (Finset.univ : Finset (OrderedFinpartition n)).erase
        (OrderedFinpartition.oneBlock n hn), A c.length * ∏ i, P (c.partSize i)) :=
  spatialForcing_allProper _ _ y n hn A P hA hP hroot hbranch

end AcceleratedLogConcave.Tensor.ActualPartitionTree
