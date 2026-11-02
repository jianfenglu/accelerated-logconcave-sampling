import AcceleratedLogConcave.Oracle.ExecutableShiftMass
import AcceleratedLogConcave.Oracle.SourceMeanShift

/-! Exact mass of the actual source mean's shift. Held-fixed final draws are
present in the program and cost counts, but contribute zero shift mass. -/
noncomputable section
namespace AcceleratedLogConcave.Oracle.SourceExecutableMass
open Numerics.AffineGraph TapeLowering ExecutableShiftMass CovarianceSetup
open SourceMeanExecutable
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

variable (M : MeanGeometry m) (nodes : Fin n ≃ M.MeanNode)
  (anchors : Fin a ≃ M.Anchor) (seeds : Fin h ≃ Fin m × M.Kernel)
  (r σ Ds : ℝ) (main : Fin n → ExecutableData) (final : Fin m → ExecutableData)
  (sampling : ExecutableData) (layers : ℕ)

theorem body_mass :
    slotMass (body (a := a) (h := h) M nodes main final sampling layers)
      (bodyShift M nodes r σ Ds main final sampling layers) =
      (layers:ℝ) * ∑ i, shiftSq (mainRaw M nodes r σ Ds main i) := by
  unfold body bodyShift SourceExecutableShift.meanBlock NonterminalMeanBlock.code
  rw [initializeWeights_mass]
  calc
    _ = (layers:ℝ) * (∑ i, shiftSq (mainRaw M nodes r σ Ds main i)) + 0 := by
      apply iterateWeights_mass
      intro Δ old direct saved
      exact slotMass_zero _
    _ = _ := add_zero _

theorem incoming_mass (privateShift : GaussianSlot sampling.program → ℝ) :
    slotMass (incoming M nodes anchors seeds main final sampling layers)
      (incomingShift M nodes anchors seeds r σ Ds main final sampling layers privateShift) =
      slotMass sampling.program privateShift +
        (layers:ℝ) * ∑ i, shiftSq (mainRaw M nodes r σ Ds main i) := by
  unfold incoming incomingShift SourceExecutableShift.meanPrefix MeanExecutablePrefix.code
  unfold MeanGaussianSetup.setup
  simp only [slotMass_batch, Sum.elim_inl, Sum.elim_inr]
  simp only [slotMass_zero, Finset.sum_const_zero, zero_add]
  rw [body_mass]
  congr 1
  simp only [Fin.sum_univ_one]
  exact lowerWeights_mass _ _ _ _ _ _

theorem build_mass (δ t w : ℝ) (privateShift : GaussianSlot sampling.program → ℝ) :
    shiftSq (build M nodes anchors seeds r σ Ds δ t w main final sampling layers
      privateShift).shiftVector = slotMass sampling.program privateShift +
        (layers:ℝ) * ∑ i, shiftSq (mainRaw M nodes r σ Ds main i) := by
  rw [shiftVector_mass]
  change slotMass (program M nodes anchors seeds main final sampling layers)
    (shift M nodes anchors seeds r σ Ds main final sampling layers privateShift) = _
  unfold program shift
  erw [slotMass_step,slotMass_step]
  change (∑ _s : PEmpty.{1}, (0:ℝ)) + ((∑ _s : PEmpty.{1}, (0:ℝ)) +
    slotMass _ (incomingShift M nodes anchors seeds r σ Ds main final sampling layers privateShift)) = _
  simp only [Fintype.sum_empty,zero_add]
  exact incoming_mass M nodes anchors seeds r σ Ds main final sampling layers privateShift

/-- Quantitative source main-layer bound. Each executed occurrence contributes
at most 36 times its actual smaller shift mass; active-final slots contribute zero. -/
theorem build_mass_le (δ t w : ℝ) (privateShift : GaussianSlot sampling.program → ℝ)
    (hr : 0 < r) (hpsi : M.psi ≤ M.R^4)
    (hm : ∀ i, ChildAbsorption.Admissible (RecursiveMeanPublicTable.centerNoise r M.R Ds)
      (M.radius r (nodes i)) Ds (main i).shiftVector) :
    shiftSq (build M nodes anchors seeds r σ Ds δ t w main final sampling layers
      privateShift).shiftVector ≤ slotMass sampling.program privateShift +
        36 * (layers:ℝ) * ∑ i, shiftSq (main i).shiftVector := by
  rw [build_mass]
  apply add_le_add le_rfl
  have hb : (∑ i, shiftSq (mainRaw M nodes r σ Ds main i)) ≤
      36 * ∑ i, shiftSq (main i).shiftVector := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    exact (LayerShift.shiftBounds (hm i)
      (SourceMeanShift.centerShift_ratio M nodes r σ hr hpsi i)).1
  have hn := mul_le_mul_of_nonneg_left hb (show (0:ℝ) ≤ layers by positivity)
  simpa only [mul_left_comm,mul_assoc] using hn

end AcceleratedLogConcave.Oracle.SourceExecutableMass
