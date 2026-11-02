import AcceleratedLogConcave.Numerics.CenterMeanPhaseKernelCalculus

/-! Literal phase weighted columns. The positive scale is not needed for these
algebraic identities; division by the physical scale is handled by the ODE join. -/
noncomputable section
open scoped ContDiff
namespace AcceleratedLogConcave.Numerics.CenterMeanSecondJetSource
open Conditional CenteringFlowLp Tensor.AdjointReduction Tensor.SkewCoordinateGenerator
variable {D : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin D)
local notation "EP" => EuclideanSpace ℝ (Fin (D+D))
local notation "e" => EuclideanSpace.basisFun (Fin D) ℝ
local notation "ep" => EuclideanSpace.basisFun (Fin (D+D)) ℝ

private theorem differentiable_phaseKernelEntry (d : Data (Fin D)) (i j : Fin D) :
    Differentiable ℝ (fun v : EP => inner ℝ (e i) (K d (phasePosition v) (e j))) := by
  have hK := (Transport.contDiff_infty_transportedSteinKernelTranspose d.hF d.hell d.hlo d.hup
    d.x d.hr d.hb d.hb1 d.hsmall).comp smooth_phasePosition
  exact (contDiff_const.inner ℝ (hK.clm_apply contDiff_const)).differentiable (by simp)

private theorem sum_phase_indices (f : Fin (D+D) → ℝ) :
    (∑ i, f i) = (∑ i, f (finSumFinEquiv (.inl i))) +
      ∑ i, f (finSumFinEquiv (.inr i)) := by
  rw [← finSumFinEquiv.sum_comp f,Fintype.sum_sum_type]

theorem phase_column_momentum (d : Data (Fin D)) (ellScale : ℝ) (z : EP) (j : Fin D) :
    column ep (phaseTransportEntry d ellScale) (phasePotential d) z (finSumFinEquiv (.inr j)) =
      ellScale⁻¹ * inner ℝ (M d (phasePosition z) - meanOffset d) (e j) := by
  unfold column
  rw [sum_phase_indices]
  have hi (i : Fin D) :
      (-dir (ep (finSumFinEquiv (.inl i)))
        (phaseTransportEntry d ellScale (finSumFinEquiv (.inl i)) (finSumFinEquiv (.inr j))) z +
      dir (ep (finSumFinEquiv (.inl i))) (phasePotential d) z *
        phaseTransportEntry d ellScale (finSumFinEquiv (.inl i)) (finSumFinEquiv (.inr j)) z) =
      ellScale⁻¹ * (-fderiv ℝ (fun y => inner ℝ (e i) (K d y (e j)))
        (phasePosition z) (e i) + inner ℝ (sourceScore d (phasePosition z)) (e i) *
          inner ℝ (e i) (K d (phasePosition z) (e j))) := by
    have he : phaseTransportEntry d ellScale (finSumFinEquiv (.inl i))
        (finSumFinEquiv (.inr j)) =
        fun v => ellScale⁻¹ * inner ℝ (e i) (K d (phasePosition v) (e j)) := by
      funext v
      simp only [phaseTransportEntry,Equiv.symm_apply_apply,skewBlockEntry]
    rw [he]
    simp only [dir]
    rw [fderiv_const_mul (differentiable_phaseKernelEntry d i j z),smul_apply,smul_eq_mul,
      phaseKernelEntry_position_derivative,phasePotential_position_derivative]
    ring
  have hz (i : Fin D) :
      (-dir (ep (finSumFinEquiv (.inr i)))
        (phaseTransportEntry d ellScale (finSumFinEquiv (.inr i)) (finSumFinEquiv (.inr j))) z +
      dir (ep (finSumFinEquiv (.inr i))) (phasePotential d) z *
        phaseTransportEntry d ellScale (finSumFinEquiv (.inr i)) (finSumFinEquiv (.inr j)) z) = 0 := by
    have he : phaseTransportEntry d ellScale (finSumFinEquiv (.inr i))
        (finSumFinEquiv (.inr j)) = fun _ => 0 := by
      funext v
      simp only [phaseTransportEntry,Equiv.symm_apply_apply,skewBlockEntry,mul_zero]
    rw [he]
    simp [dir]
  simp_rw [hi,hz]
  rw [Finset.sum_const_zero,add_zero,← Finset.mul_sum,source_weighted_column]

end AcceleratedLogConcave.Numerics.CenterMeanSecondJetSource
