import AcceleratedLogConcave.Numerics.CenterMeanPhaseColumns

noncomputable section
open scoped ContDiff
namespace AcceleratedLogConcave.Numerics.CenterMeanSecondJetSource
open Conditional CenteringFlowLp Tensor.AdjointReduction Tensor.SkewCoordinateGenerator
variable {D : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin D)
local notation "EP" => EuclideanSpace ℝ (Fin (D+D))
local notation "e" => EuclideanSpace.basisFun (Fin D) ℝ
local notation "ep" => EuclideanSpace.basisFun (Fin (D+D)) ℝ

private theorem kernel_coordinate_sum (A : E →L[ℝ] E) (g : E) (j : Fin D) :
    (∑ i, inner ℝ g (e i) * inner ℝ (e j) (A (e i))) = inner ℝ (e j) (A g) := by
  have h := congrArg (fun v => inner ℝ (e j) (A v))
    (OrthonormalBasis.sum_repr' e g)
  simpa only [map_sum,map_smul,inner_sum,inner_smul_right,real_inner_comm] using h

theorem phase_column_position (d : Data (Fin D)) (ellScale : ℝ) (z : EP) (j : Fin D) :
    column ep (phaseTransportEntry d ellScale) (phasePotential d) z (finSumFinEquiv (.inl j)) =
      -ellScale⁻¹ * inner ℝ (e j) (K d (phasePosition z) (phaseMomentum z)) := by
  unfold column
  rw [← finSumFinEquiv.sum_comp,Fintype.sum_sum_type]
  have hz (i : Fin D) :
      (-dir (ep (finSumFinEquiv (.inl i)))
        (phaseTransportEntry d ellScale (finSumFinEquiv (.inl i)) (finSumFinEquiv (.inl j))) z +
      dir (ep (finSumFinEquiv (.inl i))) (phasePotential d) z *
        phaseTransportEntry d ellScale (finSumFinEquiv (.inl i)) (finSumFinEquiv (.inl j)) z) = 0 := by
    have he : phaseTransportEntry d ellScale (finSumFinEquiv (.inl i))
        (finSumFinEquiv (.inl j)) = fun _ => 0 := by
      funext v
      simp only [phaseTransportEntry,Equiv.symm_apply_apply,skewBlockEntry,mul_zero]
    rw [he]
    simp [dir]
  have hi (i : Fin D) :
      (-dir (ep (finSumFinEquiv (.inr i)))
        (phaseTransportEntry d ellScale (finSumFinEquiv (.inr i)) (finSumFinEquiv (.inl j))) z +
      dir (ep (finSumFinEquiv (.inr i))) (phasePotential d) z *
        phaseTransportEntry d ellScale (finSumFinEquiv (.inr i)) (finSumFinEquiv (.inl j)) z) =
      -ellScale⁻¹ * (inner ℝ (phaseMomentum z) (e i) *
          inner ℝ (e j) (K d (phasePosition z) (e i))) := by
    have hK := (Transport.contDiff_infty_transportedSteinKernelTranspose d.hF d.hell d.hlo d.hup
      d.x d.hr d.hb d.hb1 d.hsmall).comp smooth_phasePosition
    have hf : DifferentiableAt ℝ (fun v : EP => -inner ℝ (e j) (K d (phasePosition v) (e i))) z :=
      ((contDiff_const.inner ℝ (hK.clm_apply contDiff_const)).neg.differentiable (by simp)) z
    have he : phaseTransportEntry d ellScale (finSumFinEquiv (.inr i))
        (finSumFinEquiv (.inl j)) =
        fun v => ellScale⁻¹ * (-inner ℝ (e j) (K d (phasePosition v) (e i))) := by
      funext v
      simp only [phaseTransportEntry,Equiv.symm_apply_apply,skewBlockEntry]
    rw [he]
    simp only [dir]
    rw [fderiv_const_mul hf,fderiv_fun_neg,smul_apply,smul_eq_mul]
    simp only [neg_apply,phaseKernelEntry_momentum_derivative,neg_zero,
      mul_zero,zero_add,phasePotential_momentum_derivative]
    ring
  simp_rw [hz,hi]
  rw [Finset.sum_const_zero,zero_add,← Finset.mul_sum,kernel_coordinate_sum]

end AcceleratedLogConcave.Numerics.CenterMeanSecondJetSource
