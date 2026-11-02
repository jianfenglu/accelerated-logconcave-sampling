import AcceleratedLogConcave.Tensor.MaterialWordsLp
import AcceleratedLogConcave.Numerics.SmoothKernelWords

noncomputable section
open scoped BigOperators
namespace AcceleratedLogConcave.Tensor.ActualCoefficientIntegrability
open Conditional Analysis Analysis.PositiveVarianceSlab Analysis.OrderedJacobianWords MeasureTheory Set
variable {D : ℕ} (d : PositiveVarianceFlowData (EuclideanSpace ℝ (Fin D)))

theorem actual_leftWordSum_integral_norm_sq_le (hsmall : d.r^2*d.ell ≤ 1/2)
    (m : ℕ) (hm : 0<m) {t M : ℝ} (ht : t ∈ Icc 0 d.b) (hM0 : 0≤M)
    (hM : ∀ u ∈ materialWordsTerms (d.ell*d.r^2) m,
      (∫ y, ‖Expr.evaluate (coefficientEnvironment d.F d.x d.ell d.r t)
        (interpolationPotential d.F d.x d.r t) u.expression y‖^2
        ∂interpolationLaw d.F d.x d.r t) ≤ M^2) :
    (∫ y, ‖operatorTensor (d.jacobian t y *
      evaluateSum (fun j u => d.jacobianCoefficientJet j u y) (words m) t)‖^2
      ∂interpolationLaw d.F d.x d.r d.b) ≤
      (Real.exp (1/2:ℝ)*((d.ell*d.r^2)*(m.factorial:ℝ)*(materialWordMassBase m)^m)*M)^2 := by
  let W := fun y => evaluateSum (fun j u => d.jacobianCoefficientJet j u y) (words m) t
  have hti := source_subset d.hb0 d.hb1 ht
  have hL := (actualTerms_memLp d (materialWordsTerms (d.ell*d.r^2) m)
    ⟨hti.1.le,hti.2.le⟩).comp_measurePreserving (d.state_fst_measurePreserving ht)
  have hW : MemLp (fun y => operatorTensor (W y)) 2 (interpolationLaw d.F d.x d.r d.b) := by
    convert hL using 1
    funext y
    exact actual_wordSum_tensor_expansion d m hm hti y
  have hi : Integrable (fun y => ‖operatorTensor (W y)‖^2)
      (interpolationLaw d.F d.x d.r d.b) :=
    (memLp_two_iff_integrable_sq hW.aestronglyMeasurable.norm).mp hW.norm
  have hB (y) : ‖d.jacobian t y‖ ≤ Real.exp (1/2:ℝ) :=
    (d.norm_jacobian_le t y).trans (Real.exp_le_exp.mpr hsmall)
  have hp (y) : ‖operatorTensor (d.jacobian t y * W y)‖^2 ≤
      (Real.exp (1/2:ℝ))^2 * ‖operatorTensor (W y)‖^2 := by
    have hh := (operatorTensor_norm_mul_le (d.jacobian t y) (W y)).trans
      (mul_le_mul_of_nonneg_right (hB y) (norm_nonneg _))
    nlinarith [norm_nonneg (operatorTensor (d.jacobian t y * W y)),
      mul_nonneg (Real.exp_pos (1/2:ℝ)).le (norm_nonneg (operatorTensor (W y)))]
  have hh := integral_mono_of_nonneg (Filter.Eventually.of_forall (fun y => sq_nonneg
      ‖operatorTensor (d.jacobian t y * W y)‖))
    (hi.const_mul ((Real.exp (1/2:ℝ))^2)) (Filter.Eventually.of_forall hp)
  rw [integral_const_mul] at hh
  have hw := actual_wordSum_integral_norm_sq_le d hsmall m hm ht hM0 hM
  have hx := mul_le_mul_of_nonneg_left hw (sq_nonneg (Real.exp (1/2:ℝ)))
  exact hh.trans (by convert hx using 1; ring)

end AcceleratedLogConcave.Tensor.ActualCoefficientIntegrability

namespace AcceleratedLogConcave.Numerics.MeanResidualBridge
open MeanFlowLp AffineGraph AffineGraph.MeanGeometry Analysis.PositiveVarianceSlab
open Tensor.ActualCoefficientIntegrability MeasureTheory Set
variable {D m : ℕ}

/-- The inherited smooth-kernel receiver, with the single whole-expression RMS
supplier still explicit and all transport/word/B/L2 bookkeeping discharged. -/
theorem norm_iteratedDeriv_smoothKernel_le_expressionRMS
    (d : MeanFlowLp.Data (Fin D) m) (j : Fin m) (n : ℕ) {t M : ℝ}
    (ht : t ∈ Icc 0 (backwardEnd d.G.R)) (hM0 : 0≤M)
    (hM : ∀ u ∈ materialWordsTerms ((kernelData d).ell*(kernelData d).r^2) (n+1),
      (∫ y, ‖Tensor.Expr.evaluate
        (coefficientEnvironment (kernelData d).F (kernelData d).x (kernelData d).ell (kernelData d).r t)
        (Conditional.interpolationPotential (kernelData d).F (kernelData d).x (kernelData d).r t)
        u.expression y‖^2 ∂Conditional.interpolationLaw (kernelData d).F (kernelData d).x
          (kernelData d).r t) ≤ M^2) :
    ‖iteratedDeriv (n+1) (smoothKernel d j) t‖ ≤
      Real.exp (1/2:ℝ)*(((kernelData d).ell*(kernelData d).r^2)*((n+1).factorial:ℝ)*
        (materialWordMassBase (n+1))^(n+1))*M := by
  let sd := KernelFlowLp.smoothData (kernelData d)
  have hh := actual_leftWordSum_integral_norm_sq_le sd (kernelData d).hsmall
    (n+1) (by omega) ht hM0 hM
  have he := norm_sq_iteratedDeriv_smoothKernel_eq_words d j n ht
  have hi : (∫ y, ‖operatorTensor (sd.jacobian t y *
      Analysis.OrderedJacobianWords.evaluateSum (fun k u => sd.jacobianCoefficientJet k u y)
        (Analysis.OrderedJacobianWords.words (n+1)) t)‖^2
      ∂Conditional.interpolationLaw sd.F sd.x sd.r sd.b) =
      ‖iteratedDeriv (n+1) (smoothKernel d j) t‖^2 := by
    rw [he]
    apply integral_congr_ae
    filter_upwards [] with y
    exact operatorTensor_norm_sq_basis (stdOrthonormalBasis ℝ (EuclideanSpace ℝ (Fin D))) _
  rw [hi] at hh
  have hn : 0 ≤ Real.exp (1/2:ℝ)*(((kernelData d).ell*(kernelData d).r^2)*
      ((n+1).factorial:ℝ)*(materialWordMassBase (n+1))^(n+1))*M := by
    apply mul_nonneg _ hM0
    apply mul_nonneg (Real.exp_pos _).le
    have hl := (kernelData d).hell
    have hb := (materialWordMassBase_one_le (n+1)).trans' (by norm_num : (0:ℝ) ≤ 1)
    positivity
  change ‖iteratedDeriv (n+1) (smoothKernel d j) t‖^2 ≤
    (Real.exp (1/2:ℝ)*(((kernelData d).ell*(kernelData d).r^2)*((n+1).factorial:ℝ)*
      (materialWordMassBase (n+1))^(n+1))*M)^2 at hh
  nlinarith [norm_nonneg (iteratedDeriv (n+1) (smoothKernel d j) t)]

end AcceleratedLogConcave.Numerics.MeanResidualBridge
