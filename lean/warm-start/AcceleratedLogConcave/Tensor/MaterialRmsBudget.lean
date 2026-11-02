import AcceleratedLogConcave.Tensor.MaterialJacobianLp
import AcceleratedLogConcave.Tensor.TerminalBudgetBounds

noncomputable section
namespace AcceleratedLogConcave.Tensor.ActualCoefficientIntegrability
open Conditional Analysis Analysis.PositiveVarianceSlab MeasureTheory Set

/-- Literal terminal count times terminal coefficient budget, with the one loop factor. -/
def materialRmsNumeric (D s : ℕ) : ℝ :=
  (D:ℝ) * ((2*s:ℕ):ℝ)^(2*s) * (2:ℝ)^(2*s) * ((2*s).factorial:ℝ)

theorem materialRmsNumeric_nonneg (D s : ℕ) : 0 ≤ materialRmsNumeric D s := by
  unfold materialRmsNumeric
  positivity

theorem materialRmsNumeric_mono (D : ℕ) {s S : ℕ} (hs : s≤S) (hS : 1≤S) :
    materialRmsNumeric D s ≤ materialRmsNumeric D S := by
  have hss : 2*s≤2*S := by omega
  have hc : ((2*s:ℕ):ℝ)≤((2*S:ℕ):ℝ) := by exact_mod_cast hss
  have hb : (1:ℝ)≤((2*S:ℕ):ℝ) := by exact_mod_cast (show 1≤2*S by omega)
  have hp : (((2*s:ℕ):ℝ)^(2*s))≤(((2*S:ℕ):ℝ)^(2*S)) :=
    (pow_le_pow_left₀ (by positivity) hc _).trans (pow_le_pow_right₀ hb hss)
  have h2 : (2:ℝ)^(2*s)≤(2:ℝ)^(2*S) := pow_le_pow_right₀ (by norm_num) hss
  have hf : ((2*s).factorial:ℝ)≤((2*S).factorial:ℝ) := by exact_mod_cast Nat.factorial_le hss
  unfold materialRmsNumeric
  exact mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left hp (by positivity)) h2
    (by positivity) (by positivity)) hf (by positivity) (by positivity)

theorem materialRmsBudget_mono (D : ℕ) {s S : ℕ} (hs : s≤S) (hS : 1≤S)
    {w W R : ℝ} (hw : w≤W) (hR : 0<R) (hR1 : R≤1) :
    materialRmsNumeric D s * R^(-2*w) ≤ materialRmsNumeric D S * R^(-2*W) := by
  exact mul_le_mul (materialRmsNumeric_mono D hs hS)
    (Real.rpow_le_rpow_of_exponent_ge hR hR1 (by linarith))
    (by positivity) (materialRmsNumeric_nonneg D S)

/-- Specialize the exact individual-expression bound to all literal word terms.
The individual RMS theorem remains a premise until the network proof supplies it. -/
theorem materialWords_expression_moment_uniform {D : ℕ}
    (d : PositiveVarianceFlowData (EuclideanSpace ℝ (Fin D))) (k : ℕ) (hk : 0<k)
    {t R : ℝ} (hR : 0<R) (hR1 : R≤1)
    (hRMS : ∀ (e : Expr signature 2), IsMaterialExpression e →
      (∫ y, ‖Expr.evaluate (coefficientEnvironment d.F d.x d.ell d.r t)
        (interpolationPotential d.F d.x d.r t) e y‖^2
        ∂interpolationLaw d.F d.x d.r t) ≤
      materialRmsNumeric D e.size * R^(-2*(e.weight:ℝ))) :
    ∀ u ∈ materialWordsTerms (d.ell*d.r^2) k,
      (∫ y, ‖Expr.evaluate (coefficientEnvironment d.F d.x d.ell d.r t)
        (interpolationPotential d.F d.x d.r t) u.expression y‖^2
        ∂interpolationLaw d.F d.x d.r t) ≤
      materialRmsNumeric D (3*k-1) * R^(-4*((k-1:ℕ):ℝ)) := by
  intro u hu
  obtain ⟨he,hs,hw,_⟩ := materialWordsTerms_source_budgets _ k hk u hu
  have hw' : (u.expression.weight:ℝ)≤2*((k-1:ℕ):ℝ) := by exact_mod_cast hw
  have hh := materialRmsBudget_mono D hs (by omega) hw' hR hR1
  have heq : -2*(2*((k-1:ℕ):ℝ)) = -4*((k-1:ℕ):ℝ) := by ring
  rw [heq] at hh
  exact (hRMS u.expression he).trans hh

theorem sqrtVariance_rpow_budget {v : ℝ} (hv : 0≤v) (n : ℕ) :
    (Real.sqrt v)^(-4*(n:ℝ)) = (1/v^n)^2 := by
  rw [←Real.rpow_div_two_eq_sqrt _ hv]
  have he : (-4*(n:ℝ))/2 = -((2*n:ℕ):ℝ) := by push_cast; ring
  rw [he,Real.rpow_neg hv,Real.rpow_natCast,pow_mul]
  simp only [one_div,inv_pow]
  congr 1
  rw [←pow_mul,←pow_mul,Nat.mul_comm]

theorem materialWords_expression_moment_variance {D : ℕ}
    (d : PositiveVarianceFlowData (EuclideanSpace ℝ (Fin D))) (k : ℕ) (hk : 0<k)
    {t : ℝ} (ht : t ∈ Icc 0 d.b)
    (hRMS : ∀ (e : Expr signature 2), IsMaterialExpression e →
      (∫ y, ‖Expr.evaluate (coefficientEnvironment d.F d.x d.ell d.r t)
        (interpolationPotential d.F d.x d.r t) e y‖^2
        ∂interpolationLaw d.F d.x d.r t) ≤
      materialRmsNumeric D e.size * (Real.sqrt (conditionalVariance t))^(-2*(e.weight:ℝ))) :
    ∀ u ∈ materialWordsTerms (d.ell*d.r^2) k,
      (∫ y, ‖Expr.evaluate (coefficientEnvironment d.F d.x d.ell d.r t)
        (interpolationPotential d.F d.x d.r t) u.expression y‖^2
        ∂interpolationLaw d.F d.x d.r t) ≤
      (Real.sqrt (materialRmsNumeric D (3*k-1)) / (1-t^2)^(k-1))^2 := by
  have hv : 0<conditionalVariance t := conditionalVariance_pos (by linarith [ht.1])
    (by linarith [ht.2,d.hb1])
  have hR1 : Real.sqrt (conditionalVariance t)≤1 := by
    apply (Real.sqrt_le_one).2
    simp only [conditionalVariance]
    nlinarith [sq_nonneg t]
  intro u hu
  have hh := materialWords_expression_moment_uniform d k hk (Real.sqrt_pos.2 hv) hR1 hRMS u hu
  rw [sqrtVariance_rpow_budget hv.le] at hh
  convert hh using 1
  rw [div_pow,Real.sq_sqrt (materialRmsNumeric_nonneg D (3*k-1))]
  simp [conditionalVariance,div_eq_mul_inv]

end AcceleratedLogConcave.Tensor.ActualCoefficientIntegrability

namespace AcceleratedLogConcave.Numerics.MeanResidualBridge
open MeanFlowLp AffineGraph AffineGraph.MeanGeometry Analysis.PositiveVarianceSlab
open Tensor.ActualCoefficientIntegrability MeasureTheory Set
variable {D m : ℕ}

def materialKernelDerivativeBudget (d : MeanFlowLp.Data (Fin D) m) (k : ℕ) : ℝ :=
  Real.exp (1/2:ℝ)*(((kernelData d).ell*(kernelData d).r^2)*(k.factorial:ℝ)*
    (materialWordMassBase k)^k)*Real.sqrt (materialRmsNumeric D (3*k-1))

theorem materialKernelDerivativeBudget_nonneg (d : MeanFlowLp.Data (Fin D) m) (k : ℕ) :
    0≤materialKernelDerivativeBudget d k := by
  unfold materialKernelDerivativeBudget
  have hl := (kernelData d).hell
  have hb := (materialWordMassBase_one_le k).trans' (by norm_num : (0:ℝ)≤1)
  positivity

/-- Exact kernel_bound order and denominator of Regularity. The network RMS
premise is explicit; the other six Regularity families are not asserted. -/
theorem smoothKernel_regularity_bound_of_expressionRMS
    (d : MeanFlowLp.Data (Fin D) m)
    (hRMS : ∀ t ∈ Icc (0:ℝ) (backwardEnd d.G.R),
      ∀ (e : Tensor.Expr signature 2), IsMaterialExpression e →
      (∫ y, ‖Tensor.Expr.evaluate
        (coefficientEnvironment (kernelData d).F (kernelData d).x (kernelData d).ell (kernelData d).r t)
        (Conditional.interpolationPotential (kernelData d).F (kernelData d).x (kernelData d).r t)
        e y‖^2 ∂Conditional.interpolationLaw (kernelData d).F (kernelData d).x (kernelData d).r t) ≤
      materialRmsNumeric D e.size * (Real.sqrt (Conditional.conditionalVariance t))^(-2*(e.weight:ℝ))) :
    ∀ j, ∀ t ∈ Icc (0:ℝ) (backwardEnd d.G.R),
      ‖iteratedDeriv (m+2) (smoothKernel d j) t‖ ≤
        materialKernelDerivativeBudget d (m+2) / (1-t^2)^(m+2) := by
  intro j t ht
  let sd := KernelFlowLp.smoothData (kernelData d)
  have hv : 0<1-t^2 := Conditional.conditionalVariance_pos (by linarith [ht.1])
    (by linarith [ht.2,d.G.backwardEnd_lt_one])
  have hv1 : 1-t^2≤1 := by nlinarith [sq_nonneg t]
  have hmoment := materialWords_expression_moment_variance sd (m+2) (by omega) ht (hRMS t ht)
  have hM0 : 0≤Real.sqrt (materialRmsNumeric D (3*(m+2)-1))/(1-t^2)^(m+2-1) := by positivity
  have hh := norm_iteratedDeriv_smoothKernel_le_expressionRMS d j (m+1) ht hM0 hmoment
  have he : Real.exp (1/2:ℝ)*(((kernelData d).ell*(kernelData d).r^2)*((m+2).factorial:ℝ)*
      (materialWordMassBase (m+2))^(m+2)) *
      (Real.sqrt (materialRmsNumeric D (3*(m+2)-1))/(1-t^2)^(m+2-1)) =
      materialKernelDerivativeBudget d (m+2)/(1-t^2)^(m+1) := by
    simp only [materialKernelDerivativeBudget,show m+2-1=m+1 by omega]
    ring
  rw [he] at hh
  have hp : (1-t^2)^(m+2) ≤ (1-t^2)^(m+1) := by
    rw [show m+2=(m+1)+1 by omega,pow_succ]
    exact mul_le_of_le_one_right (pow_nonneg hv.le (m+1)) hv1
  exact hh.trans (div_le_div_of_nonneg_left (materialKernelDerivativeBudget_nonneg d (m+2))
    (pow_pos hv _) hp)

end AcceleratedLogConcave.Numerics.MeanResidualBridge
