import AcceleratedLogConcave.Numerics.SourceFiniteOutput
import AcceleratedLogConcave.Numerics.SmoothRowPayments

/-! All quadrature powers in the literal source receiver, including its full
centering contribution. The explicit row coefficient inventory still needs
its uniform numerical majorant before this becomes the manuscript's sharp
complexity estimate. -/
noncomputable section
set_option autoImplicit false
namespace AcceleratedLogConcave.Numerics.SourcePaidOutput
open MeanFlowLp MeanResidualBridge MeanCollocationLp
open SmoothQuantitativeAssembly SmoothQuadraturePayments SourceNumericalData
variable {D m : ℕ}

/-- No hidden initializer or row-residual bound is an input: both are paid from
the original data and the actual coefficient inventory. -/
theorem output_bound (P : Inputs (Fin D) m) (hm : 2 ≤ m)
    (hδone : P.δ ≤ 1) (hhhalf : P.δ^P.w ≤ 1/2)
    (hwt : P.w ≤ P.t) (ht : P.t ≤ (1:ℝ)/60)
    {b S : ℝ} (hb : (1:ℝ)/2 ≤ b) (hS : 1 ≤ S)
    (hsizeR : P.ell*P.r^2 ≤ S*P.δ^b)
    (hsizeS : P.ell*P.r/P.sigma ≤ S*P.δ^b)
    (hres : P.δ ≤ (520*(m:ℝ)^5*S)^(-12:ℝ))
    (hvelocity : VelocityBounds (data P)) (hangle : AngleBounds (data P)) (N : ℕ) :
    ‖output (data P) N - terminalTarget (data P)‖ ≤
      P.ell*((P.δ^((1:ℝ)/3)/2)^N *
        (2*(rowMass (data P) (P.δ^P.w)*
          (P.ell*directBudget (data P)+meanBudget (data P))+
          ‖SmoothRowPayments.rowCoefficient (data P)‖*
            P.δ^(SmoothRowPayments.exponent m P.w P.t))) +
        2*‖SmoothRowPayments.rowCoefficient (data P)‖*
          P.δ^(SmoothRowPayments.exponent m P.w P.t)) +
      (2*centerCoefficient (data P)/(m.factorial:ℝ))*P.δ^((m:ℝ)/3) := by
  let d := data P
  have hmesh := data_meshConditions P hm hδone hhhalf
  have hs := centerSpeed_le_of_resolution d hm P.hδ hδone P.hw.le hwt ht hb hS
    rfl hsizeS hres
  have hr := SmoothRowPayments.residual_payment d P.hδ hδone P.hw.le hwt ht
    hmesh hs rfl rfl (data_forward P) (data_conditional P) hvelocity hangle
  have hfinal := SourceFiniteOutput.output_bound P hm hδone hhhalf hwt ht hb hS
    hsizeR hsizeS hres hvelocity hangle N
  apply hfinal.trans
  have hell : 0 ≤ P.ell := P.hell
  have hp : 0 ≤ (P.δ^((1:ℝ)/3)/2)^N := by have := P.hδ.le; positivity
  apply add_le_add_left
  apply mul_le_mul_of_nonneg_left _ hell
  have htwo := mul_le_mul_of_nonneg_left hr (by norm_num : (0:ℝ) ≤ 2)
  have hseed := mul_le_mul_of_nonneg_left (add_le_add_right hr
    (rowMass (data P) (P.δ^P.w)*(P.ell*directBudget (data P)+meanBudget (data P))))
    (by norm_num : (0:ℝ) ≤ 2)
  exact (add_le_add (mul_le_mul_of_nonneg_left hseed hp) htwo).trans_eq (by ring)

end AcceleratedLogConcave.Numerics.SourcePaidOutput
