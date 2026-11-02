import AcceleratedLogConcave.Numerics.SourcePhysicalSmallness
import AcceleratedLogConcave.Numerics.SourcePaidOutput
import AcceleratedLogConcave.Numerics.SmoothInventoryDimension

/-! Dimension-explicit quadrature and finite-output bounds on the actual
source data. The coefficient A(m) contains only numerical order-dependent
terms; the unresolved analytic interfaces remain visible in the types. -/
noncomputable section
set_option autoImplicit false
namespace AcceleratedLogConcave.Numerics.SourceUniformOutput
open MeanFlowLp MeanResidualBridge MeanCollocationLp
open SmoothQuantitativeAssembly SmoothQuadraturePayments SourceNumericalData
variable {D m : ℕ}

variable (P : Inputs (Fin D) m) (hm : 2 ≤ m)
    (hδone : P.δ ≤ 1) (hhhalf : P.δ^P.w ≤ 1/2)
    (hwt : P.w ≤ P.t) (ht : P.t ≤ (1:ℝ)/60)
    {b S : ℝ} (hb : (1:ℝ)/2 ≤ b) (hS : 1 ≤ S)
    (hsizeS : P.ell*P.r/P.sigma ≤ S*P.δ^b)
    (hres : P.δ ≤ (520*(m:ℝ)^5*S)^(-12:ℝ))
    (hvelocity : VelocityBounds (data P)) (hangle : AngleBounds (data P))
include hm hδone hhhalf hwt ht hb hS hsizeS hres hvelocity hangle

/-- All source quadrature rows satisfy the dimension-explicit physical bound. -/
theorem residual_bound :
    residualBudget (data P) (P.δ^P.w) (budget (data P)) ≤
      P.r*Real.sqrt (D:ℝ)*SmoothInventoryDimension.A m*
        P.δ^(SmoothRowPayments.exponent m P.w P.t) := by
  let d := data P
  have hmesh := data_meshConditions P hm hδone hhhalf
  have hs := centerSpeed_le_of_resolution d hm P.hδ hδone P.hw.le hwt ht hb hS
    rfl hsizeS hres
  have hr := SmoothRowPayments.residual_payment d P.hδ hδone P.hw.le hwt ht
    hmesh hs rfl rfl (data_forward P) (data_conditional P) hvelocity hangle
  have hscale := SourcePhysicalSmallness.ratio_small (by omega : 1 ≤ m) P.hδ hδone hb hS hsizeS hres
  have hcoef := SmoothInventoryDimension.norm_rowCoefficient_le_dimension d
    (by omega) (d.G.R_le_half.trans (by norm_num)) hscale
  exact hr.trans (mul_le_mul_of_nonneg_right hcoef (Real.rpow_nonneg P.hδ.le _))

/-- Explicit finite output with both quadrature and centering powers paid.
The initializer here is the derived coarse seed bound, not yet the sharp C.6
physical-displacement estimate. -/
theorem output_bound (hsizeR : P.ell*P.r^2 ≤ S*P.δ^b) (N : ℕ) :
    ‖output (data P) N - terminalTarget (data P)‖ ≤
      P.ell*((P.δ^((1:ℝ)/3)/2)^N *
        (2*(rowMass (data P) (P.δ^P.w)*
          (P.ell*directBudget (data P)+meanBudget (data P))+
          P.r*Real.sqrt (D:ℝ)*SmoothInventoryDimension.A m*
            P.δ^(SmoothRowPayments.exponent m P.w P.t))) +
        2*(P.r*Real.sqrt (D:ℝ)*SmoothInventoryDimension.A m*
          P.δ^(SmoothRowPayments.exponent m P.w P.t))) +
      (2*centerCoefficient (data P)/(m.factorial:ℝ))*P.δ^((m:ℝ)/3) := by
  have hr := residual_bound P hm hδone hhhalf hwt ht hb hS hsizeS hres hvelocity hangle
  have hfinal := SourceFiniteOutput.output_bound P hm hδone hhhalf hwt ht hb hS
    hsizeR hsizeS hres hvelocity hangle N
  apply hfinal.trans
  have hp : 0 ≤ (P.δ^((1:ℝ)/3)/2)^N := by have := P.hδ.le; positivity
  apply add_le_add_left
  apply mul_le_mul_of_nonneg_left _ P.hell
  have htwo := mul_le_mul_of_nonneg_left hr (by norm_num : (0:ℝ) ≤ 2)
  have hseed := mul_le_mul_of_nonneg_left (add_le_add_right hr
    (rowMass (data P) (P.δ^P.w)*(P.ell*directBudget (data P)+meanBudget (data P))))
    (by norm_num : (0:ℝ) ≤ 2)
  exact add_le_add (mul_le_mul_of_nonneg_left hseed hp) htwo

end AcceleratedLogConcave.Numerics.SourceUniformOutput
