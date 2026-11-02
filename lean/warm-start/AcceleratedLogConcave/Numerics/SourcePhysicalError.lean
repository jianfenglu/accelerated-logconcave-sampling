import AcceleratedLogConcave.Numerics.SourceUniformOutput
import AcceleratedLogConcave.Numerics.SmoothInitialDisplacementBound
import AcceleratedLogConcave.Numerics.SmoothInventoryGrowth

/-! Actual-flow initializer and explicit exponential-order quadrature in one
finite-output estimate. The initial coefficient is the proved finite physical
row inventory, not a supplied bound on the unknown reference state. -/
noncomputable section
set_option autoImplicit false
namespace AcceleratedLogConcave.Numerics.SourcePhysicalError
open MeanFlowLp MeanResidualBridge MeanCollocationLp AffineGraph
open SmoothQuantitativeAssembly SmoothQuadraturePayments SourceNumericalData
open Analysis.PositiveVarianceSlab
variable {D m : ℕ}

theorem A_value_bound (hm : 1 ≤ m) :
    SmoothInventoryDimension.A m ≤ Real.exp (10200*((m:ℝ)+3)*Real.log ((m:ℝ)+3)) :=
  (Real.le_exp_log _).trans (Real.exp_le_exp.mpr (by simpa only [Nat.cast_add, Nat.cast_ofNat] using SmoothInventoryDimension.A_log_le m hm))

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
          (P.r*‖SmoothInitialDisplacementBound.rowCoefficient (data P)‖) +
        2*(P.r*Real.sqrt (D:ℝ)*Real.exp (10200*((m:ℝ)+3)*Real.log ((m:ℝ)+3)))*
          P.δ^(SmoothRowPayments.exponent m P.w P.t)) +
      (2*centerCoefficient (data P)/(m.factorial:ℝ))*P.δ^((m:ℝ)/3) := by
  let d := data P
  have hmesh := data_meshConditions P hm hδone hhhalf
  have hq := SmoothInitialError.contraction_le_resolution d (P.δ^P.w) hmesh
    P.hδ hδone P.hw.le hwt ht hb hS rfl rfl hsizeR hsizeS hres
  have hp : P.δ^((1:ℝ)/3) ≤ 1 := Real.rpow_le_one P.hδ.le hδone (by norm_num)
  have hhalf : contraction d (P.δ^P.w) ≤ 1/2 := by linarith
  have hq0 := contraction_nonneg d (P.δ^P.w) hmesh
  have hq1 : contraction d (P.δ^P.w) < 1 := by linarith
  have hinit := SmoothInitialDisplacementBound.initialError_le_data d
  have hinitp := mul_le_mul (pow_le_pow_left₀ hq0 hq N) hinit (norm_nonneg _)
    (by have := P.hδ.le; positivity : 0 ≤ (P.δ^((1:ℝ)/3)/2)^N)
  have hr := SourceUniformOutput.residual_bound P hm hδone hhhalf hwt ht hb hS
    hsizeS hres hvelocity hangle
  have hA := A_value_bound (by omega : 1 ≤ m)
  have hR : residualBudget d (P.δ^P.w) (budget d) ≤
      P.r*Real.sqrt (D:ℝ)*Real.exp (10200*((m:ℝ)+3)*Real.log ((m:ℝ)+3))*
        P.δ^(SmoothRowPayments.exponent m P.w P.t) := by
    apply hr.trans
    have := P.hr.le
    have := P.hδ.le
    gcongr
  have hden : 0 < 1-contraction d (P.δ^P.w) := by linarith
  have hrhalf : residualBudget d (P.δ^P.w) (budget d)/(1-contraction d (P.δ^P.w)) ≤
      2*residualBudget d (P.δ^P.w) (budget d) := by
    apply (div_le_iff₀ hden).mpr
    nlinarith [show 0 ≤ residualBudget d (P.δ^P.w) (budget d) from norm_nonneg _]
  have hrr := hrhalf.trans (mul_le_mul_of_nonneg_left hR (by norm_num : (0:ℝ) ≤ 2))
  have hs := centerSpeed_le_of_resolution d hm P.hδ hδone P.hw.le hwt ht hb hS rfl hsizeS hres
  have hc := centering_defect_le d (by omega) P.hδ hs
  have ho := SmoothQuantitativeGuarantees.geometric_output_bound d (P.δ^P.w) hmesh hvelocity hangle N hq1
  have hmain := mul_le_mul_of_nonneg_left (add_le_add hinitp hrr) P.hell
  have ho' : ‖output d N-terminalTarget d‖ ≤
      d.ell*(contraction d (P.δ^P.w)^N*initialError d+
        residualBudget d (P.δ^P.w) (budget d)/(1-contraction d (P.δ^P.w)))+
      2*(budget d).center/(m.factorial:ℝ) := by
    convert ho using 1; ring
  exact ho'.trans ((add_le_add hmain hc).trans_eq (by dsimp only [d, SourceNumericalData.data]; ring))

end AcceleratedLogConcave.Numerics.SourcePhysicalError
