import AcceleratedLogConcave.Numerics.SourceNumericalData
import AcceleratedLogConcave.Numerics.SmoothInitialError
import AcceleratedLogConcave.Numerics.SmoothStepPayments

/-! Finite smooth-receiver output on the literal source partitions. The seed
payment is derived from the actual direct vector, and the complete center
payment is derived from the original-data center supplier. The row residual
is still the explicit seven-component residual, not a claimed sharp bound. -/
noncomputable section
set_option autoImplicit false
namespace AcceleratedLogConcave.Numerics.SourceFiniteOutput
open MeanFlowLp MeanResidualBridge MeanCollocationLp AffineGraph AffineGraph.MeanGeometry
open SmoothQuantitativeAssembly SmoothQuadraturePayments SourceNumericalData
open Analysis.PositiveVarianceSlab
variable {D m : ℕ}

/-- Original data and source scalar conditions pay the actual finite output.
Only the two advertised source analytic interfaces remain analytic premises. -/
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
          residualBudget (data P) (P.δ^P.w) (budget (data P)))) +
        2*residualBudget (data P) (P.δ^P.w) (budget (data P))) +
      (2*centerCoefficient (data P)/(m.factorial:ℝ))*P.δ^((m:ℝ)/3) := by
  let d := data P
  have hmesh := data_meshConditions P hm hδone hhhalf
  have hreg := regularity d (by omega) hvelocity hangle
  have hfinal := SmoothInitialError.final_payment_of_resolution d (P.δ^P.w) hmesh
    (left (backwardEnd d.G.R)) (right (backwardEnd d.G.R))
    (left_margin d) (right_margin d) (budget d) hreg N
    P.hδ hδone P.hw.le hwt ht hb hS rfl rfl hsizeR hsizeS hres
  have hs := centerSpeed_le_of_resolution d hm P.hδ hδone P.hw.le hwt ht hb hS
    rfl hsizeS hres
  exact hfinal.trans (add_le_add_right (centering_defect_le d (by omega) P.hδ hs) _)

/-- The iteration factor carries the literal N/3 precision power, with its
extra geometric gain retained rather than dropped. -/
theorem iteration_factor {δ : ℝ} (hδ : 0 < δ) (N : ℕ) :
    (δ^((1:ℝ)/3)/2)^N = δ^((N:ℝ)/3)/(2:ℝ)^N := by
  rw [div_pow, SmoothStepPayments.step_power hδ]
  congr 2
  ring

end AcceleratedLogConcave.Numerics.SourceFiniteOutput
