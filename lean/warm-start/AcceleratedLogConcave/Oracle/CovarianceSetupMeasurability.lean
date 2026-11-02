import Mathlib.Analysis.Matrix.MeasurableSpace
import AcceleratedLogConcave.Oracle.CovarianceSetup
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Measurable

/-! Joint measurability of the literal covariance-root coefficients used by
the recursive compiler. No positivity premise is needed for measurability. -/
noncomputable section
set_option autoImplicit false
namespace AcceleratedLogConcave.Oracle.CovarianceSetup
open scoped MatrixOrder Matrix.Norms.L2Operator
variable {X : Type*} [MeasurableSpace X] {n N : ℕ}

theorem measurable_sigma (rho rowBound : X → ℝ) (hr : Measurable rho)
    (hb : Measurable rowBound) : Measurable (fun x => sigma n (rho x) (rowBound x)) := by
  unfold sigma
  fun_prop

theorem measurable_residualCovariance (A : X → Mat n) (rho rowBound : X → ℝ)
    (hA : Measurable A) (hr : Measurable rho) (hb : Measurable rowBound) :
    Measurable (fun x => residualCovariance (A x) (rho x) (rowBound x)) := by
  unfold residualCovariance
  have hs := measurable_sigma (n := n) rho rowBound hr hb
  fun_prop

theorem measurable_residualRoot (A : X → Mat n) (rho rowBound : X → ℝ)
    (hA : Measurable A) (hr : Measurable rho) (hb : Measurable rowBound) :
    Measurable (fun x => residualRoot (A x) (rho x) (rowBound x)) := by
  exact CFC.measurable_sqrt.comp (measurable_residualCovariance A rho rowBound hA hr hb)

theorem measurable_scaledShift (rho radius : X → ℝ) (v : X → Fin N → ℝ)
    (hr : Measurable rho) (hs : Measurable radius) (hv : Measurable v) :
    Measurable (fun x => scaledShift (rho x) (radius x) (v x)) := by
  unfold scaledShift
  fun_prop

theorem measurable_childCovariance (rho radius : X → ℝ) (v : X → Fin N → ℝ)
    (hr : Measurable rho) (hs : Measurable radius) (hv : Measurable v) :
    Measurable (fun x => childCovariance (rho x) (radius x) (v x)) := by
  unfold childCovariance
  have h := measurable_scaledShift rho radius v hr hs hv
  fun_prop

theorem measurable_childRoot (rho radius : X → ℝ) (v : X → Fin N → ℝ)
    (hr : Measurable rho) (hs : Measurable radius) (hv : Measurable v) :
    Measurable (fun x => childRoot (rho x) (radius x) (v x)) := by
  exact CFC.measurable_sqrt.comp (measurable_childCovariance rho radius v hr hs hv)

end AcceleratedLogConcave.Oracle.CovarianceSetup
