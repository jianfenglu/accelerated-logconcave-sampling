import AcceleratedLogConcave.Root.CoolingSourceLocalKL
import AcceleratedLogConcave.Root.CoolingDyadicReference
import AcceleratedLogConcave.Schedule.DyadicReturnedLaw

/-! The cooling local-KL supplier at every literal public dyadic variance.
The implemented family below is the actual original-gradient program. -/
noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory InformationTheory
open scoped NNReal ENNReal
namespace AcceleratedLogConcave.Root.CoolingSourceDyadicKL
open Oracle Numerics Numerics.AffineGraph TapeLowering SourceExecutableTables

/-- The two existing descriptions have the same physical variance. -/
theorem variance_eq (h : ℝ) (j : ℕ) :
    Schedule.Dyadic.variance (Schedule.Dyadic.sourceVariance h) j = CoolingDyadicReference.variance h j := by
  apply NNReal.coe_injective
  change (2*h^2)/↑((2:ℝ≥0)^j) = 2*h^2/(2:ℝ)^j
  rw [NNReal.coe_pow]
  rfl

variable (P : SourceSchedule) (hK : 10≤P.K) (hc : 0<P.csch) (hsmall : P.csch<1/160)
  (hC : 8≤P.Csch) (hy : MeanSourceScalarAbsorption.threshold P≤P.y)
local notation "hyPrivate" => MeanSourceScalarAbsorption.private_threshold P hc (by linarith : P.csch≤1) (by linarith : 1≤P.Csch) hy
local notation "baseHy" => PrivateSourceScalarAbsorption.base_threshold P hc (by linarith : P.csch≤1) (by linarith : 1≤P.Csch) hyPrivate
local notation "hR" => CubicSchedulePayments.radius_guard P hK hc hsmall hC baseHy
local notation "Q" => CoolingPrescribedPayments.setup P hR hc hsmall
variable {d : ℕ} (V : Point d → ℝ)

/-- Literal native public cooling at each dyadic width and precision K. -/
def implemented : ℕ → Kernel (Point d) (Point d) := fun j =>
  CoolingExecutable.originalGradientKernel Q P.delta
    (Schedule.Dyadic.variance (Schedule.Dyadic.sourceVariance P.delta) j) P.K V

variable (hV : ContDiff ℝ 2 V) {m : ℝ} (hm : 0<m)
  (hlo : ∀ z w,m*‖w‖^2≤fderiv ℝ (fderiv ℝ V) z w w)
  (hup : ∀ z w,fderiv ℝ (fderiv ℝ V) z w w≤‖w‖^2)

include hV in
theorem implemented_markov (j : ℕ) : IsMarkovKernel (implemented P hK hc hsmall hC hy V j) :=
  CoolingExecutable.originalGradientKernel_markov Q P.delta _ P.K V hV

include hup

/-- Original-data local KL, without any supplied implementation accuracy. -/
theorem averaged_KL_le (j : ℕ) :
    let hI := Gibbs.integrable_exp_neg_of_hessian_lower hV hm hlo
    (∫⁻ x,klDiv (Schedule.Dyadic.coolingKernel V hV.continuous.measurable hI
      (Schedule.Dyadic.sourceVariance P.delta) j x)
      (implemented P hK hc hsmall hC hy V j x)
      ∂Schedule.Dyadic.cooledLaw V (Schedule.Dyadic.sourceVariance P.delta) j)≤
      ENNReal.ofReal (180*(d:ℝ)*P.delta^(2*P.K)) := by
  dsimp only
  have hv := Schedule.Dyadic.variance_pos (Schedule.Dyadic.sourceVariance_pos P.delta_pos) j
  have hu : ((Schedule.Dyadic.variance (Schedule.Dyadic.sourceVariance P.delta) j):ℝ)≤2*P.delta^2 := by
    rw [variance_eq]
    exact CoolingDyadicReference.variance_le P.delta j
  exact CoolingSourceLocalKL.averaged_KL_le P hK hc hsmall hC hy _ hv hu hV hm hlo hup

/-- The exact supplier expected by the existing source returned-law theorem. -/
theorem source_KL_le (j : ℕ) :
    let hI := Gibbs.integrable_exp_neg_of_hessian_lower hV hm hlo
    (∫⁻ x,klDiv (Schedule.Dyadic.coolingKernel V hV.continuous.measurable hI
      (Schedule.Dyadic.sourceVariance P.delta) j x)
      (implemented P hK hc hsmall hC hy V j x)
      ∂Schedule.Dyadic.cooledLaw V (Schedule.Dyadic.sourceVariance P.delta) j)≤
      ENNReal.ofReal (180*(d:ℝ)*P.delta^(2*P.K-2)) := by
  have hd := PrivateSourceScalarAbsorption.delta_le_hundredth P hK hc
    (by linarith : P.csch≤1) (by linarith : 1≤P.Csch) hyPrivate
  refine (averaged_KL_le P hK hc hsmall hC hy V hV hm hlo hup j).trans ?_
  apply ENNReal.ofReal_le_ofReal
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_of_le_one P.delta_pos.le (hd.trans (by norm_num)) (Nat.sub_le _ _)) (by positivity)
end AcceleratedLogConcave.Root.CoolingSourceDyadicKL
