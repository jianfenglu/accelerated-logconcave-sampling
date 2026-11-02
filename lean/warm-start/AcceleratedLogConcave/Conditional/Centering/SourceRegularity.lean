import AcceleratedLogConcave.Conditional.Transport.KernelRegularity
noncomputable section
namespace AcceleratedLogConcave.Conditional.Centering
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
local notation "E" => EuclideanSpace ℝ ι

omit [DecidableEq ι] in
theorem sourceKernel_contDiff_one {F : E → ℝ} (hF : ContDiff ℝ 2 F) {ell : ℝ}
    (hell : 0 ≤ ell)
    (hlo : ∀ z a, 0 ≤ fderiv ℝ (fderiv ℝ F) z a a)
    (hup : ∀ z a, fderiv ℝ (fderiv ℝ F) z a a ≤ ell * ‖a‖ ^ 2)
    (x : E) {r : ℝ} (hr : 0 < r) {b : ℝ} (hb : 0 ≤ b) (hb1 : b < 1)
    (hsmall : r ^ 2 * ell ≤ 1/2) :
    ContDiff ℝ 1 (transportedSteinKernelTranspose hF hell hlo hup x hr hb hb1) := by
  apply (Transport.contDiff_infty_transportedSteinKernelTranspose hF hell hlo hup x hr hb hb1 hsmall).of_le
  simp
end AcceleratedLogConcave.Conditional.Centering
