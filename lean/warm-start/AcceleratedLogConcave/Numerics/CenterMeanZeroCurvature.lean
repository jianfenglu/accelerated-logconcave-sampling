import AcceleratedLogConcave.Numerics.CenterMeanFirstReceiver
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-! Zero curvature is handled before any division by the physical scale L.
The actual common-seed center curve is constant, including its retained offset. -/
noncomputable section
open scoped ContDiff
namespace AcceleratedLogConcave.Numerics.MeanFlowLp
variable {D m : ℕ}

theorem centerMeanFirstLp_eq_zero_of_ell_zero (d : Data (Fin D) m)
    (he : (kernelData d).ell = 0) (t : ℝ) : centerMeanFirstLp d t = 0 := by
  have hn := norm_centerMeanFirstLp_sq_le d t
  simp only [CenterMeanSecondJetSource.firstEnergyScale,he,mul_zero,zero_mul,
    zero_pow (by decide : 2 ≠ 0)] at hn
  apply norm_eq_zero.mp
  nlinarith [norm_nonneg (centerMeanFirstLp d t)]

theorem centerMeanLp_constant_of_ell_zero (d : Data (Fin D) m)
    (he : (kernelData d).ell = 0) : centerMeanLp d = fun _ => centerMeanLp d 0 := by
  funext t
  exact is_const_of_deriv_eq_zero
    (fun u => (hasDerivAt_centerMeanLp d u).differentiableAt)
    (fun u => (hasDerivAt_centerMeanLp d u).deriv.trans
      (centerMeanFirstLp_eq_zero_of_ell_zero d he u)) t 0

theorem centerMeanLp_contDiff_of_ell_zero (d : Data (Fin D) m)
    (he : (kernelData d).ell = 0) : ContDiff ℝ ∞ (centerMeanLp d) := by
  rw [centerMeanLp_constant_of_ell_zero d he]
  exact contDiff_const

theorem iteratedDeriv_centerMeanLp_eq_zero_of_ell_zero (d : Data (Fin D) m)
    (he : (kernelData d).ell = 0) (k : ℕ) :
    iteratedDeriv (k+1) (centerMeanLp d) = 0 := by
  rw [centerMeanLp_constant_of_ell_zero d he]
  funext t
  simp [iteratedDeriv_const]

end AcceleratedLogConcave.Numerics.MeanFlowLp
