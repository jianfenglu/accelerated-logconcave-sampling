import AcceleratedLogConcave.Numerics.MeanFlowLp

noncomputable section
open scoped ContDiff
namespace AcceleratedLogConcave.Numerics.MeanFlowLp
variable {D m : ℕ}

theorem velocityLp_eq_zero_of_ell_zero (d : Data (Fin D) m) (he : (kernelData d).ell = 0) :
    velocityLp d = 0 := by
  funext t
  have hn := CenteringFlowLp.norm_kernelLp_le (kernelData d) (d.sigma/2) (half_pos d.hsigma) t
  have hz : CenteringFlowLp.kernelLp (kernelData d) (d.sigma/2) (half_pos d.hsigma) t = 0 := by
    apply norm_eq_zero.mp
    apply le_antisymm _ (norm_nonneg _)
    simpa [CenteringFlowLp.alpha,he] using hn
  simp [velocityLp_eq,hz]

theorem velocityLp_contDiff_of_ell_zero (d : Data (Fin D) m) (he : (kernelData d).ell = 0) :
    ContDiff ℝ ∞ (velocityLp d) := by
  rw [velocityLp_eq_zero_of_ell_zero d he]
  exact contDiff_const

theorem iteratedDeriv_velocityLp_eq_zero_of_ell_zero (d : Data (Fin D) m)
    (he : (kernelData d).ell = 0) (k : ℕ) : iteratedDeriv k (velocityLp d) = 0 := by
  rw [velocityLp_eq_zero_of_ell_zero d he]
  exact funext fun t => iteratedDeriv_const_zero

end AcceleratedLogConcave.Numerics.MeanFlowLp
