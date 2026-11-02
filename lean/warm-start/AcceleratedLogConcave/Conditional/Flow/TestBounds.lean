import AcceleratedLogConcave.Analysis.Poisson.ReferenceTransport

/-! Uniform bounds for the derivatives of compact space-time tests on a
compact interior time interval. The common support gives the required bound
even though the spatial domain is unbounded. -/

noncomputable section
open Set Filter Function
open scoped Topology

namespace AcceleratedLogConcave.Conditional

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedSpace ℝ E] in
/-- A continuous test with common compact spatial support is uniformly
bounded on a compact time interval. -/
theorem compactTest_norm_bound {c d : ℝ} {ψ : ℝ × E → ℝ}
    (hψ : Continuous ψ) {K : Set E} (hK : IsCompact K)
    (hz : ∀ t x, x ∉ K → ψ (t, x) = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Icc c d, ∀ x, ‖ψ (t, x)‖ ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod hK).exists_bound_of_continuousOn
    hψ.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun t ht x => ?_⟩
  by_cases hx : x ∈ K
  · exact (hC (t, x) ⟨ht, hx⟩).trans (le_max_left _ _)
  · rw [hz t x hx, norm_zero]
    exact le_max_right _ _

/-- A common compact spatial support bounds the full space-time derivative. -/
theorem compactTest_fderiv_bound {a b c d : ℝ} {ψ : ℝ × E → ℝ}
    (hψ : ∀ p, p.1 ∈ Ioo a b → ContDiffAt ℝ 1 ψ p)
    (hcd : Icc c d ⊆ Ioo a b) {K : Set E} (hK : IsCompact K)
    (hz : ∀ t x, x ∉ K → ψ (t, x) = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Icc c d, ∀ x, ‖fderiv ℝ ψ (t, x)‖ ≤ C := by
  have hψon : ContDiffOn ℝ 1 ψ (Ioo a b ×ˢ (univ : Set E)) :=
    fun p hp => (hψ p hp.1).contDiffWithinAt
  have hcont := hψon.continuousOn_fderiv_of_isOpen
    (isOpen_Ioo.prod isOpen_univ) le_rfl
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod hK).exists_bound_of_continuousOn
    (hcont.mono (fun p hp => ⟨hcd hp.1, mem_univ p.2⟩))
  refine ⟨max C 0, le_max_right _ _, fun t ht x => ?_⟩
  by_cases hx : x ∈ K
  · exact (hC (t, x) ⟨ht, hx⟩).trans (le_max_left _ _)
  · have he : ψ =ᶠ[𝓝 (t, x)] fun _ => (0 : ℝ) := by
      filter_upwards [(continuous_snd.tendsto (t, x))
        (hK.isClosed.isOpen_compl.mem_nhds hx)] with p hp
      exact hz p.1 p.2 hp
    have hd : HasFDerivAt ψ 0 (t, x) :=
      (hasFDerivAt_const (𝕜 := ℝ) (0 : ℝ) (t, x)).congr_of_eventuallyEq he
    rw [hd.fderiv, norm_zero]
    exact le_max_right _ _

end AcceleratedLogConcave.Conditional
