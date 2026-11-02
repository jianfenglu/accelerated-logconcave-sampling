import AcceleratedLogConcave.Conditional.Flow.ExtendedLp
import AcceleratedLogConcave.Analysis.FiniteDerivativeLadder

/-! Exact canonical L² derivatives of the actual enlarged-slab momentum
jets. This identifies the objects to which quantitative estimates must apply;
it does not replace those estimates with existential polynomial envelopes. -/
noncomputable section
open Set MeasureTheory
open scoped Topology
set_option autoImplicit false
namespace AcceleratedLogConcave.Conditional.PositiveVarianceFlowData
open Analysis.PositiveVarianceSlab
variable {ι : Type*} [Fintype ι]
variable (d : PositiveVarianceFlowData (EuclideanSpace ℝ ι))

theorem hasDerivAt_momentumJetLp (k : ℕ) {t : ℝ}
    (ht : t ∈ Ioo (left d.b) (right d.b)) :
    HasDerivAt (d.momentumJetLp k) (d.momentumJetLp (k + 1) t) t := by
  obtain ⟨B, hB, hb⟩ := d.exists_momentumJet_envelope (k + 1)
  exact Analysis.DominatedLp.hasDerivAt_toLp_of_dominated
    (d.momentumJet k) (d.momentumJet (k + 1)) (d.continuous_momentumJet (k + 1))
    B hB hb (d.momentumJet_memLp k) (d.momentumJet_memLp (k + 1))
    (fun u hu z => d.hasDerivAt_momentumJet k hu z) ht

theorem iteratedDeriv_momentumJetLp (n k : ℕ) {t : ℝ}
    (ht : t ∈ Ioo (left d.b) (right d.b)) :
    iteratedDeriv n (d.momentumJetLp k) t = d.momentumJetLp (k + n) t := by
  have h := Analysis.iteratedDeriv_eq_of_finite_ladder n
    (fun q => d.momentumJetLp (k + q)) isOpen_Ioo
    (fun q _ u hu => by simpa only [Nat.add_assoc] using d.hasDerivAt_momentumJetLp (k + q) hu) ht
  simpa only [Nat.add_zero] using h

theorem hasDerivAt_kernelLp (t : ℝ) (ht : t ∈ Ioo (left d.b) (right d.b)) :
    HasDerivAt d.kernelLp (d.momentumJetLp 1 t) t :=
  (d.hasDerivAt_momentumJetLp 0 ht).sub_const (d.momentumJetLp 0 d.b)

/-- Positive orders remove the subtracted reference value. Only derivatives
through the requested order are used by the finite ladder. -/
theorem iteratedDeriv_kernelLp_succ (n : ℕ) {t : ℝ}
    (ht : t ∈ Ioo (left d.b) (right d.b)) :
    iteratedDeriv (n + 1) d.kernelLp t = d.momentumJetLp (n + 1) t := by
  rw [iteratedDeriv_succ']
  have he : deriv d.kernelLp =ᶠ[𝓝 t] d.momentumJetLp 1 := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with u hu
    exact (d.hasDerivAt_kernelLp u hu).deriv
  exact ((he.iteratedDeriv n).eq_of_nhds).trans
    (by simpa only [Nat.add_comm] using d.iteratedDeriv_momentumJetLp n 1 ht)

end AcceleratedLogConcave.Conditional.PositiveVarianceFlowData
