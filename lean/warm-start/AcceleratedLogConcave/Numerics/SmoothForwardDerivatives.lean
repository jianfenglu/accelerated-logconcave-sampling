import AcceleratedLogConcave.Numerics.SmoothForwardReplacement
import AcceleratedLogConcave.Analysis.FiniteDerivativeLadder

/-! Exact fixed-angle forward time derivatives on the enlarged open slab.
The L2 derivative ladder uses the actual common seed and the published
dominating envelopes. No angle derivative or quantitative bound is assumed. -/
noncomputable section
open Set MeasureTheory
open scoped ContDiff Topology
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

namespace AcceleratedLogConcave.Numerics.MeanResidualBridge
open MeanFlowLp AffineGraph Analysis.PositiveVarianceSlab
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ}
variable (d : MeanFlowLp.Data ι m) (j : Fin m) (ρ : d.G.Kernel) (z : ℝ)

/-- Consecutive derivatives of the literal shared-seed L2 jets. -/
theorem hasDerivAt_forwardJetLp (k : ℕ) {t : ℝ}
    (ht : t ∈ Ioo (left (backwardEnd d.G.R)) (right (backwardEnd d.G.R))) :
    HasDerivAt (forwardJetLp d j ρ z k) (forwardJetLp d j ρ z (k+1) t) t := by
  obtain ⟨B,hB,hbound⟩ := exists_forwardJet_envelope d j ρ z (k+1)
  exact Analysis.DominatedLp.hasDerivAt_toLp_of_dominated
    (forwardJet d j ρ z k) (forwardJet d j ρ z (k+1))
    (continuous_forwardJet d j ρ z (k+1)) B hB hbound
    (forwardJet_memLp d j ρ z k) (forwardJet_memLp d j ρ z (k+1))
    (fun _ ht' w => hasDerivAt_forwardJet d j ρ z k ht' w) ht

theorem iteratedDeriv_forwardJetLp (k n : ℕ) {t : ℝ}
    (ht : t ∈ Ioo (left (backwardEnd d.G.R)) (right (backwardEnd d.G.R))) :
    iteratedDeriv n (forwardJetLp d j ρ z k) t = forwardJetLp d j ρ z (k+n) t := by
  simpa only [Nat.add_zero, Nat.add_assoc] using
    Analysis.iteratedDeriv_eq_of_finite_ladder n (fun i => forwardJetLp d j ρ z (k+i))
      isOpen_Ioo (fun i _ _ ht' => by
        simpa only [Nat.add_assoc] using hasDerivAt_forwardJetLp d j ρ z (k+i) ht') ht

theorem iteratedDeriv_smoothForward (k : ℕ) {t : ℝ}
    (ht : t ∈ Ioo (left (backwardEnd d.G.R)) (right (backwardEnd d.G.R))) :
    iteratedDeriv k (smoothForward d j ρ z) t = forwardJetLp d j ρ z k t := by
  unfold smoothForward
  simpa only [Nat.zero_add] using iteratedDeriv_forwardJetLp d j ρ z 0 k ht

/-- Mean order k is state-jet order k+1, with the physical radius d.r. -/
theorem iteratedDeriv_smoothForwardMean (k : ℕ) {t : ℝ}
    (ht : t ∈ Ioo (left (backwardEnd d.G.R)) (right (backwardEnd d.G.R))) :
    iteratedDeriv k (smoothForwardMean d j ρ z) t =
      (-d.r)⁻¹ • forwardJetLp d j ρ z (k+1) t := by
  unfold smoothForwardMean
  exact Analysis.iteratedDeriv_eq_of_finite_ladder k
    (fun i t => (-d.r)⁻¹ • forwardJetLp d j ρ z (i+1) t)
    isOpen_Ioo (fun i _ _ ht' =>
      (hasDerivAt_forwardJetLp d j ρ z (i+1) ht').const_smul (-d.r)⁻¹) ht

/-- Transfer through the published open-neighborhood receiver identity. -/
theorem iteratedDeriv_replacement_forwardMean (U : H d → ℝ → H d)
    (hu : PrimitiveSpec (primitiveData d) (seedMeasure d) U) (k : ℕ) {t : ℝ}
    (ht : t ∈ Ioo (left (backwardEnd d.G.R)) (right (backwardEnd d.G.R))) :
    iteratedDeriv k ((curvesWithForward d).forwardMean d.G U 0 d.r j ρ z) t =
      (-d.r)⁻¹ • forwardJetLp d j ρ z (k+1) t := by
  have he : (curvesWithForward d).forwardMean d.G U 0 d.r j ρ z =ᶠ[𝓝 t]
      smoothForwardMean d j ρ z := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with u hu'
    exact smoothForwardReplacement_forwardMean_eq_smooth d U hu j ρ z hu'
  exact (he.iteratedDeriv_eq k).trans (iteratedDeriv_smoothForwardMean d j ρ z k ht)

theorem iteratedDeriv_replacement_forwardMean_source (U : H d → ℝ → H d)
    (hu : PrimitiveSpec (primitiveData d) (seedMeasure d) U) (k : ℕ) {t : ℝ}
    (ht : t ∈ Icc 0 (backwardEnd d.G.R)) :
    iteratedDeriv k ((curvesWithForward d).forwardMean d.G U 0 d.r j ρ z) t =
      (-d.r)⁻¹ • forwardJetLp d j ρ z (k+1) t :=
  iteratedDeriv_replacement_forwardMean d j ρ z U hu k
    (source_subset d.G.backwardEnd_pos.le d.G.backwardEnd_lt_one ht)

end AcceleratedLogConcave.Numerics.MeanResidualBridge
