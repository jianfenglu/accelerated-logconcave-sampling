import AcceleratedLogConcave.Numerics.SmoothConditionalReplacement
import AcceleratedLogConcave.Analysis.FiniteDerivativeLadder

/-!
Exact ordinary conditional time derivatives on the enlarged open slab.
The consecutive L² derivatives come from dominated differentiation of the
actual common-seed jets. No quantitative cell budget is asserted here.
-/

noncomputable section
open Set MeasureTheory
open scoped ContDiff Topology
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

namespace AcceleratedLogConcave.Numerics.MeanResidualBridge
open MeanFlowLp AffineGraph Analysis.PositiveVarianceSlab
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ}
variable (d : MeanFlowLp.Data ι m) (j : Fin m) (ρ : d.G.Kernel)

/-- Actual consecutive L² derivatives, from the pointwise ladder and its
common-seed L² envelopes, rather than merely qualitative smoothness. -/
theorem hasDerivAt_conditionalJetLp (k : ℕ) {t : ℝ}
    (ht : t ∈ Ioo (left conditionalEnd) (right conditionalEnd)) :
    HasDerivAt (conditionalJetLp d j ρ k) (conditionalJetLp d j ρ (k+1) t) t := by
  obtain ⟨B,hB,hbound⟩ := exists_conditionalJet_envelope d j ρ (k+1)
  exact Analysis.DominatedLp.hasDerivAt_toLp_of_dominated
    (conditionalJet d j ρ k) (conditionalJet d j ρ (k+1))
    (continuous_conditionalJet d j ρ (k+1)) B hB hbound
    (conditionalJet_memLp d j ρ k) (conditionalJet_memLp d j ρ (k+1))
    (fun _ ht' w => hasDerivAt_conditionalJet d j ρ k ht' w) ht

theorem iteratedDeriv_conditionalJetLp (k n : ℕ) {t : ℝ}
    (ht : t ∈ Ioo (left conditionalEnd) (right conditionalEnd)) :
    iteratedDeriv n (conditionalJetLp d j ρ k) t = conditionalJetLp d j ρ (k+n) t := by
  simpa only [Nat.add_zero, Nat.add_assoc] using
    Analysis.iteratedDeriv_eq_of_finite_ladder n (fun i => conditionalJetLp d j ρ (k+i))
      isOpen_Ioo (fun i _ _ ht' => by
        simpa only [Nat.add_assoc] using hasDerivAt_conditionalJetLp d j ρ (k+i) ht') ht

theorem iteratedDeriv_smoothConditional (k : ℕ) {t : ℝ}
    (ht : t ∈ Ioo (left conditionalEnd) (right conditionalEnd)) :
    iteratedDeriv k (smoothConditional d j ρ) t = conditionalJetLp d j ρ k t := by
  unfold smoothConditional
  simpa only [Nat.zero_add] using iteratedDeriv_conditionalJetLp d j ρ 0 k ht

/-- The mean's k-th derivative uses the (k+1)-st state jet and the inverse
positive local radius. -/
theorem iteratedDeriv_smoothConditionalMean (k : ℕ) {t : ℝ}
    (ht : t ∈ Ioo (left conditionalEnd) (right conditionalEnd)) :
    iteratedDeriv k (smoothConditionalMean d j ρ) t =
      (-(conditionalData d ρ).r)⁻¹ • conditionalJetLp d j ρ (k+1) t := by
  unfold smoothConditionalMean
  exact Analysis.iteratedDeriv_eq_of_finite_ladder k
    (fun i t => (-(conditionalData d ρ).r)⁻¹ • conditionalJetLp d j ρ (i+1) t)
    isOpen_Ioo (fun i _ _ ht' => by
      exact (hasDerivAt_conditionalJetLp d j ρ (i+1) ht').const_smul
        (-(conditionalData d ρ).r)⁻¹) ht

/-- Open-slab equality transfers ordinary derivatives of the literal receiver. -/
theorem iteratedDeriv_replacement_conditionalMean (U : H d → ℝ → H d)
    (hu : PrimitiveSpec (primitiveData d) (seedMeasure d) U) (k : ℕ) {t : ℝ}
    (ht : t ∈ Ioo (left conditionalEnd) (right conditionalEnd)) :
    iteratedDeriv k ((curvesWithConditional d).conditionalMean d.G U 0 d.r j ρ) t =
      (-(conditionalData d ρ).r)⁻¹ • conditionalJetLp d j ρ (k+1) t := by
  have he : (curvesWithConditional d).conditionalMean d.G U 0 d.r j ρ =ᶠ[𝓝 t]
      smoothConditionalMean d j ρ := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with u hu'
    exact replacement_conditionalMean_eq_smooth d U hu j ρ hu'
  exact (he.iteratedDeriv_eq k).trans (iteratedDeriv_smoothConditionalMean d j ρ k ht)

theorem iteratedDeriv_replacement_conditionalMean_source (U : H d → ℝ → H d)
    (hu : PrimitiveSpec (primitiveData d) (seedMeasure d) U) (k : ℕ) {t : ℝ}
    (ht : t ∈ Icc 0 conditionalEnd) :
    iteratedDeriv k ((curvesWithConditional d).conditionalMean d.G U 0 d.r j ρ) t =
      (-(conditionalData d ρ).r)⁻¹ • conditionalJetLp d j ρ (k+1) t :=
  iteratedDeriv_replacement_conditionalMean d j ρ U hu k
    (source_subset conditionalEnd_pos.le conditionalEnd_lt_one ht)

end AcceleratedLogConcave.Numerics.MeanResidualBridge
