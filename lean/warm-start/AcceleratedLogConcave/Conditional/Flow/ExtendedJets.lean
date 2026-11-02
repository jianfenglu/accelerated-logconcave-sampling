import AcceleratedLogConcave.Conditional.Flow.ExtendedState

/-! Actual material jets of the existing flow/Jacobian pair. The outer time
projection only totalizes the fields beyond the construction slab. Every
ordinary derivative below is strictly inside that slab. -/
noncomputable section
open Set Function
open scoped ContDiff Topology
namespace AcceleratedLogConcave.Conditional.PositiveVarianceFlowData
open Analysis.PositiveVarianceSlab Analysis.CoupledVelocityPolynomial Analysis.ODEJet

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (d : PositiveVarianceFlowData E)

def jet (k : ℕ) (t : ℝ) (y : E) : CoupledState E :=
  stateJet (openDomain (CoupledState E)) (conditionalCoupledVelocity d.F d.x d.r) k
    (d.time t, d.state (d.time t) y)

theorem continuous_jet (k : ℕ) : Continuous (uncurry (d.jet k)) := by
  have ht : Continuous d.time := continuous_subtype_val.comp continuous_projIcc
  have hs : Continuous (fun p : ℝ × E => d.state (d.time p.1) p.2) :=
    d.state_joint_continuous.comp
      (continuous_snd.prodMk ((continuous_projIcc (h := d.interval_le)).comp continuous_fst))
  have hj := (contDiffOn_stateJet (isOpen_openDomain (CoupledState E)).uniqueDiffOn
    (contDiffOn_conditionalCoupledVelocity d.hF d.hlo d.hhi d.x d.r) k).continuousOn
  exact hj.comp_continuous ((ht.comp continuous_fst).prodMk hs)
        (fun p => construction_subset d.hb0 d.hb1 (d.time_mem p.1))

/-- Uniform polynomial envelopes in the original spatial input. This uses
the derived linear bound for the actual pair, rather than a polynomial
Gronwall argument or a higher spatial derivative of the flow. -/
theorem exists_jet_polynomial_bound (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ t y, ‖d.jet k t y‖ ≤ C * (1 + ‖y‖) ^ N := by
  obtain ⟨D, hD, hstate⟩ := d.exists_state_linear_bound
  obtain ⟨C, hC, N, hjet⟩ := exists_polynomial_conditionalStateJet_bound d.hF d.hlo d.hhi
    d.hb0 d.hb1 d.x d.r k k 0 (by omega)
  refine ⟨C * (D + 2) ^ N, mul_nonneg hC (pow_nonneg (by positivity) _), N, ?_⟩
  intro t y
  have ht := d.time_mem t
  have hp := construction_subset d.hb0 d.hb1 ht
  have htn : ‖d.time t‖ ≤ 1 := by
    rw [Real.norm_eq_abs]
    exact abs_le.mpr ⟨hp.1.le, hp.2.le⟩
  have hpair : ‖(d.time t, d.state (d.time t) y)‖ ≤ (D + 1) * (1 + ‖y‖) := by
    rw [Prod.norm_def]
    apply max_le
    · nlinarith [norm_nonneg y, mul_nonneg hD (norm_nonneg y)]
    · exact (hstate (d.time t) ht y).trans
        (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) (by positivity))
  have hrad : 1 + ‖(d.time t, d.state (d.time t) y)‖ ≤ (D + 2) * (1 + ‖y‖) := by
    nlinarith [norm_nonneg y]
  have hj := hjet (d.time t, d.state (d.time t) y) ht
  rw [norm_iteratedFDerivWithin_zero] at hj
  calc
    ‖d.jet k t y‖ ≤ C * (1 + ‖(d.time t, d.state (d.time t) y)‖) ^ N := hj
    _ ≤ C * ((D + 2) * (1 + ‖y‖)) ^ N :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hrad N) hC
    _ = (C * (D + 2) ^ N) * (1 + ‖y‖) ^ N := by rw [mul_pow, mul_assoc]

theorem hasDerivAt_jet (k : ℕ) {t : ℝ}
    (ht : t ∈ Ioo (left d.b) (right d.b)) (y : E) :
    HasDerivAt (fun u => d.jet k u y) (d.jet (k + 1) t y) t := by
  have ht' : t ∈ Icc (left d.b) (right d.b) := ⟨ht.1.le, ht.2.le⟩
  have hh := hasDerivAt_stateJet_along (isOpen_openDomain (CoupledState E))
    (contDiffOn_conditionalCoupledVelocity d.hF d.hlo d.hhi d.x d.r)
    (construction_subset d.hb0 d.hb1 ht') (d.hasDerivAt_state ht y) k
  have he : (fun u => d.jet k u y) =ᶠ[𝓝 t]
      (fun u => stateJet (openDomain (CoupledState E))
        (conditionalCoupledVelocity d.F d.x d.r) k (u, d.state u y)) := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with u hu
    simp only [jet, d.time_eq ⟨hu.1.le, hu.2.le⟩]
  simpa only [jet, d.time_eq ht'] using hh.congr_of_eventuallyEq he

end AcceleratedLogConcave.Conditional.PositiveVarianceFlowData
