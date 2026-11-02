import AcceleratedLogConcave.Kinetic.Reheating.HeatEvolution.PhaseCurrentBound
import AcceleratedLogConcave.Kinetic.Reheating.HeatEvolution.InitialCorrector
import AcceleratedLogConcave.Kinetic.Reheating.HeatEvolution.CurrentIntegration

/-! The ordinary heat-current estimate on the actual compact joint phase core.
The final time is interior to the supplied smooth source window; the initial
operator is the genuine initial weighted Poisson inverse. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set InnerProductSpace
open scoped RealInnerProductSpace
namespace AcceleratedLogConcave.Kinetic.Reheating
open Analysis.Poisson
variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι

/-- Integrating the proved material derivative uses precisely the true ordinary
heat norm loss, including the original left endpoint. -/
theorem phaseHeatCurrent_increment_le {a b : ℝ} (F : ReferencePoissonFamily E a b)
    {f : E×E → ℝ} (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f)
    (hheat : ∀ t ∈ Icc a b, F.law t = heatedLaw (F.law a) (t-a))
    (hscale : ∀ t ∈ Ioo a b, F.scale t = -(1/2:ℝ))
    (τ : ℝ) (hτ : τ ∈ Ico a b) :
    let g := compactTestL2 ((F.law a).prod (stdGaussian E)) f hf.continuous hc
    |phaseHeatCurrent F hf hc hheat τ - phaseHeatCurrent F hf hc hheat a| ≤
      ((τ-a)/4)*‖g‖^2 + Real.sqrt ((τ-a)*(‖g‖^2-‖ordinaryHeatDensity (F.law a) (τ-a) g‖^2))*‖g‖ := by
  let g := compactTestL2 ((F.law a).prod (stdGaussian E)) f hf.continuous hc
  let Q := fun t => Kinetic.hiddenEmbedding (F.law a) (phaseHeatMovingCoreLp F hf hc hheat t)
  have hQ : Continuous Q := (Kinetic.hiddenEmbedding (F.law a)).continuous.comp
    (phaseHeatMovingCoreLp_continuous F hf hc hheat)
  have hJ : ContinuousOn (phaseHeatCurrent F hf hc hheat) (Icc a τ) := by
    have hA := (corrector_continuousOn_Ico F).mono
      (show Icc a τ ⊆ Ico a b from fun t ht => ⟨ht.1,ht.2.trans_lt hτ.2⟩)
    exact hQ.continuousOn.inner (hA.clm_apply hQ.continuousOn)
  have hn (t : ℝ) (ht : t ∈ Icc a τ) : 0 ≤ phaseHeatDissipation F hf hc hheat t := by
    rw [phaseHeatDissipation_eq_norm_sq F hf hc hheat t ⟨ht.1,ht.2.trans hτ.2.le⟩]
    positivity
  have henergy : (∫ t in a..τ, phaseHeatDissipation F hf hc hheat t) =
      ‖g‖^2 - ‖ordinaryHeatDensity (F.law a) (τ-a) g‖^2 := by
    rw [ordinaryHeatDensity_core_energy_identity_to F hf hc hheat hscale τ ⟨hτ.1,hτ.2.le⟩]
    apply intervalIntegral.integral_congr
    intro t ht
    have hti : t ∈ Icc a τ := by simpa only [uIcc_of_le hτ.1] using ht
    have ht' : t ∈ Icc a b := ⟨hti.1,hti.2.trans hτ.2.le⟩
    simpa only [projIcc_of_mem _ ht'] using
      phaseHeatDissipation_eq_gradient_energy F hf hc hheat t ht'
  exact current_increment_le_of_dissipation hτ.1 (norm_nonneg g)
    (phaseHeatCurrent F hf hc hheat) (phaseHeatDissipation F hf hc hheat) hJ
    (phaseHeatDissipation_continuous F hf hc hheat) hn henergy
    (fun t ht => phaseHeatCurrent_derivative_bound F hf hc hheat hscale t ⟨ht.1,ht.2.trans hτ.2⟩)

end AcceleratedLogConcave.Kinetic.Reheating
