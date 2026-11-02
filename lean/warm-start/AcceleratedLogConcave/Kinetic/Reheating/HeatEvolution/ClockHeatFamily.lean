import AcceleratedLogConcave.Kinetic.Reheating.HeatEvolution.VarianceFamily

/-! The genuine forward heat family for each reverse-clock collision. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set InnerProductSpace
namespace AcceleratedLogConcave.Kinetic.Reheating
open Analysis.Poisson
variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι

/-- Reheat from variance A(1-rho²) toward A inside a strictly larger envelope. -/
def clockReheatFamily {μ : Measure E} {A R : ℝ}
    (H : VarianceHeatFamily μ (3*A/4) R) (hA : 0 < A) (hR : A < R)
    (ρ : ℝ) (hρ : ρ ∈ Icc (0:ℝ) (1/2)) :
    ReferencePoissonFamily E 0 (R-A*(1-ρ^2)) :=
  H.shiftedFamily (A*(1-ρ^2)) (VarianceHeatFamily.clock_segment hA hR hρ).1

theorem clockReheatFamily_heat {μ : Measure E} [IsProbabilityMeasure μ] {A R : ℝ}
    (H : VarianceHeatFamily μ (3*A/4) R) (hA : 0 < A) (hR : A < R)
    (ρ : ℝ) (hρ : ρ ∈ Icc (0:ℝ) (1/2))
    (u : ℝ) (hu : u ∈ Icc 0 (R-A*(1-ρ^2))) :
    (clockReheatFamily H hA hR ρ hρ).law u =
      heatedLaw ((clockReheatFamily H hA hR ρ hρ).law 0) (u-0) :=
  H.shiftedFamily_heat _ (VarianceHeatFamily.clock_segment hA hR hρ).1
    (VarianceHeatFamily.clock_segment hA hR hρ).2.1 u hu

theorem clockReheatFamily_scale {μ : Measure E} {A R : ℝ}
    (H : VarianceHeatFamily μ (3*A/4) R) (hA : 0 < A) (hR : A < R)
    (ρ : ℝ) (hρ : ρ ∈ Icc (0:ℝ) (1/2))
    (u : ℝ) (hu : u ∈ Ioo 0 (R-A*(1-ρ^2))) :
    (clockReheatFamily H hA hR ρ hρ).scale u = -(1/2:ℝ) :=
  H.shiftedFamily_scale _ (VarianceHeatFamily.clock_segment hA hR hρ).1 u (Ioo_subset_Icc_self hu)

/-- The source endpoint is physical even at the zero clock; it always lies
strictly below the upper endpoint of the common regularity envelope. -/
theorem clockReheatFamily_endpoint {A R ρ : ℝ} (hA : 0 < A) (hR : A < R)
    (hρ : ρ ∈ Icc (0:ℝ) (1/2)) : A*ρ^2 ∈ Ico 0 (R-A*(1-ρ^2)) :=
  (VarianceHeatFamily.clock_segment hA hR hρ).2.2.1

theorem clockReheatFamily_initial_law {μ : Measure E} {A R : ℝ}
    (H : VarianceHeatFamily μ (3*A/4) R) (hA : 0 < A) (hR : A < R)
    (ρ : ℝ) (hρ : ρ ∈ Icc (0:ℝ) (1/2)) :
    (clockReheatFamily H hA hR ρ hρ).law 0 = H.source.law (A*(1-ρ^2)) := by
  simpa only [clockReheatFamily, add_zero] using H.shiftedFamily_law _
    (VarianceHeatFamily.clock_segment hA hR hρ).1 0
    ⟨le_rfl,sub_nonneg.mpr (VarianceHeatFamily.clock_segment hA hR hρ).1.2⟩

theorem clockReheatFamily_final_law {μ : Measure E} {A R : ℝ}
    (H : VarianceHeatFamily μ (3*A/4) R) (hA : 0 < A) (hR : A < R)
    (ρ : ℝ) (hρ : ρ ∈ Icc (0:ℝ) (1/2)) :
    (clockReheatFamily H hA hR ρ hρ).law (A*ρ^2) = H.source.law A := by
  have he := clockReheatFamily_endpoint hA hR hρ
  simpa only [clockReheatFamily, (VarianceHeatFamily.clock_segment hA hR hρ).2.2.2] using H.shiftedFamily_law _
    (VarianceHeatFamily.clock_segment hA hR hρ).1 (A*ρ^2) ⟨he.1,he.2.le⟩

theorem clockReheatFamily_initial_potential {μ : Measure E} {A R : ℝ}
    (H : VarianceHeatFamily μ (3*A/4) R) (hA : 0 < A) (hR : A < R)
    (ρ : ℝ) (hρ : ρ ∈ Icc (0:ℝ) (1/2)) :
    (clockReheatFamily H hA hR ρ hρ).potential 0 = H.source.potential (A*(1-ρ^2)) := by
  simpa only [clockReheatFamily, add_zero] using H.shiftedFamily_potential _
    (VarianceHeatFamily.clock_segment hA hR hρ).1 0
    ⟨le_rfl,sub_nonneg.mpr (VarianceHeatFamily.clock_segment hA hR hρ).1.2⟩

theorem clockReheatFamily_final_potential {μ : Measure E} {A R : ℝ}
    (H : VarianceHeatFamily μ (3*A/4) R) (hA : 0 < A) (hR : A < R)
    (ρ : ℝ) (hρ : ρ ∈ Icc (0:ℝ) (1/2)) :
    (clockReheatFamily H hA hR ρ hρ).potential (A*ρ^2) = H.source.potential A := by
  have he := clockReheatFamily_endpoint hA hR hρ
  simpa only [clockReheatFamily, (VarianceHeatFamily.clock_segment hA hR hρ).2.2.2] using H.shiftedFamily_potential _
    (VarianceHeatFamily.clock_segment hA hR hρ).1 (A*ρ^2) ⟨he.1,he.2.le⟩

end AcceleratedLogConcave.Kinetic.Reheating
