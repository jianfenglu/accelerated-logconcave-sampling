import AcceleratedLogConcave.Kinetic.Reheating.HeatEvolution.PhaseCurrent
import AcceleratedLogConcave.Kinetic.Reheating.HeatEvolution.PhaseEndpoint
import AcceleratedLogConcave.Kinetic.Reheating.DenseExtension

/-! The ordinary heat-current inequality for every actual visible L2 input.
The compact-core estimate is proved from the physical heat PDE and weighted
Poisson calculus; continuity of the actual norm defect extends it to all inputs. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set InnerProductSpace
open scoped RealInnerProductSpace
namespace AcceleratedLogConcave.Kinetic.Reheating
open Analysis.Poisson
variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι

/-- Actual ordinary heat current, including arbitrary position-momentum dependence.
No current bound or dissipation estimate is assumed. -/
theorem ordinaryHeatDensity_current_le {a b : ℝ} (F : ReferencePoissonFamily E a b)
    (hheat : ∀ t ∈ Icc a b, F.law t = heatedLaw (F.law a) (t-a))
    (hscale : ∀ t ∈ Ioo a b, F.scale t = -(1/2:ℝ))
    (t : ℝ) (ht : t ∈ Ico a b)
    (g : Lp ℝ 2 ((F.law a).prod (stdGaussian E))) :
    let ht' : t ∈ Icc a b := ⟨ht.1,ht.2.le⟩
    let v := ordinaryHeatDensity (F.law a) (t-a) g
    let A := visibleCorrector (heatedLaw (F.law a) (t-a)) (F.potential t) (F.potential_C2 t)
      (F.integrable t ht') ((hheat t ht').symm.trans (F.gibbs_law t ht'))
      (F.lower t) 1 (F.lower_pos t ht') (F.hessian_lower t ht')
      (by simpa only [one_mul] using F.hessian_upper t ht')
    |inner ℝ (A v) v - inner ℝ (phaseVisibleCorrector F a ⟨le_rfl,F.ordered⟩ g) g| ≤
      ((t-a)/4)*‖g‖^2 + Real.sqrt ((t-a)*(‖g‖^2-‖v‖^2))*‖g‖ := by
  dsimp only
  apply heat_current_le_of_dense (ordinaryHeatDensity (F.law a) (t-a))
    (phaseVisibleCorrector F a ⟨le_rfl,F.ordered⟩) _ (t-a) _
    (compactC2_dense ((F.law a).prod (stdGaussian E))) _ g
  rintro v ⟨φ,he,hc,hφ⟩
  have hv : v = compactTestL2 ((F.law a).prod (stdGaussian E)) φ hφ.continuous hc :=
    Lp.ext (he.trans (compactTest_memLp ((F.law a).prod (stdGaussian E)) φ hφ.continuous hc).coeFn_toLp.symm)
  subst v
  have hh := phaseHeatCurrent_increment_le F hφ hc hheat hscale t ht
  rw [phaseHeatCurrent_eq_ordinaryHeatDensity_Ico F hφ hc hheat t ht,
    phaseHeatCurrent_initial F hφ hc hheat] at hh
  exact hh

end AcceleratedLogConcave.Kinetic.Reheating
