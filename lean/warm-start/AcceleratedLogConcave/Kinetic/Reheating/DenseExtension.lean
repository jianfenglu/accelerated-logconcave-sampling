import AcceleratedLogConcave.Kinetic.Mixing.Energy
import Mathlib.Analysis.Normed.Lp.SmoothApprox

/-! Extend endpoint current estimates from a dense smooth core. This uses only
bounded endpoint operators and continuity of their true squared-norm defect;
it does not assert strong time differentiability or dissipation equality for
arbitrary L2 input. -/
noncomputable section
open InnerProductSpace Set
open MeasureTheory
open scoped RealInnerProductSpace ContDiff
namespace AcceleratedLogConcave.Kinetic.Reheating
variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [NormedAddCommGroup K] [InnerProductSpace ℝ K]

/-- The concrete compact C2 scalar representatives are dense for every finite
Borel measure on a finite-dimensional normed space, including visible phase. -/
theorem compactC2_dense {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [FiniteDimensional ℝ X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] :
    Dense {f : Lp ℝ 2 μ | ∃ φ : X → ℝ,
      f =ᵐ[μ] φ ∧ HasCompactSupport φ ∧ ContDiff ℝ 2 φ} := by
  have hd : Dense {f : Lp ℝ 2 μ | ∃ φ : X → ℝ,
      f =ᵐ[μ] φ ∧ HasCompactSupport φ ∧ ContDiff ℝ ∞ φ} :=
    Lp.dense_hasCompactSupport_contDiff (by norm_num)
  apply hd.mono
  rintro f ⟨φ, he, hc, hφ⟩
  exact ⟨φ, he, hc, hφ.of_le (by norm_num)⟩

/-- The actual heat norm defect is continuous on the entire input space. -/
theorem normDefect_continuous (T : H →L[ℝ] K) :
    Continuous (fun f => ‖f‖^2 - ‖T f‖^2) :=
  (continuous_norm.pow 2).sub (T.continuous.norm.pow 2)

/-- The ordinary heat-current inequality extends from any genuine dense core.
Its defect is computed from the bounded physical heat operator itself. -/
theorem heat_current_le_of_dense (T : H →L[ℝ] K)
    (A₀ : H →L[ℝ] H) (Aₜ : K →L[ℝ] K) (t : ℝ)
    (S : Set H) (hS : Dense S)
    (hcore : ∀ f ∈ S,
      |inner ℝ (Aₜ (T f)) (T f) - inner ℝ (A₀ f) f| ≤
        (t/4)*‖f‖^2 + Real.sqrt (t*(‖f‖^2-‖T f‖^2))*‖f‖) (f : H) :
    |inner ℝ (Aₜ (T f)) (T f) - inner ℝ (A₀ f) f| ≤
      (t/4)*‖f‖^2 + Real.sqrt (t*(‖f‖^2-‖T f‖^2))*‖f‖ := by
  refine hS.induction hcore ?_ f
  apply isClosed_le
  · exact (((Aₜ.continuous.comp T.continuous).inner T.continuous).sub
      (A₀.continuous.inner continuous_id)).abs
  · exact (continuous_const.mul (continuous_norm.pow 2)).add
      ((Real.continuous_sqrt.comp (continuous_const.mul (normDefect_continuous T))).mul
        continuous_norm)

/-- Likewise for the final bounded correlated reheating energy estimate. -/
theorem reheating_energy_le_of_dense (T : H →L[ℝ] K)
    (A₀ : H →L[ℝ] H) (Aₜ : K →L[ℝ] K) (ε t C : ℝ)
    (S : Set H) (hS : Dense S)
    (hcore : ∀ f ∈ S, quadraticEnergy Aₜ ε (T f) ≤ quadraticEnergy A₀ ε f -
      (‖f‖^2-‖T f‖^2)/4 + C*(ε+ε^2)*t*‖f‖^2) (f : H) :
    quadraticEnergy Aₜ ε (T f) ≤ quadraticEnergy A₀ ε f -
      (‖f‖^2-‖T f‖^2)/4 + C*(ε+ε^2)*t*‖f‖^2 := by
  refine hS.induction hcore ?_ f
  apply isClosed_le ((quadraticEnergy_continuous Aₜ ε).comp T.continuous)
  exact ((quadraticEnergy_continuous A₀ ε).sub
    ((normDefect_continuous T).div_const 4)).add
      (continuous_const.mul (continuous_norm.pow 2))

end AcceleratedLogConcave.Kinetic.Reheating
