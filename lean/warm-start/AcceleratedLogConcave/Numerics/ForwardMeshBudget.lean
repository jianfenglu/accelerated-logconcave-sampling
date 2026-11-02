import AcceleratedLogConcave.Numerics.ProbabilityGeometricMesh

/-! Prescribed forward meshes and the literal forward/angle finite sums in
velocityError. All analytic cell and angle budgets remain explicit premises. -/
noncomputable section
open scoped BigOperators
open AcceleratedLogConcave.Numerics.AffineGraph
open AcceleratedLogConcave.Numerics.AffineGraph.MeanGeometry
set_option autoImplicit false
namespace AcceleratedLogConcave.Numerics

def forwardGeometricInterval {m : ℕ} (G : MeanGeometry m) (ρ : G.Kernel)
    (h₀ : ℝ) (hh : 0 < h₀) : IntervalMesh (G.rho ρ) (backwardEnd G.R) :=
  probabilityGeometricInterval (G.rho ρ) (backwardEnd G.R) h₀
    (G.rho_mem ρ).2 G.backwardEnd_lt_one hh

theorem forwardGeometricInterval_step {m : ℕ} (G : MeanGeometry m) (ρ : G.Kernel)
    (h₀ : ℝ) (hh : 0 < h₀) (hhalf : h₀ ≤ 1/2)
    (c : (forwardGeometricInterval G ρ h₀ hh).Cell) :
    (forwardGeometricInterval G ρ h₀ hh).length c ≤
      2*h₀*(1-((forwardGeometricInterval G ρ h₀ hh).right c)^2) :=
  probabilityGeometricInterval_step (G.rho ρ) (backwardEnd G.R) h₀
    (G.rho_mem ρ).2 G.backwardEnd_lt_one hh hhalf (G.rho_mem ρ).1 c

namespace AffineResidual.Mean.DerivativeBudget
variable {m : ℕ} (G : MeanGeometry m) (D : AffineResidual.Mean.DerivativeBudget G)

/-- Prescribed forward quadrature, before kernel and angle weighting. -/
theorem forward_cellBudget_le (h₀ AF : ℝ) (hh : 0 < h₀) (hhalf : h₀ ≤ 1/2)
    (hAF : 0 ≤ AF) (j : Fin m) (ρ : G.Kernel) (z : Fin m)
    (hforward : G.forward ρ = forwardGeometricInterval G ρ h₀ hh)
    (hF : ∀ c, D.forward j ρ z c ≤ AF/(1-((G.forward ρ).right c)^2)^m) :
    cellBudget (G.forward ρ) m (D.forward j ρ z) ≤
      2^(m+1)*AF*h₀^m/(m.factorial:ℝ) := by
  have hs : ∀ c, (G.forward ρ).length c ≤ 2*h₀*(1-((G.forward ρ).right c)^2) := by
    rw [hforward]
    exact forwardGeometricInterval_step G ρ h₀ hh hhalf
  have hb := probability_cellBudget_le (G.forward ρ) (G.rho_mem ρ).1
    G.backwardEnd_lt_one m (D.forward j ρ z) AF h₀ hAF hh.le hs hF
  have hlen : backwardEnd G.R - G.rho ρ ≤ 1 := by
    linarith [(G.rho_mem ρ).1, G.backwardEnd_lt_one]
  calc
    _ ≤ 2^(m+1)*(backwardEnd G.R-G.rho ρ)*AF*h₀^m/(m.factorial:ℝ) := hb
    _ ≤ 2^(m+1)*1*AF*h₀^m/(m.factorial:ℝ) := by gcongr
    _ = _ := by ring

/-- Exact forward finite sum appearing in velocityError. The factor 40 and
m^5 are derived from the existing kernel and angle coefficient mass theorems. -/
theorem forward_weighted_cellBudget_le (hm : 2 ≤ m) (h₀ AF : ℝ)
    (hh : 0 < h₀) (hhalf : h₀ ≤ 1/2) (hAF : 0 ≤ AF) (j : Fin m)
    (hback : h₀/4 ≤ G.backward.length 0)
    (hforward : ∀ ρ, G.forward ρ = forwardGeometricInterval G ρ h₀ hh)
    (hF : ∀ ρ z c, D.forward j ρ z c ≤ AF/(1-((G.forward ρ).right c)^2)^m) :
    (∑ ρ : G.Kernel, |G.kernelCoeff ρ| * ∑ z : Fin m,
      |G.angleDerivative z| * cellBudget (G.forward ρ) m (D.forward j ρ z)) ≤
      40*2^(m+1)*(m:ℝ)^5*AF*h₀^(m-1)/(G.psi*(m.factorial:ℝ)) := by
  let C : ℝ := 2^(m+1)*AF*h₀^m/(m.factorial:ℝ)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have inner (ρ : G.Kernel) :
      (∑ z : Fin m, |G.angleDerivative z| * cellBudget (G.forward ρ) m
        (D.forward j ρ z)) ≤ ((m:ℝ)^3/G.psi)*C := by
    calc
      _ ≤ ∑ z : Fin m, |G.angleDerivative z| * C := by
        apply Finset.sum_le_sum
        intro z _
        exact mul_le_mul_of_nonneg_left
          (forward_cellBudget_le G D h₀ AF hh hhalf hAF j ρ z (hforward ρ) (hF ρ z))
          (abs_nonneg _)
      _ = (∑ z : Fin m, |G.angleDerivative z|)*C := (Finset.sum_mul _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_right G.sum_abs_angleDerivative_le hC
  calc
    _ ≤ ∑ ρ : G.Kernel, |G.kernelCoeff ρ| * (((m:ℝ)^3/G.psi)*C) := by
      exact Finset.sum_le_sum fun ρ _ => mul_le_mul_of_nonneg_left (inner ρ) (abs_nonneg _)
    _ = G.kernelMass * (((m:ℝ)^3/G.psi)*C) := by rw [← Finset.sum_mul]; rfl
    _ ≤ (40*(m:ℝ)^2/h₀) * (((m:ℝ)^3/G.psi)*C) :=
      mul_le_mul_of_nonneg_right (G.kernelMass_le_of_firstWidth hm h₀ hh hback)
        (mul_nonneg (div_nonneg (by positivity) G.psi_pos.le) hC)
    _ = _ := by
      have hp : h₀^m = h₀^(m-1)*h₀ := by
        rw [← pow_succ]; congr 1; omega
      dsimp [C]
      rw [hp]
      field_simp [hh.ne']

/-- Exact Gaussian-angle finite sum in velocityError; no new angle mesh or
analytic angle-derivative estimate is introduced. -/
theorem angle_weighted_budget_le (hm : 2 ≤ m) (h₀ AA : ℝ)
    (hh : 0 < h₀) (hAA : 0 ≤ AA) (j : Fin m)
    (hback : h₀/4 ≤ G.backward.length 0)
    (hAngle : ∀ ρ, D.angle j ρ ≤ AA) :
    (∑ ρ : G.Kernel, |G.kernelCoeff ρ| *
      ((m:ℝ)^3*G.psi^(m-1)*D.angle j ρ/(m.factorial:ℝ))) ≤
      40*(m:ℝ)^5*AA*G.psi^(m-1)/(h₀*(m.factorial:ℝ)) := by
  have hpsi := G.psi_pos
  let C : ℝ := (m:ℝ)^3*G.psi^(m-1)*AA/(m.factorial:ℝ)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hcell (ρ : G.Kernel) :
      (m:ℝ)^3*G.psi^(m-1)*D.angle j ρ/(m.factorial:ℝ) ≤ C := by
    dsimp [C]
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hAngle ρ) (by positivity)) (by positivity)
  calc
    _ ≤ ∑ ρ : G.Kernel, |G.kernelCoeff ρ| * C :=
      Finset.sum_le_sum fun ρ _ => mul_le_mul_of_nonneg_left (hcell ρ) (abs_nonneg _)
    _ = G.kernelMass*C := by rw [← Finset.sum_mul]; rfl
    _ ≤ (40*(m:ℝ)^2/h₀)*C :=
      mul_le_mul_of_nonneg_right (G.kernelMass_le_of_firstWidth hm h₀ hh hback) hC
    _ = _ := by dsimp [C]; ring

end AffineResidual.Mean.DerivativeBudget
end AcceleratedLogConcave.Numerics
