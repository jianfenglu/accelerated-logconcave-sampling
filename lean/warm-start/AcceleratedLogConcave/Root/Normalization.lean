import AcceleratedLogConcave.Root.RetainedLaw

noncomputable section
open MeasureTheory ProbabilityTheory
open AcceleratedLogConcave.Conditional
set_option autoImplicit false
namespace AcceleratedLogConcave.Root.RetainedLaw
variable {ι : Type*} [Fintype ι] {m : ℕ}
local notation "E" => EuclideanSpace ℝ ι

/-- Positive weights summing to a clock at most 1/2 satisfy the actual assembly budget. -/
theorem quadrature_admissible (ω : Fin m → ℝ) (ρ : ℝ)
    (hω : ∀ i, 0 ≤ ω i) (hsum : ∑ i, ω i = ρ) (hρ : ρ ≤ 1/2) :
    GaussianAssembly.mass (fun i => -ω i) < 1 := by
  have hp : 0 ≤ ρ := hsum ▸ Finset.sum_nonneg (fun i _ => hω i)
  have hs := Finset.sum_sq_le_sq_sum_of_nonneg (s := Finset.univ) (fun i _ => hω i)
  rw [hsum] at hs
  simp only [GaussianAssembly.mass, neg_sq]
  nlinarith

/-- The source lower bound for the recovered Gaussian reserve. -/
theorem quadrature_reserve_lower (ω : Fin m → ℝ) (ρ : ℝ)
    (hω : ∀ i, 0 ≤ ω i) (hsum : ∑ i, ω i = ρ) (hρ : ρ ≤ 1/2) :
    Real.sqrt 3 / 2 ≤ GaussianAssembly.reserve (fun i => -ω i) := by
  have ha := quadrature_admissible ω ρ hω hsum hρ
  have hr := GaussianAssembly.reserve_sq ha.le
  have hs := Finset.sum_sq_le_sq_sum_of_nonneg (s := Finset.univ) (fun i _ => hω i)
  have hp : 0 ≤ ρ := hsum ▸ Finset.sum_nonneg (fun i _ => hω i)
  rw [hsum] at hs
  simp only [GaussianAssembly.mass, neg_sq] at hr
  have hthree := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)
  have hn := GaussianAssembly.reserve_pos ha
  nlinarith [Real.sqrt_nonneg 3]

/-- At clock zero the same original H₀ is returned, regardless of child kernels. -/
theorem zero_weight_output (d : Data ι m) (hzero : ∀ i, d.weight i = 0)
    (z : Execution (ι := ι) (m := m)) : output d z = z.1.1 := by
  have h := innovation d z
  simp only [hzero, neg_zero, zero_smul, Finset.sum_const_zero] at h
  exact sub_eq_zero.mp h

/-- The source's initial reserve formula has the correct plus sign for coefficient −ω. -/
theorem reserve_formula (d : Data ι m) (h : Host (ι := ι) (m := m)) :
    reserve d h = beta d • h.1 + ∑ i, d.weight i • h.2 i := by
  simp only [reserve, GaussianAssembly.residual, coefficient, GaussianAssembly.noiseSum,
    neg_smul, Finset.sum_neg_distrib, sub_neg_eq_add, beta]

end AcceleratedLogConcave.Root.RetainedLaw
