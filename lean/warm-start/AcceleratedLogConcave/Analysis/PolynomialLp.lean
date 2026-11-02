import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Order.Ring.Basic
import Mathlib.Tactic.FunProp

/-! Polynomial position envelopes combined with independent momentum.
These lemmas retain the actual product measure. They do not assume that any
non-product transported law has independent components. -/
noncomputable section
open MeasureTheory
set_option backward.isDefEq.respectTransparency false
namespace AcceleratedLogConcave.Analysis.PolynomialLp
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  {μ : Measure X} {ν : Measure Y} [IsFiniteMeasure μ] [IsFiniteMeasure ν]

omit [IsFiniteMeasure μ] in
/-- Two genuine L² factors on their separate laws give an L² product on the
product law. Hölder on a single law would only give L¹ and is not used here. -/
theorem memLp_two_mul_prod {f : X → ℝ} {g : Y → ℝ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 ν) :
    MemLp (fun z : X × Y => f z.1 * g z.2) 2 (μ.prod ν) := by
  apply (memLp_two_iff_integrable_sq
    (hf.aestronglyMeasurable.comp_fst.mul hg.aestronglyMeasurable.comp_snd)).mpr
  simpa only [Pi.mul_apply, mul_pow] using hf.integrable_sq.mul_prod hg.integrable_sq

section Norm
variable [NormedAddCommGroup X] [BorelSpace X]

/-- A position moment of order 2N supplies the polynomial L² envelope needed
for an N-th degree growth bound. No moment of larger order is requested. -/
theorem memLp_two_one_add_norm_pow (N : ℕ)
    (hm : Integrable (fun x : X => ‖x‖ ^ (2 * N)) μ) :
    MemLp (fun x : X => (1 + ‖x‖) ^ N) 2 μ := by
  apply (memLp_two_iff_integrable_sq (by fun_prop)).mpr
  apply (((integrable_const (1 : ℝ)).add hm).const_mul (2 ^ (2 * N - 1))).mono'
    (by fun_prop)
  filter_upwards [] with x
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← pow_mul, Nat.mul_comm N 2]
  simpa only [Pi.add_apply, one_pow] using add_pow_le (show (0 : ℝ) ≤ 1 from zero_le_one) (norm_nonneg x) (2 * N)

/-- The exact phase-product envelope is square integrable from one required
position moment and the momentum's second moment. -/
theorem memLp_two_polynomial_momentum [NormedAddCommGroup Y] [BorelSpace Y]
    (N : ℕ) (C : ℝ)
    (hposition : Integrable (fun x : X => ‖x‖ ^ (2 * N)) μ)
    (hmomentum : MemLp (fun y : Y => ‖y‖) 2 ν) :
    MemLp (fun z : X × Y => C * (1 + ‖z.1‖) ^ N * ‖z.2‖) 2 (μ.prod ν) := by
  simpa only [mul_assoc] using
    (memLp_two_mul_prod (memLp_two_one_add_norm_pow N hposition) hmomentum).const_mul C

/-- Finite moments survive an actual affine combination of two product-law
coordinates. No restriction on the real coefficients is necessary. -/
theorem integrable_norm_smul_add_prod [NormedSpace ℝ X] [SecondCountableTopology X]
    {ν' : Measure X} [IsFiniteMeasure ν'] (n : ℕ) (u v : ℝ)
    (hμ : Integrable (fun x : X => ‖x‖ ^ n) μ)
    (hν : Integrable (fun x : X => ‖x‖ ^ n) ν') :
    Integrable (fun p : X × X => ‖u • p.1 + v • p.2‖ ^ n) (μ.prod ν') := by
  apply ((((hμ.comp_fst ν').const_mul (|u| ^ n)).add
    ((hν.comp_snd μ).const_mul (|v| ^ n))).const_mul (2 ^ (n - 1))).mono'
    (by fun_prop)
  filter_upwards [] with p
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (norm_nonneg _) n)]
  have hh : ‖u • p.1 + v • p.2‖ ≤ |u| * ‖p.1‖ + |v| * ‖p.2‖ := by
    simpa only [norm_smul, Real.norm_eq_abs] using norm_add_le (u • p.1) (v • p.2)
  calc
    _ ≤ (|u| * ‖p.1‖ + |v| * ‖p.2‖) ^ n := pow_le_pow_left₀ (norm_nonneg _) hh n
    _ ≤ 2 ^ (n - 1) * ((|u| * ‖p.1‖) ^ n + (|v| * ‖p.2‖) ^ n) :=
      add_pow_le (mul_nonneg (abs_nonneg _) (norm_nonneg _))
        (mul_nonneg (abs_nonneg _) (norm_nonneg _)) n
    _ = _ := by simp only [mul_pow, Pi.add_apply]

/-- The preceding moment calculation is for the literal pushforward law. -/
theorem integrable_norm_pow_map_smul_add [NormedSpace ℝ X] [SecondCountableTopology X]
    {ν' : Measure X} [IsFiniteMeasure ν'] (n : ℕ) (u v : ℝ)
    (hμ : Integrable (fun x : X => ‖x‖ ^ n) μ)
    (hν : Integrable (fun x : X => ‖x‖ ^ n) ν') :
    Integrable (fun x : X => ‖x‖ ^ n)
      ((μ.prod ν').map (fun p : X × X => u • p.1 + v • p.2)) := by
  exact (integrable_map_measure (by fun_prop) (by fun_prop)).mpr
    (integrable_norm_smul_add_prod n u v hμ hν)

end Norm
end AcceleratedLogConcave.Analysis.PolynomialLp
