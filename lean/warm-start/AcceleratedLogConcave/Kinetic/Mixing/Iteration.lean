import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Iterating a proved discrete energy estimate and transferring its L2 rate
by the genuine Hilbert adjoint. Apply on the centered phase Hilbert space.
No same-energy contraction of the test adjoint is inferred. -/
noncomputable section
open InnerProductSpace
open scoped RealInnerProductSpace
namespace AcceleratedLogConcave.Kinetic
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Iteration of an already-proved one-step energy estimate. -/
theorem energy_pow_le (T : H →L[ℝ] H) (E : H → ℝ) (r : ℝ) (hr : 0 ≤ r)
    (hstep : ∀ f, E (T f) ≤ r * E f) (n : ℕ) (f : H) :
    E ((T ^ n) f) ≤ r ^ n * E f := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc
      _ = E (T ((T ^ n) f)) := by rw [pow_succ', mul_apply_eq_comp]
      _ ≤ r * E ((T ^ n) f) := hstep _
      _ ≤ r * (r ^ n * E f) := mul_le_mul_of_nonneg_left ih hr
      _ = r ^ (n + 1) * E f := by rw [pow_succ]; ring

/-- Energy equivalence turns the iterated estimate into the sharp L2 prefactor. -/
theorem norm_sq_pow_le_of_energy (T : H →L[ℝ] H) (E : H → ℝ)
    (α β r : ℝ) (hα : 0 < α) (hr : 0 ≤ r)
    (hlow : ∀ f, α * ‖f‖ ^ 2 ≤ E f) (hup : ∀ f, E f ≤ β * ‖f‖ ^ 2)
    (hstep : ∀ f, E (T f) ≤ r * E f) (n : ℕ) (f : H) :
    ‖(T ^ n) f‖ ^ 2 ≤ (β / α) * r ^ n * ‖f‖ ^ 2 := by
  have hi := energy_pow_le T E r hr hstep n f
  have hu := mul_le_mul_of_nonneg_left (hup f) (pow_nonneg hr n)
  have hh := (hlow ((T ^ n) f)).trans (hi.trans hu)
  have hd : ‖(T ^ n) f‖ ^ 2 ≤ (r ^ n * (β * ‖f‖ ^ 2)) / α :=
    (le_div_iff₀ hα).mpr (by nlinarith [hh])
  convert hd using 1
  ring

/-- The actual ordinary operator norm of the n-step transition. -/
theorem opNorm_pow_le_of_energy (T : H →L[ℝ] H) (E : H → ℝ)
    (α β r : ℝ) (hα : 0 < α) (hβ : 0 ≤ β) (hr : 0 ≤ r)
    (hlow : ∀ f, α * ‖f‖ ^ 2 ≤ E f) (hup : ∀ f, E f ≤ β * ‖f‖ ^ 2)
    (hstep : ∀ f, E (T f) ≤ r * E f) (n : ℕ) :
    ‖T ^ n‖ ≤ Real.sqrt ((β / α) * r ^ n) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
  intro f
  have hsq := norm_sq_pow_le_of_energy T E α β r hα hr hlow hup hstep n f
  have hcoef : 0 ≤ (β / α) * r ^ n := by positivity
  have heq := Real.sq_sqrt hcoef
  have hn : 0 ≤ Real.sqrt ((β / α) * r ^ n) * ‖f‖ := by positivity
  nlinarith [sq_nonneg (‖(T ^ n) f‖ + Real.sqrt ((β / α) * r ^ n) * ‖f‖)]

/-- Adjoint powers have exactly the same ordinary L2 norm. -/
theorem opNorm_adjoint_pow [CompleteSpace H] (T : H →L[ℝ] H) (n : ℕ) :
    ‖T.adjoint ^ n‖ = ‖T ^ n‖ := by
  rw [← ContinuousLinearMap.star_eq_adjoint, ← star_pow, ContinuousLinearMap.star_eq_adjoint]
  exact ContinuousLinearMap.adjoint.norm_map (T ^ n)

/-- Both actual density and test operators obey the resulting iterated L2 rate.
This conclusion uses adjoint norm equality, not a false same-energy inference. -/
theorem opNorm_adjoint_pow_le_of_energy [CompleteSpace H]
    (T : H →L[ℝ] H) (E : H → ℝ)
    (α β r : ℝ) (hα : 0 < α) (hβ : 0 ≤ β) (hr : 0 ≤ r)
    (hlow : ∀ f, α * ‖f‖ ^ 2 ≤ E f) (hup : ∀ f, E f ≤ β * ‖f‖ ^ 2)
    (hstep : ∀ f, E (T f) ≤ r * E f) (n : ℕ) :
    ‖T.adjoint ^ n‖ ≤ Real.sqrt ((β / α) * r ^ n) := by
  rw [opNorm_adjoint_pow]
  exact opNorm_pow_le_of_energy T E α β r hα hβ hr hlow hup hstep n

end AcceleratedLogConcave.Kinetic
