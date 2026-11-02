import AcceleratedLogConcave.Kinetic.Corrector
import Mathlib.Analysis.Convex.Integral

/-! Convexity and averaging of the actual corrected quadratic energy. -/
noncomputable section
open MeasureTheory InnerProductSpace Set
open scoped RealInnerProductSpace ContDiff
namespace AcceleratedLogConcave.Kinetic
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Positive-sign corrected energy for a bounded corrector. -/
def quadraticEnergy (A : H →L[ℝ] H) (ε : ℝ) (f : H) : ℝ :=
  (1 / 2 : ℝ) * ‖f‖ ^ 2 + ε * inner ℝ (A f) f

theorem quadraticEnergy_continuous (A : H →L[ℝ] H) (ε : ℝ) :
    Continuous (quadraticEnergy A ε) :=
  (continuous_const.mul (continuous_norm.pow 2)).add
    (continuous_const.mul (A.continuous.inner continuous_id))

/-- The exact quadratic Jensen defect; symmetry of A is not needed. -/
theorem quadraticEnergy_convex_identity (A : H →L[ℝ] H) (ε a b : ℝ)
    (hab : a + b = 1) (f g : H) :
    a * quadraticEnergy A ε f + b * quadraticEnergy A ε g -
      quadraticEnergy A ε (a • f + b • g) = a * b * quadraticEnergy A ε (f - g) := by
  simp only [quadraticEnergy, ← real_inner_self_eq_norm_sq, map_add, map_smul,
    map_sub, inner_add_left, inner_add_right, inner_sub_left, inner_sub_right,
    real_inner_smul_left, real_inner_smul_right]
  have hb : b = 1 - a := by linarith
  rw [hb]
  ring

/-- Nonnegativity of a quadratic energy proves its convexity. -/
theorem quadraticEnergy_convex (A : H →L[ℝ] H) (ε : ℝ)
    (hpos : ∀ f, 0 ≤ quadraticEnergy A ε f) :
    ConvexOn ℝ univ (quadraticEnergy A ε) := by
  refine ⟨convex_univ, ?_⟩
  intro f hf g hg a b ha hb hab
  have hd := quadraticEnergy_convex_identity A ε a b hab f g
  have hn := mul_nonneg (mul_nonneg ha hb) (hpos (f - g))
  simp only [smul_eq_mul]
  linarith

/-- Jensen for a genuine strongly integrable family of phase densities. -/
theorem quadraticEnergy_integral_le [CompleteSpace H]
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : H →L[ℝ] H) (ε : ℝ) (hpos : ∀ f, 0 ≤ quadraticEnergy A ε f)
    (f : Ω → H) (hf : Integrable f μ)
    (hE : Integrable (fun z => quadraticEnergy A ε (f z)) μ) :
    quadraticEnergy A ε (∫ z, f z ∂μ) ≤ ∫ z, quadraticEnergy A ε (f z) ∂μ :=
  (quadraticEnergy_convex A ε hpos).map_integral_le
    (quadraticEnergy_continuous A ε).continuousOn isClosed_univ
    (Filter.Eventually.of_forall fun _ => mem_univ _) hf hE

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [IsProbabilityMeasure μ]
  (V : E → ℝ) (hV : ContDiff ℝ 2 V) (hI : Integrable (fun x => Real.exp (-V x)))
  (hμ : μ = volume.tilted (fun x => -V x))
  (m L : ℝ) (hm : 0 < m)
  (hlower : ∀ x a, m * ‖a‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x a a)
  (hupper : ∀ x a, fderiv ℝ (fderiv ℝ V) x a a ≤ L * ‖a‖ ^ 2)

/-- Convexity of the actual source energy, proved from W04's energy bound. -/
theorem gaussianCorrectedEnergy_convex (θ : ℝ) (hθ : 0 ≤ θ) (hθq : θ ≤ 1 / 4) :
    ConvexOn ℝ univ
      (gaussianCorrectedEnergy μ V hV hI hμ m L hm hlower hupper (θ * Real.sqrt m)) := by
  apply quadraticEnergy_convex
  intro f
  exact (mul_nonneg (by norm_num : (0 : ℝ) ≤ 3 / 8) (sq_nonneg ‖f‖)).trans
    (gaussianCorrectedEnergy_bounds_quarter μ V hV hI hμ m L hm hlower hupper θ hθ hθq f).1

end AcceleratedLogConcave.Kinetic
