import AcceleratedLogConcave.Analysis.AnglePhaseJetLp
import Mathlib.MeasureTheory.Function.L2Space

/-! The actual angle L² ladder has the sharp whole-expression energy bound,
with dimension appearing only under a square root. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ContDiff
namespace AcceleratedLogConcave.Analysis.AnglePhase
open Tensor Tensor.Ordered.Graph Tensor.PhaseExpression Tensor.PhaseSourceJetInduction
open Kinetic.Reheating
variable {D : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin D)
local notation "EP" => EuclideanSpace ℝ (Fin (D+D))

theorem norm_toLp_le_sqrt_energy {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (f : X → EP) (hf : MemLp f 2 μ) {B : ℝ} (hB : ∫ x, ‖f x‖^2 ∂μ ≤ B) :
    ‖hf.toLp f‖ ≤ Real.sqrt B := by
  have he : ‖hf.toLp f‖^2 = ∫ x, ‖f x‖^2 ∂μ := by
    rw [← real_inner_self_eq_norm_sq,L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hf.coeFn_toLp] with x hx
    rw [hx,real_inner_self_eq_norm_sq]
  rw [← Real.sqrt_sq (norm_nonneg (hf.toLp f))]
  exact Real.sqrt_le_sqrt (he.le.trans hB)

theorem norm_angleSourceJetLp_le (μ : Measure E) [IsProbabilityMeasure μ]
    (T : E → E) (hT : ContDiff ℝ ∞ T) (q a C S : ℝ)
    (hC : 1 ≤ C) (hS : 0 < S) (hS1 : S ≤ 1)
    (hb : ∀ M, PhasePrimitiveBudgets (angleCoefficients T M q a) gaussianPotential C S)
    (k : ℕ) (t : ℝ) :
    ‖angleSourceJetLp μ T hT q a C S hC hS hS1 hb k t‖ ≤
      ‖(q⁻¹)^(k+1)‖ * Real.sqrt
        (((D+D : ℕ) : ℝ) * Tensor.AdjointReduction.PhaseBudget.Q C (jet F k).size *
          S^(-2*((jet F k).weight : ℝ))) := by
  let f := fun p : E × EP => vectorSection (angleCoefficients T p.1 q a)
    gaussianPotential (jet F k) p.2
  have hf := angle_product_expression_memLp μ T hT q a C S hC hS hS1 hb (jet F k)
  rw [angleSourceJetLp,norm_parameterLpOrbit]
  change ‖(hf.const_smul ((q⁻¹)^(k+1))).toLp (((q⁻¹)^(k+1)) • f)‖ ≤ _
  rw [MemLp.toLp_const_smul ((q⁻¹)^(k+1)) hf,norm_smul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  exact norm_toLp_le_sqrt_energy _ f hf
    (angle_product_expression_energy μ T hT q a C S hC hS hS1 hb (jet F k))
end AcceleratedLogConcave.Analysis.AnglePhase
