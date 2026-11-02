import AcceleratedLogConcave.Numerics.AngleGaussianPhase
import AcceleratedLogConcave.Numerics.CenterMeanPhaseCoordinates

noncomputable section
open MeasureTheory ProbabilityTheory
namespace AcceleratedLogConcave.Analysis.AnglePhase
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem prod_stdGaussian_toLp :
    ((stdGaussian E).prod (stdGaussian E)).map (WithLp.toLp 2) =
      stdGaussian (WithLp 2 (E × E)) := by
  apply Measure.ext_of_charFun
  ext t
  rw [charFun_prod,charFun_stdGaussian,charFun_stdGaussian,charFun_stdGaussian,
    ← Complex.exp_add]
  simp only [← Complex.ofReal_pow,WithLp.prod_norm_sq_eq_of_L2]
  congr 1
  push_cast
  change _ = (-((‖t.ofLp.1‖ : ℂ)^2 + (‖t.ofLp.2‖ : ℂ)^2) / 2)
  ring
end AcceleratedLogConcave.Analysis.AnglePhase
