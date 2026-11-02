import AcceleratedLogConcave.Numerics.RotatedSeedLaw
noncomputable section
open MeasureTheory ProbabilityTheory
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace AcceleratedLogConcave.Numerics
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
def gaussianRow3 (a b c : ℝ) : (E × E) × E →L[ℝ] E :=
  a • (ContinuousLinearMap.fst ℝ E E).comp (ContinuousLinearMap.fst ℝ (E × E) E) +
  b • (ContinuousLinearMap.snd ℝ E E).comp (ContinuousLinearMap.fst ℝ (E × E) E) +
  c • ContinuousLinearMap.snd ℝ (E × E) E

theorem gaussianRow3_preserving (a b c : ℝ) (h : a^2+b^2+c^2=1) :
    MeasurePreserving (fun p : (E × E) × E => a • p.1.1+b • p.1.2+c • p.2)
      (((stdGaussian E).prod (stdGaussian E)).prod (stdGaussian E)) (stdGaussian E) := by
  refine ⟨by fun_prop, ?_⟩
  change Measure.map (gaussianRow3 (E := E) a b c) _ = _
  apply Measure.ext_of_charFunDual
  funext L
  rw [charFunDual_map,charFunDual_prod,charFunDual_prod]
  have h1 : ((L.comp (gaussianRow3 a b c)).comp (ContinuousLinearMap.inl ℝ (E × E) E)).comp
      (ContinuousLinearMap.inl ℝ E E) = a • L := by
    ext x
    simp [gaussianRow3]
  have h2 : ((L.comp (gaussianRow3 a b c)).comp (ContinuousLinearMap.inl ℝ (E × E) E)).comp
      (ContinuousLinearMap.inr ℝ E E) = b • L := by
    ext x
    simp [gaussianRow3]
  have h3 : (L.comp (gaussianRow3 a b c)).comp (ContinuousLinearMap.inr ℝ (E × E) E) = c • L := by
    ext x
    simp [gaussianRow3]
  rw [h1,h2,h3]
  simp only [charFunDual_stdGaussian,norm_smul,Real.norm_eq_abs,← Complex.exp_add]
  congr 1
  have hh : -(|a| *‖L‖)^2/2 + -(|b| *‖L‖)^2/2 + -(|c| *‖L‖)^2/2 = -‖L‖^2/2 := by
    simp only [mul_pow,sq_abs]
    nlinarith [h]
  exact_mod_cast hh
end AcceleratedLogConcave.Numerics
