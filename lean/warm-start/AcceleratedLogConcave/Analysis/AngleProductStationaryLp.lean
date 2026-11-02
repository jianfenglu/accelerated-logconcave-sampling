import AcceleratedLogConcave.Analysis.AnglePhaseStationaryLp
import AcceleratedLogConcave.Analysis.StationaryLpFTC
import AcceleratedLogConcave.Analysis.DominatedLp

/-! Actual joint midpoint/Gaussian rotation and the genuine L² source derivative
lift. The midpoint remains fixed and its law is arbitrary. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace AcceleratedLogConcave.Analysis.AnglePhase
variable {D : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin D)
local notation "EP" => EuclideanSpace ℝ (Fin (D+D))
local notation "X" => E × EP

def parameterRotation (q t : ℝ) (p : X) : X :=
  (p.1,rotationOrbit (D := D) q p.2 t)

theorem continuous_parameterRotation (q : ℝ) :
    Continuous (fun p : ℝ × X => parameterRotation q p.1 p.2) := by
  unfold parameterRotation rotationOrbit AngleGaussianPhase.phase Kinetic.gaussianRotate
  fun_prop

theorem parameterRotation_preserving (μ : Measure E) [IsProbabilityMeasure μ] (q t : ℝ) :
    MeasurePreserving (parameterRotation (D := D) q t)
      (μ.prod (stdGaussian EP)) (μ.prod (stdGaussian EP)) :=
  (MeasurePreserving.id μ).prod (rotationOrbit_preserving (D := D) q t)

def parameterRotationMap (q t : ℝ) : C(X,X) :=
  ⟨parameterRotation (D := D) q t,by
    have h : Continuous (fun z : X => (t,z)) := continuous_const.prodMk continuous_id
    exact (continuous_parameterRotation (D := D) q).comp h⟩

theorem continuous_parameterRotationMap (q : ℝ) :
    Continuous (parameterRotationMap (D := D) q) :=
  ContinuousMap.continuous_of_continuous_uncurry _ (continuous_parameterRotation (D := D) q)

def parameterLpOrbit (μ : Measure E) [IsProbabilityMeasure μ] (q : ℝ)
    (f : Lp EP 2 (μ.prod (stdGaussian EP))) (t : ℝ) : Lp EP 2 (μ.prod (stdGaussian EP)) :=
  Lp.compMeasurePreserving (parameterRotationMap (D := D) q t)
    (parameterRotation_preserving μ q t) f

theorem continuous_parameterLpOrbit (μ : Measure E) [IsProbabilityMeasure μ] (q : ℝ)
    (f : Lp EP 2 (μ.prod (stdGaussian EP))) : Continuous (parameterLpOrbit μ q f) := by
  exact continuous_const.compMeasurePreservingLp (continuous_parameterRotationMap (D := D) q)
    (parameterRotation_preserving μ q) (by norm_num)

theorem norm_parameterLpOrbit (μ : Measure E) [IsProbabilityMeasure μ] (q : ℝ)
    (f : Lp EP 2 (μ.prod (stdGaussian EP))) (t : ℝ) :
    ‖parameterLpOrbit μ q f t‖ = ‖f‖ :=
  Lp.norm_compMeasurePreserving f (parameterRotation_preserving μ q t)

theorem hasDerivAt_parameterLpOrbit_of_source (μ : Measure E) [IsProbabilityMeasure μ]
    (q : ℝ) (f g : X → EP)
    (hf : MemLp f 2 (μ.prod (stdGaussian EP)))
    (hg : MemLp g 2 (μ.prod (stdGaussian EP))) (hgc : Continuous g)
    (hd : ∀ t z, HasDerivAt (fun u => f (parameterRotation q u z))
      (g (parameterRotation q t z)) t) (t : ℝ) :
    HasDerivAt (parameterLpOrbit μ q (hf.toLp f))
      (parameterLpOrbit μ q (hg.toLp g) t) t := by
  have hfg (u : ℝ) : MemLp (fun z => f (parameterRotation q u z)) 2
      (μ.prod (stdGaussian EP)) := hf.comp_measurePreserving (parameterRotation_preserving μ q u)
  have hgg (u : ℝ) : MemLp (fun z => g (parameterRotation q u z)) 2
      (μ.prod (stdGaussian EP)) := hg.comp_measurePreserving (parameterRotation_preserving μ q u)
  have he (u : ℝ) : (∫ z, ‖g (parameterRotation q u z)‖^2 ∂μ.prod (stdGaussian EP)) =
      ‖hg.toLp g‖^2 := by
    rw [← DominatedLp.norm_sq_toLp (hgg u)]
    change ‖parameterLpOrbit μ q (hg.toLp g) u‖^2 = _
    rw [norm_parameterLpOrbit]
  exact StationaryLpFTC.hasDerivAt_toLp_of_energy
    (fun u z => f (parameterRotation q u z)) (fun u z => g (parameterRotation q u z))
    (hgc.comp (continuous_parameterRotation q)) hfg hgg
    (continuous_parameterLpOrbit μ q (hg.toLp g)) (sq_nonneg ‖hg.toLp g‖)
    (fun u => (he u).le) hd t
end AcceleratedLogConcave.Analysis.AnglePhase
