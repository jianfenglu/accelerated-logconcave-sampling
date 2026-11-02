import AcceleratedLogConcave.Numerics.AngleIndependentSourceLaw
import AcceleratedLogConcave.Analysis.AnglePhaseStationary

/-! New literal joint coordinate identities. The midpoint and Gaussian phase
are both retained; this is not a marginal-law or independence assumption. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace AcceleratedLogConcave.Numerics.MeanFlowLp
open Conditional Analysis.AnglePhase CenterMeanSecondJetSource AffineGraph AffineGraph.MeanGeometry
variable {D m : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin D)
local notation "EP" => EuclideanSpace ℝ (Fin (D+D))

def angleObservationCoordinates (d : Data (Fin D) m) (k : d.G.Kernel)
    (p : (E × E) × E) : E × EP :=
  let M := (d.G.rho k/(1+(d.G.rho k)^2)) • (p.1.2+d.G.rho k • p.1.1)
  (M, phaseMeasurableEquiv.symm ((d.G.rotationScale k)⁻¹ • (p.1.1-M),p.2))

def angleSeedCoordinates (d : Data (Fin D) m) (j : Fin m) (k : d.G.Kernel)
    (w : Seed d) : E × EP :=
  angleObservationCoordinates d k
    ((backward d j (d.G.rho k) w,
      observationFromNoise d k (backward d j (d.G.rho k) w) (w.2 j k)),
      score d (centerNode j) w)

def angleIndependentMidpoint (d : Data (Fin D) m) (k : d.G.Kernel)
    (p : E × E) : E := d.G.rho k • p.1 + (d.G.rho k*d.G.rotationScale k) • p.2

theorem continuous_angleObservationCoordinates (d : Data (Fin D) m) (k : d.G.Kernel) :
    Continuous (angleObservationCoordinates d k) := by
  unfold angleObservationCoordinates phaseMeasurableEquiv
  change Continuous (fun p : (E × E) × E =>
    ((d.G.rho k/(1+(d.G.rho k)^2)) • (p.1.2+d.G.rho k • p.1.1),
    phaseCoordinateEquiv.symm (WithLp.toLp 2
      ((d.G.rotationScale k)⁻¹ • (p.1.1-
      (d.G.rho k/(1+(d.G.rho k)^2)) • (p.1.2+d.G.rho k • p.1.1)),p.2))))
  fun_prop

theorem measurable_angleSeedCoordinates (d : Data (Fin D) m) (j : Fin m)
    (k : d.G.Kernel) : Measurable (angleSeedCoordinates d j k) := by
  have ho : Continuous (fun p : (E × E) × E => observationFromNoise d k p.1.1 p.2) :=
    (continuous_observationFromNoise d k).comp (continuous_fst.fst.prodMk continuous_snd)
  have hp : Measurable (fun p : (E × E) × E =>
      ((p.1.1,observationFromNoise d k p.1.1 p.2),p.1.2)) :=
    ((continuous_fst.fst.prodMk ho).prodMk continuous_fst.snd).measurable
  exact (continuous_angleObservationCoordinates d k).measurable.comp
    (hp.comp (backward_score_noise_preserving d j k).measurable)

theorem angleObservationCoordinates_independent (d : Data (Fin D) m) (k : d.G.Kernel)
    (u a c s : E) :
    angleObservationCoordinates d k
      ((d.G.rho k • u+Real.sqrt (d.G.variance k) •
          ((Real.sqrt (1+(d.G.rho k)^2))⁻¹ • (a+d.G.rho k • c)),
        u+Real.sqrt (d.G.variance k) •
          ((Real.sqrt (1+(d.G.rho k)^2))⁻¹ • (-d.G.rho k • a+c))),s) =
      (angleIndependentMidpoint d k (u,c),phaseMeasurableEquiv.symm (a,s)) := by
  have hden : 0 < 1+(d.G.rho k)^2 := by positivity
  have hn := (Real.sqrt_pos.mpr hden).ne'
  have hq := (d.G.rotationScale_pos k).ne'
  rw [← rotationScale_mul_sqrt d k]
  apply Prod.ext
  · dsimp [angleObservationCoordinates,angleIndependentMidpoint]
    simp only [smul_add,smul_smul]
    match_scalars <;> field_simp [hn,hden.ne']
    ring
  · dsimp [angleObservationCoordinates]
    congr 1
    apply Prod.ext
    · simp only [smul_add,smul_sub,smul_smul]
      match_scalars <;> field_simp [hn,hden.ne',hq] <;> ring
    · rfl
end AcceleratedLogConcave.Numerics.MeanFlowLp
