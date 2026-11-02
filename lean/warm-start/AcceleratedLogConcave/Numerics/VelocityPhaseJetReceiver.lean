import AcceleratedLogConcave.Numerics.VelocityPhaseJetBase
import AcceleratedLogConcave.Numerics.MeanFlowLp

noncomputable section
open MeasureTheory
open scoped ContDiff
namespace AcceleratedLogConcave.Numerics.MeanFlowLp
open Tensor.Ordered.Graph CenterMeanSecondJetSource
variable {D m : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin D)

def velocitySourceJetLp (d : Data (Fin D) m) (L a : ℝ) {c R : ℝ}
    (hb : PhasePrimitiveBudgets (phaseCoefficients (kernelData d) L a)
      (phasePotential (kernelData d)) c R) (k : ℕ) (t : ℝ) : Lp E 2 (seedMeasure d) :=
  phasePullback d (velocityJetLp (kernelData d) L a (d.sigma/2) (half_pos d.hsigma) hb k t)

theorem velocitySourceJetLp_zero (d : Data (Fin D) m) (L a : ℝ)
    (hL : L ≠ 0) {c R : ℝ}
    (hb : PhasePrimitiveBudgets (phaseCoefficients (kernelData d) L a)
      (phasePotential (kernelData d)) c R) :
    velocitySourceJetLp d L a hb 0 = velocityLp d := by
  funext t
  rw [velocitySourceJetLp,velocityJetLp_zero_eq _ _ _ _ hL, map_smul,velocityLp_eq]

theorem hasDerivAt_velocitySourceJetLp (d : Data (Fin D) m) (L a : ℝ)
    (hL : L ≠ 0) {c R : ℝ}
    (hb : PhasePrimitiveBudgets (phaseCoefficients (kernelData d) L a)
      (phasePotential (kernelData d)) c R) (k : ℕ) (t : ℝ) :
    HasDerivAt (velocitySourceJetLp d L a hb k) (velocitySourceJetLp d L a hb (k+1) t) t :=
  (phasePullback d).hasFDerivAt.comp_hasDerivAt t
    (hasDerivAt_velocityJetLp (kernelData d) L a (d.sigma/2) hL (half_pos d.hsigma) hb k t)

theorem iteratedDeriv_velocityLp_from_primitives (d : Data (Fin D) m) (L a : ℝ)
    (hL : L ≠ 0) {c R : ℝ}
    (hb : PhasePrimitiveBudgets (phaseCoefficients (kernelData d) L a)
      (phasePotential (kernelData d)) c R) (k : ℕ) :
    iteratedDeriv k (velocityLp d) = velocitySourceJetLp d L a hb k := by
  induction k with
  | zero => simpa using (velocitySourceJetLp_zero d L a hL hb).symm
  | succ k ih =>
    rw [iteratedDeriv_succ,ih]
    exact funext fun t => (hasDerivAt_velocitySourceJetLp d L a hL hb k t).deriv

theorem velocityLp_contDiff_from_primitives (d : Data (Fin D) m) (L a : ℝ)
    (hL : L ≠ 0) {c R : ℝ}
    (hb : PhasePrimitiveBudgets (phaseCoefficients (kernelData d) L a)
      (phasePotential (kernelData d)) c R) : ContDiff ℝ ∞ (velocityLp d) := by
  rw [← velocitySourceJetLp_zero d L a hL hb]
  exact (phasePullback d).contDiff.comp
    (contDiff_velocityJetLp (kernelData d) L a (d.sigma/2) hL (half_pos d.hsigma) hb 0)

end AcceleratedLogConcave.Numerics.MeanFlowLp
