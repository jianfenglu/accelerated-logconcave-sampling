import AcceleratedLogConcave.Numerics.CenterMeanPhaseJetBase
import AcceleratedLogConcave.Numerics.CenterMeanFirstReceiver

/-! Actual common-seed positive source ladder. The primitive split hypothesis
remains explicit until its independent analytic supplier is installed. -/
noncomputable section
open MeasureTheory
open scoped ContDiff
namespace AcceleratedLogConcave.Numerics.MeanFlowLp
open Tensor.Ordered.Graph CenterMeanSecondJetSource
variable {D m : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin D)

def centerMeanSourceJetLp (d : Data (Fin D) m) (L a : ℝ) {c R : ℝ}
    (hb : PhasePrimitiveBudgets (phaseCoefficients (kernelData d) L a)
      (phasePotential (kernelData d)) c R) (k : ℕ) (t : ℝ) : Lp E 2 (seedMeasure d) :=
  phasePullback d (sourceJetLp (kernelData d) L a (d.sigma/2) (half_pos d.hsigma) hb k t)

theorem centerMeanSourceJetLp_zero (d : Data (Fin D) m) (L a : ℝ)
    (hL : L ≠ 0) (ha : a ≠ 0) {c R : ℝ}
    (hb : PhasePrimitiveBudgets (phaseCoefficients (kernelData d) L a)
      (phasePotential (kernelData d)) c R) :
    centerMeanSourceJetLp d L a hb 0 = centerMeanFirstLp d := by
  funext t
  exact congrArg (fun f => phasePullback d (f t))
    (sourceJetLp_zero_eq_firstLp (kernelData d) L a (d.sigma/2) hL ha (half_pos d.hsigma) hb)

theorem hasDerivAt_centerMeanSourceJetLp (d : Data (Fin D) m) (L a : ℝ)
    (hL : L ≠ 0) {c R : ℝ}
    (hb : PhasePrimitiveBudgets (phaseCoefficients (kernelData d) L a)
      (phasePotential (kernelData d)) c R) (k : ℕ) (t : ℝ) :
    HasDerivAt (centerMeanSourceJetLp d L a hb k) (centerMeanSourceJetLp d L a hb (k+1) t) t :=
  (phasePullback d).hasFDerivAt.comp_hasDerivAt t
    (hasDerivAt_sourceJetLp (kernelData d) L a (d.sigma/2) hL (half_pos d.hsigma) hb k t)

theorem iteratedDeriv_centerMeanLp_from_primitives (d : Data (Fin D) m) (L a : ℝ)
    (hL : L ≠ 0) (ha : a ≠ 0) {c R : ℝ}
    (hb : PhasePrimitiveBudgets (phaseCoefficients (kernelData d) L a)
      (phasePotential (kernelData d)) c R) (k : ℕ) :
    iteratedDeriv (k+1) (centerMeanLp d) = centerMeanSourceJetLp d L a hb k := by
  induction k with
  | zero =>
    rw [Nat.zero_add,iteratedDeriv_one,centerMeanSourceJetLp_zero d L a hL ha hb]
    exact funext fun t => (hasDerivAt_centerMeanLp d t).deriv
  | succ k ih =>
    rw [iteratedDeriv_succ,ih]
    exact funext fun t => (hasDerivAt_centerMeanSourceJetLp d L a hL hb k t).deriv

theorem centerMeanLp_contDiff_from_primitives (d : Data (Fin D) m) (L a : ℝ)
    (hL : L ≠ 0) (ha : a ≠ 0) {c R : ℝ}
    (hb : PhasePrimitiveBudgets (phaseCoefficients (kernelData d) L a)
      (phasePotential (kernelData d)) c R) : ContDiff ℝ ∞ (centerMeanLp d) := by
  apply contDiff_of_differentiable_iteratedDeriv
  intro n _
  cases n with
  | zero =>
    rw [iteratedDeriv_zero]
    exact fun t => (hasDerivAt_centerMeanLp d t).differentiableAt
  | succ k =>
    rw [iteratedDeriv_centerMeanLp_from_primitives d L a hL ha hb k]
    exact fun t => (hasDerivAt_centerMeanSourceJetLp d L a hL hb k t).differentiableAt

end AcceleratedLogConcave.Numerics.MeanFlowLp
