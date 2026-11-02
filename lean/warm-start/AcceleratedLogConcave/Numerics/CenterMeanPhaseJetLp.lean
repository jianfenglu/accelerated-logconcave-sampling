import AcceleratedLogConcave.Numerics.CenterMeanPhaseJetSources
import AcceleratedLogConcave.Numerics.CenterMeanStationaryFTC

/-! Genuine stationary L² jet ladder, conditional only on the explicitly named
primitive rectangular split supplier. This does not assert that supplier. -/
noncomputable section
open MeasureTheory
open scoped ContDiff
namespace AcceleratedLogConcave.Numerics.CenterMeanSecondJetSource
open Conditional CenteringFlowLp Tensor.Ordered.Graph
variable {D : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin D)
local notation "P" => WithLp 2 (E × E)

theorem hasDerivAt_seedSourceJet (d : Data (Fin D)) (L a s : ℝ)
    (hL : L ≠ 0) (hs : 0 < s) (k : ℕ) (z : P) (t : ℝ) :
    HasDerivAt (fun u => seedSourceJet d L a s k (phase d s hs u z))
      (seedSourceJet d L a s (k+1) (phase d s hs t z)) t := by
  simpa only [seedSourceJet,phaseOrbit,LinearIsometryEquiv.apply_symm_apply] using
    hasDerivAt_phaseSourceJet d L a s hL hs k (phaseCoordinateEquiv.symm z) t

def sourceJetLp (d : Data (Fin D)) (L a s : ℝ) (hs : 0 < s) {c R : ℝ}
    (hb : PhasePrimitiveBudgets (phaseCoefficients d L a) (phasePotential d) c R)
    (k : ℕ) (t : ℝ) : Lp E 2 (seedMeasure d) :=
  CenterMeanStationaryLp.orbit d s hs
    ((seedSourceJet_memLp d L a s hb k).toLp (seedSourceJet d L a s k)) t

theorem continuous_sourceJetLp (d : Data (Fin D)) (L a s : ℝ) (hs : 0 < s) {c R : ℝ}
    (hb : PhasePrimitiveBudgets (phaseCoefficients d L a) (phasePotential d) c R) (k : ℕ) :
    Continuous (sourceJetLp d L a s hs hb k) :=
  CenterMeanStationaryLp.continuous_orbit d s hs _

theorem hasDerivAt_sourceJetLp (d : Data (Fin D)) (L a s : ℝ)
    (hL : L ≠ 0) (hs : 0 < s) {c R : ℝ}
    (hb : PhasePrimitiveBudgets (phaseCoefficients d L a) (phasePotential d) c R)
    (k : ℕ) (t : ℝ) :
    HasDerivAt (sourceJetLp d L a s hs hb k) (sourceJetLp d L a s hs hb (k+1) t) t :=
  CenterMeanStationaryLp.hasDerivAt_orbit_of_source d s hs
    (seedSourceJet d L a s k) (seedSourceJet d L a s (k+1))
    (seedSourceJet_memLp d L a s hb k) (seedSourceJet_memLp d L a s hb (k+1))
    (seedSourceJet_contDiff d L a s (k+1)).continuous
    (fun t z => hasDerivAt_seedSourceJet d L a s hL hs k z t) t

theorem iteratedDeriv_sourceJetLp (d : Data (Fin D)) (L a s : ℝ)
    (hL : L ≠ 0) (hs : 0 < s) {c R : ℝ}
    (hb : PhasePrimitiveBudgets (phaseCoefficients d L a) (phasePotential d) c R)
    (k n : ℕ) :
    iteratedDeriv n (sourceJetLp d L a s hs hb k) = sourceJetLp d L a s hs hb (k+n) := by
  induction n with
  | zero => simp only [iteratedDeriv_zero,Nat.add_zero]
  | succ n ih =>
    rw [iteratedDeriv_succ,ih]
    funext t
    exact (hasDerivAt_sourceJetLp d L a s hL hs hb (k+n) t).deriv

theorem contDiff_sourceJetLp (d : Data (Fin D)) (L a s : ℝ)
    (hL : L ≠ 0) (hs : 0 < s) {c R : ℝ}
    (hb : PhasePrimitiveBudgets (phaseCoefficients d L a) (phasePotential d) c R) (k : ℕ) :
    ContDiff ℝ ∞ (sourceJetLp d L a s hs hb k) := by
  apply contDiff_of_differentiable_iteratedDeriv
  intro n _
  rw [iteratedDeriv_sourceJetLp d L a s hL hs hb k n]
  intro t
  exact (hasDerivAt_sourceJetLp d L a s hL hs hb (k+n) t).differentiableAt

end AcceleratedLogConcave.Numerics.CenterMeanSecondJetSource
