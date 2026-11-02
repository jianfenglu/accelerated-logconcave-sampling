import AcceleratedLogConcave.Analysis.ActualAngleLpPullback
import AcceleratedLogConcave.Analysis.AngleNormalizedJetBudget
import AcceleratedLogConcave.Analysis.AnglePhaseOriginalScale
import AcceleratedLogConcave.Tensor.MeanFlowAngleZeroCurvature

/-! New original-data common-seed all-order angle L²/RMS endpoint.
No additional budget, environment, law, or regularity hypotheses are retained.
The physical amplitude is 2*(r^2*ell)*G.R, and the radius is exactly G.R.
Zero curvature is separated before normalization; no order-zero bound is claimed. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ContDiff
namespace AcceleratedLogConcave.Numerics.MeanFlowLp
open Analysis.AnglePhase Tensor.Ordered.Graph
variable {D m : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin D)
local notation "EP" => EuclideanSpace ℝ (Fin (D+D))

theorem actionLp_contDiff_original_data (d : Data (Fin D) m) (j : Fin m) (k : d.G.Kernel) :
    ContDiff ℝ ∞ (actionLp d j k) := by
  by_cases he : d.ell = 0
  · exact contDiff_actionLp_of_zero_curvature d he j k
  have hell : 0 < d.ell := lt_of_le_of_ne d.hell (Ne.symm he)
  have hr := d.hr
  have hR := d.G.R_pos
  let a := 2*(d.r^2*d.ell)*d.G.R
  have ha : a ≠ 0 := ne_of_gt (by dsimp [a]; positivity)
  have hb := actual_anglePrimitiveBudgets d k hell (d.G.rotationScale k) (d.G.rotationScale_pos k)
  have hi : actionLp d j k = fun t => angleLpPullback d j k a
      (displacementLp (angleMidpointLaw d k) (angleEndpoint d k) (d.G.rotationScale k) a
        (parameterDisplacement_memLp_original_data d j k a) t) :=
    funext (actionLp_eq_angleLpPullback d j k a ha)
  rw [hi]
  exact (angleLpPullback d j k a).contDiff.comp
    (contDiff_displacementLp (angleMidpointLaw d k) (angleEndpoint d k)
      (contDiff_angleEndpoint d k) (d.G.rotationScale k) a 256
      (radius d.G.R (d.G.rotationScale k)) (by norm_num)
      (radius_pos d.G.R_pos (d.G.rotationScale_pos k)) (radius_le_one _ _) hb
      (parameterDisplacement_memLp_original_data d j k a))

theorem norm_iteratedDeriv_actionLp_le_original_data (d : Data (Fin D) m)
    (j : Fin m) (k : d.G.Kernel) (n : ℕ) (t : ℝ) :
    ‖iteratedDeriv (n+1) (actionLp d j k) t‖ ≤
      (2*(d.r^2*d.ell)*d.G.R) *
      Real.sqrt (((D+D : ℕ) : ℝ) * Tensor.AdjointReduction.PhaseBudget.Q 256 (5*(n+1)+1)) *
      (2/d.G.R^2)^(n+1) := by
  by_cases he : d.ell = 0
  · rw [positive_actionLp_derivative_zero_of_zero_curvature d he j k n t]
    simp [he]
  have hell : 0 < d.ell := lt_of_le_of_ne d.hell (Ne.symm he)
  have hr := d.hr
  have hR := d.G.R_pos
  let q := d.G.rotationScale k
  let a := 2*(d.r^2*d.ell)*d.G.R
  let S := radius d.G.R q
  have ha0 : 0 < a := by dsimp [a]; positivity
  have ha := ne_of_gt ha0
  have hb := actual_anglePrimitiveBudgets d k hell q (d.G.rotationScale_pos k)
  let L := angleLpPullback d j k a
  let f := displacementLp (angleMidpointLaw d k) (angleEndpoint d k) q a
    (parameterDisplacement_memLp_original_data d j k a)
  let g := angleSourceJetLp (angleMidpointLaw d k) (angleEndpoint d k)
    (contDiff_angleEndpoint d k) q a 256 S (by norm_num)
    (radius_pos d.G.R_pos (d.G.rotationScale_pos k)) (radius_le_one _ _) hb
  have hf (u : ℝ) : HasDerivAt f (g 0 u) u :=
    hasDerivAt_displacementLp _ _ (contDiff_angleEndpoint d k) q a 256 S (by norm_num)
      (radius_pos d.G.R_pos (d.G.rotationScale_pos k)) (radius_le_one _ _) hb _ u
  have hg (l : ℕ) (u : ℝ) : HasDerivAt (g l) (g (l+1) u) u :=
    hasDerivAt_angleSourceJetLp _ _ (contDiff_angleEndpoint d k) q a 256 S (by norm_num)
      (radius_pos d.G.R_pos (d.G.rotationScale_pos k)) (radius_le_one _ _) hb l u
  have hi : actionLp d j k = fun u => L (f u) :=
    funext (actionLp_eq_angleLpPullback d j k a ha)
  have hj (l : ℕ) : iteratedDeriv (l+1) (actionLp d j k) = fun u => L (g l u) := by
    induction l with
    | zero =>
      rw [Nat.zero_add,iteratedDeriv_one,hi]
      exact funext fun u => (L.hasFDerivAt.comp_hasDerivAt u (hf u)).deriv
    | succ l ih =>
      rw [iteratedDeriv_succ,ih]
      exact funext fun u => (L.hasFDerivAt.comp_hasDerivAt u (hg l u)).deriv
  rw [hj]
  have hnorm := norm_angleLpPullback_apply_le d j k a (g n t)
  rw [Real.norm_eq_abs,abs_of_pos ha0] at hnorm
  have hbudget := norm_angleSourceJetLp_normalized_le (angleMidpointLaw d k)
    (angleEndpoint d k) (contDiff_angleEndpoint d k) q a d.G.R d.G.R_pos
    (d.G.rotationScale_pos k) (original_normalized_speed_le d.G k) hb n t
  have h := hnorm.trans (mul_le_mul_of_nonneg_left hbudget ha0.le)
  simpa only [L,a,mul_assoc] using h
end AcceleratedLogConcave.Numerics.MeanFlowLp
