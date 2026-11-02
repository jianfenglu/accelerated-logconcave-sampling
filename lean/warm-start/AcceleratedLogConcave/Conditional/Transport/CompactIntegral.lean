import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-! Smoothness of finite-interval integrals from compact local domination. -/
noncomputable section
open Set Metric MeasureTheory Filter
open scoped Topology ContDiff
namespace AcceleratedLogConcave.Conditional.Transport

universe u
variable {H G : Type u} [NormedAddCommGroup H] [NormedSpace ℝ H] [FiniteDimensional ℝ H]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]

def spatialPartialDerivative (F : ℝ × H → G) (p : ℝ × H) : H →L[ℝ] G :=
  (fderiv ℝ F p).comp (ContinuousLinearMap.inr ℝ ℝ H)

omit [FiniteDimensional ℝ H] [CompleteSpace G] in
lemma contDiff_spatialPartialDerivative {F : ℝ × H → G} (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (spatialPartialDerivative F) :=
  (hF.fderiv_right (by simp)).clm_comp contDiff_const

omit [FiniteDimensional ℝ H] [CompleteSpace G] in
lemma hasFDerivAt_spatialPartialDerivative {F : ℝ × H → G} (hF : ContDiff ℝ ∞ F)
    (t : ℝ) (x : H) : HasFDerivAt (fun y => F (t,y)) (spatialPartialDerivative F (t,x)) x := by
  exact (hF.differentiable (by simp) (t,x)).hasFDerivAt.comp x
    ((hasFDerivAt_const (𝕜 := ℝ) t x).prodMk (hasFDerivAt_id x))

omit [CompleteSpace G] in
lemma hasFDerivAt_intervalIntegral_of_contDiff {F : ℝ × H → G} (hF : ContDiff ℝ ∞ F)
    {a b : ℝ} (hab : a ≤ b) (x : H) :
    HasFDerivAt (fun y => ∫ t in a..b, F (t,y))
      (∫ t in a..b, spatialPartialDerivative F (t,x)) x := by
  let D := spatialPartialDerivative F
  have hD : Continuous D := (contDiff_spatialPartialDerivative hF).continuous
  obtain ⟨M,hM⟩ := (isCompact_Icc.prod (isCompact_closedBall x 1)).exists_bound_of_continuousOn
    hD.continuousOn
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le''
    (s := ball x 1) (bound := fun _ => M) (ball_mem_nhds x (by norm_num))
  · exact Filter.Eventually.of_forall (fun y =>
      (hF.continuous.comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable)
  · exact (hF.continuous.comp (continuous_id.prodMk continuous_const)).intervalIntegrable _ _
  · exact (hD.comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_uIoc] with t ht
    have ht' : t ∈ Icc a b := by
      rw [uIoc_of_le hab] at ht
      exact ⟨ht.1.le,ht.2⟩
    intro y hy
    exact hM (t,y) ⟨ht',mem_closedBall.mpr (mem_ball.mp hy).le⟩
  · exact intervalIntegrable_const
  · exact Filter.Eventually.of_forall (fun t y _ => hasFDerivAt_spatialPartialDerivative hF t y)

theorem contDiff_intervalIntegral (n : ℕ) :
    ∀ {H G : Type u} [NormedAddCommGroup H] [NormedSpace ℝ H] [FiniteDimensional ℝ H]
      [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
      {F : ℝ × H → G} (_hF : ContDiff ℝ ∞ F) {a b : ℝ} (_hab : a ≤ b),
      ContDiff ℝ n (fun x => ∫ t in a..b, F (t,x)) := by
  induction n with
  | zero =>
    intro H G _ _ _ _ _ _ F hF a b hab
    apply contDiff_zero.mpr
    exact continuous_iff_continuousAt.mpr (fun x =>
      (hasFDerivAt_intervalIntegral_of_contDiff hF hab x).continuousAt)
  | succ n ih =>
    intro H G _ _ _ _ _ _ F hF a b hab
    rw [show ((n+1:ℕ) : WithTop ℕ∞) = (n : WithTop ℕ∞)+1 by simp]
    apply contDiff_succ_iff_fderiv.mpr
    refine ⟨fun x => (hasFDerivAt_intervalIntegral_of_contDiff hF hab x).differentiableAt,by simp,?_⟩
    have heq : fderiv ℝ (fun x => ∫ t in a..b, F (t,x)) =
        fun x => ∫ t in a..b, spatialPartialDerivative F (t,x) :=
      funext (fun x => (hasFDerivAt_intervalIntegral_of_contDiff hF hab x).fderiv)
    rw [heq]
    exact ih (contDiff_spatialPartialDerivative hF) hab

theorem contDiff_infty_intervalIntegral {F : ℝ × H → G} (hF : ContDiff ℝ ∞ F)
    {a b : ℝ} (hab : a ≤ b) : ContDiff ℝ ∞ (fun x => ∫ t in a..b, F (t,x)) :=
  contDiff_infty.mpr (fun n => contDiff_intervalIntegral n hF hab)

end AcceleratedLogConcave.Conditional.Transport
