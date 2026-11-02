import AcceleratedLogConcave.Analysis.SpatialVariationCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!

-/
noncomputable section
set_option autoImplicit false
open Set Metric Filter MeasureTheory
open scoped Topology ContDiff
namespace AcceleratedLogConcave.Analysis.SpatialVariation
variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Positive slab: uniqueness of the WITHIN time derivative identifies the
representative's actual time derivative with the original zeroth-order RHS. -/
theorem representative_time_eq {Y R : ℝ → E → V} {C : ℝ × E → V}
    {b : ℝ} (hb : 0 < b) (hC : ContDiff ℝ ∞ C) (y : E)
    (hCY : ∀ s ∈ Icc 0 b, ∀ z ∈ ball y 1, C (s,z) = Y s z)
    (hODE : ∀ s ∈ Icc 0 b, ∀ z ∈ ball y 1,
      HasDerivWithinAt (fun u => Y u z) (R s z) (Icc 0 b) s)
    {s : ℝ} (hs : s ∈ Icc 0 b) {z : E} (hz : z ∈ ball y 1) :
    fderiv ℝ C (s,z) (1,0) = R s z := by
  have hd := (hC.differentiable (by simp) (s,z)).hasFDerivAt.comp_hasDerivAt s
    ((hasDerivAt_id s).prodMk (hasDerivAt_const s z))
  have ha := (hODE s hs z hz).congr_of_mem (fun u hu => hCY u hu z hz) hs
  have hdw : HasDerivWithinAt (fun u => C (u,z))
      (fderiv ℝ C (s,z) (1,0)) (Icc 0 b) s := hd.hasDerivWithinAt
  exact (hdw.derivWithin (uniqueDiffOn_Icc hb s hs)).symm.trans
    (ha.derivWithin (uniqueDiffOn_Icc hb s hs))

/-- Exact vector-valued Volterra identity for arbitrary fixed spatial lists.
The representative is local only in space but valid on the whole closed slab.
The singleton slab is handled without derivative uniqueness or division by b. -/
theorem along_volterra_of_local_representative [CompleteSpace V]
    {Y R : ℝ → E → V} {C : ℝ × E → V} {b : ℝ} (hb : 0 ≤ b)
    (hC : ContDiff ℝ ∞ C) (y : E)
    (hCY : ∀ s ∈ Icc 0 b, ∀ z ∈ ball y 1, C (s,z) = Y s z)
    (hODE : ∀ s ∈ Icc 0 b, ∀ z ∈ ball y 1,
      HasDerivWithinAt (fun u => Y u z) (R s z) (Icc 0 b) s)
    (J : List E) {t : ℝ} (ht : t ∈ Icc 0 b) :
    along J (Y t) y = along J (Y b) y - ∫ s in t..b, along J (R s) y := by
  by_cases hbpos : 0 < b
  · let A : ℝ → V := fun s => along J (fun z => C (s,z)) y
    let Q : ℝ → V := fun s => along J (fun z => fderiv ℝ C (s,z) (1,0)) y
    have hD : ContDiff ℝ ∞ (fun p : ℝ × E => fderiv ℝ C p (1,0)) :=
      (hC.fderiv_right (by simp)).clm_apply contDiff_const
    have hQ : Continuous Q := by
      have he : Q = fun s => jointAlong J (fun p => fderiv ℝ C p (1,0)) (s,y) := by
        funext s
        exact (congrFun (jointAlong_slice J hD s) y).symm
      rw [he]
      exact (contDiff_jointAlong J hD).continuous.comp
        (continuous_id.prodMk continuous_const)
    have hAeq (s : ℝ) (hs : s ∈ Icc 0 b) : A s = along J (Y s) y := by
      apply (along_eventuallyEq (J := J) ?_).eq_of_nhds
      filter_upwards [Metric.ball_mem_nhds y (by norm_num : (0:ℝ) < 1)] with z hz
      exact hCY s hs z hz
    have hQeq (s : ℝ) (hs : s ∈ Icc 0 b) : Q s = along J (R s) y := by
      apply (along_eventuallyEq (J := J) ?_).eq_of_nhds
      filter_upwards [Metric.ball_mem_nhds y (by norm_num : (0:ℝ) < 1)] with z hz
      exact representative_time_eq hbpos hC y hCY hODE hs hz
    have hFTC : (∫ s in t..b, Q s) = A b - A t :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun s _ => hasDerivAt_along_slice J hC s y) (hQ.intervalIntegrable t b)
    have hi : (∫ s in t..b, Q s) = ∫ s in t..b, along J (R s) y := by
      apply intervalIntegral.integral_congr
      intro s hs
      rw [uIcc_of_le ht.2] at hs
      exact hQeq s ⟨ht.1.trans hs.1, hs.2⟩
    rw [hi, hAeq b ⟨hb,le_rfl⟩, hAeq t ht] at hFTC
    exact (eq_sub_iff_add_eq).2 (by rw [hFTC]; abel)
  · have hbzero : b = 0 := le_antisymm (not_lt.mp hbpos) hb
    subst b
    have htzero : t = 0 := le_antisymm ht.2 ht.1
    subst t
    simp only [intervalIntegral.integral_same, sub_zero]

/-- A continuous linear output readout commutes with every ordered spatial jet. -/
theorem along_clm {f : E → V} (hf : ContDiff ℝ ∞ f)
    (L : V →L[ℝ] ℝ) (J : List E) :
    along J (fun z => L (f z)) = fun z => L (along J f z) := by
  induction J with
  | nil => rfl
  | cons v J ih =>
    funext y
    change fderiv ℝ (along J (fun z => L (f z))) y v = _
    rw [ih]
    have hd := L.hasFDerivAt.comp y
      ((contDiff_along J hf).differentiable (by simp) y).hasFDerivAt
    exact congrArg (fun T : E →L[ℝ] ℝ => T v) hd.fderiv

/-- Scalar readout version: all output coordinates can be selected independently.
No interchange premise is assumed: apply the same representative argument to L C. -/
theorem along_volterra_readout
    {Y R : ℝ → E → V} {C : ℝ × E → V} {b : ℝ} (hb : 0 ≤ b)
    (hC : ContDiff ℝ ∞ C) (y : E)
    (hCY : ∀ s ∈ Icc 0 b, ∀ z ∈ ball y 1, C (s,z) = Y s z)
    (hODE : ∀ s ∈ Icc 0 b, ∀ z ∈ ball y 1,
      HasDerivWithinAt (fun u => Y u z) (R s z) (Icc 0 b) s)
    (L : V →L[ℝ] ℝ) (J : List E) {t : ℝ} (ht : t ∈ Icc 0 b) :
    along J (fun z => L (Y t z)) y = along J (fun z => L (Y b z)) y -
      ∫ s in t..b, along J (fun z => L (R s z)) y := by
  exact along_volterra_of_local_representative hb (L.contDiff.comp hC) y
    (fun s hs z hz => congrArg L (hCY s hs z hz))
    (fun s hs z hz => L.hasFDerivAt.comp_hasDerivWithinAt s (hODE s hs z hz)) J ht

end AcceleratedLogConcave.Analysis.SpatialVariation
