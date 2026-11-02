import AcceleratedLogConcave.Analysis.Poisson.ReferenceTransportFlow
import AcceleratedLogConcave.Kinetic.ReferenceFlow.TransportDerivative
import AcceleratedLogConcave.Kinetic.ReferenceFlow.CoreDerivative

/-! Smooth compact tests transported by the actual full flow and observed in
another actual flow frame. Both flows are constructed from their vector fields. -/
noncomputable section
open Set Function MeasureTheory Filter
open scoped NNReal Topology
open OAI.LogConcaveSampling.GlobalODE
namespace AcceleratedLogConcave.Kinetic
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [ProperSpace E]
  {a b : ℝ} (hab : a ≤ b)
  {v w : ℝ → E → E} (hv : Continuous (uncurry v)) (hw : Continuous (uncurry w))
  {K L : ℝ≥0} (hV : ∀ t ∈ Icc a b, LipschitzWith K (v t))
  (hW : ∀ t ∈ Icc a b, LipschitzWith L (w t))

def movingFrameCore (T : Icc a b) (φ : E → ℝ) (p : ℝ × E) : ℝ :=
  backwardTest hab hv hV T φ (spaceTimeForward hab hw hW p)

omit [ProperSpace E] in
theorem movingFrameCore_continuous (T : Icc a b) {φ : E → ℝ} (hφ : Continuous φ) :
    Continuous (movingFrameCore hab hv hw hV hW T φ) :=
  (backwardTest_continuous hab hv hV T hφ).comp (spaceTimeForward_continuous hab hw hW)

omit [ProperSpace E] in
theorem movingFrameCore_common_compact_support (T : Icc a b) {φ : E → ℝ}
    (hc : HasCompactSupport φ) :
    ∃ S : Set E, IsCompact S ∧ ∀ t x, x ∉ S → movingFrameCore hab hv hw hV hW T φ (t,x) = 0 := by
  obtain ⟨Q,hQ,hzero⟩ := backwardTest_common_compact_support hab hv hV T hc
  let S := (fun p : ℝ × E => (spaceTimeBackward hab hw hW p).2) '' (Icc a b ×ˢ Q)
  refine ⟨S, (isCompact_Icc.prod hQ).image (spaceTimeBackward_continuous hab hw hW).snd, ?_⟩
  intro t x hx
  let y := (spaceTimeForward hab hw hW (t,x)).2
  have hy : y ∉ Q := by
    intro hy
    apply hx
    refine ⟨((projIcc a b hab t : ℝ),y), ⟨(projIcc a b hab t).property,hy⟩, ?_⟩
    change flow hW hw (projIcc a b hab (projIcc a b hab t : ℝ)) y a = x
    rw [projIcc_of_mem _ (projIcc a b hab t).property]
    change flow hW hw (projIcc a b hab t)
      (flow hW hw ⟨a,le_rfl,hab⟩ x (projIcc a b hab t)) a = x
    exact (flow_cocycle hW hw ⟨a,le_rfl,hab⟩ (projIcc a b hab t) ⟨a,le_rfl,hab⟩ x).trans
      (flow_initial hW hw ⟨a,le_rfl,hab⟩ x)
  exact hzero t y hy

variable {Dv Dw : ℝ → E → E →L[ℝ] E}
  (hvD : Continuous (uncurry Dv)) (hwD : Continuous (uncurry Dw))
  (hvd : ∀ t x, HasFDerivAt (v t) (Dv t x) x)
  (hwd : ∀ t x, HasFDerivAt (w t) (Dw t x) x)

include hvD hwD hvd hwd in
theorem movingFrameCore_contDiffAt (T : Icc a b) {φ : E → ℝ}
    (hφ : ContDiff ℝ 1 φ) (p : ℝ × E) (hp : p.1 ∈ Ioo a b) :
    ContDiffAt ℝ 1 (movingFrameCore hab hv hw hV hW T φ) p :=
  (backwardTest_contDiffAt_one hab hv hV hvD hvd T hφ
    (spaceTimeForward hab hw hW p) hp).comp p
      (spaceTimeForward_contDiffAt_one hab hw hW hwD hwd p hp)

include hvD hvd in
/-- The actual pointwise material derivative is precisely the residual drift. -/
theorem movingFrameCore_hasDerivAt (T : Icc a b) {φ : E → ℝ}
    (hφ : Differentiable ℝ φ) (t : ℝ) (ht : t ∈ Ioo a b) (x : E) :
    HasDerivAt (fun u => movingFrameCore hab hv hw hV hW T φ (u,x))
      (fderiv ℝ (fun y => backwardTest hab hv hV T φ (t,y))
        (spaceTimeForward hab hw hW (t,x)).2
        (w t (spaceTimeForward hab hw hW (t,x)).2 - v t (spaceTimeForward hab hw hW (t,x)).2)) t :=
  backwardTest_along_hasDerivAt hab hv hV hvD hvd T hφ
    (fun u => (spaceTimeForward hab hw hW (u,x)).2) t ht _
    (spaceTimeForward_time_deriv hab hw hW (t,x) ht)

variable [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [IsProbabilityMeasure μ]

omit [ProperSpace E] in
theorem movingFrameCore_memLp (T : Icc a b) {φ : E → ℝ}
    (hφ : Continuous φ) (hc : HasCompactSupport φ) (t : ℝ) :
    MemLp (fun x => movingFrameCore hab hv hw hV hW T φ (t,x)) 2 μ := by
  obtain ⟨S,hS,hzero⟩ := movingFrameCore_common_compact_support hab hv hw hV hW T hc
  exact ((movingFrameCore_continuous hab hv hw hV hW T hφ).comp
    (continuous_const.prodMk continuous_id)).memLp_of_hasCompactSupport
      (HasCompactSupport.intro hS (hzero t))

/-- The actual L2 class of the backward-transported core test in the chosen frame. -/
def movingFrameCoreLp (T : Icc a b) {φ : E → ℝ}
    (hφ : Continuous φ) (hc : HasCompactSupport φ) (t : ℝ) : Lp ℝ 2 μ :=
  (movingFrameCore_memLp hab hv hw hV hW μ T hφ hc t).toLp _

include hvD hwD hvd hwd in
omit [MeasurableSpace E] [BorelSpace E] in
theorem movingFrameCore_time_deriv (T : Icc a b) {φ : E → ℝ}
    (hφ : ContDiff ℝ 1 φ) (t : ℝ) (ht : t ∈ Ioo a b) (x : E) :
    HasDerivAt (fun u => movingFrameCore hab hv hw hV hW T φ (u,x))
      (fderiv ℝ (movingFrameCore hab hv hw hV hW T φ) (t,x) (1,0)) t := by
  have hd := ((movingFrameCore_contDiffAt hab hv hw hV hW hvD hwD hvd hwd T hφ (t,x) ht).differentiableAt
    one_ne_zero).hasFDerivAt
  have hp : HasDerivAt (fun u : ℝ => (u,x)) (1,0) t :=
    (hasDerivAt_id t).prodMk (hasDerivAt_const t x)
  have hh := hd.comp_hasDerivAt t hp
  exact hh

include hvD hwD hvd hwd in
omit [MeasurableSpace E] [BorelSpace E] in
/-- The strong derivative's representative is the spatial derivative against
the actual drift difference, obtained by uniqueness of pointwise derivatives. -/
theorem movingFrameCore_derivative_eq (T : Icc a b) {φ : E → ℝ}
    (hφ : ContDiff ℝ 1 φ) (t : ℝ) (ht : t ∈ Ioo a b) (x : E) :
    fderiv ℝ (movingFrameCore hab hv hw hV hW T φ) (t,x) (1,0) =
      fderiv ℝ (fun y => backwardTest hab hv hV T φ (t,y))
        (spaceTimeForward hab hw hW (t,x)).2
        (w t (spaceTimeForward hab hw hW (t,x)).2 - v t (spaceTimeForward hab hw hW (t,x)).2) :=
  (movingFrameCore_time_deriv hab hv hw hV hW hvD hwD hvd hwd T hφ t ht x).unique
    (movingFrameCore_hasDerivAt hab hv hw hV hW hvD hvd T
      (hφ.differentiable one_ne_zero) t ht x)

include hvD hwD hvd hwd in
theorem movingFrameCore_derivative_memLp (T : Icc a b) {φ : E → ℝ}
    (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ) (t : ℝ) (ht : t ∈ Ioo a b) :
    MemLp (fun x => fderiv ℝ (movingFrameCore hab hv hw hV hW T φ) (t,x) (1,0)) 2 μ := by
  obtain ⟨S,hS,hzero⟩ := movingFrameCore_common_compact_support hab hv hw hV hW T hc
  have hcont : Continuous (fun x => fderiv ℝ (movingFrameCore hab hv hw hV hW T φ) (t,x) (1,0)) := by
    rw [continuous_iff_continuousAt]
    intro x
    exact (((movingFrameCore_contDiffAt hab hv hw hV hW hvD hwD hvd hwd T hφ (t,x) ht).continuousAt_fderiv one_ne_zero).clm_apply continuousAt_const).comp
      (continuous_const.prodMk continuous_id).continuousAt
  apply hcont.memLp_of_hasCompactSupport (HasCompactSupport.intro hS _)
  intro x hx
  have he : (fun u => movingFrameCore hab hv hw hV hW T φ (u,x)) = fun _ => (0 : ℝ) :=
    funext fun u => hzero u x hx
  have hd := movingFrameCore_time_deriv hab hv hw hV hW hvD hwD hvd hwd T hφ t ht x
  rw [he] at hd
  exact hd.unique (hasDerivAt_const t (0 : ℝ))

include hvD hwD hvd hwd in
/-- Strong L2 differentiation of the actual moving-frame smooth core. All
domination follows from the proved common compact support and joint C1 flow. -/
theorem movingFrameCoreLp_hasDerivAt (T : Icc a b) {φ : E → ℝ}
    (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ) (t : ℝ) (ht : t ∈ Ioo a b) :
    HasDerivAt (movingFrameCoreLp hab hv hw hV hW μ T hφ.continuous hc)
      ((movingFrameCore_derivative_memLp hab hv hw hV hW hvD hwD hvd hwd μ T hφ hc t ht).toLp _) t := by
  obtain ⟨S,hS,hzero⟩ := movingFrameCore_common_compact_support hab hv hw hV hW T hc
  apply hasDerivAt_L2_of_common_compact_support μ _ _
    (fun u x => movingFrameCore hab hv hw hV hW T φ (u,x))
    (fun u x => fderiv ℝ (movingFrameCore hab hv hw hV hW T φ) (u,x) (1,0)) ht
  · intro u
    exact (movingFrameCore_memLp hab hv hw hV hW μ T hφ.continuous hc u).coeFn_toLp
  · exact (movingFrameCore_derivative_memLp hab hv hw hV hW hvD hwD hvd hwd μ T hφ hc t ht).coeFn_toLp
  · intro p hp
    exact (((movingFrameCore_contDiffAt hab hv hw hV hW hvD hwD hvd hwd T hφ p hp.1).continuousAt_fderiv one_ne_zero).clm_apply continuousAt_const).continuousWithinAt
  · intro u hu x
    exact movingFrameCore_time_deriv hab hv hw hV hW hvD hwD hvd hwd T hφ u hu x
  · exact hS
  · intro u _ x hx
    exact hzero u x hx

end AcceleratedLogConcave.Kinetic
