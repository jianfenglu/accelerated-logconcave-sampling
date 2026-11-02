import AcceleratedLogConcave.Numerics.SmoothBackwardKernelReplacement
import AcceleratedLogConcave.Numerics.SmoothConditionalReplacement
import AcceleratedLogConcave.Numerics.SmoothForwardReplacement

/-! One original-data receiver carrying all four proved smooth branch fields.
This is an algebraic assembly, not a full quantitative Regularity theorem. -/
noncomputable section
open Set MeasureTheory
open scoped ContDiff Topology
set_option autoImplicit false
set_option maxHeartbeats 250000
namespace AcceleratedLogConcave.Numerics.MeanResidualBridge
open MeanFlowLp AffineGraph AffineGraph.MeanGeometry

section Algebraic
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  {m : ℕ} (G : MeanGeometry m) (C : AffineResidual.Mean.Curves G X)
  (D : Fin m → G.Kernel → ℝ → X) (F : Fin m → G.Kernel → ℝ → ℝ → X)
  (hD : ∀ j k t, t ∈ Icc 0 conditionalEnd → D j k t = C.conditional j k t)
  (hF : ∀ j k z t, t ∈ Icc 0 (backwardEnd G.R) → F j k z t = C.forward j k z t)

include hD in
private theorem branches_conditional_eq (U : X → ℝ → X) (x : X) (r : ℝ)
    (j : Fin m) (k : G.Kernel) {t : ℝ} (ht : t ∈ Icc 0 conditionalEnd) :
    ({ C with conditional := D, forward := F } : AffineResidual.Mean.Curves G X).conditionalMean
      G U x r j k t = C.conditionalMean G U x r j k t := by
  change U (x+(r*G.rho k) • C.backward j (G.rho k)+
    (r*Real.sqrt (G.variance k)*t) • D j k t) _ = _
  rw [hD j k t ht]
  rfl

include hD in
private theorem branches_rotation_eq (j : Fin m) (k : G.Kernel) (z : ℝ) :
    ({ C with conditional := D, forward := F } : AffineResidual.Mean.Curves G X).rotation
      G j k z = C.rotation G j k z := by
  simp only [AffineResidual.Mean.Curves.rotation,
    hD j k conditionalEnd ⟨conditionalEnd_pos.le,le_rfl⟩]

include hF in
private theorem branches_forward_eq (U : X → ℝ → X) (x : X) (r : ℝ)
    (j : Fin m) (k : G.Kernel) (z : ℝ) {t : ℝ} (ht : t ∈ Icc 0 (backwardEnd G.R)) :
    ({ C with conditional := D, forward := F } : AffineResidual.Mean.Curves G X).forwardMean
      G U x r j k z t = C.forwardMean G U x r j k z t := by
  change U (x+(r*t) • F j k z t) _ = _
  rw [hF j k z t ht]
  rfl

include hF in
private theorem branches_action_eq (U : X → ℝ → X) (x : X) (r : ℝ)
    (j : Fin m) (k : G.Kernel) (z : ℝ) :
    ({ C with conditional := D, forward := F } : AffineResidual.Mean.Curves G X).forwardAction
      G U x r j k z = C.forwardAction G U x r j k z := by
  unfold AffineResidual.Mean.Curves.forwardAction
  congr 1
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le (G.rho_mem k).2.le] at ht
  exact branches_forward_eq G C D F hF U x r j k z ⟨(G.rho_mem k).1.trans ht.1,ht.2⟩

include hD hF in
private theorem branches_reference_eq (x : X) (r : ℝ) :
    ({ C with conditional := D, forward := F } : AffineResidual.Mean.Curves G X).reference G x r =
      C.reference G x r := by
  funext i
  rcases i with _ | j | ⟨j,q⟩ | ⟨j,⟨k,q⟩⟩ | ⟨j,⟨k,z,q⟩⟩
  · rfl
  · rfl
  · rfl
  · have ht := (G.conditional k).location_mem_interval m q
    change x+(r*G.rho k) • C.backward j (G.rho k)+
      (r*Real.sqrt (G.variance k)*(G.conditional k).location m q) •
        D j k ((G.conditional k).location m q) = _
    rw [hD j k _ ⟨ht.1.le,ht.2.le⟩]
    rfl
  · have ht := (G.forward k).location_mem_interval m q
    change x+(r*(G.forward k).location m q) • F j k (G.angleNode z)
      ((G.forward k).location m q) = _
    rw [hF j k (G.angleNode z) _ ⟨(G.rho_mem k).1.trans ht.1.le,ht.2.le⟩]
    rfl

include hD hF in
private theorem branches_equations (U : X → ℝ → X) (r σ : ℝ)
    (x y0 g0 : X) (ζ : Fin m → G.Kernel → X)
    (h : AffineResidual.Mean.Equations G C U r σ x y0 g0 ζ) :
    AffineResidual.Mean.Equations G { C with conditional := D, forward := F }
      U r σ x y0 g0 ζ := by
  refine ⟨h.position,h.score,h.backward,?_,?_,?_,h.velocity_kernel⟩
  · intro j k t ht
    have hi : (∫ u in 0..t,
        ({ C with conditional := D, forward := F } : AffineResidual.Mean.Curves G X).conditionalMean
          G U x r j k u) = ∫ u in 0..t, C.conditionalMean G U x r j k u := by
      apply intervalIntegral.integral_congr
      intro u hu
      rw [uIcc_of_le ht.1] at hu
      exact branches_conditional_eq G C D F hD U x r j k ⟨hu.1,hu.2.trans ht.2⟩
    change D j k t = ζ j k - (r*Real.sqrt (G.variance k)) • _
    rw [hD j k t ht,hi]
    exact h.conditional j k t ht
  · intro j k z t hz ht
    have hi : (∫ u in G.rho k..t,
        ({ C with conditional := D, forward := F } : AffineResidual.Mean.Curves G X).forwardMean
          G U x r j k z u) = ∫ u in G.rho k..t, C.forwardMean G U x r j k z u := by
      apply intervalIntegral.integral_congr
      intro u hu
      rw [uIcc_of_le ht.1] at hu
      exact branches_forward_eq G C D F hF U x r j k z
        ⟨(G.rho_mem k).1.trans hu.1,hu.2.trans ht.2⟩
    change F j k z t = _
    rw [hF j k z t ⟨(G.rho_mem k).1.trans ht.1,ht.2⟩,
      branches_rotation_eq G C D F hD,hi]
    exact h.forward j k z t hz ht
  · intro j k
    rw [funext (branches_action_eq G C D F hF U x r j k)]
    exact h.kernel_angle j k

private theorem backwardMean_eq_of_field (C' : AffineResidual.Mean.Curves G X)
    (hB : C.backward = C'.backward) (U : X → ℝ → X) (x : X) (r : ℝ) :
    C.backwardMean G U x r = C'.backwardMean G U x r := by
  funext j t
  simp only [AffineResidual.Mean.Curves.backwardMean,hB]

private theorem conditionalMean_eq_of_fields (C' : AffineResidual.Mean.Curves G X)
    (hB : ∀ j k, C.backward j (G.rho k) = C'.backward j (G.rho k))
    (hC : C.conditional = C'.conditional) (U : X → ℝ → X) (x : X) (r : ℝ) :
    C.conditionalMean G U x r = C'.conditionalMean G U x r := by
  funext j k t
  simp only [AffineResidual.Mean.Curves.conditionalMean,hB j k,hC]

private theorem forwardMean_eq_of_field (C' : AffineResidual.Mean.Curves G X)
    (hF' : C.forward = C'.forward) (U : X → ℝ → X) (x : X) (r : ℝ) :
    C.forwardMean G U x r = C'.forwardMean G U x r := by
  funext j k z t
  simp only [AffineResidual.Mean.Curves.forwardMean,hF']

private theorem action_eq_of_field (C' : AffineResidual.Mean.Curves G X)
    (hF' : C.forward = C'.forward) (U : X → ℝ → X) (x : X) (r : ℝ) :
    C.forwardAction G U x r = C'.forwardAction G U x r := by
  funext j k z
  simp only [AffineResidual.Mean.Curves.forwardAction,AffineResidual.Mean.Curves.forwardMean,hF']

private theorem rotation_eq_of_samples (C' : AffineResidual.Mean.Curves G X)
    (hB : ∀ j k, C.backward j (G.rho k) = C'.backward j (G.rho k))
    (hC : ∀ j k, C.conditional j k conditionalEnd = C'.conditional j k conditionalEnd)
    (hS : C.score = C'.score) : C.rotation G = C'.rotation G := by
  funext j k z
  simp only [AffineResidual.Mean.Curves.rotation,hB j k,hC j k,hS]
end Algebraic

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ}

def curvesWithSmoothBranches (d : Data ι m) : AffineResidual.Mean.Curves d.G (H d) :=
  { curvesWithBackwardKernel d with conditional := smoothConditional d, forward := smoothForward d }

theorem smoothBranches_equations (d : Data ι m) (U : H d → ℝ → H d)
    (hu : PrimitiveSpec (primitiveData d) (seedMeasure d) U) :
    AffineResidual.Mean.Equations d.G (curvesWithSmoothBranches d) U d.r d.sigma 0
      (initialPosition d) (initialScore d) (initialNoise d) :=
  branches_equations d.G (curvesWithBackwardKernel d) (smoothConditional d) (smoothForward d)
    (fun j k _ ht => smoothConditional_eq d j k ht)
    (fun j k z _ ht => smoothForward_eq d j k z ht) U d.r d.sigma 0
    (initialPosition d) (initialScore d) (initialNoise d) (backwardKernel_equations d U hu)

theorem smoothBranches_canonical_equations (d : Data ι m) :
    AffineResidual.Mean.Equations d.G (curvesWithSmoothBranches d)
      (primitiveLp (primitiveData d) (seedMeasure d)) d.r d.sigma 0
      (initialPosition d) (initialScore d) (initialNoise d) :=
  smoothBranches_equations d _ (primitiveLp_spec _ _)

theorem smoothBranches_reference_eq (d : Data ι m) :
    (curvesWithSmoothBranches d).reference d.G 0 d.r = (curves d).reference d.G 0 d.r :=
  (branches_reference_eq d.G (curvesWithBackwardKernel d) (smoothConditional d) (smoothForward d)
    (fun j k _ ht => smoothConditional_eq d j k ht)
    (fun j k z _ ht => smoothForward_eq d j k z ht) 0 d.r).trans (backwardKernel_reference_eq d)

theorem smoothBranches_meanOutput_eq (d : Data ι m) (U : H d → ℝ → H d) :
    d.G.meanOutput d.sigma (initialScore d)
      (fun i => U ((curvesWithSmoothBranches d).reference d.G 0 d.r i) (d.G.radius d.r i)) =
    d.G.meanOutput d.sigma (initialScore d)
      (fun i => U ((curves d).reference d.G 0 d.r i) (d.G.radius d.r i)) := by
  rw [smoothBranches_reference_eq]

/-- These are whole-function equalities, not just closed-slab agreement. -/
theorem smoothBranches_backwardMean_eq (d : Data ι m) (U : H d → ℝ → H d) :
    (curvesWithSmoothBranches d).backwardMean d.G U 0 d.r =
      (curvesWithBackward d).backwardMean d.G U 0 d.r :=
  backwardMean_eq_of_field d.G (curvesWithSmoothBranches d) (curvesWithBackward d) rfl U 0 d.r

theorem smoothBranches_conditionalMean_eq (d : Data ι m) (U : H d → ℝ → H d) :
    (curvesWithSmoothBranches d).conditionalMean d.G U 0 d.r =
      (curvesWithConditional d).conditionalMean d.G U 0 d.r :=
  conditionalMean_eq_of_fields d.G (curvesWithSmoothBranches d) (curvesWithConditional d)
    (fun j k => smoothBackward_eq d j ⟨(d.G.rho_mem k).1,(d.G.rho_mem k).2.le⟩) rfl U 0 d.r

theorem smoothBranches_forwardMean_eq (d : Data ι m) (U : H d → ℝ → H d) :
    (curvesWithSmoothBranches d).forwardMean d.G U 0 d.r =
      (curvesWithForward d).forwardMean d.G U 0 d.r :=
  forwardMean_eq_of_field d.G (curvesWithSmoothBranches d) (curvesWithForward d) rfl U 0 d.r

theorem smoothBranches_rotation_eq (d : Data ι m) :
    (curvesWithSmoothBranches d).rotation d.G = (curves d).rotation d.G :=
  rotation_eq_of_samples d.G (curvesWithSmoothBranches d) (curves d)
    (fun j k => smoothBackward_eq d j ⟨(d.G.rho_mem k).1,(d.G.rho_mem k).2.le⟩)
    (fun j k => smoothConditional_eq d j k ⟨conditionalEnd_pos.le,le_rfl⟩) rfl

theorem smoothBranches_forwardAction_eq (d : Data ι m) (U : H d → ℝ → H d)
    (j : Fin m) (k : d.G.Kernel) (z : ℝ) :
    (curvesWithSmoothBranches d).forwardAction d.G U 0 d.r j k z =
      (curves d).forwardAction d.G U 0 d.r j k z := by
  have h := action_eq_of_field d.G (curvesWithSmoothBranches d) (curvesWithForward d) rfl U 0 d.r
  exact (congrFun (congrFun (congrFun h j) k) z).trans
    (smoothForwardReplacement_forwardAction_eq d U j k z)

theorem smoothBranches_contDiffAt_backwardMean (d : Data ι m) (U : H d → ℝ → H d)
    (hu : PrimitiveSpec (primitiveData d) (seedMeasure d) U) (j : Fin m) (n : ℕ) {t : ℝ}
    (ht : t ∈ Icc 0 (backwardEnd d.G.R)) :
    ContDiffAt ℝ n ((curvesWithSmoothBranches d).backwardMean d.G U 0 d.r j) t := by
  rw [smoothBranches_backwardMean_eq]
  exact contDiffAt_replacement_backwardMean d U hu j n ht

theorem smoothBranches_contDiffAt_conditionalMean (d : Data ι m) (U : H d → ℝ → H d)
    (hu : PrimitiveSpec (primitiveData d) (seedMeasure d) U) (j : Fin m) (k : d.G.Kernel)
    (n : ℕ) {t : ℝ} (ht : t ∈ Icc 0 conditionalEnd) :
    ContDiffAt ℝ n ((curvesWithSmoothBranches d).conditionalMean d.G U 0 d.r j k) t := by
  rw [smoothBranches_conditionalMean_eq]
  exact contDiffAt_replacement_conditionalMean d U hu j k n ht

theorem smoothBranches_contDiffAt_forwardMean (d : Data ι m) (U : H d → ℝ → H d)
    (hu : PrimitiveSpec (primitiveData d) (seedMeasure d) U) (j : Fin m) (k : d.G.Kernel)
    (z : ℝ) (n : ℕ) {t : ℝ} (ht : t ∈ Icc 0 (backwardEnd d.G.R)) :
    ContDiffAt ℝ n ((curvesWithSmoothBranches d).forwardMean d.G U 0 d.r j k z) t := by
  rw [smoothBranches_forwardMean_eq]
  exact smoothForwardReplacement_contDiffAt_forwardMean d U hu j k z n ht

theorem smoothBranches_position_eq (d : Data ι m) :
    (curvesWithSmoothBranches d).position = (curves d).position := rfl

theorem smoothBranches_score_eq (d : Data ι m) :
    (curvesWithSmoothBranches d).score = (curves d).score := rfl

theorem smoothBranches_velocity_eq (d : Data ι m) :
    (curvesWithSmoothBranches d).velocity = (curves d).velocity := rfl

theorem smoothBranches_kernel_eq (d : Data ι m) :
    (curvesWithSmoothBranches d).kernel = smoothKernel d := rfl

end AcceleratedLogConcave.Numerics.MeanResidualBridge
