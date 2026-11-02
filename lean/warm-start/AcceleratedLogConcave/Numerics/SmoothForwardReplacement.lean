import AcceleratedLogConcave.Numerics.SmoothForward

/-! A forward-only endpoint-safe replacement of the actual original-data
receiver. The fixed-angle qualitative theorem asserts no angle or cell budget. -/
noncomputable section
open Set MeasureTheory
open scoped ContDiff Topology
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
namespace AcceleratedLogConcave.Numerics.MeanResidualBridge
open MeanFlowLp AffineGraph AffineGraph.MeanGeometry ConditionalSmoothing
open Analysis.PositiveVarianceSlab
section ForwardAlgebraic
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  {m : ℕ} (G : MeanGeometry m) (C : AffineResidual.Mean.Curves G X)
  (D : Fin m → G.Kernel → ℝ → ℝ → X)
  (hD : ∀ j k z t, t ∈ Icc 0 (backwardEnd G.R) → D j k z t = C.forward j k z t)
private theorem forwardReplacement_rotation_eq :
    ({ C with forward := D } : AffineResidual.Mean.Curves G X).rotation G = C.rotation G := rfl

include hD

private theorem forwardReplacement_mean_eq (U : X → ℝ → X) (x : X) (r : ℝ)
    (j : Fin m) (k : G.Kernel) (z : ℝ) {t : ℝ} (ht : t ∈ Icc 0 (backwardEnd G.R)) :
    ({ C with forward := D } : AffineResidual.Mean.Curves G X).forwardMean G U x r j k z t =
      C.forwardMean G U x r j k z t := by
  change U (x + (r*t) • D j k z t) _ = _
  rw [hD j k z t ht]
  rfl

private theorem forwardReplacement_action_eq (U : X → ℝ → X) (x : X) (r : ℝ)
    (j : Fin m) (k : G.Kernel) (z : ℝ) :
    ({ C with forward := D } : AffineResidual.Mean.Curves G X).forwardAction G U x r j k z =
      C.forwardAction G U x r j k z := by
  unfold AffineResidual.Mean.Curves.forwardAction
  congr 1
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le (G.rho_mem k).2.le] at ht
  exact forwardReplacement_mean_eq G C D hD U x r j k z
    ⟨(G.rho_mem k).1.trans ht.1,ht.2⟩

private theorem forwardReplacement_reference_eq (x : X) (r : ℝ) :
    ({ C with forward := D } : AffineResidual.Mean.Curves G X).reference G x r =
      C.reference G x r := by
  funext i
  rcases i with _ | j | ⟨j,q⟩ | ⟨j,⟨k,q⟩⟩ | ⟨j,⟨k,z,q⟩⟩
  · rfl
  · rfl
  · rfl
  · rfl
  · have ht := (G.forward k).location_mem_interval m q
    change x + (r*(G.forward k).location m q) • D j k (G.angleNode z)
      ((G.forward k).location m q) = _
    rw [hD j k (G.angleNode z) _ ⟨(G.rho_mem k).1.trans ht.1.le,ht.2.le⟩]
    rfl

private theorem forwardReplacement_equations (U : X → ℝ → X) (r σ : ℝ)
    (x y0 g0 : X) (ζ : Fin m → G.Kernel → X)
    (h : AffineResidual.Mean.Equations G C U r σ x y0 g0 ζ) :
    AffineResidual.Mean.Equations G { C with forward := D } U r σ x y0 g0 ζ := by
  refine ⟨h.position,h.score,h.backward,h.conditional,?_,?_,h.velocity_kernel⟩
  · intro j k z t hz ht
    have hi : (∫ u in G.rho k..t,
        ({ C with forward := D } : AffineResidual.Mean.Curves G X).forwardMean G U x r j k z u) =
        ∫ u in G.rho k..t, C.forwardMean G U x r j k z u := by
      apply intervalIntegral.integral_congr
      intro u hu
      rw [uIcc_of_le ht.1] at hu
      exact forwardReplacement_mean_eq G C D hD U x r j k z
        ⟨(G.rho_mem k).1.trans hu.1,hu.2.trans ht.2⟩
    change D j k z t = C.rotation G j k z - r • _
    rw [hD j k z t ⟨(G.rho_mem k).1.trans ht.1,ht.2⟩,hi]
    exact h.forward j k z t hz ht
  · intro j k
    rw [funext (forwardReplacement_action_eq G C D hD U x r j k)]
    exact h.kernel_angle j k
end ForwardAlgebraic

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ}
local notation "E" => EuclideanSpace ℝ ι

def curvesWithForward (d : Data ι m) : AffineResidual.Mean.Curves d.G (H d) :=
  { curves d with forward := smoothForward d }

theorem smoothForwardReplacement_forwardMean_eq (d : Data ι m) (U : H d → ℝ → H d)
    (j : Fin m) (k : d.G.Kernel) (z : ℝ) {t : ℝ}
    (ht : t ∈ Icc 0 (backwardEnd d.G.R)) :
    (curvesWithForward d).forwardMean d.G U 0 d.r j k z t =
      (curves d).forwardMean d.G U 0 d.r j k z t :=
  forwardReplacement_mean_eq d.G (curves d) (smoothForward d)
    (fun j k z _ ht => smoothForward_eq d j k z ht) U 0 d.r j k z ht

theorem smoothForwardReplacement_rotation_eq (d : Data ι m) :
    (curvesWithForward d).rotation d.G = (curves d).rotation d.G :=
  forwardReplacement_rotation_eq d.G (curves d) (smoothForward d)

theorem smoothForwardReplacement_forwardAction_eq (d : Data ι m) (U : H d → ℝ → H d)
    (j : Fin m) (k : d.G.Kernel) (z : ℝ) :
    (curvesWithForward d).forwardAction d.G U 0 d.r j k z =
      (curves d).forwardAction d.G U 0 d.r j k z :=
  forwardReplacement_action_eq d.G (curves d) (smoothForward d)
    (fun j k z _ ht => smoothForward_eq d j k z ht) U 0 d.r j k z

theorem smoothForwardReplacement_reference_eq (d : Data ι m) :
    (curvesWithForward d).reference d.G 0 d.r = (curves d).reference d.G 0 d.r :=
  forwardReplacement_reference_eq d.G (curves d) (smoothForward d)
    (fun j k z _ ht => smoothForward_eq d j k z ht) 0 d.r

theorem smoothForwardReplacement_equations (d : Data ι m) (U : H d → ℝ → H d)
    (hu : PrimitiveSpec (primitiveData d) (seedMeasure d) U) :
    AffineResidual.Mean.Equations d.G (curvesWithForward d) U d.r d.sigma 0
      (initialPosition d) (initialScore d) (initialNoise d) :=
  forwardReplacement_equations d.G (curves d) (smoothForward d)
    (fun j k z _ ht => smoothForward_eq d j k z ht) U d.r d.sigma 0
    (initialPosition d) (initialScore d) (initialNoise d) (equations d U hu)

theorem smoothForwardReplacement_canonical_equations (d : Data ι m) :
    AffineResidual.Mean.Equations d.G (curvesWithForward d)
      (primitiveLp (primitiveData d) (seedMeasure d)) d.r d.sigma 0
      (initialPosition d) (initialScore d) (initialNoise d) :=
  smoothForwardReplacement_equations d _ (primitiveLp_spec _ _)

theorem smoothForwardReplacement_meanOutput_eq (d : Data ι m) (U : H d → ℝ → H d) :
    d.G.meanOutput d.sigma (initialScore d)
      (fun i => U ((curvesWithForward d).reference d.G 0 d.r i) (d.G.radius d.r i)) =
    d.G.meanOutput d.sigma (initialScore d)
      (fun i => U ((curves d).reference d.G 0 d.r i) (d.G.radius d.r i)) := by
  rw [smoothForwardReplacement_reference_eq]

/-- First time jet is the actual physical posterior mean on the enlarged open slab. -/
theorem smoothForwardMean_ae (d : Data ι m) (j : Fin m) (k : d.G.Kernel) (z : ℝ) {t : ℝ}
    (ht : t ∈ Ioo (left (backwardEnd d.G.R)) (right (backwardEnd d.G.R))) :
    (smoothForwardMean d j k z t : Seed d → E) =ᵐ[seedMeasure d]
      (fun w => Gibbs.primitiveMean d.F (d.x + (d.r*t) • forwardJet d j k z 0 t w)
        (d.r*Real.sqrt (1-t^2))) := by
  have htime : time (transportData d) t = t := time_eq _ ⟨ht.1.le,ht.2.le⟩
  have ht' := construction_subset d.G.backwardEnd_pos.le d.G.backwardEnd_lt_one
    ⟨ht.1.le,ht.2.le⟩
  filter_upwards [Lp.coeFn_smul ((-d.r)⁻¹) (forwardJetLp d j k z 1 t),
    (forwardJet_memLp d j k z 1 t).coeFn_toLp] with w h1 h2
  change (((-d.r)⁻¹ • forwardJetLp d j k z 1 t : H d) w) = _
  change (forwardJetLp d j k z 1 t : Seed d → E) w = _ at h2
  rw [h1,Pi.smul_apply,h2]
  change (-d.r)⁻¹ • (jet (transportData d) 1 t (forwardInput d j k z w)).2 = _
  rw [jet_one]
  change (-d.r)⁻¹ • (-d.r • Conditional.conditionalMean d.F
    ((jointPath (transportData d) t (forwardInput d j k z w)).1) d.r
    (time (transportData d) t) ((jointPath (transportData d) t (forwardInput d j k z w)).2)) = _
  rw [jointPath_fst,smul_smul,inv_mul_cancel₀ (neg_ne_zero.mpr d.hr.ne'),one_smul,htime]
  exact AffineFlowIdentities.conditionalMean_eq_primitiveMean d.hF d.hell d.hlo d.hup
    d.x d.hr ht'.1 ht'.2 _

theorem smoothForwardReplacement_forwardMean_eq_smooth (d : Data ι m) (U : H d → ℝ → H d)
    (hu : PrimitiveSpec (primitiveData d) (seedMeasure d) U)
    (j : Fin m) (k : d.G.Kernel) (z : ℝ) {t : ℝ}
    (ht : t ∈ Ioo (left (backwardEnd d.G.R)) (right (backwardEnd d.G.R))) :
    (curvesWithForward d).forwardMean d.G U 0 d.r j k z t = smoothForwardMean d j k z t := by
  have ht' := construction_subset d.G.backwardEnd_pos.le d.G.backwardEnd_lt_one
    ⟨ht.1.le,ht.2.le⟩
  have hq : 0 < d.r*Real.sqrt (1-t^2) :=
    mul_pos d.hr (Real.sqrt_pos.mpr (by nlinarith [ht'.1,ht'.2]))
  simp only [AffineResidual.Mean.Curves.forwardMean,zero_add,curvesWithForward]
  apply Lp.ext
  filter_upwards [hu.2.1 ((d.r*t) • smoothForward d j k z t) _ hq,
    Lp.coeFn_smul (d.r*t) (smoothForward d j k z t),
    (forwardJet_memLp d j k z 0 t).coeFn_toLp,
    smoothForwardMean_ae d j k z ht] with w h1 h2 h3 h4
  erw [h1,h2,h4]
  simp only [Pi.smul_apply,primitiveData]
  change (smoothForward d j k z t : Seed d → E) w = _ at h3
  rw [h3]

theorem smoothForwardReplacement_contDiffAt_forwardMean (d : Data ι m)
    (U : H d → ℝ → H d) (hu : PrimitiveSpec (primitiveData d) (seedMeasure d) U)
    (j : Fin m) (k : d.G.Kernel) (z : ℝ) (n : ℕ) {t : ℝ}
    (ht : t ∈ Icc 0 (backwardEnd d.G.R)) :
    ContDiffAt ℝ n ((curvesWithForward d).forwardMean d.G U 0 d.r j k z) t := by
  have ht' := source_subset d.G.backwardEnd_pos.le d.G.backwardEnd_lt_one ht
  have hs := (contDiffOn_smoothForwardMean d j k z n).contDiffAt (isOpen_Ioo.mem_nhds ht')
  apply hs.congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.mem_nhds ht'] with u hu'
  exact smoothForwardReplacement_forwardMean_eq_smooth d U hu j k z hu'

theorem smoothForwardReplacement_position_eq (d : Data ι m) :
    (curvesWithForward d).position = (curves d).position := rfl

theorem smoothForwardReplacement_score_eq (d : Data ι m) :
    (curvesWithForward d).score = (curves d).score := rfl

theorem smoothForwardReplacement_velocity_eq (d : Data ι m) :
    (curvesWithForward d).velocity = (curves d).velocity := rfl

theorem smoothForwardReplacement_backward_eq (d : Data ι m) :
    (curvesWithForward d).backward = (curves d).backward := rfl

theorem smoothForwardReplacement_conditional_eq (d : Data ι m) :
    (curvesWithForward d).conditional = (curves d).conditional := rfl

theorem smoothForwardReplacement_kernel_eq (d : Data ι m) :
    (curvesWithForward d).kernel = (curves d).kernel := rfl

end AcceleratedLogConcave.Numerics.MeanResidualBridge
