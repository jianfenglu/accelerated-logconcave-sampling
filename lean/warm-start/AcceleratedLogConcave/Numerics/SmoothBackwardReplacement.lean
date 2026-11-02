import AcceleratedLogConcave.Numerics.SmoothBackwardMean

/-! Backward-only replacement. Kernel, conditional and forward fields are
literally unchanged; agreement is asserted only on the original closed slab. -/
noncomputable section
open Set MeasureTheory
open scoped ContDiff Topology
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace AcceleratedLogConcave.Numerics.MeanResidualBridge
open MeanFlowLp AffineGraph AffineGraph.MeanGeometry
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ}

def curvesWithBackward (d : Data ι m) : AffineResidual.Mean.Curves d.G (H d) :=
  { curves d with backward := smoothBackward d }

theorem replacement_backwardMean_eq (d : Data ι m) (U : H d → ℝ → H d)
    (j : Fin m) {t : ℝ} (ht : t ∈ Icc 0 (backwardEnd d.G.R)) :
    (curvesWithBackward d).backwardMean d.G U 0 d.r j t =
      (curves d).backwardMean d.G U 0 d.r j t := by
  simp only [AffineResidual.Mean.Curves.backwardMean, curvesWithBackward,
    smoothBackward_eq d j ht, curves]

theorem replacement_conditionalMean_eq (d : Data ι m) (U : H d → ℝ → H d)
    (j : Fin m) (k : d.G.Kernel) (t : ℝ) :
    (curvesWithBackward d).conditionalMean d.G U 0 d.r j k t =
      (curves d).conditionalMean d.G U 0 d.r j k t := by
  simp only [AffineResidual.Mean.Curves.conditionalMean, curvesWithBackward,
    smoothBackward_eq d j ⟨(d.G.rho_mem k).1, (d.G.rho_mem k).2.le⟩, curves]

theorem replacement_rotation_eq (d : Data ι m) (j : Fin m) (k : d.G.Kernel) (z : ℝ) :
    (curvesWithBackward d).rotation d.G j k z = (curves d).rotation d.G j k z := by
  simp only [AffineResidual.Mean.Curves.rotation, curvesWithBackward,
    smoothBackward_eq d j ⟨(d.G.rho_mem k).1, (d.G.rho_mem k).2.le⟩, curves]

theorem replacement_reference_eq (d : Data ι m) :
    (curvesWithBackward d).reference d.G 0 d.r = (curves d).reference d.G 0 d.r := by
  funext i
  rcases i with i | j | ⟨j,q⟩ | ⟨j,k,q⟩ | ⟨j,k,z,q⟩
  · rfl
  · rfl
  · simp only [AffineResidual.Mean.Curves.reference, curvesWithBackward,
      smoothBackward_eq d j ⟨(d.G.backward.location_mem_interval m q).1.le,
        (d.G.backward.location_mem_interval m q).2.le⟩, curves]
  · simp only [AffineResidual.Mean.Curves.reference, curvesWithBackward,
      smoothBackward_eq d j ⟨(d.G.rho_mem k).1, (d.G.rho_mem k).2.le⟩, curves]
  · rfl

theorem replacement_equations (d : Data ι m) (U : H d → ℝ → H d)
    (hu : PrimitiveSpec (primitiveData d) (seedMeasure d) U) :
    AffineResidual.Mean.Equations d.G (curvesWithBackward d) U d.r d.sigma 0
      (initialPosition d) (initialScore d) (initialNoise d) := by
  have h := equations d U hu
  refine ⟨h.position, h.score, ?_, ?_, ?_, h.kernel_angle, h.velocity_kernel⟩
  · intro j a ha
    have hi : (∫ t in backwardEnd d.G.R..a,
        (curvesWithBackward d).backwardMean d.G U 0 d.r j t) =
        ∫ t in backwardEnd d.G.R..a, (curves d).backwardMean d.G U 0 d.r j t := by
      apply intervalIntegral.integral_congr
      intro t ht
      exact replacement_backwardMean_eq d U j
        (by rw [uIcc_of_ge ha.2] at ht; exact ⟨ha.1.trans ht.1, ht.2⟩)
    change smoothBackward d j a = positionLp d (centerNode j) - d.r • _
    rw [smoothBackward_eq d j ha, hi]
    exact h.backward j a ha
  · intro j k a ha
    simp only [replacement_conditionalMean_eq]
    exact h.conditional j k a ha
  · intro j k z a hz ha
    rw [replacement_rotation_eq]
    exact h.forward j k z a hz ha

/-- The terminal score and all finite graph/output inputs are unchanged. -/
theorem replacement_score_eq (d : Data ι m) :
    (curvesWithBackward d).score = (curves d).score := rfl

theorem replacement_kernel_eq (d : Data ι m) :
    (curvesWithBackward d).kernel = (curves d).kernel := rfl

theorem replacement_forward_eq (d : Data ι m) :
    (curvesWithBackward d).forward = (curves d).forward := rfl

theorem replacement_conditional_eq (d : Data ι m) :
    (curvesWithBackward d).conditional = (curves d).conditional := rfl

/-- Agreement with the actual receiver primitive holds on an open neighborhood,
not merely on the closed slab; this is the endpoint-sensitive identification. -/
theorem replacement_backwardMean_eq_smooth (d : Data ι m) (U : H d → ℝ → H d)
    (hu : PrimitiveSpec (primitiveData d) (seedMeasure d) U) (j : Fin m) {t : ℝ}
    (ht : t ∈ Ioo (Analysis.PositiveVarianceSlab.left (backwardEnd d.G.R))
      (Analysis.PositiveVarianceSlab.right (backwardEnd d.G.R))) :
    (curvesWithBackward d).backwardMean d.G U 0 d.r j t = smoothBackwardMean d j t := by
  have hdom := Analysis.PositiveVarianceSlab.construction_subset
    d.G.backwardEnd_pos.le d.G.backwardEnd_lt_one ⟨ht.1.le, ht.2.le⟩
  have hrad : 0 < d.r * Real.sqrt (1-t^2) :=
    mul_pos d.hr (Real.sqrt_pos.mpr (by nlinarith [hdom.1, hdom.2]))
  let hm0 := ((backwardSmoothData d).positionJet_memLp 0 t).comp_measurePreserving
    (position_center_preserving d j)
  let hm1 := ((backwardSmoothData d).positionJet_memLp 1 t).comp_measurePreserving
    (position_center_preserving d j)
  have h0 : (smoothBackward d j t : Seed d → EuclideanSpace ℝ ι) =ᵐ[seedMeasure d]
      (fun z => (backwardSmoothData d).positionJet 0 t (position d (centerNode j) z)) := hm0.coeFn_toLp
  have h1 : (pulledPositionJet d j 1 t : Seed d → EuclideanSpace ℝ ι) =ᵐ[seedMeasure d]
      (fun z => (backwardSmoothData d).positionJet 1 t (position d (centerNode j) z)) := hm1.coeFn_toLp
  simp only [AffineResidual.Mean.Curves.backwardMean, zero_add, curvesWithBackward]
  apply Lp.ext
  filter_upwards [hu.2.1 ((d.r*t) • smoothBackward d j t) _ hrad,
    Lp.coeFn_smul (d.r*t) (smoothBackward d j t), h0,
    Lp.coeFn_smul (-d.r⁻¹) (pulledPositionJet d j 1 t), h1] with z hU hs0 hz0 hs1 hz1
  change U ((d.r*t) • smoothBackward d j t) (d.r * Real.sqrt (1-t^2)) z =
    (-d.r⁻¹ • pulledPositionJet d j 1 t : H d) z
  rw [hs1, Pi.smul_apply, hz1, (backwardSmoothData d).positionJet_one_eq_mean ht]
  change _ = -d.r⁻¹ • (-d.r • Conditional.conditionalMean d.F d.x d.r t _)
  rw [smul_smul, neg_mul_neg, inv_mul_cancel₀ (ne_of_gt d.hr), one_smul]
  rw [AffineFlowIdentities.conditionalMean_eq_primitiveMean d.hF d.hell d.hlo d.hup
    d.x d.hr hdom.1 hdom.2]
  simpa only [hs0, Pi.smul_apply, hz0, primitiveData] using hU

/-- Ordinary regularity of the actual replacement receiver, including endpoints. -/
theorem contDiffAt_replacement_backwardMean (d : Data ι m) (U : H d → ℝ → H d)
    (hu : PrimitiveSpec (primitiveData d) (seedMeasure d) U) (j : Fin m) (n : ℕ) {t : ℝ}
    (ht : t ∈ Icc 0 (backwardEnd d.G.R)) :
    ContDiffAt ℝ n ((curvesWithBackward d).backwardMean d.G U 0 d.r j) t := by
  have he : ((curvesWithBackward d).backwardMean d.G U 0 d.r j) =ᶠ[nhds t]
      smoothBackwardMean d j := by
    filter_upwards [isOpen_Ioo.mem_nhds (Analysis.PositiveVarianceSlab.source_subset
      d.G.backwardEnd_pos.le d.G.backwardEnd_lt_one ht)] with u hu'
    exact replacement_backwardMean_eq_smooth d U hu j hu'
  exact (contDiffAt_smoothBackwardMean d j n ht).congr_of_eventuallyEq he

theorem iteratedDeriv_replacement_backwardMean (d : Data ι m) (U : H d → ℝ → H d)
    (hu : PrimitiveSpec (primitiveData d) (seedMeasure d) U) (j : Fin m) (n : ℕ) {t : ℝ}
    (ht : t ∈ Icc 0 (backwardEnd d.G.R)) :
    iteratedDeriv n ((curvesWithBackward d).backwardMean d.G U 0 d.r j) t =
      -d.r⁻¹ • pulledPositionJet d j (n + 1) t := by
  have ht' := Analysis.PositiveVarianceSlab.source_subset
    d.G.backwardEnd_pos.le d.G.backwardEnd_lt_one ht
  have he : ((curvesWithBackward d).backwardMean d.G U 0 d.r j) =ᶠ[nhds t]
      smoothBackwardMean d j := by
    filter_upwards [isOpen_Ioo.mem_nhds ht'] with u hu'
    exact replacement_backwardMean_eq_smooth d U hu j hu'
  exact ((he.iteratedDeriv n).eq_of_nhds).trans (iteratedDeriv_smoothBackwardMean d j n ht')

/-- Any source reply vector evaluated on the replacement reference gives the
same literal mean output. In particular this applies to the canonical primitive. -/
theorem replacement_meanOutput_eq (d : Data ι m) (U : H d → ℝ → H d) :
    d.G.meanOutput d.sigma (initialScore d)
      (fun i => U ((curvesWithBackward d).reference d.G 0 d.r i) (d.G.radius d.r i)) =
    d.G.meanOutput d.sigma (initialScore d)
      (fun i => U ((curves d).reference d.G 0 d.r i) (d.G.radius d.r i)) := by
  rw [replacement_reference_eq]

theorem norm_iteratedDeriv_replacement_backwardMean (d : Data ι m)
    (U : H d → ℝ → H d) (hu : PrimitiveSpec (primitiveData d) (seedMeasure d) U)
    (j : Fin m) (n : ℕ) {t : ℝ} (ht : t ∈ Icc 0 (backwardEnd d.G.R)) :
    ‖iteratedDeriv n ((curvesWithBackward d).backwardMean d.G U 0 d.r j) t‖ =
      d.r⁻¹ * ‖(backwardSmoothData d).positionJetLp (n + 1) t‖ := by
  rw [iteratedDeriv_replacement_backwardMean d U hu j n ht, norm_smul,
    Real.norm_eq_abs, abs_neg, abs_of_pos (inv_pos.mpr d.hr), norm_pulledPositionJet]

end AcceleratedLogConcave.Numerics.MeanResidualBridge
