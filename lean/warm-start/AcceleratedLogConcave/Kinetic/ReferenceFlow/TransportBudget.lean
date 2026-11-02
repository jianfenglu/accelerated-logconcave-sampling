import AcceleratedLogConcave.Kinetic.Mixing.PhysicalFactorization
import AcceleratedLogConcave.Kinetic.Mixing.IntegralContinuity
import AcceleratedLogConcave.Kinetic.Mixing.CenteredCore
import AcceleratedLogConcave.Kinetic.ReferenceFlow.TransportInitial
import Mathlib.Topology.MetricSpace.UniformConvergence
import AcceleratedLogConcave.Kinetic.Mixing.IntervalBounded

/-! Extension of the genuine integrated transport estimate to every centered
phase L2 input. The microscopic integral is continuous by uniform operator
bounds, and its measurability is proved by density of compact smooth tests. -/
noncomputable section
open MeasureTheory Set Filter InnerProductSpace
open scoped Topology
namespace AcceleratedLogConcave.Kinetic
open Analysis.Poisson Reheating
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {a b : ℝ} (F : ReferencePoissonFamily E a b) (ell s n : ℝ) (hsn : s^2+n^2=1)

/-- Actual density transport in the fixed spatial frame. The identity extension
only specifies times outside the open reference interval. -/
def physicalFrameDensity (t : ℝ) : Lp ℝ 2 (gaussianPhaseMeasure (F.law a)) →L[ℝ]
    Lp ℝ 2 (gaussianPhaseMeasure (F.law a)) :=
  if ht : t ∈ Ioo a b then
    (F.phaseUnitary ⟨t,ht.1.le,ht.2.le⟩).toContinuousLinearEquiv.toContinuousLinearMap.comp
      (physicalDensityTransport F ell s n hsn ⟨t,ht.1.le,ht.2.le⟩).toContinuousLinearEquiv.toContinuousLinearMap
  else ContinuousLinearMap.id ℝ _

theorem physicalFrameDensity_interior (t : ℝ) (ht : t ∈ Ioo a b)
    (f : Lp ℝ 2 (gaussianPhaseMeasure (F.law a))) :
    physicalFrameDensity F ell s n hsn t f =
      F.phaseUnitary ⟨t,ht.1.le,ht.2.le⟩ (physicalDensityTransport F ell s n hsn ⟨t,ht.1.le,ht.2.le⟩ f) := by
  simp only [physicalFrameDensity, dite_eq_left ht, ContinuousLinearMap.comp_apply,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv, ContinuousLinearEquiv.coe_coe]

theorem physicalFrameDensity_initial (f : Lp ℝ 2 (gaussianPhaseMeasure (F.law a))) :
    physicalFrameDensity F ell s n hsn a f = f := by simp [physicalFrameDensity]

theorem physicalFrameDensity_norm (t : ℝ) (f : Lp ℝ 2 (gaussianPhaseMeasure (F.law a))) :
    ‖physicalFrameDensity F ell s n hsn t f‖ = ‖f‖ := by
  by_cases ht : t ∈ Ioo a b
  · rw [physicalFrameDensity_interior F ell s n hsn t ht]
    simp only [LinearIsometryEquiv.norm_map]
  · simp only [physicalFrameDensity, dite_eq_right ht, ContinuousLinearMap.id_apply]

theorem physicalFrameDensity_norm_le (t : ℝ) : ‖physicalFrameDensity F ell s n hsn t‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  simp only [physicalFrameDensity_norm, one_mul, le_refl]

/-- The spatial phase pullback is exactly the identity initially. -/
theorem phaseUnitary_initial (f : Lp ℝ 2 (gaussianPhaseMeasure (F.law a))) :
    F.phaseUnitary F.leftTime f = f := by
  apply Lp.ext
  filter_upwards [gaussianPhasePullback_coe (F.flow F.leftTime).toMeasurableEquiv
    (F.flow_measurePreserving F.leftTime) f] with z hz
  change (F.phaseUnitary F.leftTime f) z = f ((F.flow F.leftTime z.1.1,z.1.2),z.2) at hz
  rw [hz]
  have hi := referenceFlow_initial F.potential F.scale (fun t _ => F.potential_C2 t)
    F.gradient_continuous F.scale_continuous F.scaleBound F.scale_bounded
    F.hessian_nonneg F.hessian_upper F.leftTime z.1.1
  change F.flow F.leftTime z.1.1 = z.1.1 at hi
  rw [hi]

/-- Full physical density transport is exactly the identity initially. -/
theorem physicalDensityTransport_initial (f : Lp ℝ 2 (gaussianPhaseMeasure (F.law a))) :
    physicalDensityTransport F ell s n hsn F.leftTime f = f := by
  apply Lp.ext
  filter_upwards [physicalDensityTransport_coe F ell s n hsn F.leftTime f] with z hz
  apply hz.trans
  have hi := physicalReferenceFlow_initial F ell s n hsn
    ((physicalReferenceFlow F ell s n hsn F.leftTime).symm z)
  rw [Homeomorph.apply_symm_apply] at hi
  exact congrArg f hi.symm

/-- The frame representation includes the initial endpoint, using the proved
initial identities rather than an artificial endpoint continuity premise. -/
theorem physicalFrameDensity_Ico (t : ℝ) (ht : t ∈ Ico a b)
    (f : Lp ℝ 2 (gaussianPhaseMeasure (F.law a))) :
    physicalFrameDensity F ell s n hsn t f =
      F.phaseUnitary ⟨t,ht.1,ht.2.le⟩ (physicalDensityTransport F ell s n hsn ⟨t,ht.1,ht.2.le⟩ f) := by
  rcases ht.1.eq_or_lt with h | h
  · subst t
    rw [physicalFrameDensity_initial]
    change f = F.phaseUnitary F.leftTime (physicalDensityTransport F ell s n hsn F.leftTime f)
    rw [physicalDensityTransport_initial, phaseUnitary_initial]
  · exact physicalFrameDensity_interior F ell s n hsn t ⟨h,ht.2⟩ f

/-- On the entire left-closed source interval, the actual bounded operator
agrees with the compact core curve used in the differential estimate. -/
theorem physicalFrameDensity_compact (φ : GaussianPhase E → ℝ)
    (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ) (t : ℝ) (ht : t ∈ Ico a b) :
    physicalFrameDensity F ell s n hsn t
      (compactTestL2 (gaussianPhaseMeasure (F.law a)) φ hφ.continuous hc) =
      physicalMovingCoreLp F ell s n hsn F.leftTime hφ.continuous hc t := by
  rcases ht.1.eq_or_lt with h | h
  · subst t
    rw [physicalFrameDensity_initial, physicalMovingCoreLp_initial]
  · rw [physicalFrameDensity_interior F ell s n hsn t ⟨h,ht.2⟩,
      physicalMovingCoreLp_eq_densityTransport F ell s n hsn hφ hc t ⟨h,ht.2⟩]
    rfl

/-- Strong measurability is derived for every L2 input by a pointwise limit of
actual compact core curves. No operator-family measurability is assumed. -/
theorem physicalFrameDensity_aestronglyMeasurable
    (f : Lp ℝ 2 (gaussianPhaseMeasure (F.law a))) :
    AEStronglyMeasurable (fun t => physicalFrameDensity F ell s n hsn t f) volume := by
  refine (Reheating.compactC2_dense (gaussianPhaseMeasure (F.law a))).induction ?_ ?_ f
  · intro g hg
    obtain ⟨φ,hg,hc,hφ⟩ := hg
    have hg' : g = compactTestL2 (gaussianPhaseMeasure (F.law a)) φ hφ.continuous hc :=
      Lp.ext (hg.trans (compactTest_memLp (gaussianPhaseMeasure (F.law a)) φ hφ.continuous hc).coeFn_toLp.symm)
    have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (by norm_num)
    have he : (fun t => physicalFrameDensity F ell s n hsn t g) =
        (Ioo a b).piecewise
          (physicalMovingCoreLp F ell s n hsn F.leftTime hφ.continuous hc) (fun _ => g) := by
      funext t
      by_cases ht : t ∈ Ioo a b
      · simp only [Set.piecewise, ite_eq_left ht]
        rw [hg']
        exact physicalFrameDensity_compact F ell s n hsn φ hφ1 hc t ⟨ht.1.le,ht.2⟩
      · simp only [Set.piecewise, ite_eq_right ht, physicalFrameDensity, dite_eq_right ht,
          ContinuousLinearMap.id_apply]
    rw [he]
    exact (StronglyMeasurable.piecewise measurableSet_Ioo
      (physicalMovingCoreLp_continuous F ell s n hsn F.leftTime hφ1 hc).stronglyMeasurable
      stronglyMeasurable_const).aestronglyMeasurable
  · apply IsSeqClosed.isClosed
    intro u g hu hug
    exact aestronglyMeasurable_of_tendsto_ae atTop hu
      (Eventually.of_forall fun t => ((physicalFrameDensity F ell s n hsn t).continuous.tendsto g).comp hug)

/-- The microscopic part as an actual bounded operator on the fixed space. -/
def physicalFrameMicro (t : ℝ) : Lp ℝ 2 (gaussianPhaseMeasure (F.law a)) →L[ℝ]
    Lp ℝ 2 (gaussianPhaseMeasure (F.law a)) :=
  (ContinuousLinearMap.id ℝ _ - gaussianPositionProjection (F.law a)).comp
    (physicalFrameDensity F ell s n hsn t)

theorem physicalFrameMicro_apply (t : ℝ) (f : Lp ℝ 2 (gaussianPhaseMeasure (F.law a))) :
    physicalFrameMicro F ell s n hsn t f = physicalFrameDensity F ell s n hsn t f -
      gaussianPositionProjection (F.law a) (physicalFrameDensity F ell s n hsn t f) := rfl

theorem physicalFrameMicro_norm_le (t : ℝ) : ‖physicalFrameMicro F ell s n hsn t‖ ≤ 2 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro f
  rw [physicalFrameMicro_apply]
  have hp := ContinuousLinearMap.le_of_opNorm_le _ (gaussianPositionProjection_norm_le (F.law a))
    (physicalFrameDensity F ell s n hsn t f)
  have hd := norm_sub_le (physicalFrameDensity F ell s n hsn t f)
    (gaussianPositionProjection (F.law a) (physicalFrameDensity F ell s n hsn t f))
  rw [physicalFrameDensity_norm] at hd hp
  simpa only [one_mul] using hd.trans (by linarith)

theorem physicalFrameMicro_aestronglyMeasurable
    (f : Lp ℝ 2 (gaussianPhaseMeasure (F.law a))) :
    AEStronglyMeasurable (fun t => physicalFrameMicro F ell s n hsn t f) volume :=
  (ContinuousLinearMap.id ℝ _ - gaussianPositionProjection (F.law a)).continuous.comp_aestronglyMeasurable
    (physicalFrameDensity_aestronglyMeasurable F ell s n hsn f)

/-- Strong continuity on the left-closed source interval extends from the
actual compact curves by uniform convergence of isometric transports. -/
theorem physicalFrameDensity_continuousOn
    (f : Lp ℝ 2 (gaussianPhaseMeasure (F.law a))) :
    ContinuousOn (fun t => physicalFrameDensity F ell s n hsn t f) (Ico a b) := by
  refine (Reheating.compactC2_dense (gaussianPhaseMeasure (F.law a))).induction ?_ ?_ f
  · intro g hg
    obtain ⟨φ,hg,hc,hφ⟩ := hg
    have hg' : g = compactTestL2 (gaussianPhaseMeasure (F.law a)) φ hφ.continuous hc :=
      Lp.ext (hg.trans (compactTest_memLp (gaussianPhaseMeasure (F.law a)) φ hφ.continuous hc).coeFn_toLp.symm)
    have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (by norm_num)
    apply (physicalMovingCoreLp_continuous F ell s n hsn F.leftTime hφ1 hc).continuousOn.congr
    intro t ht
    rw [hg']
    exact physicalFrameDensity_compact F ell s n hsn φ hφ1 hc t ht
  · apply IsSeqClosed.isClosed
    intro u g hu hug
    have hunif : TendstoUniformlyOn
        (fun k t => physicalFrameDensity F ell s n hsn t (u k))
        (fun t => physicalFrameDensity F ell s n hsn t g) atTop (Ico a b) := by
      rw [Metric.tendstoUniformlyOn_iff]
      intro δ hδ
      have hh := Metric.tendsto_atTop.mp hug δ hδ
      filter_upwards [Filter.eventually_atTop.mpr hh] with k hk t _
      rw [dist_eq_norm, ← map_sub, physicalFrameDensity_norm, ← dist_eq_norm, dist_comm]
      exact hk
    exact hunif.continuousOn (Eventually.of_forall hu).frequently

/-- The microscopic squared norm is integrable on every finite interval. -/
theorem physicalFrameMicro_intervalIntegrable
    (f : Lp ℝ 2 (gaussianPhaseMeasure (F.law a))) (v w : ℝ) :
    IntervalIntegrable (fun t => ‖physicalFrameMicro F ell s n hsn t f‖^2) volume v w := by
  apply IntervalIntegrable.mono_fun (intervalIntegrable_const (c := (2*‖f‖)^2))
    ((physicalFrameMicro_aestronglyMeasurable F ell s n hsn f).norm.pow 2).restrict
  apply Eventually.of_forall
  intro t
  change ‖(‖physicalFrameMicro F ell s n hsn t f‖^2 : ℝ)‖ ≤ ‖((2*‖f‖)^2 : ℝ)‖
  simp only [Real.norm_eq_abs, abs_sq]
  exact pow_le_pow_left₀ (norm_nonneg _)
    (ContinuousLinearMap.le_of_opNorm_le _ (physicalFrameMicro_norm_le F ell s n hsn t) f) 2

/-- Dependence of the integrated microscopic squared norm on the input is
continuous, from actual scalar measurability and a uniform operator bound. -/
theorem physicalFrameMicro_integral_continuous (v w : ℝ) (hvw : v ≤ w) :
    Continuous (fun f : Lp ℝ 2 (gaussianPhaseMeasure (F.law a)) =>
      ∫ t in v..w, ‖physicalFrameMicro F ell s n hsn t f‖^2) := by
  simp_rw [intervalIntegral.integral_of_le hvw]
  exact integral_norm_sq_continuous (volume.restrict (Ioc v w))
    (physicalFrameMicro F ell s n hsn) 2 (by norm_num)
    (physicalFrameMicro_norm_le F ell s n hsn)
    (fun f => ((physicalFrameMicro_aestronglyMeasurable F ell s n hsn f).norm.pow 2).restrict)

/-- The source integrated transport estimate for every centered full-phase L2
input. The proof extends the actual compact-core estimate by density; the
transport-energy budget is a conclusion, not an assumption. -/
theorem physicalTransportEnergy_integrated_L2 (ε : ℝ) (hell : 0 ≤ ell) (hε : 0 ≤ ε)
    (u : ℝ) (hu : u ∈ Ico a b)
    (hscale : ∀ t ∈ Icc a u, |F.scale t| ≤ ell / 4)
    (f : centered (gaussianPhaseMeasure (F.law a))) :
    quadraticEnergy (F.corrector u) ε
      (physicalFrameDensity F ell (1/2) (Real.sqrt 3/2) source_split_coefficients u f) ≤
    quadraticEnergy (F.corrector a) ε f - ε*ell*(u-a)/8 * ‖(f : Lp ℝ 2 (gaussianPhaseMeasure (F.law a)))‖^2 +
      3*ε*ell * ∫ t in a..u,
        ‖physicalFrameMicro F ell (1/2) (Real.sqrt 3/2) source_split_coefficients t f‖^2 := by
  refine (centered_compactC2_dense (gaussianPhaseMeasure (F.law a))).induction ?_ ?_ f
  · intro g hg
    obtain ⟨φ,hg,hc,hφ⟩ := hg
    have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (by norm_num)
    have hg' : (g : Lp ℝ 2 (gaussianPhaseMeasure (F.law a))) = compactTestL2 (gaussianPhaseMeasure (F.law a)) φ hφ.continuous hc :=
      Lp.ext (hg.trans (compactTest_memLp (gaussianPhaseMeasure (F.law a)) φ hφ.continuous hc).coeFn_toLp.symm)
    have hmean : (∫ z, φ z ∂gaussianPhaseMeasure (F.law a)) = 0 := by
      rw [← integral_congr_ae hg]
      exact (mean_apply (gaussianPhaseMeasure (F.law a)) g).symm.trans g.property
    have hn : (∫ z, (φ z)^2 ∂gaussianPhaseMeasure (F.law a)) = ‖(g : Lp ℝ 2 (gaussianPhaseMeasure (F.law a)))‖^2 := by
      rw [← real_inner_self_eq_norm_sq, L2.inner_def]
      apply integral_congr_ae
      filter_upwards [hg] with z hz
      rw [hz]
      simp only [real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]
    have he (t : ℝ) (ht : t ∈ Ico a b) :
        physicalFrameDensity F ell (1/2) (Real.sqrt 3/2) source_split_coefficients t g =
          physicalMovingCoreLp F ell (1/2) (Real.sqrt 3/2) source_split_coefficients F.leftTime hφ.continuous hc t := by
      rw [hg']
      exact physicalFrameDensity_compact F ell (1/2) (Real.sqrt 3/2) source_split_coefficients φ hφ1 hc t ht
    have hi := physicalTransportEnergy_integrated F ell ε hell hε F.leftTime hφ1 hc hmean
      le_rfl hu.2 hu.1 hscale
    dsimp only at hi
    have hri : (∫ t in a..u,
        ‖physicalFrameMicro F ell (1/2) (Real.sqrt 3/2) source_split_coefficients t g‖^2) =
      ∫ t in a..u,
        ‖physicalMovingCoreLp F ell (1/2) (Real.sqrt 3/2) source_split_coefficients F.leftTime hφ.continuous hc t -
          gaussianPositionProjection (F.law a)
            (physicalMovingCoreLp F ell (1/2) (Real.sqrt 3/2) source_split_coefficients F.leftTime hφ.continuous hc t)‖^2 := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_le hu.1] at ht
      change ‖physicalFrameDensity F ell (1/2) (Real.sqrt 3/2) source_split_coefficients t g -
        gaussianPositionProjection (F.law a)
          (physicalFrameDensity F ell (1/2) (Real.sqrt 3/2) source_split_coefficients t g)‖^2 = _
      exact congrArg (fun v => ‖v - gaussianPositionProjection (F.law a) v‖^2)
        (he t ⟨ht.1,ht.2.trans_lt hu.2⟩)
    have hn' : (∫ z, (φ z)^2 ∂gaussianPhaseMeasure (F.law F.leftTime)) =
        ‖(g : Lp ℝ 2 (gaussianPhaseMeasure (F.law a)))‖^2 := hn
    rw [← he u hu, physicalMovingCoreLp_initial, ← hg', hn', ← hri] at hi
    exact hi
  · apply isClosed_le
    · exact ((quadraticEnergy_continuous (F.corrector u) ε).comp
        (physicalFrameDensity F ell (1/2) (Real.sqrt 3/2) source_split_coefficients u).continuous).comp
        continuous_subtype_val
    · exact (((quadraticEnergy_continuous (F.corrector a) ε).comp continuous_subtype_val).sub
        (continuous_const.mul (continuous_subtype_val.norm.pow 2))).add
        (continuous_const.mul ((physicalFrameMicro_integral_continuous F ell (1/2)
          (Real.sqrt 3/2) source_split_coefficients a u hu.1).comp continuous_subtype_val))

/-- Time continuity of the actual fixed-frame microscopic squared norm. -/
theorem physicalFrameMicro_norm_sq_continuousOn
    (f : Lp ℝ 2 (gaussianPhaseMeasure (F.law a))) :
    ContinuousOn (fun t => ‖physicalFrameMicro F ell s n hsn t f‖^2) (Ico a b) := by
  have hs := physicalFrameDensity_continuousOn F ell s n hsn f
  exact ((ContinuousLinearMap.id ℝ _ - gaussianPositionProjection (F.law a)).continuous.comp_continuousOn hs).norm.pow 2

/-- Time continuity of the actual corrected transport energy up to the left
endpoint. No assertion of continuity at the unused right endpoint is made. -/
theorem physicalFrameEnergy_continuousOn (ε : ℝ)
    (f : Lp ℝ 2 (gaussianPhaseMeasure (F.law a))) :
    ContinuousOn (fun t => quadraticEnergy (F.corrector t) ε
      (physicalFrameDensity F ell s n hsn t f)) (Ico a b) := by
  have hs := physicalFrameDensity_continuousOn F ell s n hsn f
  unfold quadraticEnergy
  exact ((hs.norm.pow 2).const_mul (1/2 : ℝ)).add
    ((((corrector_continuousOn_Ico F).clm_apply hs).inner hs).const_mul ε)

end AcceleratedLogConcave.Kinetic
