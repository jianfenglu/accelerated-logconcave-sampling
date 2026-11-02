import AcceleratedLogConcave.Conditional.LiftedObservableMoments
import AcceleratedLogConcave.Conditional.JetCumulantCoordinates

noncomputable section
open MeasureTheory InnerProductSpace Filter
open scoped Topology
open scoped ContDiff RealInnerProductSpace
set_option autoImplicit false
namespace AcceleratedLogConcave.Conditional
variable {D : ℕ}

/-- Isolated position block of the Euclidean observable lift. -/
def positionLiftCLM : (EuclideanSpace ℝ (Fin D)) →L[ℝ] (EuclideanSpace ℝ (Fin D ⊕ Fin D)) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin D ⊕ Fin D => ℝ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (Sum.elim (fun i => EuclideanSpace.proj i) (fun _ => 0)))

/-- Isolated normalized-observable block of the Euclidean observable lift. -/
def observableLiftCLM : (EuclideanSpace ℝ (Fin D)) →L[ℝ] (EuclideanSpace ℝ (Fin D ⊕ Fin D)) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin D ⊕ Fin D => ℝ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (Sum.elim (fun _ => 0) (fun i => EuclideanSpace.proj i)))

@[simp] theorem positionLiftCLM_inl (z : (EuclideanSpace ℝ (Fin D))) (i : Fin D) :
    positionLiftCLM z (Sum.inl i) = z i := rfl
@[simp] theorem positionLiftCLM_inr (z : (EuclideanSpace ℝ (Fin D))) (i : Fin D) :
    positionLiftCLM z (Sum.inr i) = 0 := rfl
@[simp] theorem observableLiftCLM_inl (z : (EuclideanSpace ℝ (Fin D))) (i : Fin D) :
    observableLiftCLM z (Sum.inl i) = 0 := rfl
@[simp] theorem observableLiftCLM_inr (z : (EuclideanSpace ℝ (Fin D))) (i : Fin D) :
    observableLiftCLM z (Sum.inr i) = z i := rfl

theorem inner_positionLift (F : (EuclideanSpace ℝ (Fin D)) → ℝ) (x : (EuclideanSpace ℝ (Fin D))) (r ell : ℝ) (θ z : (EuclideanSpace ℝ (Fin D))) :
    inner ℝ (positionLiftCLM θ) (normalizedObservableLift F x r ell z) =
      inner ℝ θ z := by
  simp [PiLp.inner_apply, Fintype.sum_sum_type]

theorem inner_observableLift (F : (EuclideanSpace ℝ (Fin D)) → ℝ) (x : (EuclideanSpace ℝ (Fin D))) (r ell : ℝ) (u z : (EuclideanSpace ℝ (Fin D))) :
    inner ℝ (observableLiftCLM u) (normalizedObservableLift F x r ell z) =
      (r*ell)⁻¹ * inner ℝ u (primitiveObservable F x r z) := by
  simp [PiLp.inner_apply, Fintype.sum_sum_type, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem norm_positionLiftCLM (z : (EuclideanSpace ℝ (Fin D))) :
    ‖positionLiftCLM z‖ = ‖z‖ := by
  have hh : ‖positionLiftCLM z‖^2 = ‖z‖^2 := by
    simp [EuclideanSpace.real_norm_sq_eq, Fintype.sum_sum_type]
  nlinarith [norm_nonneg (positionLiftCLM z), norm_nonneg z]

namespace PositiveVarianceFlowData
variable (d : PositiveVarianceFlowData (EuclideanSpace ℝ (Fin D)))

def liftedConditionalLaw (t : ℝ) (y : (EuclideanSpace ℝ (Fin D))) : Measure (EuclideanSpace ℝ (Fin D ⊕ Fin D)) :=
  (conditionalLaw d.F d.x d.r t y).map (normalizedObservableLift d.F d.x d.r d.ell)

theorem laplace_liftedConditionalLaw_position (t : ℝ) (y θ : (EuclideanSpace ℝ (Fin D))) :
    Appell.laplace (d.liftedConditionalLaw t y) (fun _ => (1 : ℝ)) (positionLiftCLM θ) =
      Appell.laplace (conditionalLaw d.F d.x d.r t y) (fun _ => (1 : ℝ)) θ := by
  unfold Appell.laplace liftedConditionalLaw
  rw [integral_map (contDiff_normalizedObservableLift d.hF d.x d.r d.ell).continuous.measurable.aemeasurable
    (show AEStronglyMeasurable (fun z : (EuclideanSpace ℝ (Fin D ⊕ Fin D)) => Real.exp (inner ℝ (positionLiftCLM θ) z) • (1 : ℝ)) _ by
      exact (by fun_prop : Continuous _).aestronglyMeasurable)]
  simp only [inner_positionLift]

theorem laplace_liftedConditionalLaw_observable (t : ℝ) (y θ u : (EuclideanSpace ℝ (Fin D)))
    (hi : Integrable (fun z => Real.exp (inner ℝ θ z) • primitiveObservable d.F d.x d.r z)
      (conditionalLaw d.F d.x d.r t y)) :
    Appell.laplace (d.liftedConditionalLaw t y) (fun z => inner ℝ (observableLiftCLM u) z)
        (positionLiftCLM θ) =
      (d.r*d.ell)⁻¹ * inner ℝ u
        (Appell.laplace (conditionalLaw d.F d.x d.r t y) (primitiveObservable d.F d.x d.r) θ) := by
  unfold Appell.laplace liftedConditionalLaw
  rw [integral_map (contDiff_normalizedObservableLift d.hF d.x d.r d.ell).continuous.measurable.aemeasurable
    (show AEStronglyMeasurable
      (fun z : (EuclideanSpace ℝ (Fin D ⊕ Fin D)) => Real.exp (inner ℝ (positionLiftCLM θ) z) • inner ℝ (observableLiftCLM u) z) _ by
      exact (by fun_prop : Continuous _).aestronglyMeasurable)]
  simp only [inner_positionLift,inner_observableLift,smul_eq_mul]
  have hh := (innerSL ℝ u).integral_comp_comm hi
  change _ = (d.r*d.ell)⁻¹ * (innerSL ℝ u) _
  rw [← hh, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with z
  change _ = (d.r*d.ell)⁻¹ * inner ℝ u
    (Real.exp (inner ℝ θ z) • primitiveObservable d.F d.x d.r z)
  rw [inner_smul_right]
  ring


/-- The fixed actual conditional law has the local MGF required by the
weighted Laplace differentiation rules. -/
theorem conditionalLaw_hasLocalMGF {t : ℝ} (ht : -1 < t ∧ t < 1)
    (y : (EuclideanSpace ℝ (Fin D))) :
    HasLocalMGF (conditionalLaw d.F d.x d.r t y) := by
  exact posterior_hasLocalMGF (contDiff_primitivePotential d.hF d.x d.r)
    (le_refl 0) (conditionalVariance_pos ht.1 ht.2) (t • y)
    (by simpa using primitivePotential_hessian_nonneg d.hF d.hlo d.x d.r)

private theorem primitiveObservable_hasGrowth :
    Appell.HasGrowth (primitiveObservable d.F d.x d.r) := by
  let A := ‖gradient d.F 0‖ + |d.ell| * ‖d.x‖
  let C := |d.ell| * |d.r|
  refine ⟨A+C, by dsimp [A,C]; positivity, 1, ?_⟩
  intro z
  have hh := norm_primitiveObservable_le_affine d.hF d.hlo d.hhi d.x d.r z
  change ‖primitiveObservable d.F d.x d.r z‖ ≤ A+C*‖z‖ at hh
  simp only [pow_one]
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  nlinarith [norm_nonneg z]

/-- Original-data local output-slot identity for the lifted log-Laplace
transform. The neighborhood is uniform in the output direction u. -/
theorem exists_lifted_log_laplace_derivative (hell : 0 < d.ell)
    {t : ℝ} (ht : -1 < t ∧ t < 1) (y : (EuclideanSpace ℝ (Fin D))) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ θ ∈ Metric.ball (0 : (EuclideanSpace ℝ (Fin D))) ε,
      ∀ u : (EuclideanSpace ℝ (Fin D)),
      fderiv ℝ (fun w => Real.log
        (Appell.laplace (d.liftedConditionalLaw t y) (fun _ => (1 : ℝ)) w))
        (positionLiftCLM θ) (observableLiftCLM u) =
        (d.r*d.ell)⁻¹ * inner ℝ u (d.conditionalTiltMean t y θ) := by
  let := conditionalLaw_isProbabilityMeasure d.hF d.hlo d.x d.r ht.1 ht.2 y
  let : IsProbabilityMeasure (d.liftedConditionalLaw t y) :=
    conditionalLift_isProbabilityMeasure d.hF d.hlo d.x y d.r d.ell ht.1 ht.2
  have hν : HasLocalMGF (d.liftedConditionalLaw t y) :=
    conditionalLift_hasLocalMGF d.hF hell d.hr d.hlo d.hhi d.x y ht.1 ht.2
  obtain ⟨a,ha,hma⟩ := (d.conditionalLaw_hasLocalMGF ht y).exists_integrable_exp_norm
  obtain ⟨b,hb,hnb⟩ := hν.exists_integrable_exp_norm
  refine ⟨min (a/2) (b/2), lt_min (by positivity) (by positivity), ?_⟩
  intro θ hθ u
  have hθa : ‖θ‖ < a/2 := (by simpa using hθ : ‖θ‖ < min (a/2) (b/2)).trans_le (min_le_left _ _)
  have hθb : positionLiftCLM θ ∈ Metric.ball (0 : (EuclideanSpace ℝ (Fin D ⊕ Fin D))) (b/2) := by
    simpa only [Metric.mem_ball, dist_zero_right, norm_positionLiftCLM] using
      (by simpa using hθ : ‖θ‖ < min (a/2) (b/2)).trans_le (min_le_right _ _)
  have hi := Appell.integrable_laplace_of_exp_norm ha hma
    (continuous_primitiveObservable d.hF d.x d.r).aestronglyMeasurable
    d.primitiveObservable_hasGrowth hθa.le
  rw [Appell.fderiv_log_laplace_one_of_exp_norm hb hnb hθb,
    d.laplace_liftedConditionalLaw_position,
    d.laplace_liftedConditionalLaw_observable t y θ u hi]
  unfold conditionalTiltMean
  rw [inner_smul_right]
  ring


/-- The actual fixed-law linear-tilt mean is smooth on all natural parameters,
by its exact positive-variance posterior center representation. -/
theorem contDiff_conditionalTiltMean {t : ℝ} (ht : -1 < t ∧ t < 1)
    (y : (EuclideanSpace ℝ (Fin D))) : ContDiff ℝ (⊤ : ℕ∞) (d.conditionalTiltMean t y) := by
  have hN := Tilt.contDiff_integral_heatPosterior (contDiff_primitivePotential d.hF d.x d.r)
    (le_refl 0) (conditionalVariance_pos ht.1 ht.2)
    (by simpa using primitivePotential_hessian_nonneg d.hF d.hlo d.x d.r)
    (continuous_primitiveObservable d.hF d.x d.r)
    (‖gradient d.F 0‖ + |d.ell| * ‖d.x‖) (|d.ell| * |d.r|) 1
    (by simpa only [pow_one] using norm_primitiveObservable_le_affine d.hF d.hlo d.hhi d.x d.r)
  have he : d.conditionalTiltMean t y = fun θ =>
      ∫ z, primitiveObservable d.F d.x d.r z ∂Gibbs.heatPosterior
        (primitivePotential d.F d.x d.r) (conditionalVariance t)
        (t • y + conditionalVariance t • θ) := funext (d.conditionalTiltMean_eq_shift ht y)
  rw [he]
  exact hN.comp (contDiff_const.add (contDiff_id.const_smul _))

/-- Actual scaled-jet coordinates are mixed log-Laplace derivatives of the
normalized observable lift. The list can repeat directions and probability
time zero is included. This is a coordinate identity, not a norm estimate. -/
theorem scaledJet_coordinate_eq_lifted_logJet {I : Type*} (hell : 0 < d.ell)
    {t : ℝ} (ht : -1 < t ∧ t < 1) (y u : (EuclideanSpace ℝ (Fin D)))
    (v : I → (EuclideanSpace ℝ (Fin D))) (l : List I) :
    inner ℝ u (scaledJet l.length d.F d.x d.r t y (fun i => v (l.get i))) =
      (conditionalVariance t ^ l.length)⁻¹ * (d.r*d.ell) *
        JetCalculus.jet
          (Sum.elim (fun i => positionLiftCLM (v i))
            (fun _ : Unit => observableLiftCLM u))
          (l.map Sum.inl ++ [Sum.inr ()])
          (fun θ => Real.log (Appell.laplace (d.liftedConditionalLaw t y)
            (fun _ => (1 : ℝ)) θ)) 0 := by
  let : IsProbabilityMeasure (d.liftedConditionalLaw t y) :=
    conditionalLift_isProbabilityMeasure d.hF d.hlo d.x y d.r d.ell ht.1 ht.2
  have hν : HasLocalMGF (d.liftedConditionalLaw t y) :=
    conditionalLift_hasLocalMGF d.hF hell d.hr d.hlo d.hhi d.x y ht.1 ht.2
  obtain ⟨M,he⟩ := hν.exists_momentModel
  let f := fun θ => Real.log (Appell.laplace (d.liftedConditionalLaw t y)
    (fun _ => (1 : ℝ)) θ)
  let g := fun θ => Real.log (M.toFun θ)
  have hg : ContDiff ℝ (⊤ : ℕ∞) g := M.smooth.log (fun θ => (M.positive θ).ne')
  have hlog : f =ᶠ[𝓝 0] g := he.mono fun θ hθ => congrArg Real.log hθ
  have hdir := (JetCalculus.jet_eventuallyEq (fun _ : Unit => observableLiftCLM u)
    [()] hlog)
  have hcomp : (fun θ : (EuclideanSpace ℝ (Fin D)) =>
      JetCalculus.dir (observableLiftCLM u) f (positionLiftCLM θ)) =ᶠ[𝓝 0]
      (fun θ => JetCalculus.dir (observableLiftCLM u) g (positionLiftCLM θ)) := by
    have hp : Filter.Tendsto (positionLiftCLM (D := D)) (𝓝 0) (𝓝 0) := by
      simpa only [map_zero] using
        ((positionLiftCLM (D := D)).continuous.continuousAt (x := 0)).tendsto
    simpa only [JetCalculus.jet, Function.comp_def] using hdir.comp_tendsto hp
  obtain ⟨ε,hε,hlocal⟩ := d.exists_lifted_log_laplace_derivative hell ht y
  have heq : (fun θ => inner ℝ u (d.conditionalTiltMean t y θ)) =ᶠ[𝓝 0]
      (fun θ => (d.r*d.ell) * JetCalculus.dir (observableLiftCLM u) g (positionLiftCLM θ)) := by
    filter_upwards [Metric.ball_mem_nhds (0 : (EuclideanSpace ℝ (Fin D))) hε,hcomp] with θ hθ hc
    have hh := hlocal θ hθ u
    change JetCalculus.dir (observableLiftCLM u) f (positionLiftCLM θ) = _ at hh
    rw [← hc,hh,mul_inv_cancel_left₀ (mul_pos d.hr hell).ne']
  have hjet := (JetCalculus.jet_eventuallyEq v l heq).eq_of_nhds
  have hds := JetCalculus.smooth_dir hg (observableLiftCLM u)
  have hecomp : (fun θ => JetCalculus.dir (observableLiftCLM u) g (positionLiftCLM θ)) =
      (fun θ => JetCalculus.dir (observableLiftCLM u) g (positionLiftCLM θ+0)) := by simp
  have hdscomp : ContDiff ℝ (⊤ : ℕ∞) (fun θ => JetCalculus.dir (observableLiftCLM u) g (positionLiftCLM θ)) := hds.comp positionLiftCLM.contDiff
  rw [JetCalculus.jet_const_mul hdscomp] at hjet
  rw [hecomp,JetCalculus.jet_comp_affine hds positionLiftCLM 0] at hjet
  simp only [map_zero,zero_add] at hjet
  have hmix := (JetCalculus.jet_eventuallyEq
    (Sum.elim (fun i => positionLiftCLM (v i)) (fun _ : Unit => observableLiftCLM u))
    (l.map Sum.inl ++ [Sum.inr ()]) hlog).eq_of_nhds
  simp only [JetCalculus.jet_append,JetCalculus.jet_map] at hmix
  change JetCalculus.jet (fun i => positionLiftCLM (v i)) l
      (JetCalculus.dir (observableLiftCLM u) f) 0 =
    JetCalculus.jet (fun i => positionLiftCLM (v i)) l
      (JetCalculus.dir (observableLiftCLM u) g) 0 at hmix
  have htilt := d.contDiff_conditionalTiltMean ht y
  have hs : ContDiff ℝ (⊤ : ℕ∞) (fun θ => inner ℝ u (d.conditionalTiltMean t y θ)) :=
    contDiff_const.inner ℝ htilt
  rw [JetCalculus.jet_eq_iteratedFDeriv hs] at hjet
  have hlin := (innerSL ℝ u).iteratedFDeriv_comp_left (x := 0) htilt.contDiffAt
    (show (l.length : ℕ∞ω) ≤ (⊤ : ℕ∞) by simp)
  change iteratedFDeriv ℝ l.length (fun θ => inner ℝ u (d.conditionalTiltMean t y θ)) 0 = _ at hlin
  rw [hlin] at hjet
  change inner ℝ u (iteratedFDeriv ℝ l.length (d.conditionalTiltMean t y) 0
    (fun i => v (l.get i))) = _ at hjet
  rw [d.scaledJet_eq_inv_variance_smul_tiltMeanJet l.length ht y]
  simp only [smul_apply,inner_smul_right]
  rw [hjet]
  rw [JetCalculus.jet_append,JetCalculus.jet_map]
  change _ = _ * _ * JetCalculus.jet (fun i => positionLiftCLM (v i)) l
    (JetCalculus.dir (observableLiftCLM u) f) 0
  rw [hmix]
  ring

end PositiveVarianceFlowData
end AcceleratedLogConcave.Conditional
