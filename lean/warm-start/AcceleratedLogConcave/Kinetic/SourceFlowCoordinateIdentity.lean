import AcceleratedLogConcave.Kinetic.Mixing.ClockKernel
import AcceleratedLogConcave.Kinetic.Reheating.HeatEvolution.ClockTransportFamily
noncomputable section
set_option autoImplicit false
namespace AcceleratedLogConcave.Kinetic
open MeasureTheory ProbabilityTheory Set Analysis.Poisson
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {b : ℝ} (F : ReferencePoissonFamily E 0 b) (ell : ℝ)

private theorem trajectory_comoving_hasDerivWithinAt (z : E × E)
    (hscale : ∀ t ∈ Icc (0:ℝ) b, F.scale t = ell^2 * t)
    (t : ℝ) (ht : t ∈ Icc (0:ℝ) b) :
    HasDerivWithinAt
      (fun u => (referenceCoupledTrajectory F ell z u).1 -
        (ell*u) • (referenceCoupledTrajectory F ell z u).2)
      (0:E) (Icc 0 b) t := by
  let tr := referenceCoupledTrajectory F ell z
  let g := gradient (F.potential t) (tr t).1
  have htr : HasDerivWithinAt tr
      (ell • (tr t).2 - F.scale t • g, -ell • g) (Icc 0 b) t :=
    referenceCoupledTrajectory_deriv F ell z t ht
  have hX : HasDerivWithinAt (fun u => (tr u).1)
      (ell • (tr t).2 - F.scale t • g) (Icc 0 b) t := by
    simpa [Function.comp_def, ContinuousLinearMap.fst] using
      (hasFDerivAt_fst.comp_hasDerivWithinAt t htr)
  have hY : HasDerivWithinAt (fun u => (tr u).2)
      (-ell • g) (Icc 0 b) t := by
    simpa [Function.comp_def, ContinuousLinearMap.snd] using
      (hasFDerivAt_snd.comp_hasDerivWithinAt t htr)
  have hs : HasDerivWithinAt (fun u : ℝ => ell*u) ell (Icc 0 b) t := by
    simpa only [id_eq, mul_one] using
      ((hasDerivAt_id t).const_mul ell).hasDerivWithinAt (s := Icc 0 b)
  have hprod := hs.smul hY
  have hzero : (ell • (tr t).2 - F.scale t • g) -
      ((ell*t) • (-ell • g) + ell • (tr t).2) = (0:E) := by
    rw [hscale t ht]
    simp only [pow_two]
    module
  have h := hX.sub hprod
  have hfun : ((fun u => (tr u).1) - ((fun u : ℝ => ell*u) •
      (fun u => (tr u).2))) =
      (fun u => (tr u).1 - (ell*u) • (tr u).2) := by
    funext u
    rfl
  rw [hfun, hzero] at h
  exact h


/-- At source scale `a=ℓ²`, the actual coupled flow has the exact
position/velocity coordinate identity from its ODE, not an assumed bridge. -/
theorem referenceCoupledTrajectory_position_eq (hb : 0 < b) (z : E × E)
    (hscale : ∀ u ∈ Icc (0:ℝ) b, F.scale u = ell^2 * u)
    (t : Icc (0:ℝ) b) :
    (referenceCoupledTrajectory F ell z t).1 =
      z.1 + (ell * (t:ℝ)) • (referenceCoupledTrajectory F ell z t).2 := by
  let q : ℝ → E := fun u => (referenceCoupledTrajectory F ell z u).1 -
    (ell*u) • (referenceCoupledTrajectory F ell z u).2
  have hderiv (u : ℝ) (hu : u ∈ Icc (0:ℝ) b) :
      HasDerivWithinAt q (0:E) (Icc 0 b) u :=
    trajectory_comoving_hasDerivWithinAt F ell z hscale u hu
  have hdiff : DifferentiableOn ℝ q (Icc (0:ℝ) b) :=
    fun u hu => (hderiv u hu).differentiableWithinAt
  have hzero (u : ℝ) (hu : u ∈ Icc (0:ℝ) b) :
      fderivWithin ℝ q (Icc 0 b) u = 0 := by
    simpa using (hderiv u hu).hasFDerivWithinAt.fderivWithin
      ((uniqueDiffOn_Icc hb) u hu)
  have hconst := (convex_Icc (0:ℝ) b).is_const_of_fderivWithin_eq_zero
    hdiff hzero (show (0:ℝ) ∈ Icc 0 b from ⟨le_refl _, hb.le⟩) t.property
  have hinit : referenceCoupledTrajectory F ell z 0 = z :=
    referenceCoupledTrajectory_initial F ell z
  dsimp [q] at hconst
  rw [hinit] at hconst
  simp only [mul_zero, zero_smul, sub_zero] at hconst
  exact sub_eq_iff_eq_add.mp hconst.symm

private theorem referenceCoupledPairFlow_eq_trajectory (z : E × E)
    (t : Icc (0:ℝ) b) :
    referenceCoupledPairFlow F ell t z =
      referenceCoupledTrajectory F ell z t := by
  rfl

/-- The same identity at the actual time-indexed pair-flow homeomorphism. -/
theorem referenceCoupledPairFlow_position_eq (hb : 0 < b) (z : E × E)
    (hscale : ∀ u ∈ Icc (0:ℝ) b, F.scale u = ell^2 * u)
    (t : Icc (0:ℝ) b) :
    (referenceCoupledPairFlow F ell t z).1 =
      z.1 + (ell * (t:ℝ)) • (referenceCoupledPairFlow F ell t z).2 := by
  rw [referenceCoupledPairFlow_eq_trajectory]
  exact referenceCoupledTrajectory_position_eq F ell hb z hscale t

/-- After the manuscript's initial Gaussian split and the actual flow, the
transported position is based at the original unsplit input position. -/
theorem preCollisionMap_position_eq (hb : 0 < b)
    (hscale : ∀ u ∈ Icc (0:ℝ) b, F.scale u = ell^2 * u)
    (t : Icc (0:ℝ) b) (s n : ℝ) (hsn : s^2+n^2=1)
    (z : GaussianPhase E) :
    (preCollisionMap F ell t s n hsn z).1.1 =
      z.1.1 + (ell * (t:ℝ)) • (preCollisionMap F ell t s n hsn z).1.2 := by
  have h := referenceCoupledPairFlow_position_eq F ell hb
    (phaseSplit s n hsn z).1 hscale t
  have hx : (phaseSplit s n hsn z).1.1 = z.1.1 := rfl
  rw [hx] at h
  exact h

end AcceleratedLogConcave.Kinetic

namespace AcceleratedLogConcave.Kinetic.Reheating
open MeasureTheory Set
variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι

/-- The source reverse-clock transport uses scale `A ρ` and `ℓ² = A`, so its
actual ODE has the comoving position identity at every retained clock. -/
theorem clockTransportFamily_position_eq {μ : Measure E} {A R : ℝ}
    (H : VarianceHeatFamily μ (3*A/4) R) (hA : 0 < A) (hR : A < R)
    (ell : ℝ) (hEll : ell^2 = A) (z : E × E) (t : Icc (0:ℝ) (1/2)) :
    (referenceCoupledTrajectory (clockTransportFamily H hA hR) ell z t).1 =
      z.1 + (ell * (t:ℝ)) •
        (referenceCoupledTrajectory (clockTransportFamily H hA hR) ell z t).2 := by
  apply referenceCoupledTrajectory_position_eq
    (clockTransportFamily H hA hR) ell (by norm_num) z ?_ t
  intro u hu
  rw [clockTransportFamily_scale H hA hR u hu, hEll]

/-- Source flow homeomorphism form, usable at the pre-collision readout. -/
theorem clockTransportFamily_pairFlow_position_eq {μ : Measure E} {A R : ℝ}
    (H : VarianceHeatFamily μ (3*A/4) R) (hA : 0 < A) (hR : A < R)
    (ell : ℝ) (hEll : ell^2 = A) (z : E × E) (t : Icc (0:ℝ) (1/2)) :
    (referenceCoupledPairFlow (clockTransportFamily H hA hR) ell t z).1 =
      z.1 + (ell * (t:ℝ)) •
        (referenceCoupledPairFlow (clockTransportFamily H hA hR) ell t z).2 := by
  apply referenceCoupledPairFlow_position_eq
    (clockTransportFamily H hA hR) ell (by norm_num) z ?_ t
  intro u hu
  rw [clockTransportFamily_scale H hA hR u hu, hEll]

/-- The source pre-collision state, including its initial Gaussian momentum
split, retains the original position as its comoving base point. -/
theorem clockTransportFamily_preCollisionMap_position_eq
    {μ : Measure E} {A R : ℝ}
    (H : VarianceHeatFamily μ (3*A/4) R) (hA : 0 < A) (hR : A < R)
    (ell : ℝ) (hEll : ell^2 = A) (t : Icc (0:ℝ) (1/2))
    (s n : ℝ) (hsn : s^2+n^2=1) (z : GaussianPhase E) :
    (preCollisionMap (clockTransportFamily H hA hR) ell t s n hsn z).1.1 =
      z.1.1 + (ell * (t:ℝ)) •
        (preCollisionMap (clockTransportFamily H hA hR) ell t s n hsn z).1.2 := by
  apply preCollisionMap_position_eq
    (clockTransportFamily H hA hR) ell (by norm_num) ?_ t s n hsn z
  intro u hu
  rw [clockTransportFamily_scale H hA hR u hu, hEll]

end AcceleratedLogConcave.Kinetic.Reheating
