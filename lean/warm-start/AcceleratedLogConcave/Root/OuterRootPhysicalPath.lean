import AcceleratedLogConcave.Root.OuterRootScoreScaling
import AcceleratedLogConcave.Numerics.AffineFlowIdentities

/-! The actual conditional root path obeys the physical coupled
ODE, with the literal rescaled heat score. No abstract drift-identification
premise or zero-clock division appears. Flow uniqueness is a later bridge. -/
noncomputable section
set_option autoImplicit false
open Set
namespace AcceleratedLogConcave.Root.OuterRootPhysicalPath
open Numerics OuterRootOriginalData OuterRootScoreScaling

def variance (h u : ℝ) : ℝ := 2*h^2*(1-u^2)
def scale (h u : ℝ) : ℝ := 2*h^2*u
variable {ι : Type*} [Fintype ι]
variable {V : (EuclideanSpace ℝ ι) → ℝ} (hV : ContDiff ℝ 2 V) {h : ℝ} (hh : 0 < h)
  (hlo : ∀ z v, 0 ≤ fderiv ℝ (fderiv ℝ V) z v v)
  (hup : ∀ z v, fderiv ℝ (fderiv ℝ V) z v v ≤ ‖v‖^2)

def rawY (xF zeta : (EuclideanSpace ℝ ι)) : ℝ → (EuclideanSpace ℝ ι) :=
  let d := data hV hh hlo hup
  Conditional.convexProbabilityFlow d.hF d.hell d.hlo d.hup xF d.hr d.hb
    (by norm_num) d.hb1 ⟨0,le_rfl,d.hb⟩ zeta

def position (xF zeta : (EuclideanSpace ℝ ι)) (u : ℝ) : (EuclideanSpace ℝ ι) :=
  Real.sqrt h • xF + (Real.sqrt (2*h^2)*u) • rawY hV hh hlo hup xF zeta u

include hh in
theorem scale_sqrt : Real.sqrt (2*h) * Real.sqrt h = Real.sqrt (2*h^2) := by
  rw [← Real.sqrt_mul (by positivity)]
  congr 1
  ring

include hV hh hlo hup in
/-- Both the physical center and physical heat variance are the manuscript's
literal coordinates, including u=0 and u=1/2. -/
theorem conditional_score (xF y : (EuclideanSpace ℝ ι)) {u : ℝ} (hu : u ∈ Icc (0:ℝ) (1/2)) :
    Conditional.conditionalMean (potential V h) xF (Real.sqrt (2*h)) u y =
      Real.sqrt h • gradient (Gibbs.heatPotential V (variance h u))
        (Real.sqrt h • xF + (Real.sqrt (2*h^2)*u) • y) := by
  let d := data hV hh hlo hup
  have hv : 0 < 1-u^2 := by nlinarith [hu.1,hu.2]
  erw [AffineFlowIdentities.conditionalMean_eq_primitiveMean d.hF d.hell d.hlo d.hup
    xF d.hr (by linarith [hu.1]) (by linarith [hu.2])]
  erw [primitiveMean_eq_physical_heatScore hV hh
    (mul_pos d.hr (Real.sqrt_pos.mpr hv)) hlo hup]
  have hvar : h*(Real.sqrt (2*h)*Real.sqrt (1-u^2))^2 =
      variance h u := by
    rw [mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt hv.le]
    unfold variance
    ring
  have hscale : Real.sqrt h*(Real.sqrt (2*h)*u) = Real.sqrt (2*h^2)*u := by
    rw [← mul_assoc, mul_comm (Real.sqrt h), scale_sqrt hh]
  simp only [d, data] at *
  rw [hvar, smul_add, smul_smul, hscale]

theorem rawY_deriv (xF zeta : (EuclideanSpace ℝ ι)) {u : ℝ} (hu : u ∈ Icc (0:ℝ) (1/2)) :
    HasDerivWithinAt (rawY hV hh hlo hup xF zeta)
      ((-Real.sqrt (2*h^2)) •
        gradient (Gibbs.heatPotential V (variance h u))
          (position hV hh hlo hup xF zeta u)) (Icc (0:ℝ) (1/2)) u := by
  let d := data hV hh hlo hup
  have hd := Conditional.convexProbabilityFlow_deriv d.hF d.hell d.hlo d.hup
    xF d.hr d.hb (by norm_num) d.hb1 ⟨0,le_rfl,d.hb⟩ zeta hu
  change HasDerivWithinAt (rawY hV hh hlo hup xF zeta)
    ((-Real.sqrt (2*h)) • Conditional.conditionalMean (potential V h) xF
      (Real.sqrt (2*h)) u (rawY hV hh hlo hup xF zeta u)) _ _ at hd
  rw [conditional_score hV hh hlo hup xF _ hu, smul_smul, neg_mul, scale_sqrt hh] at hd
  exact hd

/-- The A-coordinate includes the ell*Y Hamiltonian term; the heat-flow
reference drift alone is not the conditional sampling trajectory. -/
theorem position_deriv (xF zeta : (EuclideanSpace ℝ ι)) {u : ℝ} (hu : u ∈ Icc (0:ℝ) (1/2)) :
    HasDerivWithinAt (position hV hh hlo hup xF zeta)
      (Real.sqrt (2*h^2) • rawY hV hh hlo hup xF zeta u -
        scale h u •
          gradient (Gibbs.heatPotential V (variance h u))
            (position hV hh hlo hup xF zeta u)) (Icc (0:ℝ) (1/2)) u := by
  have hd := (((hasDerivWithinAt_id u (Icc (0:ℝ) (1/2))).const_mul
    (Real.sqrt (2*h^2))).smul (rawY_deriv hV hh hlo hup xF zeta hu)).const_add
      (Real.sqrt h • xF)
  have he : (Real.sqrt (2*h^2)*u)*(-Real.sqrt (2*h^2)) =
      -scale h u := by
    have hs := Real.sq_sqrt (show 0 ≤ 2*h^2 by positivity)
    unfold scale
    calc
      _ = -(Real.sqrt (2*h^2)^2*u) := by ring
      _ = _ := by rw [hs]
  change HasDerivWithinAt (position hV hh hlo hup xF zeta) _ _ _ at hd
  simp only [id_eq, mul_one] at hd
  rw [smul_smul, he] at hd
  simpa only [neg_smul, sub_eq_add_neg, add_comm] using hd

end AcceleratedLogConcave.Root.OuterRootPhysicalPath
