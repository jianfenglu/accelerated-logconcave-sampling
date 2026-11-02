import AcceleratedLogConcave.Tensor.ActualCoefficientSplitBounds
import AcceleratedLogConcave.Conditional.FirstJet

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped ContDiff RealInnerProductSpace
namespace AcceleratedLogConcave.Conditional.PositiveVarianceFlowData
open Tensor.AdjointReduction
variable {D : ℕ} (d : PositiveVarianceFlowData (EuclideanSpace ℝ (Fin D)))

/-- Exact actual Hessian-coordinate identity, including zero time. -/
theorem hessian_coordinate_eq_firstJet {t : ℝ} (ht : -1 < t ∧ t < 1)
    (y u v : EuclideanSpace ℝ (Fin D)) :
    dir u (dir v (interpolationPotential d.F d.x d.r t)) y =
      inner ℝ v u + d.r*t^2 * inner ℝ v (firstScaledJet d.F d.x d.r t y u) := by
  have hm : ContDiff ℝ ∞ (conditionalMean d.F d.x d.r t) := by
    have hc : ContDiff ℝ ∞ (fun y : EuclideanSpace ℝ (Fin D) => (t,y)) :=
      contDiff_const.prodMk contDiff_id
    have hh := (contDiffOn_conditionalMean d.hF d.hlo d.hhi d.x d.r).comp
      hc.contDiffOn (s := Set.univ) (fun _ _ => ht)
    exact contDiffOn_univ.mp hh
  have hfm := ((hm.differentiable (by simp)) y).hasFDerivAt
  rw [fderiv_conditionalMean_eq_smul_firstScaledJet d.hF d.hlo d.hhi d.x d.r ht.1 ht.2] at hfm
  have he : dir v (interpolationPotential d.F d.x d.r t) =
      fun z => inner ℝ v (z + (d.r*t) • conditionalMean d.F d.x d.r t z) := by
    funext z
    rw [← gradient_interpolationPotential d.hF d.hlo d.hhi d.x d.r ht.1 ht.2 z]
    simp [dir]
  rw [he]
  have hs := (hasFDerivAt_id y).add (hfm.const_smul (d.r*t))
  have hc := (innerSL ℝ v).hasFDerivAt.comp y hs
  change fderiv ℝ (fun z => inner ℝ v (z + (d.r*t) • conditionalMean d.F d.x d.r t z)) y u = _
  change HasFDerivAt (fun z => inner ℝ v (z + (d.r*t) • conditionalMean d.F d.x d.r t z)) _ y at hc
  rw [hc.fderiv]
  simp only [ContinuousLinearMap.comp_apply, add_apply, smul_apply,
    ContinuousLinearMap.id_apply]
  change inner ℝ v (u + (d.r*t) • t • firstScaledJet d.F d.x d.r t y u) = _
  rw [inner_add_right,inner_smul_right,inner_smul_right]
  ring

end AcceleratedLogConcave.Conditional.PositiveVarianceFlowData

namespace AcceleratedLogConcave.Tensor.ActualCoefficientIntegrability
open Conditional
variable {D : ℕ} (d : PositiveVarianceFlowData (EuclideanSpace ℝ (Fin D)))

def identityCoefficient : Coeff (Fin 2) D := WithLp.toLp 2
  (fun a => inner ℝ (coordinateDirection D (a 0)) (coordinateDirection D (a 1)))

/-- The actual Hessian coefficient is the identity plus a small multiple of
literal J1. The original ell=0 case is retained. -/
theorem coefficientEnvironment_hessian_eq_identity_add_J1 {t : ℝ}
    (ht : -1 < t ∧ t < 1) (y : EuclideanSpace ℝ (Fin D)) :
    coefficientEnvironment d.F d.x d.ell d.r t (Sum.inr ()) y =
      identityCoefficient (D := D) + (d.r^2*d.ell*t^2) •
        (show Coeff (Fin 2) D from coefficientEnvironment d.F d.x d.ell d.r t (Sum.inl 0) y) := by
  ext a
  change Fin 2 → Fin D at a
  change AdjointReduction.dir (coordinateDirection D (a 0))
      (AdjointReduction.dir (coordinateDirection D (a 1)) (interpolationPotential d.F d.x d.r t)) y =
    inner ℝ (coordinateDirection D (a 0)) (coordinateDirection D (a 1)) +
      (d.r^2*d.ell*t^2) * ((d.ell*d.r*((0+1).factorial : ℝ))⁻¹ *
        inner ℝ (coordinateDirection D (a 0))
          (scaledJet 1 d.F d.x d.r t y (fun i => coordinateDirection D (a i.succ))))
  rw [d.hessian_coordinate_eq_firstJet ht,
    ScaledJetPolynomial.scaledJet_one_apply_eq_firstScaledJet d.hF d.hlo d.hhi d.x d.r ht.1 ht.2]
  have hs := firstScaledJet_symmetric d.hF d.hlo d.hhi d.x d.hr.ne' ht.1 ht.2 y
  have he : inner ℝ (coordinateDirection D (a 1))
      (firstScaledJet d.F d.x d.r t y (coordinateDirection D (a 0))) =
      inner ℝ (coordinateDirection D (a 0))
        (firstScaledJet d.F d.x d.r t y (coordinateDirection D (a 1))) := by
    rw [real_inner_comm]
    exact hs _ _
  rw [he,real_inner_comm (coordinateDirection D (a 1))]
  norm_num
  rcases lt_or_eq_of_le d.hell with hell | hflat
  · field_simp [hell.ne',d.hr.ne']
  · have hz : firstScaledJet d.F d.x d.r t y = 0 := norm_le_zero_iff.mp
      (by simpa [←hflat] using norm_firstScaledJet_le d.hF d.hell d.hlo d.hhi d.x d.hr ht.1 ht.2 y)
    simp [hz,←hflat]

end AcceleratedLogConcave.Tensor.ActualCoefficientIntegrability
