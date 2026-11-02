import AcceleratedLogConcave.Analysis.AngleAffinePullback
import AcceleratedLogConcave.Analysis.AngleDirectionalScaling
import AcceleratedLogConcave.Numerics.CenterMeanPhaseCoordinates

/-! Exact gradient-jet affine pullback, including zero momentum directions.
The gradient input is placed first among the physical derivative slots. -/
noncomputable section
open scoped ContDiff
namespace AcceleratedLogConcave.Analysis.AnglePhase
open Tensor.AdjointReduction Tensor.PolynomialClosure Numerics.CenterMeanSecondJetSource
variable {D : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin D)
local notation "EP" => EuclideanSpace ℝ (Fin (D+D))

def phasePositionCLM : EP →L[ℝ] E :=
  (WithLp.fstL 2 ℝ E E).comp phaseCoordinateEquiv.toContinuousLinearEquiv.toContinuousLinearMap

private theorem partialAlong_map_id {I V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (d : I → V) (J : List I) (f : V → ℝ) :
    partialAlong id (J.map d) f = partialAlong d J f := by
  induction J with
  | nil => rfl
  | cons i J ih => simp only [List.map_cons,partialAlong,id_eq,ih]

theorem ordered_gradient_affine_pullback (f : E → ℝ) (hf : ContDiff ℝ ∞ f)
    (M : E) (q a : ℝ) (w : EP) (J : List EP) (z : EP) :
    partialAlong id J (dir w (fun x => a⁻¹ * f (M+q • phasePosition x))) z =
      (a⁻¹ * q^(J.length+1)) *
        partialAlong phasePosition (w::J) f (M+q • phasePosition z) := by
  let L : EP →L[ℝ] E := q • phasePositionCLM
  have hs : ContDiff ℝ ∞ (fun x => f (M+L x)) :=
    hf.comp (contDiff_const.add L.contDiff)
  change partialAlong id J (dir w (fun x => a⁻¹ * f (M+L x))) z = _
  rw [partialAlong_dir id J (contDiff_const.mul hs) w]
  change partialAlong id (w::J) (fun x => a⁻¹ * f (M+L x)) z = _
  rw [partialAlong_const_mul id (w::J) _ hs,partialAlong_comp_affine hf M L]
  rw [partialAlong_map_id]
  change a⁻¹ * partialAlong (fun v => q • phasePosition v) (w::J) f
    (M+q • phasePosition z) = _
  rw [partialAlong_scaled_directions phasePosition (w::J) q hf]
  simp only [List.length_cons,mul_assoc]
end AcceleratedLogConcave.Analysis.AnglePhase
