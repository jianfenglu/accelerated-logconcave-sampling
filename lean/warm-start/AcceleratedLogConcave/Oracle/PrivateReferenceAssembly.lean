import AcceleratedLogConcave.Oracle.MeanPrivateReferenceBridge

/-! Exact law of the literal final reference affine row, with its returned
child vector, actual final residual coefficient and separate reserve. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set
open scoped NNReal
namespace AcceleratedLogConcave.Oracle.PrivateReferenceAssembly
open Conditional Numerics.AffineGraph
variable {d m n : ℕ} (S : SamplingGeometry m) (e : Fin n ≃ S.Node) (r : ℝ)
  (hm : 0 < m) (hr : 0 < r)
  {F : Point d → ℝ} (hF : ContDiff ℝ 2 F) {ell : ℝ} (hell : 0 ≤ ell)
  (hlo : ∀ z v, 0 ≤ fderiv ℝ (fderiv ℝ F) z v v)
  (hup : ∀ z v, fderiv ℝ (fderiv ℝ F) z v v ≤ ell*‖v‖^2) (x : Point d)

/-- Literal reference outputs enter through the source final weights/widths.
The stored seed and reserve are distinct coordinates. -/
def output (z : (Point d × ((Fin n → Point d) × Point d)) × Point d) : Point d :=
  (PrivateSamplingReferenceLaw.readout S hF hell hlo hup x hr z.1.1 +
    PrivateFinalGaussian.preNoise S e r z.1.2) + (S.τ/2) • z.2

include hm hr in
/-- Normalize the complete actual final weighted Gaussian aggregation; this
uses the joint vector law, not coordinate marginals or centered moment bounds. -/
theorem normalized_preNoise_preserving :
    MeasurePreserving (fun z => (S.τ/Real.sqrt 2)⁻¹ • PrivateFinalGaussian.preNoise S e r z)
      ((Measure.pi (fun _ : Fin n => stdGaussian (Point d))).prod (stdGaussian (Point d)))
      (stdGaussian (Point d)) := by
  have hn : S.τ/Real.sqrt 2 ≠ 0 := ne_of_gt (div_pos
    (S.R_pos.trans_le S.R_le_τ) (by positivity))
  have hs : MeasurePreserving (fun y : Point d => (S.τ/Real.sqrt 2)⁻¹ • y)
      ((stdGaussian (Point d)).map (fun y => (S.τ/Real.sqrt 2) • y)) (stdGaussian (Point d)) := by
    refine ⟨by fun_prop,?_⟩
    rw [Measure.map_map (by fun_prop) (by fun_prop)]
    simp only [Function.comp_def,smul_smul,inv_mul_cancel₀ hn,one_smul]
    exact Measure.map_id
  exact hs.comp (PrivateFinalGaussian.preNoise_preserving S e r hm hr)

include hm in
/-- Full reference affine row on the exact returned-vector/residual/reserve
joint law has the required heat posterior law. -/
theorem output_preserving :
    MeasurePreserving (output S e r hr hF hell hlo hup x)
      (((stdGaussian (Point d)).prod
        ((Measure.pi (fun _ : Fin n => stdGaussian (Point d))).prod (stdGaussian (Point d)))).prod
          (stdGaussian (Point d)))
      (Channels.forward (baseLaw F x r) ⟨S.τ^2,by positivity⟩) := by
  have hp := ((MeasurePreserving.id (stdGaussian (Point d))).prod
    (normalized_preNoise_preserving (d := d) S e r hm hr)).prod
      (MeasurePreserving.id (stdGaussian (Point d)))
  have hh := (PrivateSamplingReferenceLaw.reference_preserving S hF hell hlo hup x hr).comp hp
  convert hh using 1
  funext z
  dsimp only [output,Function.comp_apply,Prod.map,Prod.fst,Prod.snd,id_eq]
  rw [smul_smul,mul_inv_cancel₀ (ne_of_gt (div_pos
    (S.R_pos.trans_le S.R_le_τ) (by positivity))),one_smul]

end AcceleratedLogConcave.Oracle.PrivateReferenceAssembly
