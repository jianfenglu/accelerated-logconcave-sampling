import AcceleratedLogConcave.Kinetic.ReferenceFlow.PhysicalLaw
import AcceleratedLogConcave.Kinetic.ReferenceFlow.TransportEstimate
import AcceleratedLogConcave.Kinetic.Mixing.Energy

/-! Actual transport energy differentiation on the centered compact core. -/
noncomputable section
open Set Filter MeasureTheory InnerProductSpace
open scoped Topology
namespace AcceleratedLogConcave.Kinetic
open Analysis.Poisson
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {a b : ℝ} (F : ReferencePoissonFamily E a b)

theorem physicalMovingCore_norm_sq_hasDerivAt (ell s n : ℝ) (hsn : s^2+n^2=1)
    (T : Icc a b) {φ : GaussianPhase E → ℝ} (hφ : ContDiff ℝ 1 φ)
    (hc : HasCompactSupport φ) (t : ℝ) (ht : t ∈ Ioo a b) :
    HasDerivAt (fun u => ‖physicalMovingCoreLp F ell s n hsn T hφ.continuous hc u‖^2) 0 t := by
  have he : (fun u => ‖physicalMovingCoreLp F ell s n hsn T hφ.continuous hc u‖^2) =ᶠ[𝓝 t]
      fun _ => ∫ z, (φ z)^2 ∂gaussianPhaseMeasure (F.law T) := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with u hu
    rw [physicalMovingCoreLp_eq_phaseUnitary F ell s n hsn T hφ hc u hu,
      LinearIsometryEquiv.norm_map,physicalTransportLp_norm_sq F ell s n hsn T hφ hc u hu]
  exact (hasDerivAt_const t (∫ z, (φ z)^2 ∂gaussianPhaseMeasure (F.law T))).congr_of_eventuallyEq he

theorem physicalTransportEnergy_derivative_le (ell ε : ℝ) (hell : 0 ≤ ell) (hε : 0 ≤ ε)
    (T : Icc a b) {φ : GaussianPhase E → ℝ} (hφ : ContDiff ℝ 1 φ)
    (hc : HasCompactSupport φ) (hmean : (∫ z, φ z ∂gaussianPhaseMeasure (F.law T)) = 0)
    (t : ℝ) (ht : t ∈ Ioo a b) (hscale : |F.scale t| ≤ ell/4) :
    let g := physicalMovingCoreLp F ell (1/2) (Real.sqrt 3/2) source_split_coefficients T hφ.continuous hc;
    let f := physicalTransportLp F ell (1/2) (Real.sqrt 3/2) source_split_coefficients T hφ hc t ht;
    ∃ D : ℝ, HasDerivAt (fun u => quadraticEnergy (F.corrector u) ε (g u)) D t ∧
      D ≤ -ε*ell*‖f‖^2/8 + 3*ε*ell*‖f-gaussianPositionProjection (F.law t) f‖^2 := by
  dsimp only
  have hm := (physicalTransportLp_mean F ell (1/2) (Real.sqrt 3/2)
    source_split_coefficients T hφ hc t ht).trans hmean
  obtain ⟨D,hD,hbound⟩ := physicalCoreCurrent_derivative_le F ell hell T hφ hc t ht hscale hm
  have hn := physicalMovingCore_norm_sq_hasDerivAt F ell (1/2) (Real.sqrt 3/2)
    source_split_coefficients T hφ hc t ht
  refine ⟨ε*D, ?_, ?_⟩
  · have hd := (hn.const_mul (1/2:ℝ)).add (hD.const_mul ε)
    convert hd using 1
    · funext u
      simp only [quadraticEnergy,Pi.add_apply]
      rw [real_inner_comm]
    · ring
  · have hh := mul_le_mul_of_nonneg_left hbound hε
    nlinarith

end AcceleratedLogConcave.Kinetic
