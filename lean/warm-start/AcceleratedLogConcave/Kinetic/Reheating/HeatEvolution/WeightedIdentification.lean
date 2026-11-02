import AcceleratedLogConcave.Kinetic.ReferenceChannel

/-! A weighted pushforward identity identifies the L2 density adjoint of an
actual coupling. This is used with proved positive perturbation laws, not with
an assumed formula for the desired signed density. -/
noncomputable section
open MeasureTheory InnerProductSpace
open scoped RealInnerProductSpace ENNReal
namespace AcceleratedLogConcave.Kinetic.Reheating
variable {X Y Ω : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Ω]
  {μ : Measure X} {ν : Measure Y} {η : Measure Ω} {p : Ω → X} {q : Ω → Y}

theorem referenceChannel_adjoint_toLp_of_weighted_map
    (hp : MeasurePreserving p η μ) (hq : MeasurePreserving q η ν)
    {f : X → ℝ} {g : Y → ℝ} (hf : Measurable f) (hg : Measurable g)
    (hfpos : ∀ x, 0 ≤ f x) (hgpos : ∀ y, 0 ≤ g y)
    (hfL : MemLp f 2 μ) (hgL : MemLp g 2 ν)
    (hw : (η.withDensity (fun ω => ENNReal.ofReal (f (p ω)))).map q =
      ν.withDensity (fun y => ENNReal.ofReal (g y))) :
    (referenceChannel hp hq).adjoint (hfL.toLp f) = hgL.toLp g := by
  apply ext_inner_right ℝ
  intro φ
  rw [ContinuousLinearMap.adjoint_inner_left, referenceChannel_pairing, L2.inner_def]
  have hmeas : AEStronglyMeasurable φ ((η.withDensity
      (fun ω => ENNReal.ofReal (f (p ω)))).map q) := by
    rw [hw]
    exact (Lp.aestronglyMeasurable φ).mono_ac (withDensity_absolutelyContinuous _ _)
  have hi := integral_map hq.measurable.aemeasurable hmeas
  rw [hw, integral_withDensity_eq_integral_toReal_smul hg.ennreal_ofReal (by simp),
    integral_withDensity_eq_integral_toReal_smul (f := fun ω => ENNReal.ofReal (f (p ω)))
      (hf.comp hp.measurable).ennreal_ofReal (by simp)] at hi
  simp only [ENNReal.toReal_ofReal, hfpos, hgpos, smul_eq_mul] at hi
  calc
    _ = ∫ ω, f (p ω) * φ (q ω) ∂η := by
      apply integral_congr_ae
      filter_upwards [hp.quasiMeasurePreserving.ae hfL.coeFn_toLp] with ω hω
      rw [hω]
    _ = ∫ y, g y * φ y ∂ν := hi.symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [hgL.coeFn_toLp] with y hy
      simp only [hy, RCLike.inner_apply, conj_trivial, mul_comm]

end AcceleratedLogConcave.Kinetic.Reheating
