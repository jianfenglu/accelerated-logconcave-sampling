import AcceleratedLogConcave.Analysis.Poisson.ReferencePoisson
import AcceleratedLogConcave.Kinetic.MovingCorrector
import AcceleratedLogConcave.Kinetic.PhasePullback

/-! The actual moving-corrector estimates, instantiated with the constructed
weighted Poisson gradient inverse. Differentiation of the corrector is asserted
in scalar pairings; no unjustified strong-adjoint derivative is used. -/
noncomputable section
open MeasureTheory InnerProductSpace Set
open scoped Topology
namespace AcceleratedLogConcave.Analysis.Poisson.ReferencePoissonFamily
open AcceleratedLogConcave.Kinetic
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {a b : ℝ} (F : ReferencePoissonFamily E a b)

/-- The actual corrector in the fixed reference Gaussian phase space. -/
def corrector (t : ℝ) : Lp ℝ 2 (gaussianPhaseMeasure (F.law a)) →L[ℝ]
    Lp ℝ 2 (gaussianPhaseMeasure (F.law a)) :=
  referenceCorrector (F.law a) (F.gradientInverse t)

/-- Composition by the actual flow on position, leaving both Gaussian coordinates fixed. -/
def phaseUnitary (t : Icc a b) : Lp ℝ 2 (gaussianPhaseMeasure (F.law t)) ≃ₗᵢ[ℝ]
    Lp ℝ 2 (gaussianPhaseMeasure (F.law a)) :=
  gaussianPhasePullback (F.flow t).toMeasurableEquiv (F.flow_measurePreserving t)

/-- The actual target-time weighted Poisson corrector. -/
def physicalCorrector (t : Icc a b) : Lp ℝ 2 (gaussianPhaseMeasure (F.law t)) →L[ℝ]
    Lp ℝ 2 (gaussianPhaseMeasure (F.law t)) :=
  gaussianCorrector (F.law t) (F.potential t) (F.potential_C2 t)
    (F.integrable t t.property) (F.gibbs_law t t.property) (F.lower t) 1
    (F.lower_pos t t.property) (F.hessian_lower t t.property)
    (by simpa only [one_mul] using F.hessian_upper t t.property)

/-- The reference corrector is exactly the physical corrector conjugated by
the proved phase unitary, not a separately assumed reference operator. -/
theorem corrector_eq_physical (t : ℝ) (ht : t ∈ Ioo a b) :
    F.corrector t = (F.phaseUnitary ⟨t, ht.1.le, ht.2.le⟩).toLinearIsometry.toContinuousLinearMap ∘L
      F.physicalCorrector ⟨t, ht.1.le, ht.2.le⟩ ∘L
      (F.phaseUnitary ⟨t, ht.1.le, ht.2.le⟩).symm.toLinearIsometry.toContinuousLinearMap := by
  let τ : Icc a b := ⟨t, ht.1.le, ht.2.le⟩
  let G := gradientPoissonInverse (F.law t) (F.potential t) (F.potential_C2 t)
    (F.integrable t τ.property) (F.gibbs_law t τ.property) (F.lower t) 1
    (F.lower_pos t τ.property) (F.hessian_lower t τ.property)
    (by simpa only [one_mul] using F.hessian_upper t τ.property)
  have hG : F.gradientInverse t =
      spatialGradientConjugate (F.flow τ).toMeasurableEquiv (F.flow_measurePreserving τ) G := by
    apply ContinuousLinearMap.ext
    intro g
    exact F.gradientInverse_eq_physical t ht g
  unfold corrector
  rw [hG]
  exact (gaussianCorrector_phase_conjugacy (F.flow τ).toMeasurableEquiv
    (F.flow_measurePreserving τ) (F.potential t) (F.potential_C2 t)
    (F.integrable t τ.property) (F.gibbs_law t τ.property) (F.lower t) 1
    (F.lower_pos t τ.property) (F.hessian_lower t τ.property)
    (by simpa only [one_mul] using F.hessian_upper t τ.property)).symm

/-- The bounded weak material derivative of the actual corrector. -/
def materialCorrector (t : ℝ) (ht : t ∈ Ioo a b) :
    Lp ℝ 2 (gaussianPhaseMeasure (F.law a)) →L[ℝ]
      Lp ℝ 2 (gaussianPhaseMeasure (F.law a)) :=
  referenceCorrector (F.law a) (F.materialOperator t ht)

/-- The sharp moving-corrector bound has no spectral-gap factor. -/
theorem materialCorrector_norm_le (t : ℝ) (ht : t ∈ Ioo a b) :
    ‖F.materialCorrector t ht‖ ≤ |F.scale t| :=
  (referenceCorrector_norm_le (F.law a) _).trans (F.materialOperator_norm_le t ht)

/-- Every scalar pairing has the claimed material derivative. -/
theorem corrector_pairing_hasDerivAt (t : ℝ) (ht : t ∈ Ioo a b)
    (f g : Lp ℝ 2 (gaussianPhaseMeasure (F.law a))) :
    HasDerivAt (fun s => inner ℝ f (F.corrector s g))
      (inner ℝ f (F.materialCorrector t ht g)) t := by
  let B := fun _ : ℝ => F.materialOperator t ht
  simpa only [corrector, materialCorrector, referenceCorrector_pairing] using
    hasDerivAt_referenceCorrector_pairing (F.law a) F.gradientInverse B t
      (fun g => F.gradientInverse_hasDerivAt t ht g) f g

/-- The actual moving-current term with exact macro/micro factors. -/
theorem materialCorrector_macro_micro_bound (t : ℝ) (ht : t ∈ Ioo a b)
    (f g : Lp ℝ 2 (gaussianPhaseMeasure (F.law a))) :
    |inner ℝ f (F.materialCorrector t ht g)| ≤
      |F.scale t| * ‖gaussianPositionProjection (F.law a) f‖ *
        ‖g - gaussianPositionProjection (F.law a) g‖ := by
  unfold materialCorrector
  rw [referenceCorrector_pairing]
  apply (referenceCorrector_material_macro_micro_bound (F.law a) _ f g).trans
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (F.materialOperator_norm_le t ht) (norm_nonneg _)) (norm_nonneg _)

/-- The corrector increment is controlled by the integrated drift scale. -/
theorem corrector_norm_sub_le_integral {s t : ℝ} (hst : s ≤ t)
    (hs : s ∈ Ioo a b) (ht : t ∈ Ioo a b) :
    ‖F.corrector t - F.corrector s‖ ≤ ∫ r in s..t, |F.scale r| :=
  (referenceCorrector_norm_sub_le (F.law a) _ _).trans
    (F.gradientInverse_norm_sub_le_integral hs ht hst)

/-- The actual quadratic corrector term along a differentiable phase curve. -/
theorem corrector_quadratic_hasDerivAt (t : ℝ) (ht : t ∈ Ioo a b)
    (f : ℝ → Lp ℝ 2 (gaussianPhaseMeasure (F.law a)))
    (f' : Lp ℝ 2 (gaussianPhaseMeasure (F.law a))) (hf : HasDerivAt f f' t) :
    HasDerivAt (fun s => inner ℝ (f s) (F.corrector s (f s)))
      (inner ℝ f' (F.corrector t (f t)) + inner ℝ (f t) (F.corrector t f') +
        inner ℝ (f t) (F.materialCorrector t ht (f t))) t := by
  let B := fun _ : ℝ => F.materialOperator t ht
  simpa only [corrector, materialCorrector, referenceCorrector_pairing] using
    hasDerivAt_referenceCorrector_quadratic (F.law a) F.gradientInverse B t
      (F.gradientInverse_continuousAt t ht) (fun g => F.gradientInverse_hasDerivAt t ht g) f f' hf

end AcceleratedLogConcave.Analysis.Poisson.ReferencePoissonFamily
