import AcceleratedLogConcave.Kinetic.Mixing.PhysicalFactorization
import AcceleratedLogConcave.Kinetic.Corrector

/-!

-/
noncomputable section
open MeasureTheory ProbabilityTheory InnerProductSpace
open scoped ContDiff RealInnerProductSpace
namespace AcceleratedLogConcave.Kinetic.DirectW12
open ConditionalContraction Analysis.Poisson

section Jensen
variable {X Ω : Type*} [MeasurableSpace X] [MeasurableSpace Ω]
  {μ : Measure X} {η : Measure Ω} {p q : Ω → X}

/-- The old-state adjoint acts on the same-joint new-minus-old difference. -/
theorem observable_difference (hp : MeasurePreserving p η μ)
    (hq : MeasurePreserving q η μ) (f : Lp ℝ 2 μ) :
    referenceChannel hp hq f - f =
      (Lp.compMeasurePreservingₗᵢ ℝ p hp).toContinuousLinearMap.adjoint
        (Lp.compMeasurePreservingₗᵢ ℝ q hq f -
          Lp.compMeasurePreservingₗᵢ ℝ p hp f) := by
  let I : Lp ℝ 2 μ →ₗᵢ[ℝ] Lp ℝ 2 η := Lp.compMeasurePreservingₗᵢ ℝ p hp
  have hi : I.toContinuousLinearMap.adjoint (I f) = f :=
    congrArg (fun L : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ => L f) I.adjoint_comp_self
  rw [map_sub, hi]
  rfl

/-- Conditional Jensen, with no reversibility and no replacement coupling. -/
theorem observable_jensen (hp : MeasurePreserving p η μ)
    (hq : MeasurePreserving q η μ) (f : Lp ℝ 2 μ) :
    ‖referenceChannel hp hq f - f‖ ≤
      ‖Lp.compMeasurePreservingₗᵢ ℝ q hq f -
        Lp.compMeasurePreservingₗᵢ ℝ p hp f‖ := by
  rw [observable_difference hp hq]
  let I : Lp ℝ 2 μ →ₗᵢ[ℝ] Lp ℝ 2 η := Lp.compMeasurePreservingₗᵢ ℝ p hp
  have hi : ‖I.toContinuousLinearMap.adjoint‖ ≤ 1 := by
    rw [ContinuousLinearMap.adjoint.norm_map]
    exact I.norm_toContinuousLinearMap_le
  exact (I.toContinuousLinearMap.adjoint.le_opNorm _).trans
    (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hi (norm_nonneg _))
end Jensen

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable (μ : Measure E) [IsProbabilityMeasure μ]
  (s n : ℝ) (hsn : s^2+n^2=1)
  (κ : Kernel (GaussianPhase E) E) [IsMarkovKernel κ]
  (hκ : ConditionallyInvariant (stdGaussian E) κ)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Literal old coordinate is z.1.2, not a newly sampled Gaussian. -/
theorem physical_momentum_increment (G : E → E) (z : GaussianPhase E × E) :
    inner ℝ (G (physicalDormantNew s n hsn z).1.1)
        (physicalDormantNew s n hsn z).1.2 -
      inner ℝ (G (physicalDormantOld s n hsn z).1.1)
        (physicalDormantOld s n hsn z).1.2 =
      n * inner ℝ (z.2-z.1.2) (G z.1.1.1) := by
  change inner ℝ (G z.1.1.1) (s • z.1.1.2 + n • z.2) -
    inner ℝ (G z.1.1.1) (s • z.1.1.2 + n • z.1.2) = _
  simp only [inner_add_right, real_inner_smul_right, inner_sub_left]
  rw [real_inner_comm (G z.1.1.1) z.2, real_inner_comm (G z.1.1.1) z.1.2]
  ring

/-- Both exceptional null sets are pulled through their actual marginal maps. -/
theorem physical_lift_increment_ae (G : Lp E 2 μ) :
    (fun z => (Lp.compMeasurePreservingₗᵢ ℝ (physicalDormantNew s n hsn)
          (physicalDormantNew_preserving s n hsn μ κ hκ)
          (gaussianMomentumEmbedding μ G) -
        Lp.compMeasurePreservingₗᵢ ℝ (physicalDormantOld s n hsn)
          (physicalDormantOld_preserving s n hsn μ κ)
          (gaussianMomentumEmbedding μ G)) z) =ᵐ[
            dormantJoint (μ.prod (stdGaussian E)) (stdGaussian E) κ]
      fun z => n * inner ℝ (z.2-z.1.2) (G z.1.1.1) := by
  let hp := physicalDormantOld_preserving s n hsn μ κ
  let hq := physicalDormantNew_preserving s n hsn μ κ hκ
  let f := gaussianMomentumEmbedding μ G
  filter_upwards [Lp.coeFn_sub (Lp.compMeasurePreservingₗᵢ ℝ _ hq f)
      (Lp.compMeasurePreservingₗᵢ ℝ _ hp f),
    Lp.coeFn_compMeasurePreserving f hq, Lp.coeFn_compMeasurePreserving f hp,
    hq.quasiMeasurePreserving.ae (gaussianMomentumEmbedding_coe μ G),
    hp.quasiMeasurePreserving.ae (gaussianMomentumEmbedding_coe μ G)] with z hd hqz hpz hGq hGp
  rw [hd]
  change (Lp.compMeasurePreserving (physicalDormantNew s n hsn) hq f) z -
    (Lp.compMeasurePreserving (physicalDormantOld s n hsn) hp f) z = _
  rw [hqz, hpz]
  change (gaussianMomentumEmbedding μ G) (physicalDormantNew s n hsn z) -
    (gaussianMomentumEmbedding μ G) (physicalDormantOld s n hsn z) = _
  rw [hGq, hGp]
  exact physical_momentum_increment s n hsn G z

include s hsn hκ in
/-- Finiteness is supplied by the genuine L2 pullbacks before any covariance bound. -/
theorem physical_lift_increment_integrable_sq (G : Lp E 2 μ) :
    Integrable (fun z => (n * inner ℝ (z.2-z.1.2) (G z.1.1.1))^2)
      (dormantJoint (μ.prod (stdGaussian E)) (stdGaussian E) κ) := by
  let D := Lp.compMeasurePreservingₗᵢ ℝ (physicalDormantNew s n hsn)
      (physicalDormantNew_preserving s n hsn μ κ hκ) (gaussianMomentumEmbedding μ G) -
    Lp.compMeasurePreservingₗᵢ ℝ (physicalDormantOld s n hsn)
      (physicalDormantOld_preserving s n hsn μ κ) (gaussianMomentumEmbedding μ G)
  apply (Lp.memLp D).integrable_sq.congr
  filter_upwards [physical_lift_increment_ae μ s n hsn κ hκ G] with z hz
  exact congrArg (fun r : ℝ => r^2) hz

/-- Squared Jensen expressed as the actual dormant-joint innovation integral.
The integrability is automatic from the difference of two L2 pullbacks. -/
theorem physical_lift_jensen (G : Lp E 2 μ) :
    ‖physicalDormantChannel s n hsn μ κ hκ (gaussianMomentumEmbedding μ G) -
        gaussianMomentumEmbedding μ G‖^2 ≤
      ∫ z, (n * inner ℝ (z.2-z.1.2) (G z.1.1.1))^2
        ∂dormantJoint (μ.prod (stdGaussian E)) (stdGaussian E) κ := by
  let hp := physicalDormantOld_preserving s n hsn μ κ
  let hq := physicalDormantNew_preserving s n hsn μ κ hκ
  let f := gaussianMomentumEmbedding μ G
  let D := Lp.compMeasurePreservingₗᵢ ℝ _ hq f - Lp.compMeasurePreservingₗᵢ ℝ _ hp f
  have hn := observable_jensen hp hq f
  have he : ‖D‖^2 = ∫ z, (n * inner ℝ (z.2-z.1.2) (G z.1.1.1))^2
      ∂dormantJoint (μ.prod (stdGaussian E)) (stdGaussian E) κ := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [physical_lift_increment_ae μ s n hsn κ hκ G] with z hz
    change inner ℝ (D z) (D z) = _
    rw [hz]
    simp only [real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]
  change ‖referenceChannel hp hq f - f‖^2 ≤ _
  rw [← he]
  nlinarith [norm_nonneg (referenceChannel hp hq f-f), norm_nonneg D]

section Corrector
variable (V : E → ℝ) (hV : ContDiff ℝ 2 V)
  (hI : Integrable (fun x => Real.exp (-V x)))
  (hμ : μ = volume.tilted (fun x => -V x))
  (m L : ℝ) (hm : 0 < m)
  (hlower : ∀ x a, m * ‖a‖^2 ≤ fderiv ℝ (fderiv ℝ V) x a a)
  (hupper : ∀ x a, fderiv ℝ (fderiv ℝ V) x a a ≤ L * ‖a‖^2)

/-- Actual corrector-adjoint representative difference on the actual joint. -/
theorem physical_corrector_increment_ae (f : Lp ℝ 2 (gaussianPhaseMeasure μ)) :
    let A := gaussianCorrector μ V hV hI hμ m L hm hlower hupper
    let G := gradientPoissonInverse μ V hV hI hμ m L hm hlower hupper
      (gaussianAverage μ f)
    (fun z => (Lp.compMeasurePreservingₗᵢ ℝ (physicalDormantNew s n hsn)
          (physicalDormantNew_preserving s n hsn μ κ hκ) (A.adjoint f) -
        Lp.compMeasurePreservingₗᵢ ℝ (physicalDormantOld s n hsn)
          (physicalDormantOld_preserving s n hsn μ κ) (A.adjoint f)) z) =ᵐ[
            dormantJoint (μ.prod (stdGaussian E)) (stdGaussian E) κ]
      fun z => n * inner ℝ (z.2-z.1.2) (G z.1.1.1) := by
  dsimp only
  rw [gaussianCorrector_adjoint]
  exact physical_lift_increment_ae μ s n hsn κ hκ _

/-- The actual corrector, on all of the extended L2 space. No extra projection
on hidden or momentum coordinates is imposed on f. -/
theorem physical_corrector_jensen (f : Lp ℝ 2 (gaussianPhaseMeasure μ)) :
    let A := gaussianCorrector μ V hV hI hμ m L hm hlower hupper
    let G := gradientPoissonInverse μ V hV hI hμ m L hm hlower hupper
      (gaussianAverage μ f)
    ‖physicalDormantChannel s n hsn μ κ hκ (A.adjoint f)-A.adjoint f‖^2 ≤
      ∫ z, (n * inner ℝ (z.2-z.1.2) (G z.1.1.1))^2
        ∂dormantJoint (μ.prod (stdGaussian E)) (stdGaussian E) κ := by
  dsimp only
  rw [gaussianCorrector_adjoint]
  exact physical_lift_jensen μ s n hsn κ hκ _
end Corrector
end AcceleratedLogConcave.Kinetic.DirectW12
