import AcceleratedLogConcave.Kinetic.Reheating.OUGaussian
import AcceleratedLogConcave.Kinetic.Reheating.HeatChannel

/-! The Gaussian OU channel with an arbitrary retained coordinate. All estimates
hold for arbitrary joint L2 densities; no independence of the input is assumed. -/
noncomputable section
open MeasureTheory ProbabilityTheory InnerProductSpace
open scoped RealInnerProductSpace
namespace AcceleratedLogConcave.Kinetic.Reheating
variable {X : Type*} [MeasurableSpace X]
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure X) [IsProbabilityMeasure μ]

/-- Retain the base coordinate and refresh the Gaussian coordinate from a fresh draw. -/
def ouProductObservation (t : ℝ) (z : (X × E) × E) : X × E :=
  (z.1.1, gaussianMix E t (z.1.2, z.2))

theorem ouProductObservation_measurePreserving (t : ℝ) (ht : 0 ≤ t) :
    MeasurePreserving (ouProductObservation (X := X) (E := E) t)
      ((μ.prod (stdGaussian E)).prod (stdGaussian E)) (μ.prod (stdGaussian E)) := by
  exact ((MeasurePreserving.id μ).prod (gaussianMix_measurePreserving E t ht)).comp
    (measurePreserving_prodAssoc μ (stdGaussian E) (stdGaussian E))

/-- The actual OU Markov operator on a Gaussian coordinate of a product reference law. -/
def ouProduct (t : ℝ) (ht : 0 ≤ t) :
    Lp ℝ 2 (μ.prod (stdGaussian E)) →L[ℝ] Lp ℝ 2 (μ.prod (stdGaussian E)) :=
  referenceChannel measurePreserving_fst (ouProductObservation_measurePreserving μ t ht)

theorem ouProduct_coe (t : ℝ) (ht : 0 ≤ t) (F : Lp ℝ 2 (μ.prod (stdGaussian E))) :
    ouProduct μ t ht F =ᵐ[μ.prod (stdGaussian E)]
      fun z => ∫ y, F (z.1, gaussianMix E t (z.2, y)) ∂stdGaussian E :=
  referenceChannel_fst_coe _ _ (ouProductObservation_measurePreserving μ t ht) F

theorem ouProduct_norm_le (t : ℝ) (ht : 0 ≤ t) :
    ‖ouProduct (E := E) μ t ht‖ ≤ 1 := referenceChannel_norm_le _ _

private theorem l2_norm_sq_integral {Y : Type*} [MeasurableSpace Y]
    {ν : Measure Y} (F : Lp ℝ 2 ν) : ‖F‖^2 = ∫ y, (F y)^2 ∂ν := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun y => by simp [pow_two]

omit [BorelSpace E] in
/-- Square-integrable joint functions have square-integrable Gaussian sections. -/
theorem memLp_gaussian_section (F : Lp ℝ 2 (μ.prod (stdGaussian E))) :
    ∀ᵐ x ∂μ, MemLp (fun y => F (x,y)) 2 (stdGaussian E) := by
  have h1 := ((Lp.memLp F).integrable (by norm_num)).prod_right_ae
  have h2 := (Lp.memLp F).integrable_sq.prod_right_ae
  filter_upwards [h1, h2] with x hx1 hx2
  exact (memLp_two_iff_integrable_sq hx1.aestronglyMeasurable).2 hx2

/-- The exact sharp conditional variance contraction, without restricting the
joint input density to a tensor product. -/
theorem ouProduct_variance (t : ℝ) (ht : 0 ≤ t)
    (F : Lp ℝ 2 (μ.prod (stdGaussian E))) :
    ‖ouProduct μ t ht F‖^2 - ‖productAverage μ (stdGaussian E) F‖^2 ≤
      Real.exp (-2*t) * (‖F‖^2 - ‖productAverage μ (stdGaussian E) F‖^2) := by
  let G := ouProduct μ t ht F
  let A := productAverage μ (stdGaussian E) F
  have hG := (Lp.memLp G).integrable_sq
  have hF := (Lp.memLp F).integrable_sq
  have hA := (Lp.memLp A).integrable_sq
  have hp : ∀ᵐ x ∂μ,
      (∫ y, (G (x,y))^2 ∂stdGaussian E) - (A x)^2 ≤
        Real.exp (-2*t) * ((∫ y, (F (x,y))^2 ∂stdGaussian E) - (A x)^2) := by
    filter_upwards [memLp_gaussian_section μ F, productAverage_coe μ (stdGaussian E) F,
      Measure.ae_ae_of_ae_prod (ouProduct_coe μ t ht F)] with x hx hax hgx
    have hv := gaussianOU_variance_integral E t ht (fun y => F (x,y)) hx
    change A x = _ at hax
    rw [hax]
    have heq : (∫ y, (G (x,y))^2 ∂stdGaussian E) =
        ∫ y, (∫ z, F (x, gaussianMix E t (y,z)) ∂stdGaussian E)^2 ∂stdGaussian E := by
      apply integral_congr_ae
      filter_upwards [hgx] with y hy
      change G (x,y) = _ at hy
      rw [hy]
    rw [heq]
    exact hv
  have hi := integral_mono_ae (hG.integral_prod_left.sub hA)
    ((hF.integral_prod_left.sub hA).const_mul (Real.exp (-2*t))) hp
  simp only [Pi.sub_apply] at hi
  rw [integral_sub hG.integral_prod_left hA, integral_const_mul,
    integral_sub hF.integral_prod_left hA, ← integral_prod _ hG,
    ← integral_prod _ hF] at hi
  simpa only [← l2_norm_sq_integral] using hi

/-- The OU norm loss controls the full conditionally centered component. -/
theorem ouProduct_loss (t : ℝ) (ht : 0 ≤ t)
    (F : Lp ℝ 2 (μ.prod (stdGaussian E))) :
    (1 - Real.exp (-2*t)) *
      ‖F - productEmbedding μ (stdGaussian E) (productAverage μ (stdGaussian E) F)‖^2 ≤
      ‖F‖^2 - ‖ouProduct μ t ht F‖^2 := by
  have hv := ouProduct_variance μ t ht F
  have hl := isometry_adjoint_loss (productEmbedding μ (stdGaussian E)) F
  change ‖F‖^2 - ‖productAverage μ (stdGaussian E) F‖^2 =
    ‖F - productEmbedding μ (stdGaussian E) (productAverage μ (stdGaussian E) F)‖^2 at hl
  rw [← hl]
  nlinarith

/-- Functions of the retained coordinate are fixed by the channel. -/
theorem ouProduct_embedding (t : ℝ) (ht : 0 ≤ t) (f : Lp ℝ 2 μ) :
    ouProduct μ t ht (productEmbedding μ (stdGaussian E) f) =
      productEmbedding μ (stdGaussian E) f := by
  apply Lp.ext
  have hf := Lp.coeFn_compMeasurePreserving f
    (measurePreserving_fst (ν := stdGaussian E))
  have hq := (ouProductObservation_measurePreserving μ t ht).quasiMeasurePreserving.ae hf
  filter_upwards [ouProduct_coe μ t ht (productEmbedding μ (stdGaussian E) f),
    hf, Measure.ae_ae_of_ae_prod hq] with z hz hfz hqz
  change (ouProduct μ t ht (productEmbedding μ (stdGaussian E) f)) z = _
  change (productEmbedding μ (stdGaussian E) f) z = f z.1 at hfz
  rw [hz, hfz]
  have he : (fun y => (productEmbedding μ (stdGaussian E) f)
      (z.1, gaussianMix E t (z.2,y))) =ᵐ[stdGaussian E] fun _ => f z.1 := hqz
  rw [integral_congr_ae he]
  simp

/-- Averaging the Gaussian coordinate is unchanged by its OU evolution. -/
theorem productAverage_ouProduct (t : ℝ) (ht : 0 ≤ t)
    (F : Lp ℝ 2 (μ.prod (stdGaussian E))) :
    productAverage μ (stdGaussian E) (ouProduct μ t ht F) =
      productAverage μ (stdGaussian E) F := by
  apply Lp.ext
  filter_upwards [productAverage_coe μ (stdGaussian E) (ouProduct μ t ht F),
    productAverage_coe μ (stdGaussian E) F, memLp_gaussian_section μ F,
    Measure.ae_ae_of_ae_prod (ouProduct_coe μ t ht F)] with x hx hy hmem hOU
  rw [hx, hy, integral_congr_ae hOU]
  exact gaussianOU_integral E t ht (fun y => F (x,y)) hmem

/-- Exact action on the genuine first Gaussian chaos, allowing an arbitrary
measurable dependence of its coefficient on the retained coordinate. -/
theorem ouProduct_firstChaos (t : ℝ) (ht : 0 ≤ t)
    (F : Lp ℝ 2 (μ.prod (stdGaussian E))) (v : X → E)
    (hF : F =ᵐ[μ.prod (stdGaussian E)] fun z => inner ℝ (v z.1) z.2) :
    ouProduct μ t ht F = Real.exp (-t) • F := by
  apply Lp.ext
  have hq := (ouProductObservation_measurePreserving μ t ht).quasiMeasurePreserving.ae hF
  filter_upwards [ouProduct_coe μ t ht F, hF,
    Measure.ae_ae_of_ae_prod hq, Lp.coeFn_smul (Real.exp (-t)) F] with z hz hfz hqz hsmul
  rw [hz, hsmul]
  simp only [Pi.smul_apply, smul_eq_mul, hfz]
  have he : (fun y => F (z.1, gaussianMix E t (z.2,y))) =ᵐ[stdGaussian E]
      fun y => inner ℝ (v z.1) (gaussianMix E t (z.2,y)) := hqz
  rw [integral_congr_ae he]
  simp only [gaussianMix, inner_add_right, real_inner_smul_right]
  have hv : Integrable (fun y : E => inner ℝ (v z.1) y) (stdGaussian E) :=
    ((IsGaussian.memLp_two_id (μ := stdGaussian E)).const_inner (𝕜 := ℝ) (v z.1)).integrable
      (by norm_num)
  rw [integral_add (integrable_const _) (hv.const_mul _)]
  have hm : (∫ y : E, inner ℝ (v z.1) y ∂stdGaussian E) = 0 :=
    integral_strongDual_stdGaussian (innerSL ℝ (v z.1))
  simp [integral_const_mul, hm]

/-- Reversibility holds on the full product L2 space. -/
theorem ouProduct_symmetric (t : ℝ) (ht : 0 ≤ t)
    (F G : Lp ℝ 2 (μ.prod (stdGaussian E))) :
    inner ℝ F (ouProduct μ t ht G) = inner ℝ (ouProduct μ t ht F) G := by
  rw [L2.inner_def, L2.inner_def,
    integral_prod _ (L2.integrable_inner F (ouProduct μ t ht G)),
    integral_prod _ (L2.integrable_inner (ouProduct μ t ht F) G)]
  apply integral_congr_ae
  filter_upwards [memLp_gaussian_section μ F, memLp_gaussian_section μ G,
    Measure.ae_ae_of_ae_prod (ouProduct_coe μ t ht F),
    Measure.ae_ae_of_ae_prod (ouProduct_coe μ t ht G)] with x hf hg hF hG
  have he1 : (∫ y, inner ℝ (F (x,y)) (ouProduct μ t ht G (x,y)) ∂stdGaussian E) =
      ∫ y, F (x,y) * (∫ z, G (x, gaussianMix E t (y,z)) ∂stdGaussian E) ∂stdGaussian E := by
    apply integral_congr_ae
    filter_upwards [hG] with y hy
    simp [hy, mul_comm]
  have he2 : (∫ y, inner ℝ (ouProduct μ t ht F (x,y)) (G (x,y)) ∂stdGaussian E) =
      ∫ y, (∫ z, F (x, gaussianMix E t (y,z)) ∂stdGaussian E) * G (x,y) ∂stdGaussian E := by
    apply integral_congr_ae
    filter_upwards [hF] with y hy
    simp [hy, mul_comm]
  rw [he1, he2]
  exact gaussianOU_symmetric_integral E t ht _ _ hf hg

/-- The density operator is the same actual Gaussian operator. -/
theorem ouProduct_adjoint (t : ℝ) (ht : 0 ≤ t) :
    (ouProduct (E := E) μ t ht).adjoint = ouProduct μ t ht := by
  apply ContinuousLinearMap.ext
  intro F
  apply ext_inner_left ℝ
  intro G
  rw [ContinuousLinearMap.adjoint_inner_right, ouProduct_symmetric]

end AcceleratedLogConcave.Kinetic.Reheating
