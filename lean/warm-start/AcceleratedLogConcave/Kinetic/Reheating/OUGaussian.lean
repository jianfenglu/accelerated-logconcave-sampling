import AcceleratedLogConcave.Kinetic.Reheating.OUCore
import AcceleratedLogConcave.Analysis.Poisson.Pullback
import AcceleratedLogConcave.Kinetic.Reheating.ProductAverage

/-! The actual finite-dimensional Gaussian Mehler operator, transported from
orthonormal coordinates. Variance decay holds on the full L2 quotient. -/
noncomputable section
open MeasureTheory ProbabilityTheory InnerProductSpace WithLp
open scoped RealInnerProductSpace
namespace AcceleratedLogConcave.Kinetic.Reheating
open Analysis.Poisson GaussianFin
variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Orthonormal coordinate synthesis as an actual measurable equivalence. -/
def gaussianCoordinates : (Fin (Module.finrank ℝ E) → ℝ) ≃ᵐ E :=
  (MeasurableEquiv.toLp 2 _).trans (stdOrthonormalBasis ℝ E).repr.symm.toMeasurableEquiv

theorem gaussianCoordinates_measurePreserving :
    MeasurePreserving (gaussianCoordinates E) (γFin (Module.finrank ℝ E)) (stdGaussian E) := by
  have h1 : MeasurePreserving (MeasurableEquiv.toLp 2 (Fin (Module.finrank ℝ E) → ℝ))
      (γFin (Module.finrank ℝ E)) (stdGaussian (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))) :=
    ⟨(MeasurableEquiv.toLp 2 _).measurable, map_pi_eq_stdGaussian⟩
  have h2 : MeasurePreserving (stdOrthonormalBasis ℝ E).repr.symm
      (stdGaussian (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))) (stdGaussian E) :=
    ⟨(stdOrthonormalBasis ℝ E).repr.symm.continuous.measurable,
      stdGaussian_map (stdOrthonormalBasis ℝ E).repr.symm⟩
  exact h2.comp h1

/-- Coordinate synthesis respects the actual affine Gaussian mixing map. -/
theorem gaussianCoordinates_mix (a b : ℝ) (x y : Fin (Module.finrank ℝ E) → ℝ) :
    gaussianCoordinates E (mixCLM a b (x, y)) =
      a • gaussianCoordinates E x + b • gaussianCoordinates E y := by
  change (stdOrthonormalBasis ℝ E).repr.symm (toLp 2 (mixCLM a b (x, y))) = _
  rw [show toLp 2 (mixCLM a b (x, y)) = a • toLp 2 x + b • toLp 2 y from rfl,
    map_add, map_smul, map_smul]
  rfl

/-- The explicit Mehler mixing of two independent standard Gaussian draws. -/
def gaussianMix (t : ℝ) (z : E × E) : E :=
  Real.exp (-t) • z.1 + Real.sqrt (1 - Real.exp (-2*t)) • z.2

theorem gaussianMix_measurePreserving (t : ℝ) (ht : 0 ≤ t) :
    MeasurePreserving (gaussianMix E t) ((stdGaussian E).prod (stdGaussian E)) (stdGaussian E) := by
  let e := gaussianCoordinates E
  let he := gaussianCoordinates_measurePreserving E
  have hm : MeasurePreserving (mixCLM (n := Module.finrank ℝ E)
      (Real.exp (-t)) (Real.sqrt (1 - Real.exp (-2*t))))
      ((γFin (Module.finrank ℝ E)).prod (γFin (Module.finrank ℝ E)))
      (γFin (Module.finrank ℝ E)) :=
    ⟨(mixCLM _ _).continuous.measurable, ou_kernel_map_fin t ht⟩
  have hh := he.comp (hm.comp ((he.symm e).prod (he.symm e)))
  convert hh using 1
  funext z
  change gaussianMix E t z = gaussianCoordinates E
    (mixCLM (Real.exp (-t)) (Real.sqrt (1 - Real.exp (-2*t))) (e.symm z.1, e.symm z.2))
  rw [gaussianCoordinates_mix]
  simp only [e, MeasurableEquiv.apply_symm_apply, gaussianMix]

/-- The Gaussian coordinate pullback is unitary. -/
def gaussianCoordinatePullback : Lp ℝ 2 (stdGaussian E) ≃ₗᵢ[ℝ]
    Lp ℝ 2 (γFin (Module.finrank ℝ E)) :=
  pullback (gaussianCoordinates E) (gaussianCoordinates_measurePreserving E)

/-- The genuine Gaussian OU operator in the original Hilbert space. -/
def gaussianOU (t : ℝ) : Lp ℝ 2 (stdGaussian E) →L[ℝ] Lp ℝ 2 (stdGaussian E) :=
  (gaussianCoordinatePullback E).symm.toLinearIsometry.toContinuousLinearMap.comp
    ((ouSemigroupFinLp t).comp (gaussianCoordinatePullback E).toLinearIsometry.toContinuousLinearMap)

@[simp] theorem gaussianOU_pullback (t : ℝ) (f : Lp ℝ 2 (stdGaussian E)) :
    gaussianCoordinatePullback E (gaussianOU E t f) =
      ouSemigroupFinLp t (gaussianCoordinatePullback E f) := by
  simp [gaussianOU]

theorem gaussianCoordinatePullback_mean (f : Lp ℝ 2 (stdGaussian E)) :
    mean (γFin (Module.finrank ℝ E)) (gaussianCoordinatePullback E f) =
      mean (stdGaussian E) f := by
  simp only [mean_apply]
  exact integral_pullback (gaussianCoordinates E) (gaussianCoordinates_measurePreserving E) f

theorem gaussianOU_mean (t : ℝ) (ht : 0 ≤ t) (f : Lp ℝ 2 (stdGaussian E)) :
    mean (stdGaussian E) (gaussianOU E t f) = mean (stdGaussian E) f := by
  rw [← gaussianCoordinatePullback_mean, gaussianOU_pullback, ou_mean t ht,
    gaussianCoordinatePullback_mean]

theorem gaussianOU_variance (t : ℝ) (ht : 0 ≤ t) (f : Lp ℝ 2 (stdGaussian E)) :
    ‖gaussianOU E t f‖^2 - (mean (stdGaussian E) f)^2 ≤
      Real.exp (-2*t) * (‖f‖^2 - (mean (stdGaussian E) f)^2) := by
  have h := ou_variance t ht (gaussianCoordinatePullback E f)
  rw [← gaussianOU_pullback, LinearIsometryEquiv.norm_map,
    LinearIsometryEquiv.norm_map, gaussianCoordinatePullback_mean] at h
  exact h

theorem gaussianOU_norm_le (t : ℝ) (ht : 0 ≤ t) : ‖gaussianOU E t‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  have h := ContinuousLinearMap.le_of_opNorm_le _ (ouSemigroupFinLp_contraction t ht)
    (gaussianCoordinatePullback E f)
  simpa only [gaussianOU, ContinuousLinearMap.comp_apply,
    LinearIsometry.coe_toContinuousLinearMap, LinearIsometryEquiv.coe_toLinearIsometry,
    LinearIsometryEquiv.norm_map] using h

theorem gaussianOU_centered_norm_sq (t : ℝ) (ht : 0 ≤ t) (f : Lp ℝ 2 (stdGaussian E))
    (hf : mean (stdGaussian E) f = 0) :
    ‖gaussianOU E t f‖^2 ≤ Real.exp (-2*t) * ‖f‖^2 := by
  simpa only [hf, zero_pow (by decide : 2 ≠ 0), sub_zero] using gaussianOU_variance E t ht f

/-- Exact joint-law pairing proves that the coordinate construction is the
physical Gaussian Mehler channel. -/
theorem gaussianOU_pairing (t : ℝ) (ht : 0 ≤ t)
    (f g : Lp ℝ 2 (stdGaussian E)) :
    inner ℝ f (gaussianOU E t g) =
      ∫ z, f z.1 * g (gaussianMix E t z) ∂(stdGaussian E).prod (stdGaussian E) := by
  let d := Module.finrank ℝ E
  let e := gaussianCoordinates E
  let he := gaussianCoordinates_measurePreserving E
  let mix := mixCLM (n := d) (Real.exp (-t)) (Real.sqrt (1 - Real.exp (-2*t)))
  have hm : MeasurePreserving mix ((γFin d).prod (γFin d)) (γFin d) :=
    ⟨mix.continuous.measurable, ou_kernel_map_fin t ht⟩
  have hfinite : ouSemigroupFinLp (n := d) t =
      referenceChannel (measurePreserving_fst (μ := γFin d) (ν := γFin d)) hm := by
    unfold ouSemigroupFinLp
    simp only [max_eq_left ht]
    rfl
  rw [← (gaussianCoordinatePullback E).inner_map_map, gaussianOU_pullback, hfinite,
    referenceChannel_pairing]
  have hf := pullback_coeFn e he f
  have hg := pullback_coeFn e he g
  have hpair : (fun z => gaussianCoordinatePullback E f z.1 *
      gaussianCoordinatePullback E g (mix z)) =ᵐ[(γFin d).prod (γFin d)]
      fun z => f (e z.1) * g (e (mix z)) := by
    filter_upwards [measurePreserving_fst.quasiMeasurePreserving.ae hf,
      hm.quasiMeasurePreserving.ae hg] with z hfz hgz
    exact congrArg₂ (· * ·) hfz hgz
  rw [integral_congr_ae hpair]
  have hi := (he.prod he).integral_comp (e.prodCongr e).measurableEmbedding (fun z : E × E => f z.1 * g (gaussianMix E t z))
  rw [← hi]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun z => by
    dsimp only [Function.comp_apply, Prod.map_fst, Prod.map_snd]
    congr 1
    exact congrArg g (gaussianCoordinates_mix E _ _ z.1 z.2)

/-- Identification with the actual tape-defined Markov operator. -/
theorem gaussianOU_eq_referenceChannel (t : ℝ) (ht : 0 ≤ t) :
    gaussianOU E t = referenceChannel
      (measurePreserving_fst (μ := stdGaussian E) (ν := stdGaussian E))
      (gaussianMix_measurePreserving E t ht) := by
  apply ContinuousLinearMap.ext
  intro g
  apply ext_inner_left ℝ
  intro f
  rw [gaussianOU_pairing E t ht, referenceChannel_pairing]

/-- The actual Mehler integral formula, on the full L2 quotient. -/
theorem gaussianOU_coe (t : ℝ) (ht : 0 ≤ t) (f : Lp ℝ 2 (stdGaussian E)) :
    gaussianOU E t f =ᵐ[stdGaussian E] fun x => ∫ y, f (gaussianMix E t (x,y)) ∂stdGaussian E := by
  rw [gaussianOU_eq_referenceChannel E t ht]
  exact referenceChannel_fst_coe _ _ (gaussianMix_measurePreserving E t ht) f

/-- The integral formula for any actual square-integrable representative. -/
theorem gaussianOU_coe_of_memLp (t : ℝ) (ht : 0 ≤ t) (f : E → ℝ)
    (hf : MemLp f 2 (stdGaussian E)) :
    gaussianOU E t (hf.toLp f) =ᵐ[stdGaussian E]
      fun x => ∫ y, f (gaussianMix E t (x,y)) ∂stdGaussian E := by
  apply (gaussianOU_coe E t ht (hf.toLp f)).trans
  have hae := (gaussianMix_measurePreserving E t ht).quasiMeasurePreserving.ae hf.coeFn_toLp
  filter_upwards [Measure.ae_ae_of_ae_prod hae] with x hx
  exact integral_congr_ae hx

/-- The sharp variance inequality in raw integrals, ready for Fubini over an
arbitrary retained base coordinate. -/
theorem gaussianOU_variance_integral (t : ℝ) (ht : 0 ≤ t) (f : E → ℝ)
    (hf : MemLp f 2 (stdGaussian E)) :
    (∫ x, (∫ y, f (gaussianMix E t (x,y)) ∂stdGaussian E)^2 ∂stdGaussian E) -
      (∫ x, f x ∂stdGaussian E)^2 ≤
      Real.exp (-2*t) * ((∫ x, (f x)^2 ∂stdGaussian E) - (∫ x, f x ∂stdGaussian E)^2) := by
  have norm_sq (g : Lp ℝ 2 (stdGaussian E)) : ‖g‖^2 = ∫ x, (g x)^2 ∂stdGaussian E := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => by simp [pow_two]
  have h := gaussianOU_variance E t ht (hf.toLp f)
  rw [norm_sq, norm_sq, mean_apply, integral_congr_ae hf.coeFn_toLp] at h
  have hleft : (∫ x, (gaussianOU E t (hf.toLp f) x)^2 ∂stdGaussian E) =
      ∫ x, (∫ y, f (gaussianMix E t (x,y)) ∂stdGaussian E)^2 ∂stdGaussian E := by
    apply integral_congr_ae
    filter_upwards [gaussianOU_coe_of_memLp E t ht f hf] with x hx
    rw [hx]
  have hright : (∫ x, (hf.toLp f x)^2 ∂stdGaussian E) =
      ∫ x, (f x)^2 ∂stdGaussian E := by
    apply integral_congr_ae
    filter_upwards [hf.coeFn_toLp] with x hx
    rw [hx]
  rw [hleft, hright] at h
  exact h

/-- Reversibility of the actual Gaussian Mehler operator. -/
theorem gaussianOU_symmetric (t : ℝ) (ht : 0 ≤ t)
    (f g : Lp ℝ 2 (stdGaussian E)) :
    inner ℝ f (gaussianOU E t g) = inner ℝ (gaussianOU E t f) g := by
  rw [← (gaussianCoordinatePullback E).inner_map_map, gaussianOU_pullback,
    ouSemigroupFinLp_symmetric t ht,
    ← gaussianOU_pullback, (gaussianCoordinatePullback E).inner_map_map]

/-- Preservation of the genuine Gaussian integral for every square-integrable function. -/
theorem gaussianOU_integral (t : ℝ) (ht : 0 ≤ t) (f : E → ℝ)
    (hf : MemLp f 2 (stdGaussian E)) :
    (∫ x, ∫ y, f (gaussianMix E t (x,y)) ∂stdGaussian E ∂stdGaussian E) =
      ∫ x, f x ∂stdGaussian E := by
  have h := gaussianOU_mean E t ht (hf.toLp f)
  simp only [mean_apply] at h
  rw [integral_congr_ae (gaussianOU_coe_of_memLp E t ht f hf),
    integral_congr_ae hf.coeFn_toLp] at h
  exact h

/-- Reversibility in raw integrals, suitable for conditional Gaussian sections. -/
theorem gaussianOU_symmetric_integral (t : ℝ) (ht : 0 ≤ t) (f g : E → ℝ)
    (hf : MemLp f 2 (stdGaussian E)) (hg : MemLp g 2 (stdGaussian E)) :
    (∫ x, f x * (∫ y, g (gaussianMix E t (x,y)) ∂stdGaussian E) ∂stdGaussian E) =
      ∫ x, (∫ y, f (gaussianMix E t (x,y)) ∂stdGaussian E) * g x ∂stdGaussian E := by
  have h := gaussianOU_symmetric E t ht (hf.toLp f) (hg.toLp g)
  rw [L2.inner_def, L2.inner_def] at h
  have hl : (∫ x, inner ℝ (hf.toLp f x) (gaussianOU E t (hg.toLp g) x) ∂stdGaussian E) =
      ∫ x, f x * (∫ y, g (gaussianMix E t (x,y)) ∂stdGaussian E) ∂stdGaussian E := by
    apply integral_congr_ae
    filter_upwards [hf.coeFn_toLp, gaussianOU_coe_of_memLp E t ht g hg] with x hx hy
    simp [hx, hy, mul_comm]
  have hr : (∫ x, inner ℝ (gaussianOU E t (hf.toLp f) x) (hg.toLp g x) ∂stdGaussian E) =
      ∫ x, (∫ y, f (gaussianMix E t (x,y)) ∂stdGaussian E) * g x ∂stdGaussian E := by
    apply integral_congr_ae
    filter_upwards [hg.coeFn_toLp, gaussianOU_coe_of_memLp E t ht f hf] with x hx hy
    simp [hx, hy, mul_comm]
  rw [hl, hr] at h
  exact h

end AcceleratedLogConcave.Kinetic.Reheating
