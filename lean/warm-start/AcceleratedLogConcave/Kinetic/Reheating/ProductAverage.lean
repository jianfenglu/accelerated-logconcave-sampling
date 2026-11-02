import AcceleratedLogConcave.Kinetic.ReferenceChannel
import Mathlib.MeasureTheory.Integral.Prod

/-! Actual partial averaging on a probability product. The L2 adjoint is
identified with integration against the second reference law almost everywhere. -/
noncomputable section
open MeasureTheory InnerProductSpace
open scoped RealInnerProductSpace
namespace AcceleratedLogConcave.Kinetic.Reheating
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

/-- Embedding a function of the first coordinate in the actual product law. -/
def productEmbedding : Lp ℝ 2 μ →ₗᵢ[ℝ] Lp ℝ 2 (μ.prod ν) :=
  Lp.compMeasurePreservingₗᵢ ℝ Prod.fst measurePreserving_fst

/-- Conditional averaging of the second coordinate. -/
def productAverage : Lp ℝ 2 (μ.prod ν) →L[ℝ] Lp ℝ 2 μ :=
  (productEmbedding μ ν).toContinuousLinearMap.adjoint

omit [IsProbabilityMeasure μ] in
@[simp] theorem productAverage_embedding (f : Lp ℝ 2 μ) :
    productAverage μ ν (productEmbedding μ ν f) = f :=
  congrArg (fun T : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ => T f) (productEmbedding μ ν).adjoint_comp_self

omit [IsProbabilityMeasure μ] in
theorem productAverage_pairing (f : Lp ℝ 2 μ) (F : Lp ℝ 2 (μ.prod ν)) :
    inner ℝ f (productAverage μ ν F) = ∫ z, f z.1 * F z ∂μ.prod ν := by
  rw [productAverage, ContinuousLinearMap.adjoint_inner_right, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_compMeasurePreserving f (measurePreserving_fst (ν := ν))] with z hz
  change inner ℝ ((Lp.compMeasurePreserving Prod.fst measurePreserving_fst f) z) (F z) = _
  rw [hz]
  simp [mul_comm]

/-- The operator is exactly the Gaussian/partial integral, not an abstract projection premise. -/
theorem productAverage_coe (F : Lp ℝ 2 (μ.prod ν)) :
    productAverage μ ν F =ᵐ[μ] fun x => ∫ y, F (x, y) ∂ν := by
  have hF : Integrable F (μ.prod ν) := (Lp.memLp F).integrable (by norm_num)
  apply Integrable.ae_eq_of_forall_setIntegral_eq _ _
    ((Lp.memLp (productAverage μ ν F)).integrable (by norm_num)) hF.integral_prod_left
  intro s hs hμs
  let f : Lp ℝ 2 μ := indicatorConstLp 2 hs hμs.ne (1 : ℝ)
  have ht := productAverage_pairing μ ν f F
  have hleft : inner ℝ f (productAverage μ ν F) = ∫ x in s, productAverage μ ν F x ∂μ :=
    L2.inner_indicatorConstLp_one hs hμs.ne _
  rw [hleft] at ht
  rw [ht]
  have hcoe : (fun z : X × Y => f z.1 * F z) =ᵐ[μ.prod ν]
      fun z => s.indicator (fun x => F (x, z.2)) z.1 := by
    filter_upwards [measurePreserving_fst.quasiMeasurePreserving.ae
      (indicatorConstLp_coeFn (p := 2) (hs := hs) (hμs := hμs.ne) (c := (1 : ℝ)))] with z hz
    change f z.1 = _ at hz
    rw [hz]
    by_cases hx : z.1 ∈ s <;> simp [hx]
  rw [integral_congr_ae hcoe]
  have hi : Integrable (fun z : X × Y => s.indicator (fun x => F (x, z.2)) z.1) (μ.prod ν) := by
    convert hF.indicator (hs.preimage measurable_fst) using 1
    ext z
    by_cases hz : z.1 ∈ s <;> simp [hz]
  rw [integral_prod _ hi, ← integral_indicator hs]
  congr 1
  ext x
  by_cases hx : x ∈ s <;> simp [hx]

omit [IsProbabilityMeasure μ] in
theorem productAverage_norm_le : ‖productAverage μ ν‖ ≤ 1 := by
  rw [productAverage, ContinuousLinearMap.adjoint.norm_map]
  exact (productEmbedding μ ν).norm_toContinuousLinearMap_le

/-- An actual product tape channel is exactly integration over its fresh draw. -/
theorem referenceChannel_fst_coe {Z : Type*} [MeasurableSpace Z]
    {κ : Measure Z} {q : X × Y → Z} (hq : MeasurePreserving q (μ.prod ν) κ)
    (f : Lp ℝ 2 κ) :
    referenceChannel (measurePreserving_fst (μ := μ) (ν := ν)) hq f =ᵐ[μ]
      fun x => ∫ y, f (q (x, y)) ∂ν := by
  have hf := Lp.coeFn_compMeasurePreserving f hq
  have hh := productAverage_coe μ ν (Lp.compMeasurePreserving q hq f)
  apply hh.trans
  filter_upwards [Measure.ae_ae_of_ae_prod hf] with x hx
  exact integral_congr_ae hx

end AcceleratedLogConcave.Kinetic.Reheating
