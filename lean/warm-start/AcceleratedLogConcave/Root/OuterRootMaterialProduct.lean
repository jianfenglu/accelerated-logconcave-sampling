import AcceleratedLogConcave.Root.OuterRootOriginalData
import AcceleratedLogConcave.Numerics.SmoothConditionalCell
import Mathlib.MeasureTheory.Integral.Prod

/-! SOURCE-ONLY. Positive-order outer conditional state jets on a random-center
product law. Integrability is proved, not hidden in a totalized integral. The
uniform fixed-center material bound makes this valid for EVERY probability
center law; stationarity is needed separately for zeroth-order moments. -/
noncomputable section
set_option autoImplicit false
open Set MeasureTheory ProbabilityTheory
namespace AcceleratedLogConcave.Root.OuterRootMaterialProduct
open Numerics Numerics.ConditionalSmoothing Analysis.PositiveVarianceSlab
variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι

/-- Genuine Gaussian L2 integrability of each actual conditional time jet. -/
theorem jet_gaussian_integrable_sq (d : SamplingCenterLp.Data ι) (k : ℕ)
    (x : E) {t : ℝ} (ht : t ∈ Icc 0 d.b) :
    Integrable (fun z => ‖(jet d k t (x,z)).2‖^2) (stdGaussian E) := by
  classical
  have hp := referenceInput_measurePreserving d x
  have hi := ((fixedData d x).positionJet_memLp k t).norm.integrable_sq
  have hc := hp.integrable_comp_of_integrable hi
  simp_rw [jet_snd_eq_referencePositionJet d k x _ (source_subset d.hb d.hb1 ht)]
  exact hc

/-- No moment of the frozen center is required for these positive-order jets. -/
theorem jet_product_integrable_sq (d : SamplingCenterLp.Data ι)
    (hsmall : d.r^2*d.ell ≤ 1/2) (mu : Measure E) [IsProbabilityMeasure mu]
    (k : ℕ) {t : ℝ} (ht : t ∈ Icc 0 d.b) :
    Integrable (fun p : E × E => ‖(jet d (k+2) t p).2‖^2)
      (mu.prod (stdGaussian E)) := by
  have hc : Continuous (fun p : E × E => ‖(jet d (k+2) t p).2‖^2) :=
    (((continuous_jet d (k+2)).comp (continuous_const.prodMk continuous_id)).snd).norm.pow 2
  apply (integrable_prod_iff hc.aestronglyMeasurable).mpr
  constructor
  · exact Filter.Eventually.of_forall (fun x => jet_gaussian_integrable_sq d (k+2) x ht)
  · apply (integrable_const
      (((d.ell*d.r^2)*materialOrderFactor (Fintype.card ι) k/(1-t^2)^(k+1))^2)).mono'
      hc.norm.stronglyMeasurable.integral_prod_right'.aestronglyMeasurable
    filter_upwards [] with x
    simp only [Real.norm_eq_abs, abs_sq]
    rw [abs_of_nonneg (integral_nonneg (fun _ => sq_nonneg _))]
    exact integral_gaussian_jet_sq_le_material_fintype d hsmall k x ht

/-- The fixed-center material estimate transfers to any random-center product
law, retaining dimension, order, local radius, and source-time denominator. -/
theorem jet_product_integral_sq_le (d : SamplingCenterLp.Data ι)
    (hsmall : d.r^2*d.ell ≤ 1/2) (mu : Measure E) [IsProbabilityMeasure mu]
    (k : ℕ) {t : ℝ} (ht : t ∈ Icc 0 d.b) :
    (∫ p : E × E, ‖(jet d (k+2) t p).2‖^2 ∂mu.prod (stdGaussian E)) ≤
      ((d.ell*d.r^2)*materialOrderFactor (Fintype.card ι) k/(1-t^2)^(k+1))^2 := by
  have hi := jet_product_integrable_sq d hsmall mu k ht
  rw [integral_prod _ hi]
  have hb := integral_mono hi.integral_prod_left
    (integrable_const (((d.ell*d.r^2)*materialOrderFactor (Fintype.card ι) k/(1-t^2)^(k+1))^2))
    (fun x => integral_gaussian_jet_sq_le_material_fintype d hsmall k x ht)
  simpa using hb

/-- Literal normalized-root specialization, with amplitude 2h² rather than
an internal MAIN radius or an assumed derivative budget. -/
theorem original_product_bound {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    {h : ℝ} (hh : 0 < h) (hsmall : h ≤ 1/2)
    (hlo : ∀ z v, 0 ≤ fderiv ℝ (fderiv ℝ V) z v v)
    (hup : ∀ z v, fderiv ℝ (fderiv ℝ V) z v v ≤ ‖v‖^2)
    (mu : Measure E) [IsProbabilityMeasure mu] (k : ℕ)
    {t : ℝ} (ht : t ∈ Icc 0 (1/2 : ℝ)) :
    Integrable (fun p : E × E =>
      ‖(jet (OuterRootOriginalData.data hV hh hlo hup) (k+2) t p).2‖^2)
        (mu.prod (stdGaussian E)) ∧
    (∫ p : E × E,
      ‖(jet (OuterRootOriginalData.data hV hh hlo hup) (k+2) t p).2‖^2
        ∂mu.prod (stdGaussian E)) ≤
      ((2*h^2)*materialOrderFactor (Fintype.card ι) k/(1-t^2)^(k+1))^2 := by
  let d := OuterRootOriginalData.data hV hh hlo hup
  have hs := OuterRootOriginalData.data_small hV hh hlo hup hsmall
  refine ⟨jet_product_integrable_sq d hs mu k ht, ?_⟩
  have hb := jet_product_integral_sq_le d hs mu k ht
  have he : d.ell*d.r^2 = 2*h^2 := by
    dsimp [d, OuterRootOriginalData.data]
    rw [Real.sq_sqrt (by positivity)]
    ring
  rw [he] at hb
  exact hb

end AcceleratedLogConcave.Root.OuterRootMaterialProduct
