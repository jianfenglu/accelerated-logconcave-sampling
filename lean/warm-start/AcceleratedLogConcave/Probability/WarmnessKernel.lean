import AcceleratedLogConcave.Probability.Warmness
import Mathlib.InformationTheory.KullbackLeibler.DataProcessing
import Mathlib.Probability.Kernel.Composition.RadonNikodym

/-!
# Squared L2 warmness under common randomization

A common Markov kernel preserves the RN-square moment when the input is retained,
and contracts it when the input is discarded. No regularity assumption on the
measurable spaces is needed.

-/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace AcceleratedLogConcave.Probability

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

/-- A measurable map contracts the finite squared Radon–Nikodym moment. -/
theorem rnSquare_integral_map_le
    (ν μ : Measure X) [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
    (hνμ : ν ≪ μ) {f : X → Y} (hf : Measurable f)
    (hi : Integrable (fun x => ((ν.rnDeriv μ x).toReal)^2) μ) :
    Integrable (fun y => (((ν.map f).rnDeriv (μ.map f) y).toReal)^2) (μ.map f) ∧
    (∫ y, (((ν.map f).rnDeriv (μ.map f) y).toReal)^2 ∂μ.map f) ≤
      ∫ x, ((ν.rnDeriv μ x).toReal)^2 ∂μ := by
  have hc : ConvexOn ℝ (Ici 0) (fun x : ℝ => x^2) := convexOn_pow 2
  have hm : StronglyMeasurable (fun x : ℝ => x^2) := by fun_prop
  have ht : ContinuousWithinAt (fun x : ℝ => x^2) (Ici 0) 0 := by fun_prop
  have himap := hc.integrable_comp_rnDeriv_map hνμ hf hm ht hi
  refine ⟨himap, ?_⟩
  rw [integral_map hf.aemeasurable himap.aestronglyMeasurable]
  calc
    _ ≤ ∫ x, μ[fun z => ((ν.rnDeriv μ z).toReal)^2 |
        MeasurableSpace.comap f inferInstance] x ∂μ :=
      integral_mono_ae (himap.comp_measurable hf) integrable_condExp
        (hc.comp_rnDeriv_map_le hνμ hf hm ht hi)
    _ = _ := integral_condExp hf.comap_le

/-- Common deterministic postprocessing preserves the warmness budget. -/
theorem L2Warm.map {μ ν : Measure X} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {B : ℝ} (h : L2Warm μ ν B) {f : X → Y} (hf : Measurable f) :
    L2Warm (μ.map f) (ν.map f) B := by
  have hm := rnSquare_integral_map_le ν μ h.1 hf h.2.1
  exact ⟨h.1.map hf, hm.1, hm.2.trans h.2.2⟩

/-- Retaining the input under a common Markov kernel preserves the RN-square
integrability and moment exactly. -/
theorem rnSquare_integral_compProd
    (ν μ : Measure X) [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
    (P : Kernel X Y) [IsMarkovKernel P]
    (hi : Integrable (fun x => ((ν.rnDeriv μ x).toReal)^2) μ) :
    Integrable (fun z => (((ν ⊗ₘ P).rnDeriv (μ ⊗ₘ P) z).toReal)^2) (μ ⊗ₘ P) ∧
    (∫ z, (((ν ⊗ₘ P).rnDeriv (μ ⊗ₘ P) z).toReal)^2 ∂(μ ⊗ₘ P)) =
      ∫ x, ((ν.rnDeriv μ x).toReal)^2 ∂μ := by
  have he : (fun z => (((ν ⊗ₘ P).rnDeriv (μ ⊗ₘ P) z).toReal)^2) =ᵐ[μ ⊗ₘ P]
      fun z => ((ν.rnDeriv μ z.1).toReal)^2 := by
    filter_upwards [rnDeriv_measure_compProd_left ν μ P] with z hz
    rw [hz]
  have hmap : (μ ⊗ₘ P).map Prod.fst = μ := Measure.fst_compProd μ P
  have himap : Integrable (fun x => ((ν.rnDeriv μ x).toReal)^2)
      ((μ ⊗ₘ P).map Prod.fst) := by rwa [hmap]
  refine ⟨(himap.comp_measurable measurable_fst).congr he.symm, ?_⟩
  rw [integral_congr_ae he, ← integral_map measurable_fst.aemeasurable
    himap.aestronglyMeasurable, hmap]

/-- Common randomization with the input retained preserves the warmness budget. -/
theorem L2Warm.compProd {μ ν : Measure X} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {B : ℝ} (h : L2Warm μ ν B) (P : Kernel X Y) [IsMarkovKernel P] :
    L2Warm (μ ⊗ₘ P) (ν ⊗ₘ P) B := by
  have hm := rnSquare_integral_compProd ν μ P h.2.1
  exact ⟨h.1.compProd_left P, hm.1, hm.2.le.trans h.2.2⟩

/-- A genuine Markov kernel contracts squared L2 warmness. -/
theorem L2Warm.kernel {μ ν : Measure X} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {B : ℝ} (h : L2Warm μ ν B) (P : Kernel X Y) [IsMarkovKernel P] :
    L2Warm (P ∘ₘ μ) (P ∘ₘ ν) B := by
  have hm := (h.compProd P).map measurable_snd
  change L2Warm (μ ⊗ₘ P).snd (ν ⊗ₘ P).snd B at hm
  simpa only [Measure.snd_compProd] using hm

/-- Adjoining an independent common probability factor preserves the RN-square
integrability and moment exactly. -/
theorem rnSquare_integral_prod_right
    (ν μ : Measure X) [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
    (ρ : Measure Y) [IsProbabilityMeasure ρ]
    (hi : Integrable (fun x => ((ν.rnDeriv μ x).toReal)^2) μ) :
    Integrable (fun z => (((ν.prod ρ).rnDeriv (μ.prod ρ) z).toReal)^2) (μ.prod ρ) ∧
    (∫ z, (((ν.prod ρ).rnDeriv (μ.prod ρ) z).toReal)^2 ∂(μ.prod ρ)) =
      ∫ x, ((ν.rnDeriv μ x).toReal)^2 ∂μ := by
  simpa only [Measure.compProd_const] using
    rnSquare_integral_compProd ν μ (Kernel.const X ρ) hi

/-- Adjoining an independent common probability factor preserves warmness. -/
theorem L2Warm.prod_right {μ ν : Measure X} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {B : ℝ} (h : L2Warm μ ν B) (ρ : Measure Y) [IsProbabilityMeasure ρ] :
    L2Warm (μ.prod ρ) (ν.prod ρ) B := by
  simpa only [Measure.compProd_const] using h.compProd (Kernel.const X ρ)

end AcceleratedLogConcave.Probability
