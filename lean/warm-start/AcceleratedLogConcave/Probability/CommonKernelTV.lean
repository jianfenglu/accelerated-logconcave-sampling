import AcceleratedLogConcave.Probability.TotalVariation
import Mathlib.Probability.Kernel.Composition.RadonNikodym

/-! Exact total variation preservation when a common randomization retains
its input, and contraction when the input is discarded. Used to carry the
proved phase mixing estimate through the literal cooling suffix. -/
noncomputable section
set_option autoImplicit false
set_option Elab.async false
open MeasureTheory ProbabilityTheory
namespace AcceleratedLogConcave.Probability
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

theorem totalVariationDistance_compProd_same (μ ν : Measure X)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (K : Kernel X Y) [IsMarkovKernel K] :
    totalVariationDistance (μ ⊗ₘ K) (ν ⊗ₘ K)=totalVariationDistance μ ν := by
  let ρ := μ+ν
  have hμ : μ≪ρ := Measure.absolutelyContinuous_of_le (fun s => le_add_right (le_refl (μ s)))
  have hν : ν≪ρ := Measure.absolutelyContinuous_of_le (fun s => le_add_left (le_refl (ν s)))
  rw [totalVariationDistance_eq_integral_abs _ _ (ρ ⊗ₘ K)
    (hμ.compProd_left K) (hν.compProd_left K),
    totalVariationDistance_eq_integral_abs _ _ ρ hμ hν]
  congr 1
  have he : (fun z => |((μ ⊗ₘ K).rnDeriv (ρ ⊗ₘ K) z).toReal-
      ((ν ⊗ₘ K).rnDeriv (ρ ⊗ₘ K) z).toReal|)=ᵐ[ρ ⊗ₘ K]
      fun z => |(μ.rnDeriv ρ z.1).toReal-(ν.rnDeriv ρ z.1).toReal| := by
    filter_upwards [rnDeriv_measure_compProd_left μ ρ K,
      rnDeriv_measure_compProd_left ν ρ K] with z h1 h2
    rw [h1,h2]
  rw [integral_congr_ae he]
  have hi : Integrable (fun x => |(μ.rnDeriv ρ x).toReal-(ν.rnDeriv ρ x).toReal|) ρ :=
    (Measure.integrable_toReal_rnDeriv.sub Measure.integrable_toReal_rnDeriv).abs
  have hmap : (ρ ⊗ₘ K).map Prod.fst=ρ := Measure.fst_compProd ρ K
  have himap : Integrable (fun x => |(μ.rnDeriv ρ x).toReal-(ν.rnDeriv ρ x).toReal|)
      ((ρ ⊗ₘ K).map Prod.fst) := by simpa only [hmap] using hi
  rw [← integral_map measurable_fst.aemeasurable himap.aestronglyMeasurable,
    hmap]

theorem totalVariationDistance_common_kernel (μ ν : Measure X)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (K : Kernel X Y) [IsMarkovKernel K] :
    totalVariationDistance (K ∘ₘ μ) (K ∘ₘ ν)≤totalVariationDistance μ ν := by
  have h := totalVariationDistance_map_le (μ ⊗ₘ K) (ν ⊗ₘ K) Prod.snd measurable_snd
  change totalVariationDistance (μ ⊗ₘ K).snd (ν ⊗ₘ K).snd≤_ at h
  simpa only [Measure.snd_compProd,totalVariationDistance_compProd_same] using h
end AcceleratedLogConcave.Probability
