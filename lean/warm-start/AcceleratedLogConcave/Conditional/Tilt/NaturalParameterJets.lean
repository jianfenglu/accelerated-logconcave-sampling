import AcceleratedLogConcave.Analysis.CompactScalarProduct
import AcceleratedLogConcave.Analysis.PositiveVarianceSlab
import AcceleratedLogConcave.Conditional.Definitions
import AcceleratedLogConcave.Conditional.Tilt.HeatIntegral

/-! natural-parameter time/space adapter. Compactness is applied
only to scalar time coefficients, yielding linear spatial growth for each
finite mixed derivative. No regularity assumption on the potential occurs. -/
noncomputable section
open Set Function
open scoped ContDiff
namespace AcceleratedLogConcave.Conditional.Tilt.NaturalParameterJets
open Analysis.CompactScalarJets Analysis.PositiveVarianceSlab

def precision (t : ℝ) : ℝ := (2 * conditionalVariance t)⁻¹
def tiltScale (t : ℝ) : ℝ := t / conditionalVariance t
def inverseVariance (t : ℝ) : ℝ := (conditionalVariance t)⁻¹

theorem contDiffOn_precision : ContDiffOn ℝ ∞ precision (Ioo (-1) 1) := by
  apply ((contDiffOn_const.mul
    (contDiffOn_const.sub (contDiffOn_id.pow 2))).inv _)
  intro t ht
  exact (mul_pos (by norm_num) (conditionalVariance_pos ht.1 ht.2)).ne'

theorem contDiffOn_inverseVariance : ContDiffOn ℝ ∞ inverseVariance (Ioo (-1) 1) := by
  apply (contDiffOn_const.sub (contDiffOn_id.pow 2)).inv
  intro t ht
  exact (conditionalVariance_pos ht.1 ht.2).ne'

theorem contDiffOn_tiltScale : ContDiffOn ℝ ∞ tiltScale (Ioo (-1) 1) := by
  change ContDiffOn ℝ ∞ (fun t : ℝ => t / conditionalVariance t) (Ioo (-1) 1)
  simpa only [inverseVariance, div_eq_mul_inv, id_eq] using
    contDiffOn_id.mul contDiffOn_inverseVariance

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def domain : Set (ℝ × E) := Prod.fst ⁻¹' Ioo (-1) 1
def parameters (p : ℝ × E) : ℝ × E := (precision p.1, tiltScale p.1 • p.2)

omit [NormedSpace ℝ E] in
theorem isOpen_domain : IsOpen (domain (E := E)) := isOpen_Ioo.preimage continuous_fst

theorem contDiffOn_parameters : ContDiffOn ℝ ∞ (parameters (E := E)) domain := by
  exact (contDiffOn_precision.comp_continuousLinearMap
    (ContinuousLinearMap.fst ℝ ℝ E)).prodMk
    ((contDiffOn_tiltScale.comp_continuousLinearMap
      (ContinuousLinearMap.fst ℝ ℝ E)).smul contDiff_snd.contDiffOn)

theorem parameters_mem_gaussianDomain {p : ℝ × E} (hp : p ∈ domain) :
    parameters p ∈ gaussianDomain := by
  change 0 < (2 * conditionalVariance p.1)⁻¹
  exact inv_pos.mpr (mul_pos (by norm_num) (conditionalVariance_pos hp.1 hp.2))

/-- Each fixed-order parameter jet grows at most linearly in the full
space-time input. Time is uniformly confined to the construction slab. -/
theorem exists_linear_parameter_jet_bound {b : ℝ} (hb0 : 0 ≤ b) (hb1 : b < 1)
    (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p : ℝ × E, p.1 ∈ Icc (left b) (right b) →
      ‖iteratedFDerivWithin ℝ n parameters domain p‖ ≤ C * (1 + ‖p‖) := by
  let L := ContinuousLinearMap.fst ℝ ℝ E
  let M := ContinuousLinearMap.snd ℝ ℝ E
  have hL : ‖L‖ ≤ 1 := ContinuousLinearMap.norm_fst_le ℝ ℝ E
  have hM : ‖M‖ ≤ 1 := ContinuousLinearMap.norm_snd_le ℝ ℝ E
  have hST : Icc (left b) (right b) ⊆ Ioo (-1) 1 := construction_subset hb0 hb1
  obtain ⟨A, hA, hAbound⟩ := exists_uniform_jet_comp_linear_bound
    isOpen_Ioo isCompact_Icc hST contDiffOn_precision L hL n
  obtain ⟨B, hB, hBbound⟩ := exists_linear_jet_scalar_times_linear_bound
    isOpen_Ioo isCompact_Icc hST contDiffOn_tiltScale L hL M hM n
  refine ⟨A + B, add_nonneg hA hB, ?_⟩
  intro p hp
  have hpU : p ∈ domain := hST hp
  have hα : ContDiffOn ℝ ∞ (precision ∘ L) domain :=
    contDiffOn_precision.comp_continuousLinearMap L
  have hβ : ContDiffOn ℝ ∞ (fun q : ℝ × E => tiltScale (L q) • M q) domain :=
    (contDiffOn_tiltScale.comp_continuousLinearMap L).smul M.contDiff.contDiffOn
  change ‖iteratedFDerivWithin ℝ n
    (fun q : ℝ × E => ((precision ∘ L) q, tiltScale (L q) • M q)) domain p‖ ≤ _
  rw [iteratedFDerivWithin_prodMk (hα p hpU) (hβ p hpU)
    isOpen_domain.uniqueDiffOn hpU (by simp : (n : ℕ∞ω) ≤ ∞),
    ContinuousMultilinearMap.opNorm_prod, max_le_iff]
  constructor
  · apply (hAbound p hp).trans
    apply (le_mul_of_one_le_right hA (le_add_of_nonneg_right (norm_nonneg p))).trans
    exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hB) (by positivity)
  · exact (hBbound p hp).trans (mul_le_mul_of_nonneg_right
      (le_add_of_nonneg_left hA) (by positivity))

/-- A uniform linear envelope for the natural tilt on the construction slab. -/
theorem exists_linear_tilt_weight_bound {b : ℝ} (hb0 : 0 ≤ b) (hb1 : b < 1) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ p : ℝ × E, p.1 ∈ Icc (left b) (right b) →
      1 + ‖(parameters p).2‖ ≤ C * (1 + ‖p‖) := by
  let B : ℝ := right b * (varianceFloor b)⁻¹
  have hB : 0 ≤ B := mul_nonneg (by dsimp [right]; positivity)
    (inv_nonneg.mpr (varianceFloor_pos hb0 hb1).le)
  refine ⟨1 + B, le_add_of_nonneg_right hB, ?_⟩
  intro p hp
  have hβ : |tiltScale p.1| ≤ B := abs_timeRatio_le hb0 hb1 hp
  have htilt : ‖(parameters p).2‖ ≤ B * ‖p‖ := by
    change ‖tiltScale p.1 • p.2‖ ≤ _
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul hβ (norm_snd_le p) (norm_nonneg _) hB
  have hmul : 0 ≤ B * ‖p‖ := mul_nonneg hB (norm_nonneg p)
  nlinarith [norm_nonneg p]

end AcceleratedLogConcave.Conditional.Tilt.NaturalParameterJets
