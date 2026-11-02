import AcceleratedLogConcave.Channels.CoolingLocalKL

/-!
# Exact cooling decoder kernel and its zero-width boundary

The standardized posterior is an explicit measurable kernel, obtained by
retaining its center and undoing the physical posterior's affine coordinates.
At positive width its fibers are the existing primitive law. Adding variance
`3/4` and then the independent variance-`1/4` reserve gives the exact bridge.

At zero width the existing normalized posterior is the base Gibbs law, so the
existing equal-width bridge is a midpoint law, not generally the identity.
The reserved decoder is the identity at zero. `zeroAwareCoolingBridge` is an
explicitly new kernel family that totalizes the positive-width identity.

The KL corollary changes only the supplied coupling's left-marginal notation.
It reuses the proved exact-to-implemented bound and does not construct a
compiler output law, select a measurable coupling, or assume the decoder law.
-/

noncomputable section

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal

namespace AcceleratedLogConcave.Channels
variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- Standardize the physical posterior while retaining the entering center. -/
def standardizedCoolingPosterior (V : E → ℝ) (hV : Measurable V)
    (w : ℝ≥0) : Kernel E E :=
  (Kernel.id ×ₖ
    Gibbs.normalizedPosteriorKernel V (fun _ : E ↦ (w : ℝ)) id
      hV measurable_const measurable_id).map
    (fun p ↦ (Real.sqrt (w : ℝ))⁻¹ • (p.2 - p.1))

/-- Exact pre-reserve law, packaged without choosing pointwise couplings. -/
def exactCoolingPreReserve (V : E → ℝ) (hV : Measurable V)
    (w : ℝ≥0) : Kernel E E :=
  forwardKernel (3 / 4 : ℝ≥0) ∘ₖ standardizedCoolingPosterior V hV w

theorem standardizedCoolingPosterior_isMarkov
    {V : E → ℝ} (hV : Measurable V)
    (hI : Integrable (fun x ↦ Real.exp (-V x))) (w : ℝ≥0) :
    IsMarkovKernel (standardizedCoolingPosterior V hV w) := by
  have := posterior_kernel_isMarkov hV hI w
  unfold standardizedCoolingPosterior
  apply Kernel.IsMarkovKernel.map
  fun_prop

theorem exactCoolingPreReserve_isMarkov
    {V : E → ℝ} (hV : Measurable V)
    (hI : Integrable (fun x ↦ Real.exp (-V x))) (w : ℝ≥0) :
    IsMarkovKernel (exactCoolingPreReserve V hV w) := by
  have := standardizedCoolingPosterior_isMarkov hV hI w
  unfold exactCoolingPreReserve
  infer_instance

theorem standardizedCoolingPosterior_apply
    {V : E → ℝ} (hV : Measurable V)
    (hI : Integrable (fun x ↦ Real.exp (-V x))) (w : ℝ≥0) (x : E) :
    standardizedCoolingPosterior V hV w x =
      (Gibbs.normalizedPosteriorKernel V (fun _ : E ↦ (w : ℝ)) id
        hV measurable_const measurable_id x).map
          (fun u ↦ (Real.sqrt (w : ℝ))⁻¹ • (u - x)) := by
  have := posterior_kernel_isMarkov hV hI w
  rw [standardizedCoolingPosterior, Kernel.map_apply _ (by fun_prop),
    Kernel.prod_apply, Kernel.id_apply, Measure.dirac_prod,
    Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

/-- Positive width allows inversion of the existing primitive affine law. -/
theorem standardizedCoolingPosterior_apply_pos
    {V : E → ℝ} (hV : Measurable V)
    (hI : Integrable (fun x ↦ Real.exp (-V x)))
    (w : ℝ≥0) (hw : 0 < w) (x : E) :
    standardizedCoolingPosterior V hV w x =
      Gibbs.primitiveLaw V x (Real.sqrt (w : ℝ)) := by
  have hs : Real.sqrt (w : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hw).ne'
  rw [standardizedCoolingPosterior_apply hV hI, ← primitiveLaw_map_sqrt hV w hw x,
    Measure.map_map (by fun_prop) (by fun_prop)]
  simp only [Function.comp_def, add_sub_cancel_left, smul_smul,
    inv_mul_cancel₀ hs, one_smul, Measure.map_id']

theorem exactCoolingPreReserve_apply_pos
    {V : E → ℝ} (hV : Measurable V)
    (hI : Integrable (fun x ↦ Real.exp (-V x)))
    (w : ℝ≥0) (hw : 0 < w) (x : E) :
    exactCoolingPreReserve V hV w x =
      forward (Gibbs.primitiveLaw V x (Real.sqrt (w : ℝ))) (3 / 4 : ℝ≥0) := by
  have := standardizedCoolingPosterior_isMarkov hV hI w
  change forwardKernel (3 / 4) ∘ₘ standardizedCoolingPosterior V hV w x = _
  rw [forwardKernel_comp, standardizedCoolingPosterior_apply_pos hV hI w hw x]

/-- Kernel equality derived from the posterior law and the `3/4 + 1/4` split. -/
theorem reservedDecoder_exactCoolingPreReserve_pos
    {V : E → ℝ} (hV : Measurable V)
    (hI : Integrable (fun x ↦ Real.exp (-V x)))
    (w : ℝ≥0) (hw : 0 < w) :
    reservedDecoder (exactCoolingPreReserve V hV w) w = equalWidthBridge V hV w := by
  have := exactCoolingPreReserve_isMarkov hV hI w
  ext x : 1
  rw [reservedDecoder_eq_map_forward, exactCoolingPreReserve_apply_pos hV hI w hw x]
  exact (equalWidthBridge_eq_map_reserve_split hV hI w hw x).symm

/-- This zero law concerns the reserved decoder, not the existing exact bridge. -/
theorem reservedDecoder_zero (pre : Kernel E E) [IsMarkovKernel pre] :
    reservedDecoder pre 0 = Kernel.id := by
  ext x : 1
  rw [reservedDecoder_apply]
  simp [Kernel.id_apply]

/-- At zero variance Lean's division convention removes the likelihood term. -/
theorem normalizedPosteriorKernel_zero_apply
    {V : E → ℝ} (hV : Measurable V)
    (hI : Integrable (fun x ↦ Real.exp (-V x))) (x : E) :
    Gibbs.normalizedPosteriorKernel V (fun _ : E ↦ (0 : ℝ)) id
      hV measurable_const measurable_id x = volume.tilted (fun u ↦ -V u) := by
  have : IsProbabilityMeasure (volume.tilted (fun u ↦ -V u)) := isProbabilityMeasure_tilted hI
  simpa using posterior_kernel_eq_tilted_prior hV hI 0 x

/-- The existing zero-width bridge remains the midpoint law of the base Gibbs measure. -/
theorem equalWidthBridge_zero_apply
    {V : E → ℝ} (hV : Measurable V)
    (hI : Integrable (fun x ↦ Real.exp (-V x))) (x : E) :
    equalWidthBridge V hV 0 x = (volume.tilted (fun u ↦ -V u)).map
      (fun u ↦ (1 / 2 : ℝ) • (x + u)) := by
  have : IsProbabilityMeasure (volume.tilted (fun u ↦ -V u)) := isProbabilityMeasure_tilted hI
  rw [equalWidthBridge_apply hV hI]
  simp only [NNReal.coe_zero]
  rw [normalizedPosteriorKernel_zero_apply hV hI x,
    noise_zero, Measure.prod_dirac, Measure.map_map (by fun_prop) (by fun_prop)]
  simp only [Function.comp_def, add_zero]

/-- A new kernel family; the existing `equalWidthBridge` is not redefined at zero. -/
def zeroAwareCoolingBridge (V : E → ℝ) (hV : Measurable V) (w : ℝ≥0) : Kernel E E :=
  if w = 0 then Kernel.id else equalWidthBridge V hV w

theorem zeroAwareCoolingBridge_isMarkov
    {V : E → ℝ} (hV : Measurable V)
    (hI : Integrable (fun x ↦ Real.exp (-V x))) (w : ℝ≥0) :
    IsMarkovKernel (zeroAwareCoolingBridge V hV w) := by
  unfold zeroAwareCoolingBridge
  split_ifs
  · infer_instance
  · exact equalWidthBridge_isMarkov hV hI w

theorem reservedDecoder_exactCoolingPreReserve_total
    {V : E → ℝ} (hV : Measurable V)
    (hI : Integrable (fun x ↦ Real.exp (-V x))) (w : ℝ≥0) :
    reservedDecoder (exactCoolingPreReserve V hV w) w = zeroAwareCoolingBridge V hV w := by
  have := exactCoolingPreReserve_isMarkov hV hI w
  by_cases hw : w = 0
  · subst w
    simp [zeroAwareCoolingBridge, reservedDecoder_zero]
  · simp only [zeroAwareCoolingBridge, hw, ↓reduceIte]
    exact reservedDecoder_exactCoolingPreReserve_pos hV hI w (pos_iff_ne_zero.mpr hw)

/-- The previous KL supplier with its left marginal expressed as the explicit
exact pre-reserve kernel. `J` is still supplied and measurable; no compiler law
or quantitative energy bound is inferred. -/
theorem cooling_localKL_of_exactPreCoupling
    {V : E → ℝ} (hV : Measurable V)
    (hI : Integrable (fun x ↦ Real.exp (-V x)))
    (w : ℝ≥0) (hw : 0 < w)
    (pre : Kernel E E) [IsMarkovKernel pre]
    (J : Kernel E (E × E)) [IsMarkovKernel J]
    (hleft : ∀ x, (J x).map Prod.fst = exactCoolingPreReserve V hV w x)
    (hright : ∀ x, (J x).map Prod.snd = pre x) :
    (∫⁻ x, klDiv (equalWidthBridge V hV w x) (reservedDecoder pre w x)
      ∂forward (volume.tilted (fun u ↦ -V u)) w) ≤
    ∫⁻ x, ∫⁻ uv, ENNReal.ofReal (2 * ‖uv.1 - uv.2‖ ^ 2)
      ∂J x ∂forward (volume.tilted (fun u ↦ -V u)) w := by
  exact cooling_localKL_of_preCoupling hV hI w hw pre J
    (fun x ↦ (hleft x).trans (exactCoolingPreReserve_apply_pos hV hI w hw x)) hright

end AcceleratedLogConcave.Channels
