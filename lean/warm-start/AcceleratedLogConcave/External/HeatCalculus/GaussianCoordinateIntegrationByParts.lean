/-
Adapted in part from openai/math, commit 1581d4cbdd69a0faf34b2089614fe2a814316a6a:
lean/OAI/Probability/FreeIsing/Gaussian/PiIntegrationByParts.lean.
https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/FreeIsing/Gaussian/PiIntegrationByParts.lean
Apache 2.0; see Upstream/LICENSE.openai-math.

measurePreserving_funSplitAt is relocated unchanged. The product integration
proof is adapted to integrability hypotheses by using almost-everywhere Fubini
sections and the scalar integrable Stein identity, removing boundedness and
continuity bounds. The final theorem is an original bridge to Mathlib's actual
stdGaussian on EuclideanSpace. No divergence isometry is assumed or asserted.
-/
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Analysis.Calculus.Deriv.Pi
import AcceleratedLogConcave.External.HeatCalculus.GaussianIntegrationByParts
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Topology.Homeomorph.Lemmas
open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace AcceleratedLogConcave.HeatCalculus
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
theorem measurePreserving_funSplitAt (μ : ι → Measure ℝ)
    [∀ j, SigmaFinite (μ j)] (i : ι) :
    MeasurePreserving (Homeomorph.funSplitAt ℝ i) (Measure.pi μ)
      ((μ i).prod (Measure.pi fun j : {j // j ≠ i} => μ j)) := by
  let e := (Homeomorph.funSplitAt ℝ i).toMeasurableEquiv.symm
  apply MeasurePreserving.symm e
  refine ⟨e.measurable, (Measure.pi_eq fun s hs => ?_).symm⟩
  rw [e.map_apply]
  have hpre : e ⁻¹' Set.pi Set.univ s =
      s i ×ˢ Set.pi Set.univ (fun j : {j // j ≠ i} => s j) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_true_left,
      Set.mem_prod]
    constructor
    · intro h
      constructor
      · simpa [e, Homeomorph.funSplitAt, Homeomorph.piSplitAt,
          Equiv.piSplitAt] using h i
      · intro j
        simpa [e, Homeomorph.funSplitAt, Homeomorph.piSplitAt,
          Equiv.piSplitAt, j.property] using h j
    · rintro ⟨hi, hj⟩ j
      by_cases hji : j = i
      · subst j
        simpa [e, Homeomorph.funSplitAt, Homeomorph.piSplitAt,
          Equiv.piSplitAt] using hi
      · simpa [e, Homeomorph.funSplitAt, Homeomorph.piSplitAt,
          Equiv.piSplitAt, hji] using hj ⟨j, hji⟩
  rw [hpre, Measure.prod_prod, Measure.pi_pi]
  simpa using (Fintype.prod_eq_mul_prod_subtype_ne (fun j => μ j (s j)) i).symm


theorem gaussian_pi_integral_centered_mul_of_integrable
    (m : ι → ℝ) (v : ι → ℝ≥0) (i : ι)
    {f f' : (ι → ℝ) → ℝ}
    (hf : ∀ z t, HasDerivAt (fun r => f (Function.update z i r))
      (f' (Function.update z i t)) t)
    (hfi : Integrable f (Measure.pi (fun j => gaussianReal (m j) (v j))))
    (hf'i : Integrable f' (Measure.pi (fun j => gaussianReal (m j) (v j))))
    (hxfi : Integrable (fun z => (z i - m i) * f z)
      (Measure.pi (fun j => gaussianReal (m j) (v j)))) :
    (∫ z, (z i - m i) * f z ∂Measure.pi (fun j => gaussianReal (m j) (v j))) =
      (v i : ℝ) * ∫ z, f' z ∂Measure.pi (fun j => gaussianReal (m j) (v j)) := by
  let μ : ι → Measure ℝ := fun j => gaussianReal (m j) (v j)
  let ν := Measure.pi (fun j : {j // j ≠ i} => μ j)
  let e := (Homeomorph.funSplitAt ℝ i).toMeasurableEquiv.symm
  have hmp : MeasurePreserving e ((μ i).prod ν) (Measure.pi μ) :=
    (measurePreserving_funSplitAt μ i).symm
  have heval (x : ℝ × ({j // j ≠ i} → ℝ)) : e x i = x.1 := by
    simp [e, Homeomorph.funSplitAt, Homeomorph.piSplitAt, Equiv.piSplitAt]
  have hupdate (x : ℝ × ({j // j ≠ i} → ℝ)) (t : ℝ) :
      Function.update (e x) i t = e (t, x.2) := by
    ext j
    by_cases hji : j = i
    · subst j
      simp [heval]
    · simp [e, Homeomorph.funSplitAt, Homeomorph.piSplitAt, Equiv.piSplitAt, hji]
  have hprod := (hmp.integrable_comp_emb e.measurableEmbedding).2 hxfi
  have hprod' := (hmp.integrable_comp_emb e.measurableEmbedding).2 hf'i
  have hprodf := (hmp.integrable_comp_emb e.measurableEmbedding).2 hfi
  have hstein : ∀ᵐ y ∂ν,
      (∫ r, (r - m i) * f (e (r, y)) ∂μ i) =
        (v i : ℝ) * ∫ r, f' (e (r, y)) ∂μ i := by
    filter_upwards [hprod.prod_left_ae, hprod'.prod_left_ae, hprodf.prod_left_ae] with y hy hy' hyf
    apply gaussian_integral_centered_mul_eq_variance_mul_deriv (m i) (v i)
    · intro r
      simpa only [hupdate] using hf (e (0, y)) r
    · exact hyf
    · exact hy'
    · simpa only [Function.comp_def, heval] using hy
  calc
    _ = ∫ x, (e x i - m i) * f (e x) ∂(μ i).prod ν :=
      (hmp.integral_comp e.measurableEmbedding _).symm
    _ = ∫ y, ∫ r, (r - m i) * f (e (r, y)) ∂μ i ∂ν := by
      simpa only [Function.comp_def, heval] using integral_prod_symm _ hprod
    _ = ∫ y, (v i : ℝ) * ∫ r, f' (e (r, y)) ∂μ i ∂ν := integral_congr_ae hstein
    _ = (v i : ℝ) * ∫ x, f' (e x) ∂(μ i).prod ν := by
      rw [integral_const_mul]
      congr 1
      exact (integral_prod_symm _ hprod').symm
    _ = _ := by rw [hmp.integral_comp e.measurableEmbedding]

local notation "E" => EuclideanSpace ℝ ι

theorem stdGaussian_integral_coordinate_mul_of_hasFDerivAt (i : ι)
    {f : E → ℝ} {f' : E → E →L[ℝ] ℝ}
    (hf : ∀ z, HasFDerivAt f (f' z) z)
    (hfi : Integrable f (stdGaussian E))
    (hf'i : Integrable (fun z => f' z (EuclideanSpace.basisFun ι ℝ i)) (stdGaussian E))
    (hxfi : Integrable (fun z => z i * f z) (stdGaussian E)) :
    (∫ z, z i * f z ∂stdGaussian E) =
      ∫ z, f' z (EuclideanSpace.basisFun ι ℝ i) ∂stdGaussian E := by
  let e := (EuclideanSpace.equiv ι ℝ).symm
  have hmp : MeasurePreserving e (Measure.pi (fun _ : ι => gaussianReal 0 1)) (stdGaussian E) :=
    ⟨e.continuous.measurable, map_pi_eq_stdGaussian⟩
  have h1 := hmp.integrable_comp_of_integrable hfi
  have h2 := hmp.integrable_comp_of_integrable hf'i
  have h3 := hmp.integrable_comp_of_integrable hxfi
  have hd (z : ι → ℝ) (t : ℝ) :
      HasDerivAt (fun r => f (e (Function.update z i r)))
        (f' (e (Function.update z i t)) (EuclideanSpace.basisFun ι ℝ i)) t := by
    have hh := (hf (e (Function.update z i t))).comp_hasDerivAt t
      (e.hasFDerivAt.comp_hasDerivAt t (hasDerivAt_update z i t))
    convert hh using 1
    · rfl
    · rw [EuclideanSpace.basisFun_apply]
      rfl
  have h := gaussian_pi_integral_centered_mul_of_integrable (fun _ => 0) (fun _ => 1) i hd h1 h2
    (by simpa only [sub_zero, Function.comp_def, e, PiLp.continuousLinearEquiv_symm_apply, WithLp.ofLp_toLp] using h3)
  simp only [sub_zero, NNReal.coe_one, one_mul] at h
  rw [← hmp.integral_comp e.toHomeomorph.toMeasurableEquiv.measurableEmbedding (fun z => z i * f z),
    ← hmp.integral_comp e.toHomeomorph.toMeasurableEquiv.measurableEmbedding (fun z => f' z (EuclideanSpace.basisFun ι ℝ i))]
  exact h

end
end AcceleratedLogConcave.HeatCalculus
