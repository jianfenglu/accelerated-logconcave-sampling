import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.InformationTheory.KullbackLeibler.DataProcessing
import Mathlib.Probability.Kernel.Composition.RadonNikodym
import Mathlib.Probability.Kernel.Composition.AbsolutelyContinuous
import Mathlib.Probability.Distributions.Gaussian.Fernique
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Gaussian reverse transport (W03)

The main theorem `gaussian_reverse_transport_independent` is the Gaussian reverse
transport inequality in exact-to-implemented KL orientation. The divergence and
energy integral are extended-valued; no finite-cost assumption is imposed.

`gaussian_reverse_transport_independent_retained` retains any measurable function
of the coupling state. The reserve is independent of that entire state.
`gaussian_reverse_transport_covariance_conditional` gives the pointwise theorem
for a supplied conditional coupling kernel and jointly measurable endpoints.
It does not assert existence of a disintegration on arbitrary measurable spaces.

Supporting results prove the same-base extended KL formula, Gaussian-shift KL,
and the positive-definite covariance/Mahalanobis identification. No decoder or
shared project definitions are used.
-/


open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal

namespace AcceleratedLogConcave.Channels

variable {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
  [MeasurableSpace.CountableOrCountablyGenerated α β]
  (μ : Measure α) [IsFiniteMeasure μ]
  (κ η : Kernel α β) [IsMarkovKernel κ] [IsMarkovKernel η]

/-- Extended-valued same-base KL chain rule for absolutely continuous fibers.
The fiber absolute-continuity premise will be discharged for Gaussian shifts. -/
theorem klDiv_compProd_eq_lintegral_of_ac
    (hac : ∀ a, κ a ≪ η a) :
    klDiv (μ ⊗ₘ κ) (μ ⊗ₘ η) = ∫⁻ a, klDiv (κ a) (η a) ∂μ := by
  have hjoint : μ ⊗ₘ κ ≪ μ ⊗ₘ η :=
    Measure.AbsolutelyContinuous.compProd_right (Filter.Eventually.of_forall hac)
  rw [klDiv_eq_lintegral_klFun_of_ac hjoint]
  calc
    ∫⁻ p, ENNReal.ofReal (klFun (((μ ⊗ₘ κ).rnDeriv (μ ⊗ₘ η)) p).toReal)
        ∂(μ ⊗ₘ η) =
        ∫⁻ p, ENNReal.ofReal (klFun ((κ.rnDeriv η p.1 p.2).toReal)) ∂(μ ⊗ₘ η) := by
      apply lintegral_congr_ae
      filter_upwards [rnDeriv_measure_compProd_right μ κ η] with p hp
      rw [hp]
    _ = ∫⁻ a, ∫⁻ b, ENNReal.ofReal (klFun ((κ.rnDeriv η a b).toReal)) ∂η a ∂μ := by
      rw [Measure.lintegral_compProd]
      fun_prop
    _ = ∫⁻ a, klDiv (κ a) (η a) ∂μ := by
      apply lintegral_congr
      intro a
      rw [klDiv_eq_lintegral_klFun_of_ac (hac a)]
      apply lintegral_congr_ae
      filter_upwards [Kernel.rnDeriv_eq_rnDeriv_measure (κ := κ) (η := η) (a := a)] with b hb
      rw [hb]

/-- Measurable marginalization may retain any common input coordinate.
Orientation is exact kernel κ to implemented kernel η throughout. -/
theorem klDiv_map_compProd_le_lintegral_of_ac
    (hac : ∀ a, κ a ≪ η a) (f : α × β → γ) (hf : Measurable f) :
    klDiv ((μ ⊗ₘ κ).map f) ((μ ⊗ₘ η).map f) ≤
      ∫⁻ a, klDiv (κ a) (η a) ∂μ := by
  rw [← klDiv_compProd_eq_lintegral_of_ac μ κ η hac]
  exact klDiv_map_le _ _ hf

end AcceleratedLogConcave.Channels

open MeasureTheory ProbabilityTheory InformationTheory Real
open scoped ENNReal NNReal

namespace AcceleratedLogConcave.Channels

lemma gaussianReal_ac_gaussianReal (a b : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    gaussianReal a v ≪ gaussianReal b v :=
  (gaussianReal_absolutelyContinuous a hv).trans (gaussianReal_absolutelyContinuous' b hv)

lemma log_gaussianPDFReal_ratio (a b x : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    Real.log (gaussianPDFReal a v x / gaussianPDFReal b v x) =
      ((a-b) / v) * (x-a) + (a-b)^2 / (2*v) := by
  have hv' : (v : ℝ) ≠ 0 := by exact_mod_cast hv
  have hvpos : 0 < (v : ℝ) := lt_of_le_of_ne v.2 (Ne.symm hv')
  have hs : (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹ ≠ 0 := by positivity
  rw [gaussianPDFReal, gaussianPDFReal, Real.log_div
    (mul_ne_zero hs (Real.exp_ne_zero _)) (mul_ne_zero hs (Real.exp_ne_zero _)),
    Real.log_mul hs (Real.exp_ne_zero _), Real.log_mul hs (Real.exp_ne_zero _),
    Real.log_exp, Real.log_exp]
  field_simp
  ring

lemma llr_gaussianReal_same_variance (a b : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    llr (gaussianReal a v) (gaussianReal b v) =ᵐ[gaussianReal a v]
      fun x => ((a-b) / v) * (x-a) + (a-b)^2 / (2*v) := by
  have hac := gaussianReal_ac_gaussianReal a b hv
  have hratio := Measure.rnDeriv_eq_div
    (gaussianReal_absolutelyContinuous a hv) (gaussianReal_absolutelyContinuous b hv)
  filter_upwards [hac.ae_le hratio,
    (gaussianReal_absolutelyContinuous a hv).ae_le (rnDeriv_gaussianReal a v),
    (gaussianReal_absolutelyContinuous a hv).ae_le (rnDeriv_gaussianReal b v)] with x hx ha hb
  simp only [llr, hx, ha, hb, ENNReal.toReal_div, toReal_gaussianPDF]
  exact log_gaussianPDFReal_ratio a b x hv

/-- KL orientation is exact mean a to implemented mean b. -/
theorem klDiv_gaussianReal_same_variance (a b : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    klDiv (gaussianReal a v) (gaussianReal b v) = ENNReal.ofReal ((a-b)^2 / (2*v)) := by
  have heq := llr_gaussianReal_same_variance a b hv
  have hid : Integrable (fun x : ℝ => x) (gaussianReal a v) := IsGaussian.integrable_id
  have hi : Integrable (fun x : ℝ => ((a-b) / v) * (x-a) + (a-b)^2 / (2*v))
      (gaussianReal a v) := ((hid.sub (integrable_const a)).const_mul _).add (integrable_const _)
  have hllr : Integrable (llr (gaussianReal a v) (gaussianReal b v))
      (gaussianReal a v) := hi.congr heq.symm
  have hlin : Integrable (fun x : ℝ => ((a-b) / v) * (x-a)) (gaussianReal a v) :=
    (hid.sub (integrable_const a)).const_mul ((a-b) / v)
  rw [klDiv_of_ac_of_integrable (gaussianReal_ac_gaussianReal a b hv) hllr,
    integral_congr_ae heq, integral_add hlin (integrable_const ((a-b)^2 / (2*v))),
    integral_const_mul, integral_sub hid (integrable_const a)]
  simp

end AcceleratedLogConcave.Channels

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal

namespace AcceleratedLogConcave.Channels

lemma klDiv_map_measurableEquiv {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν] (e : α ≃ᵐ β) :
    klDiv (μ.map e) (ν.map e) = klDiv μ ν := by
  apply le_antisymm (klDiv_map_le _ _ e.measurable)
  have h := klDiv_map_le (μ.map e) (ν.map e) e.symm.measurable
  simpa only [Measure.map_map e.symm.measurable e.measurable,
    e.symm_comp_self, Measure.map_id] using h

lemma klDiv_prod_prob {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ ν : Measure α) (ρ σ : Measure β)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    [IsProbabilityMeasure ρ] [IsProbabilityMeasure σ] :
    klDiv (μ.prod ρ) (ν.prod σ) = klDiv μ ν + klDiv ρ σ := by
  have h := klDiv_compProd_eq_add μ ν (Kernel.const α ρ) (Kernel.const α σ)
  simp only [Measure.compProd_const] at h
  rw [h]
  congr 1
  have hswap := klDiv_map_measurableEquiv (μ.prod ρ) (μ.prod σ)
    (MeasurableEquiv.prodComm : α × β ≃ᵐ β × α)
  change klDiv ((μ.prod ρ).map Prod.swap) ((μ.prod σ).map Prod.swap) = _ at hswap
  simp only [Measure.prod_swap] at hswap
  rw [← hswap]
  simpa only [Measure.compProd_const] using klDiv_compProd_left ρ σ (Kernel.const β μ)

lemma klDiv_pi_fin_prob (n : ℕ) (μ ν : Fin n → Measure ℝ)
    [∀ i, IsProbabilityMeasure (μ i)] [∀ i, IsProbabilityMeasure (ν i)] :
    klDiv (Measure.pi μ) (Measure.pi ν) = ∑ i, klDiv (μ i) (ν i) := by
  induction n with
  | zero =>
    have h : μ = ν := by funext i; exact Fin.elim0 i
    simp [h]
  | succ n ih =>
    let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) 0
    have hμ := (measurePreserving_piFinSuccAbove μ 0).map_eq
    have hν := (measurePreserving_piFinSuccAbove ν 0).map_eq
    have he := klDiv_map_measurableEquiv (Measure.pi μ) (Measure.pi ν) e
    change klDiv ((Measure.pi μ).map (MeasurableEquiv.piFinSuccAbove _ 0))
      ((Measure.pi ν).map (MeasurableEquiv.piFinSuccAbove _ 0)) = _ at he
    rw [hμ, hν, klDiv_prod_prob] at he
    rw [← he, ih]
    simp only [Fin.sum_univ_succ, Fin.succAbove_zero]

end AcceleratedLogConcave.Channels
namespace AcceleratedLogConcave.Channels

lemma klDiv_pi_gaussianReal (n : ℕ) (a b : Fin n → ℝ) :
    klDiv (Measure.pi fun i => gaussianReal (a i) 1)
      (Measure.pi fun i => gaussianReal (b i) 1) =
      ENNReal.ofReal ((∑ i, (a i - b i)^2) / 2) := by
  rw [klDiv_pi_fin_prob]
  simp_rw [klDiv_gaussianReal_same_variance _ _ one_ne_zero]
  simp only [NNReal.coe_one, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => by positivity)]
  congr 1
  exact (Finset.sum_div _ _ _).symm

lemma map_pi_gaussianReal_eq_shift_stdGaussian (n : ℕ) (a : EuclideanSpace ℝ (Fin n)) :
    (Measure.pi fun i => gaussianReal (a i) 1).map (WithLp.toLp 2) =
      (stdGaussian (EuclideanSpace ℝ (Fin n))).map (fun x => a + x) := by
  rw [← map_pi_eq_stdGaussian, Measure.map_map (by fun_prop) (by fun_prop)]
  have hpi := Measure.pi_map_pi
    (μ := fun _ : Fin n => gaussianReal 0 1)
    (f := fun i x => a i + x) (fun _ => (measurable_const_add _).aemeasurable)
  simp only [gaussianReal_map_const_add, zero_add] at hpi
  rw [← hpi, Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1

lemma klDiv_shift_stdGaussian (n : ℕ) (a b : EuclideanSpace ℝ (Fin n)) :
    klDiv ((stdGaussian (EuclideanSpace ℝ (Fin n))).map (fun x => a + x))
      ((stdGaussian (EuclideanSpace ℝ (Fin n))).map (fun x => b + x)) =
      ENNReal.ofReal (‖a-b‖^2 / 2) := by
  rw [← map_pi_gaussianReal_eq_shift_stdGaussian,
    ← map_pi_gaussianReal_eq_shift_stdGaussian]
  have h := klDiv_map_measurableEquiv
    (Measure.pi fun i => gaussianReal (a i) 1)
    (Measure.pi fun i => gaussianReal (b i) 1) (MeasurableEquiv.toLp 2 (Fin n → ℝ))
  rw [MeasurableEquiv.coe_toLp] at h
  rw [h, klDiv_pi_gaussianReal, EuclideanSpace.real_norm_sq_eq]
  rfl

end AcceleratedLogConcave.Channels

namespace AcceleratedLogConcave.Channels

lemma klDiv_affine_stdGaussian (n : ℕ)
    (A : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (a b : EuclideanSpace ℝ (Fin n)) :
    klDiv ((stdGaussian (EuclideanSpace ℝ (Fin n))).map (fun x => a + A x))
      ((stdGaussian (EuclideanSpace ℝ (Fin n))).map (fun x => b + A x)) =
      ENNReal.ofReal (‖A.symm (a-b)‖^2 / 2) := by
  have ha : (fun x => a + A x) = A ∘ (fun x => A.symm a + x) := by
    ext x; simp
  have hb : (fun x => b + A x) = A ∘ (fun x => A.symm b + x) := by
    ext x; simp
  rw [ha, hb, ← Measure.map_map (by fun_prop) (by fun_prop),
    ← Measure.map_map (by fun_prop) (by fun_prop)]
  have h := klDiv_map_measurableEquiv
    ((stdGaussian (EuclideanSpace ℝ (Fin n))).map (fun x => A.symm a + x))
    ((stdGaussian (EuclideanSpace ℝ (Fin n))).map (fun x => A.symm b + x))
    A.toHomeomorph.toMeasurableEquiv
  simp only [Homeomorph.toMeasurableEquiv_coe, ContinuousLinearEquiv.coe_toHomeomorph] at h
  rw [h, klDiv_shift_stdGaussian, map_sub]

lemma affine_stdGaussian_ac (n : ℕ)
    (A : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (a b : EuclideanSpace ℝ (Fin n)) :
    ((stdGaussian (EuclideanSpace ℝ (Fin n))).map (fun x => a + A x)) ≪
      ((stdGaussian (EuclideanSpace ℝ (Fin n))).map (fun x => b + A x)) := by
  apply (klDiv_ne_top_iff.mp _).1
  rw [klDiv_affine_stdGaussian]
  exact ENNReal.ofReal_ne_top

noncomputable def freshKernel {α Z E : Type*}
    [MeasurableSpace α] [MeasurableSpace Z] [MeasurableSpace E]
    (ν : Measure Z) [SFinite ν] (F : α × Z → E) (hF : Measurable F) : Kernel α E where
  toFun a := ν.map (fun z => F (a,z))
  measurable' := by
    rw [Measure.measurable_measure]
    intro s hs
    have hf (a : α) : Measurable (fun z => F (a,z)) := hF.comp measurable_prodMk_left
    simp only [Measure.map_apply (hf _) hs]
    exact measurable_measure_prodMk_left (hs.preimage hF)

instance freshKernel_isMarkov {α Z E : Type*}
    [MeasurableSpace α] [MeasurableSpace Z] [MeasurableSpace E]
    (ν : Measure Z) [IsProbabilityMeasure ν] (F : α × Z → E) (hF : Measurable F) :
    IsMarkovKernel (freshKernel ν F hF) where
  isProbabilityMeasure a := by
    change IsProbabilityMeasure (ν.map (fun z => F (a,z)))
    have hf : Measurable (fun z => F (a,z)) := hF.comp measurable_prodMk_left
    exact ⟨by rw [Measure.map_apply hf MeasurableSet.univ]; simp⟩

lemma compProd_freshKernel {α Z E : Type*}
    [MeasurableSpace α] [MeasurableSpace Z] [MeasurableSpace E]
    (μ : Measure α) [SFinite μ] (ν : Measure Z) [IsProbabilityMeasure ν]
    (F : α × Z → E) (hF : Measurable F) :
    μ ⊗ₘ freshKernel ν F hF =
      (μ.prod ν).map (fun p => (p.1,F p)) := by
  ext s hs
  rw [Measure.compProd_apply hs, Measure.map_apply (measurable_fst.prodMk hF) hs,
    Measure.prod_apply (hs.preimage (measurable_fst.prodMk hF))]
  apply lintegral_congr
  intro a
  change (ν.map (fun z => F (a,z))) (Prod.mk a ⁻¹' s) = _
  have hf : Measurable (fun z => F (a,z)) := hF.comp measurable_prodMk_left
  rw [Measure.map_apply hf (hs.preimage measurable_prodMk_left)]
  rfl

end AcceleratedLogConcave.Channels

namespace AcceleratedLogConcave.Channels

/-- The product measure is the fresh Gaussian reserve, independent of the entire coupling state. -/
theorem gaussian_reverse_transport_retained
    {α R : Type*} [MeasurableSpace α] [MeasurableSpace R]
    (μ : Measure α) [IsFiniteMeasure μ] (n : ℕ)
    (A : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (u v : α → EuclideanSpace ℝ (Fin n)) (hu : Measurable u) (hv : Measurable v)
    (r : α → R) (hr : Measurable r) :
    klDiv ((μ.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))).map
      (fun p => (r p.1, u p.1 + A p.2)))
      ((μ.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))).map
        (fun p => (r p.1, v p.1 + A p.2))) ≤
      ∫⁻ a, ENNReal.ofReal (‖A.symm (u a-v a)‖^2 / 2) ∂μ := by
  let Fu : α × EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) :=
    fun p => u p.1 + A p.2
  let Fv : α × EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) :=
    fun p => v p.1 + A p.2
  have hFu : Measurable Fu := (hu.comp measurable_fst).add (A.continuous.measurable.comp measurable_snd)
  have hFv : Measurable Fv := (hv.comp measurable_fst).add (A.continuous.measurable.comp measurable_snd)
  let κ := freshKernel (stdGaussian (EuclideanSpace ℝ (Fin n))) Fu hFu
  let η := freshKernel (stdGaussian (EuclideanSpace ℝ (Fin n))) Fv hFv
  have hac : ∀ a, κ a ≪ η a := fun a => affine_stdGaussian_ac n A (u a) (v a)
  have hb := klDiv_map_compProd_le_lintegral_of_ac μ κ η hac
    (fun p => (r p.1,p.2)) ((hr.comp measurable_fst).prodMk measurable_snd)
  have hKL : ∀ a, klDiv (κ a) (η a) =
      ENNReal.ofReal (‖A.symm (u a-v a)‖^2 / 2) :=
    fun a => klDiv_affine_stdGaussian n A (u a) (v a)
  simp_rw [hKL] at hb
  change klDiv ((μ ⊗ₘ freshKernel _ Fu hFu).map _)
    ((μ ⊗ₘ freshKernel _ Fv hFv).map _) ≤ _ at hb
  rw [compProd_freshKernel, compProd_freshKernel,
    Measure.map_map (by fun_prop) (by fun_prop),
    Measure.map_map (by fun_prop) (by fun_prop)] at hb
  exact hb

theorem gaussian_reverse_transport
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] (n : ℕ)
    (A : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (u v : α → EuclideanSpace ℝ (Fin n)) (hu : Measurable u) (hv : Measurable v) :
    klDiv ((μ.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))).map
      (fun p => u p.1 + A p.2))
      ((μ.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))).map
        (fun p => v p.1 + A p.2)) ≤
      ∫⁻ a, ENNReal.ofReal (‖A.symm (u a-v a)‖^2 / 2) ∂μ := by
  have h := gaussian_reverse_transport_retained μ n A u v hu hv (fun _ => ()) measurable_const
  have hmap := klDiv_map_le
    ((μ.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))).map
      (fun p => ((), u p.1 + A p.2)))
    ((μ.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))).map
      (fun p => ((), v p.1 + A p.2))) measurable_snd
  rw [Measure.map_map measurable_snd (by fun_prop),
    Measure.map_map measurable_snd (by fun_prop)] at hmap
  exact hmap.trans h

theorem gaussian_reverse_transport_conditional
    {I α : Type*} [MeasurableSpace I] [MeasurableSpace α]
    (κ : Kernel I α) [IsMarkovKernel κ] (n : ℕ)
    (A : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (u v : I × α → EuclideanSpace ℝ (Fin n)) (hu : Measurable u) (hv : Measurable v) :
    ∀ i, klDiv (((κ i).prod (stdGaussian (EuclideanSpace ℝ (Fin n)))).map
      (fun p => u (i,p.1) + A p.2))
      (((κ i).prod (stdGaussian (EuclideanSpace ℝ (Fin n)))).map
        (fun p => v (i,p.1) + A p.2)) ≤
      ∫⁻ a, ENNReal.ofReal (‖A.symm (u (i,a)-v (i,a))‖^2 / 2) ∂κ i := by
  intro i
  exact gaussian_reverse_transport (κ i) n A _ _
    (hu.comp measurable_prodMk_left) (hv.comp measurable_prodMk_left)

end AcceleratedLogConcave.Channels

namespace AcceleratedLogConcave.Channels
open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace

noncomputable def covarianceSqrtEquiv (n : ℕ) (S : Matrix (Fin n) (Fin n) ℝ)
    (hS : S.PosDef) : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n) where
  toLinearEquiv :=
    { toFun := toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S)
      map_add' := (toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S)).map_add
      map_smul' := (toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S)).map_smul
      invFun := toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S)⁻¹
      left_inv := by
        intro x
        have hdet : IsUnit (CFC.sqrt S).det :=
          (Matrix.isUnit_iff_isUnit_det _).mp
            ((CFC.isUnit_sqrt_iff S hS.posSemidef.nonneg).mpr hS.isUnit)
        change (toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S)⁻¹ * toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S)) x = x
        rw [← map_mul, Matrix.nonsing_inv_mul _ hdet, map_one]
        rfl
      right_inv := by
        intro x
        have hdet : IsUnit (CFC.sqrt S).det :=
          (Matrix.isUnit_iff_isUnit_det _).mp
            ((CFC.isUnit_sqrt_iff S hS.posSemidef.nonneg).mpr hS.isUnit)
        change (toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S) * toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S)⁻¹) x = x
        rw [← map_mul, Matrix.mul_nonsing_inv _ hdet, map_one]
        rfl }

lemma covarianceSqrtEquiv_apply (n : ℕ) (S : Matrix (Fin n) (Fin n) ℝ)
    (hS : S.PosDef) (x : EuclideanSpace ℝ (Fin n)) :
    covarianceSqrtEquiv n S hS x = toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S) x := rfl

lemma covarianceSqrtEquiv_symm_apply (n : ℕ) (S : Matrix (Fin n) (Fin n) ℝ)
    (hS : S.PosDef) (x : EuclideanSpace ℝ (Fin n)) :
    (covarianceSqrtEquiv n S hS).symm x = toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S)⁻¹ x := rfl

lemma covarianceSqrtEquiv_symm_norm_sq (n : ℕ) (S : Matrix (Fin n) (Fin n) ℝ)
    (hS : S.PosDef) (x : EuclideanSpace ℝ (Fin n)) :
    ‖(covarianceSqrtEquiv n S hS).symm x‖^2 = x ⬝ᵥ S⁻¹ *ᵥ x := by
  rw [covarianceSqrtEquiv_symm_apply, hS.posSemidef.inv_sqrt,
    ContinuousLinearMap.apply_norm_sq_eq_inner_adjoint_right]
  have hstar : star (CFC.sqrt S⁻¹) = CFC.sqrt S⁻¹ :=
    (CFC.sqrt_nonneg S⁻¹).posSemidef.isHermitian
  have hclm : (toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S⁻¹)).adjoint =
      toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S⁻¹) := by
    change star (toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S⁻¹)) = _
    rw [← map_star, hstar]
  rw [hclm]
  change RCLike.re (inner ℝ x ((toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S⁻¹) *
    toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S⁻¹)) x)) = _
  rw [← map_mul, CFC.sqrt_mul_sqrt_self S⁻¹ hS.posSemidef.inv.nonneg,
    Matrix.inner_toEuclideanCLM]
  rfl

lemma klDiv_multivariateGaussian_same_covariance (n : ℕ)
    (S : Matrix (Fin n) (Fin n) ℝ) (hS : S.PosDef)
    (a b : EuclideanSpace ℝ (Fin n)) :
    klDiv (multivariateGaussian a S) (multivariateGaussian b S) =
      ENNReal.ofReal (((a-b) ⬝ᵥ S⁻¹ *ᵥ (a-b)) / 2) := by
  have h := klDiv_affine_stdGaussian n (covarianceSqrtEquiv n S hS) a b
  simpa only [covarianceSqrtEquiv_apply, covarianceSqrtEquiv_symm_norm_sq,
    multivariateGaussian, WithLp.ofLp_sub] using h

end AcceleratedLogConcave.Channels

namespace AcceleratedLogConcave.Channels
open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator

lemma prod_multivariateGaussian_map_add_retained
    {α R : Type*} [MeasurableSpace α] [MeasurableSpace R]
    (μ : Measure α) [IsFiniteMeasure μ] (n : ℕ)
    (S : Matrix (Fin n) (Fin n) ℝ)
    (u : α → EuclideanSpace ℝ (Fin n)) (hu : Measurable u)
    (r : α → R) (hr : Measurable r) :
    (μ.prod (multivariateGaussian 0 S)).map (fun p => (r p.1, u p.1+p.2)) =
      (μ.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))).map
        (fun p => (r p.1, u p.1 + toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S) p.2)) := by
  simp only [multivariateGaussian, zero_add]
  have hp := Measure.map_prod_map μ (stdGaussian (EuclideanSpace ℝ (Fin n)))
    measurable_id (toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S)).continuous.measurable
  rw [Measure.map_id] at hp
  rw [hp, Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

theorem gaussian_reverse_transport_covariance_retained
    {α R : Type*} [MeasurableSpace α] [MeasurableSpace R]
    (μ : Measure α) [IsFiniteMeasure μ] (n : ℕ)
    (S : Matrix (Fin n) (Fin n) ℝ) (hS : S.PosDef)
    (u v : α → EuclideanSpace ℝ (Fin n)) (hu : Measurable u) (hv : Measurable v)
    (r : α → R) (hr : Measurable r) :
    klDiv ((μ.prod (multivariateGaussian 0 S)).map (fun p => (r p.1, u p.1+p.2)))
      ((μ.prod (multivariateGaussian 0 S)).map (fun p => (r p.1, v p.1+p.2))) ≤
      ∫⁻ a, ENNReal.ofReal (((u a-v a) ⬝ᵥ S⁻¹ *ᵥ (u a-v a)) / 2) ∂μ := by
  rw [prod_multivariateGaussian_map_add_retained μ n S u hu r hr,
    prod_multivariateGaussian_map_add_retained μ n S v hv r hr]
  have h := gaussian_reverse_transport_retained μ n (covarianceSqrtEquiv n S hS)
    u v hu hv r hr
  simpa only [covarianceSqrtEquiv_apply, covarianceSqrtEquiv_symm_norm_sq,
    WithLp.ofLp_sub] using h

end AcceleratedLogConcave.Channels

namespace AcceleratedLogConcave.Channels
open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator

/-- Original-space retained-law form. Noise is independent of the whole coupling state `X`. -/
theorem gaussian_reverse_transport_independent_retained
    {Ω α R : Type*} [MeasurableSpace Ω] [MeasurableSpace α] [MeasurableSpace R]
    (P : Measure Ω) [IsProbabilityMeasure P] (n : ℕ)
    (S : Matrix (Fin n) (Fin n) ℝ) (hS : S.PosDef)
    (X : Ω → α) (hX : Measurable X)
    (G : Ω → EuclideanSpace ℝ (Fin n)) (hG : Measurable G)
    (hGlaw : P.map G = multivariateGaussian 0 S) (hind : IndepFun X G P)
    (u v : α → EuclideanSpace ℝ (Fin n)) (hu : Measurable u) (hv : Measurable v)
    (r : α → R) (hr : Measurable r) :
    klDiv (P.map (fun ω => (r (X ω), u (X ω)+G ω)))
      (P.map (fun ω => (r (X ω), v (X ω)+G ω))) ≤
      ∫⁻ ω, ENNReal.ofReal (((u (X ω)-v (X ω)) ⬝ᵥ S⁻¹ *ᵥ (u (X ω)-v (X ω))) / 2) ∂P := by
  have h := gaussian_reverse_transport_covariance_retained
    (P.map X) n S hS u v hu hv r hr
  rw [← hGlaw, ← hind.map_prod_eq_prod_map_map hX.aemeasurable hG.aemeasurable,
    Measure.map_map (by fun_prop) (hX.prodMk hG),
    Measure.map_map (by fun_prop) (hX.prodMk hG), lintegral_map (by fun_prop) hX] at h
  exact h

end AcceleratedLogConcave.Channels

namespace AcceleratedLogConcave.Channels
open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator

/-- The manuscript's reverse-transport inequality, in exact-to-implemented orientation. -/
theorem gaussian_reverse_transport_independent
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (n : ℕ)
    (S : Matrix (Fin n) (Fin n) ℝ) (hS : S.PosDef)
    (U V G : Ω → EuclideanSpace ℝ (Fin n))
    (hU : Measurable U) (hV : Measurable V) (hG : Measurable G)
    (hGlaw : P.map G = multivariateGaussian 0 S)
    (hind : IndepFun (fun ω => (U ω,V ω)) G P) :
    klDiv (P.map (fun ω => U ω+G ω)) (P.map (fun ω => V ω+G ω)) ≤
      ∫⁻ ω, ENNReal.ofReal (((U ω-V ω) ⬝ᵥ S⁻¹ *ᵥ (U ω-V ω)) / 2) ∂P := by
  have h := gaussian_reverse_transport_independent_retained P n S hS
    (fun ω => (U ω,V ω)) (hU.prodMk hV) G hG hGlaw hind
    Prod.fst Prod.snd measurable_fst measurable_snd (fun _ => ()) measurable_const
  have hm := klDiv_map_le
    (P.map (fun ω => ((), U ω+G ω))) (P.map (fun ω => ((), V ω+G ω))) measurable_snd
  rw [Measure.map_map measurable_snd (by fun_prop),
    Measure.map_map measurable_snd (by fun_prop)] at hm
  exact hm.trans h

/-- Conditional reverse transport, at every supplied conditional coupling, with covariance Σ. -/
theorem gaussian_reverse_transport_covariance_conditional
    {I α : Type*} [MeasurableSpace I] [MeasurableSpace α]
    (κ : Kernel I α) [IsMarkovKernel κ] (n : ℕ)
    (S : Matrix (Fin n) (Fin n) ℝ) (hS : S.PosDef)
    (u v : I × α → EuclideanSpace ℝ (Fin n)) (hu : Measurable u) (hv : Measurable v) :
    ∀ i, klDiv (((κ i).prod (multivariateGaussian 0 S)).map (fun p => u (i,p.1)+p.2))
      (((κ i).prod (multivariateGaussian 0 S)).map (fun p => v (i,p.1)+p.2)) ≤
      ∫⁻ a, ENNReal.ofReal (((u (i,a)-v (i,a)) ⬝ᵥ S⁻¹ *ᵥ (u (i,a)-v (i,a))) / 2) ∂κ i := by
  intro i
  have h := gaussian_reverse_transport_covariance_retained (κ i) n S hS
    (fun a => u (i,a)) (fun a => v (i,a))
    (hu.comp measurable_prodMk_left) (hv.comp measurable_prodMk_left)
    (fun _ => ()) measurable_const
  have hm := klDiv_map_le
    (((κ i).prod (multivariateGaussian 0 S)).map (fun p => ((), u (i,p.1)+p.2)))
    (((κ i).prod (multivariateGaussian 0 S)).map (fun p => ((), v (i,p.1)+p.2))) measurable_snd
  rw [Measure.map_map measurable_snd (by fun_prop),
    Measure.map_map measurable_snd (by fun_prop)] at hm
  exact hm.trans h

end AcceleratedLogConcave.Channels
