import AcceleratedLogConcave.Tensor.ActualFlowCoefficientVolterra
import AcceleratedLogConcave.Tensor.FixedCutComparison

/-!

-/
noncomputable section
set_option autoImplicit false
open Set Metric Filter MeasureTheory
open scoped ContDiff BigOperators
namespace AcceleratedLogConcave.Tensor.ActualCoefficient
open Conditional Conditional.Transport.SpatialFlow
open AcceleratedLogConcave.Analysis.SpatialVariation
variable {D n : ℕ}

/-- Euclidean packing, with no norm estimate asserted or used. -/
def packCLM (I : Type*) [Fintype I] : (I → ℝ) →L[ℝ] EuclideanSpace ℝ I :=
  (show (I → ℝ) →ₗ[ℝ] EuclideanSpace ℝ I from
    { toFun := WithLp.toLp 2
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }).toContinuousLinearMap

def coordinateCLM {I : Type*} [Fintype I] (i : I) :
    EuclideanSpace ℝ I →L[ℝ] ℝ :=
  (show EuclideanSpace ℝ I →ₗ[ℝ] ℝ from
    { toFun := fun v => v i
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }).toContinuousLinearMap

/-- The exact pinned Bochner API has integral-on-left orientation. -/
theorem coefficient_integral_apply {I : Type*} [Fintype I]
    {Q : ℝ → EuclideanSpace ℝ I} (hQ : Continuous Q) (i : I) (a b : ℝ) :
    (∫ s in a..b, Q s) i = ∫ s in a..b, Q s i :=
  ((coordinateCLM i).intervalIntegral_comp_comm (hQ.intervalIntegrable a b)).symm

/-- Smooth jointly in time and the spatial center before taking a fixed slice. -/
def representativeJointCoeff (C : ℝ × Space D → Space D) (n : ℕ) :
    ℝ × Space D → Coeff (Fin n ⊕ Unit) D :=
  fun p => packCLM _ (fun a => inner ℝ (basis D (a (.inr ())))
    (jointAlong (List.ofFn (fun j : Fin n => basis D (a (.inl j))))
      (fun q => fderiv ℝ C q (1,0)) p))

theorem continuous_representativeJointCoeff {C : ℝ × Space D → Space D}
    (hC : ContDiff ℝ ∞ C) (n : ℕ) : Continuous (representativeJointCoeff C n) := by
  have hD : ContDiff ℝ ∞ (fun p : ℝ × Space D => fderiv ℝ C p (1,0)) :=
    (hC.fderiv_right (by simp)).clm_apply contDiff_const
  apply (packCLM _).continuous.comp
  apply continuous_pi
  intro a
  exact (innerSL ℝ (basis D (a (.inr ())))).continuous.comp
    (contDiff_jointAlong _ hD).continuous

abbrev actualJetCoeff (d : PositiveVarianceFlowData (Space D)) (n : ℕ)
    (y : Space D) (s : ℝ) := vectorCoeff (iteratedFDeriv ℝ n (actualY d s) y)

abbrev actualRHSCoeff (d : PositiveVarianceFlowData (Space D)) (n : ℕ)
    (y : Space D) (s : ℝ) := vectorCoeff (iteratedFDeriv ℝ n
      (fun z => probabilityVelocity d.F d.x d.r s (actualY d s z)) y)

/-- Actual RHS identification comes from the zeroth ODE and local equality,
not from any higher-variation equation or a target jet bound. -/
theorem representativeJointCoeff_eq_actual
    (d : PositiveVarianceFlowData (Space D)) (hsmall : d.r^2*d.ell ≤ 1/2)
    {C : ℝ × Space D → Space D} (hC : ContDiff ℝ ∞ C) (y : Space D)
    (hCY : ∀ s ∈ Icc 0 d.b, ∀ z ∈ ball y 1, C (s,z) = actualY d s z)
    (hb : 0 < d.b) (n : ℕ) {s : ℝ} (hs : s ∈ Icc 0 d.b) :
    representativeJointCoeff C n (s,y) = actualRHSCoeff d n y s := by
  have hD : ContDiff ℝ ∞ (fun p : ℝ × Space D => fderiv ℝ C p (1,0)) :=
    (hC.fderiv_right (by simp)).clm_apply contDiff_const
  have hR := (contDiff_probabilityVelocity_spatial d.hF d.hlo d.hhi d.x
    (r := d.r) (by linarith [hs.1]) (hs.2.trans_lt d.hb1)).comp
    (contDiff_backward_spatial d.hF d.hell d.hlo d.hhi d.x
      d.hr d.hb0 d.hb1 hsmall hs)
  ext a
  change inner ℝ (basis D (a (.inr ()))) (jointAlong _ _ (s,y)) = _
  rw [congrFun (jointAlong_slice _ hD s) y]
  have he : along (List.ofFn (fun j : Fin n => basis D (a (.inl j))))
      (fun z => fderiv ℝ C (s,z) (1,0)) y =
      along (List.ofFn (fun j : Fin n => basis D (a (.inl j))))
      (fun z => probabilityVelocity d.F d.x d.r s (actualY d s z)) y := by
    apply (along_eventuallyEq (J := _) ?_).eq_of_nhds
    filter_upwards [Metric.ball_mem_nhds y (by norm_num : (0:ℝ) < 1)] with z hz
    exact representative_time_eq hb hC y hCY
      (fun u hu w _ => backward_hasDerivWithinAt d.hF d.hell d.hlo d.hhi d.x
        d.hr d.hb0 d.hb1 hu w) hs hz
  rw [he]
  exact congrArg (fun v => inner ℝ (basis D (a (.inr ()))) v)
    (along_ofFn_eq_iteratedFDeriv hR n (fun j => basis D (a (.inl j))) y)

/-- Supplier 1: original data produce a continuous coefficient-valued actual RHS
representative and the literal coefficient Volterra equality. The singleton slab
uses a constant actual RHS, so derivative uniqueness is never invoked at b=0. -/
theorem exists_actual_coefficient_volterra
    (d : PositiveVarianceFlowData (Space D)) (hsmall : d.r^2*d.ell ≤ 1/2)
    (n : ℕ) (y : Space D) :
    ∃ Q : ℝ → Coeff (Fin n ⊕ Unit) D, Continuous Q ∧
      (∀ s ∈ Icc 0 d.b, Q s = actualRHSCoeff d n y s) ∧
      (∀ t ∈ Icc 0 d.b, actualJetCoeff d n y t = actualJetCoeff d n y d.b -
        ∫ s in t..d.b, Q s) := by
  by_cases hb : 0 < d.b
  · obtain ⟨C,hC,hCY⟩ := exists_smooth_backward_representative
      d.hF d.hell d.hlo d.hhi d.x d.hr d.hb0 d.hb1 hsmall y
    let Q : ℝ → Coeff (Fin n ⊕ Unit) D := fun s => representativeJointCoeff C n (s,y)
    have hQ : Continuous Q := (continuous_representativeJointCoeff hC n).comp
      (continuous_id.prodMk continuous_const)
    have he : ∀ s ∈ Icc 0 d.b, Q s = actualRHSCoeff d n y s :=
      fun s hs => representativeJointCoeff_eq_actual d hsmall hC y hCY hb n hs
    refine ⟨Q,hQ,he,?_⟩
    intro t ht
    ext a
    change inner ℝ (basis D (a (.inr ())))
      (iteratedFDeriv ℝ n (actualY d t) y (fun j => basis D (a (.inl j)))) =
      inner ℝ (basis D (a (.inr ())))
      (iteratedFDeriv ℝ n (actualY d d.b) y (fun j => basis D (a (.inl j)))) -
      (∫ s in t..d.b, Q s) a
    have hterminal : (actualY d d.b : Space D → Space D) = id := by
      funext z
      exact backward_spatial_terminal d.hF d.hell d.hlo d.hhi d.x
        d.hr d.hb0 d.hb1 ([] : List (Space D)) z
    rw [coefficient_integral_apply hQ, hterminal]
    have hv := actual_iteratedFDeriv_volterra_readout d hsmall n
      (fun j => basis D (a (.inl j))) y (innerSL ℝ (basis D (a (.inr ())))) ht
    change inner ℝ (basis D (a (.inr ()))) _ =
      inner ℝ (basis D (a (.inr ()))) _ - _ at hv
    rw [hv]
    congr 1
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le ht.2] at hs
    exact (congrArg (fun T : Coeff (Fin n ⊕ Unit) D => T a)
      (he s ⟨ht.1.trans hs.1,hs.2⟩)).symm
  · have hb0 : d.b = 0 := le_antisymm (not_lt.mp hb) d.hb0
    refine ⟨fun _ => actualRHSCoeff d n y 0,continuous_const,?_,?_⟩
    · intro s hs
      have hs0 : s = 0 := le_antisymm (hs.2.trans_eq hb0) hs.1
      subst s
      rfl
    · intro t ht
      have ht0 : t = d.b := by rw [hb0] at *; exact le_antisymm ht.2 ht.1
      subst t
      simp only [intervalIntegral.integral_same,sub_zero]

/-- The actual-data bridge into the pre-existing fixed-cut comparison engine.
Only the quantitative RHS/terminal inputs remain; the Volterra and continuity
inputs are now discharged rather than repeated as hypotheses. -/
theorem actual_fixed_cut_bound
    (d : PositiveVarianceFlowData (Space D)) (hsmall : d.r^2*d.ell ≤ 1/2)
    (n : ℕ) (y : Space D) (S : Finset (Fin n ⊕ Unit))
    {α δ : ℝ} {f : ℝ → ℝ} (hα : 0 ≤ α) (hf : Continuous f)
    (hb : splitNorm D S (actualJetCoeff d n y d.b) ≤ δ)
    (hbound : ∀ s ∈ Icc 0 d.b, splitNorm D S (actualRHSCoeff d n y s) ≤
      α*s*splitNorm D S (actualJetCoeff d n y s) + f s)
    {t : ℝ} (ht : t ∈ Icc 0 d.b) :
    splitNorm D S (actualJetCoeff d n y t) ≤
      AcceleratedLogConcave.Analysis.FixedCut.envelope α d.b δ f t := by
  obtain ⟨Q,hQ,he,hvol⟩ := exists_actual_coefficient_volterra d hsmall n y
  exact FixedCut.fixed_cut_volterra_bound S hα hf hQ hvol hb
    (fun s hs => by rw [he s hs]; exact hbound s hs) ht
end AcceleratedLogConcave.Tensor.ActualCoefficient
