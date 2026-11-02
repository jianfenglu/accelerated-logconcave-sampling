import AcceleratedLogConcave.External.OAI.BackwardTest
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

/-! Actual backward tests for the reference ODE: joint C1 regularity and common
compact support, used to test the density continuity equation. -/
noncomputable section
open Set Function Filter Metric
open scoped Topology NNReal

namespace OAI.LogConcaveSampling.GlobalODE
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [ProperSpace E] {a b : ℝ} (hab : a ≤ b)
  {f : ℝ → E → E} (hc : Continuous (uncurry f))
  {K : ℝ≥0} (hL : ∀ t ∈ Icc a b, LipschitzWith K (f t))
  {D : ℝ → E → E →L[ℝ] E} (hD : Continuous (uncurry D))
  (hf : ∀ t z, HasFDerivAt (f t) (D t z) z)

omit [ProperSpace E] in
/-- Uniform time control of the actual spatial linearization. -/
theorem flowLinearization_time_lipschitz (x : E) :
    LipschitzWith ⟨(K : ℝ) * Real.exp ((K : ℝ) * (b-a)),
      mul_nonneg K.coe_nonneg (Real.exp_pos _).le⟩
      (fun t : Icc a b => flowLinearization hab hc hL hD hf x t) := by
  apply LipschitzOnWith.to_restrict
  apply (convex_Icc a b).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
    (fun t ht => fundamental_deriv ⟨a, le_rfl, hab⟩
      (flowSpatialCoefficient_continuous hab hc hL hD x)
      (flowSpatialCoefficient_bound hab hc hL hf x) t ht)
  intro t ht
  change ‖_‖ ≤ (K : ℝ) * Real.exp ((K : ℝ) * (b-a))
  apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
  apply mul_le_mul
    (flowSpatialCoefficient_bound hab hc hL hf x t ht)
  · apply (fundamental_norm_bound ⟨a, le_rfl, hab⟩
      (flowSpatialCoefficient_continuous hab hc hL hD x)
      (flowSpatialCoefficient_bound hab hc hL hf x) ⟨t, ht⟩).trans
    apply Real.exp_le_exp.mpr
    apply mul_le_mul_of_nonneg_left _ K.coe_nonneg
    rw [abs_of_nonneg (sub_nonneg.mpr ht.1)]
    linarith [ht.2]
  · exact norm_nonneg _
  · exact K.coe_nonneg

omit [ProperSpace E] in
/-- Joint continuity, needed for C1 backward tests rather than only pointwise derivatives. -/
theorem flowLinearization_joint_continuous :
    Continuous (fun p : E × Icc a b => flowLinearization hab hc hL hD hf p.1 p.2) :=
  continuous_prod_of_continuous_lipschitzWith' _ _
    (flowLinearization_time_lipschitz hab hc hL hD hf)
    (flowLinearization_continuous_initial hab hc hL hD hf)

include hD hf

/-- The space-time flow is C1 at interior times under precisely the spatial C1 assumptions. -/
theorem spaceTimeForward_contDiffAt_one (p : ℝ × E) (hp : p.1 ∈ Ioo a b) :
    ContDiffAt ℝ 1 (spaceTimeForward hab hc hL) p := by
  let J (q : ℝ × E) := flowLinearization hab hc hL hD hf q.2
    (projIcc a b hab q.1)
  have hJ : Continuous J := (flowLinearization_joint_continuous hab hc hL hD hf).comp
    (continuous_snd.prodMk ((continuous_projIcc (h := hab)).comp continuous_fst))
  let v (q : ℝ × E) := f q.1 (spaceTimeForward hab hc hL q).2
  have hv : Continuous v := hc.comp
    (continuous_fst.prodMk (spaceTimeForward_continuous hab hc hL).snd)
  let A (q : ℝ × E) : (ℝ × E) →L[ℝ] (ℝ × E) :=
    (ContinuousLinearMap.fst ℝ ℝ E).prod
      (((ContinuousLinearMap.fst ℝ ℝ E).smulRight (v q)) +
        (J q).comp (ContinuousLinearMap.snd ℝ ℝ E))
  have hA : Continuous A := (ContinuousLinearMap.prodL ℝ).continuous.comp
    (continuous_const.prodMk (((ContinuousLinearMap.smulRightL ℝ (ℝ × E) E (ContinuousLinearMap.fst ℝ ℝ E)).continuous.comp hv).add (hJ.clm_comp continuous_const)))
  apply contDiffAt_one_iff.mpr
  refine ⟨A, Ioo a b ×ˢ univ, (isOpen_Ioo.prod isOpen_univ).mem_nhds ⟨hp, mem_univ _⟩,
    hA.continuousOn, ?_⟩
  intro q hq
  have hh := spaceTimeForward_hasFDerivAt hab hc hL hD hf q hq.1
  have he : A q = (triangularEquiv (f q.1 (spaceTimeForward hab hc hL q).2)
      (fundamentalEquiv (flowSpatialCoefficient_continuous hab hc hL hD q.2)
        (flowSpatialCoefficient_bound hab hc hL hf q.2) ⟨a, le_rfl, hab⟩
          ⟨q.1, hq.1.1.le, hq.1.2.le⟩) : (ℝ × E) →L[ℝ] (ℝ × E)) := by
    apply ContinuousLinearMap.ext
    intro w
    change (w.1, w.1 • v q + J q w.2) = _
    dsimp [J]
    rw [projIcc_of_mem _ ⟨hq.1.1.le, hq.1.2.le⟩]
    rfl
  rw [he]
  exact hh

/-- The inverse space-time flow is genuinely C1 at interior times. -/
theorem spaceTimeBackward_contDiffAt_one (p : ℝ × E) (hp : p.1 ∈ Ioo a b) :
    ContDiffAt ℝ 1 (spaceTimeBackward hab hc hL) p := by
  let H := spaceTimeHomeomorph hab hc hL
  exact H.toOpenPartialHomeomorph.contDiffAt_symm (mem_univ p)
    (spaceTimeForward_hasFDerivAt hab hc hL hD hf (H.symm p) hp)
    (spaceTimeForward_contDiffAt_one hab hc hL hD hf (H.symm p) hp)

/-- Compact C1 terminal tests stay C1 under backward transport. -/
theorem backwardTest_contDiffAt_one (T : Icc a b) {φ : E → ℝ}
    (hφ : ContDiff ℝ 1 φ) (p : ℝ × E) (hp : p.1 ∈ Ioo a b) :
    ContDiffAt ℝ 1 (backwardTest hab hc hL T φ) p :=
  hφ.contDiffAt.comp p ((flow_contDiff_one_left hab hc hL hD hf T).contDiffAt.comp p
    (spaceTimeBackward_contDiffAt_one hab hc hL hD hf p hp).snd)

omit hD hf [ProperSpace E] in
/-- One compact spatial set supports every backward test on the whole time interval. -/
theorem backwardTest_common_compact_support (T : Icc a b) {φ : E → ℝ}
    (hφ : HasCompactSupport φ) :
    ∃ S : Set E, IsCompact S ∧ ∀ t x, x ∉ S → backwardTest hab hc hL T φ (t,x) = 0 := by
  let S := (fun q : E × Icc a b => flow hL hc T q.1 q.2) ''
    (tsupport φ ×ˢ (univ : Set (Icc a b)))
  refine ⟨S, (hφ.prod isCompact_univ).image (flow_joint_continuous hL hc T), ?_⟩
  intro t x hx
  by_contra hne
  apply hx
  rw [backwardTest_eq] at hne
  refine ⟨(flow hL hc (projIcc a b hab t) x T, projIcc a b hab t),
    ⟨subset_tsupport φ hne, mem_univ _⟩, ?_⟩
  exact (flow_cocycle hL hc (projIcc a b hab t) T (projIcc a b hab t) x).trans
    (flow_initial hL hc (projIcc a b hab t) x)

omit hD hf [ProperSpace E] in
/-- Restricting the construction interval does not change the actual trajectory.
This uniqueness argument follows openai/math SmoothFlowJoint.flow_restrict at
revision 1581d4cbdd69a0faf34b2089614fe2a814316a6a (Apache-2.0). -/
theorem flow_eq_on_subinterval {c d : ℝ} (hsub : Icc c d ⊆ Icc a b)
    (s t : Icc c d) (x : E) :
    flow (fun r hr => hL r (hsub hr)) hc s x t =
      flow hL hc ⟨s, hsub s.2⟩ x t := by
  have hh := trajectory_dist (fun r hr => hL r (hsub hr))
    (flow_continuous (fun r hr => hL r (hsub hr)) hc s x).continuousOn
    (flow_deriv (fun r hr => hL r (hsub hr)) hc s x)
    (flow_continuous hL hc ⟨s, hsub s.2⟩ x).continuousOn
    (fun r hr => (flow_deriv hL hc ⟨s, hsub s.2⟩ x r (hsub hr)).mono hsub) s t
  simpa only [flow_initial, dist_self, zero_mul, dist_le_zero] using hh

end OAI.LogConcaveSampling.GlobalODE
