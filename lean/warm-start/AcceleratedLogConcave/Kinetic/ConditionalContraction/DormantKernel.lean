import AcceleratedLogConcave.Kinetic.ReferenceChannel
import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Actual conditional dormant collisions

The retained state can include both position and the Hamiltonian velocity.
Only the conditional dormant coordinate is resampled. Its Gaussian stationarity
is expressed at the level of the kernel; L2 contraction and macro preservation
are conclusions of the joint-law construction.
-/
noncomputable section
open MeasureTheory ProbabilityTheory InnerProductSpace
open scoped RealInnerProductSpace
namespace AcceleratedLogConcave.Kinetic.ConditionalContraction
variable {X H : Type*} [MeasurableSpace X] [MeasurableSpace H]
variable (μ : Measure X) (γ : Measure H) [IsProbabilityMeasure μ] [IsProbabilityMeasure γ]
variable (κ : Kernel (X × H) H) [IsMarkovKernel κ]

/-- Actual old-state/new-dormant-coordinate coupling. -/
def dormantJoint : Measure ((X × H) × H) := (μ.prod γ) ⊗ₘ κ

instance dormantJoint_probability : IsProbabilityMeasure (dormantJoint μ γ κ) := by
  unfold dormantJoint
  infer_instance

/-- The collision retains the first coordinate and substitutes the sampled dormant one. -/
def dormantNewState (ω : (X × H) × H) : X × H := (ω.1.1, ω.2)

theorem dormantOld_preserving :
    MeasurePreserving Prod.fst (dormantJoint μ γ κ) (μ.prod γ) := by
  refine ⟨measurable_fst, ?_⟩
  exact Measure.fst_compProd (μ.prod γ) κ

/-- Conditional stationarity is the genuine kernel input, before any operator is built. -/
def ConditionallyInvariant : Prop :=
  ∀ x s, MeasurableSet s → (∫⁻ h, κ (x, h) s ∂γ) = γ s

/-- Conditional stationarity gives the actual new-state marginal. -/
theorem dormantNew_preserving (hκ : ConditionallyInvariant γ κ) :
    MeasurePreserving dormantNewState (dormantJoint μ γ κ) (μ.prod γ) := by
  classical
  refine ⟨by unfold dormantNewState; fun_prop, ?_⟩
  apply Measure.ext_prod
  intro s t hs ht
  rw [Measure.map_apply (by unfold dormantNewState; fun_prop) (hs.prod ht),
    dormantJoint, Measure.compProd_apply ((hs.prod ht).preimage (by unfold dormantNewState; fun_prop))]
  have hsection (z : X × H) :
      Prod.mk z ⁻¹' (dormantNewState ⁻¹' (s ×ˢ t)) = if z.1 ∈ s then t else ∅ := by
    ext h
    simp only [Set.mem_preimage, dormantNewState, Set.mem_prod]
    split_ifs <;> simp_all
  simp_rw [hsection]
  have hfun : (fun z : X × H => κ z (if z.1 ∈ s then t else ∅)) =
      (fun z => if z.1 ∈ s then κ z t else 0) := by
    funext z
    split_ifs <;> simp
  rw [hfun, lintegral_prod _ ((Kernel.measurable_coe κ ht).ite
    (hs.preimage measurable_fst) measurable_const).aemeasurable]
  have hinner (x : X) : (∫⁻ h, (if x ∈ s then κ (x, h) t else 0) ∂γ) =
      if x ∈ s then γ t else 0 := by
    split_ifs with hx
    · exact hκ x t ht
    · simp
  simp_rw [hinner]
  change (∫⁻ x, s.indicator (fun _ => γ t) x ∂μ) = _
  rw [lintegral_indicator_const hs, Measure.prod_prod]
  exact mul_comm _ _

/-- The conditional test operator, derived from the actual joint law. -/
def dormantChannel (hκ : ConditionallyInvariant γ κ) :
    Lp ℝ 2 (μ.prod γ) →L[ℝ] Lp ℝ 2 (μ.prod γ) :=
  referenceChannel (dormantOld_preserving μ γ κ) (dormantNew_preserving μ γ κ hκ)

theorem dormantChannel_norm_le (hκ : ConditionallyInvariant γ κ) :
    ‖dormantChannel μ γ κ hκ‖ ≤ 1 :=
  referenceChannel_norm_le _ _

theorem dormantChannel_adjoint_norm_le (hκ : ConditionallyInvariant γ κ) :
    ‖(dormantChannel μ γ κ hκ).adjoint‖ ≤ 1 := by
  rw [ContinuousLinearMap.adjoint.norm_map]
  exact dormantChannel_norm_le μ γ κ hκ

/-- Embed functions of the retained coordinates. -/
def dormantBaseEmbedding : Lp ℝ 2 μ →ₗᵢ[ℝ] Lp ℝ 2 (μ.prod γ) :=
  Lp.compMeasurePreservingₗᵢ ℝ Prod.fst measurePreserving_fst

private theorem retained_pullbacks_eq (hκ : ConditionallyInvariant γ κ) (g : Lp ℝ 2 μ) :
    Lp.compMeasurePreservingₗᵢ ℝ dormantNewState (dormantNew_preserving μ γ κ hκ)
      (dormantBaseEmbedding μ γ g) =
    Lp.compMeasurePreservingₗᵢ ℝ Prod.fst (dormantOld_preserving μ γ κ)
      (dormantBaseEmbedding μ γ g) := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_compMeasurePreserving (dormantBaseEmbedding μ γ g)
      (dormantNew_preserving μ γ κ hκ),
    Lp.coeFn_compMeasurePreserving (dormantBaseEmbedding μ γ g)
      (dormantOld_preserving μ γ κ),
    (dormantNew_preserving μ γ κ hκ).quasiMeasurePreserving.ae
      (Lp.coeFn_compMeasurePreserving g (measurePreserving_fst (ν := γ))),
    (dormantOld_preserving μ γ κ).quasiMeasurePreserving.ae
      (Lp.coeFn_compMeasurePreserving g (measurePreserving_fst (ν := γ)))] with ω hn ho hgn hgo
  change Lp.compMeasurePreserving dormantNewState _ (dormantBaseEmbedding μ γ g) ω =
    Lp.compMeasurePreserving Prod.fst _ (dormantBaseEmbedding μ γ g) ω
  rw [hn, ho]
  change Lp.compMeasurePreserving Prod.fst measurePreserving_fst g (dormantNewState ω) =
    Lp.compMeasurePreserving Prod.fst measurePreserving_fst g ω.1
  rw [hgn, hgo]
  rfl

/-- Test functions of the retained state are fixed by the actual channel. -/
theorem dormantChannel_base (hκ : ConditionallyInvariant γ κ) (g : Lp ℝ 2 μ) :
    dormantChannel μ γ κ hκ (dormantBaseEmbedding μ γ g) = dormantBaseEmbedding μ γ g := by
  unfold dormantChannel referenceChannel
  rw [ContinuousLinearMap.comp_apply]
  change (Lp.compMeasurePreservingₗᵢ ℝ Prod.fst (dormantOld_preserving μ γ κ)).toContinuousLinearMap.adjoint
    (Lp.compMeasurePreservingₗᵢ ℝ dormantNewState (dormantNew_preserving μ γ κ hκ)
      (dormantBaseEmbedding μ γ g)) = _
  rw [retained_pullbacks_eq μ γ κ hκ g]
  apply ext_inner_left ℝ
  intro r
  rw [ContinuousLinearMap.adjoint_inner_right]
  exact (Lp.compMeasurePreservingₗᵢ ℝ Prod.fst
    (dormantOld_preserving μ γ κ)).inner_map_map r (dormantBaseEmbedding μ γ g)

/-- The density adjoint also fixes all retained-state functions. -/
theorem dormantChannel_adjoint_base (hκ : ConditionallyInvariant γ κ) (g : Lp ℝ 2 μ) :
    (dormantChannel μ γ κ hκ).adjoint (dormantBaseEmbedding μ γ g) =
      dormantBaseEmbedding μ γ g := by
  rw [dormantChannel, referenceChannel_adjoint]
  unfold referenceChannel
  rw [ContinuousLinearMap.comp_apply]
  change (Lp.compMeasurePreservingₗᵢ ℝ dormantNewState
      (dormantNew_preserving μ γ κ hκ)).toContinuousLinearMap.adjoint
    (Lp.compMeasurePreservingₗᵢ ℝ Prod.fst (dormantOld_preserving μ γ κ)
      (dormantBaseEmbedding μ γ g)) = _
  rw [← retained_pullbacks_eq μ γ κ hκ g]
  apply ext_inner_left ℝ
  intro r
  rw [ContinuousLinearMap.adjoint_inner_right]
  exact (Lp.compMeasurePreservingₗᵢ ℝ dormantNewState
    (dormantNew_preserving μ γ κ hκ)).inner_map_map r (dormantBaseEmbedding μ γ g)

/-- Averaging out the dormant coordinate is unchanged by the density adjoint. -/
theorem dormantChannel_adjoint_average (hκ : ConditionallyInvariant γ κ)
    (f : Lp ℝ 2 (μ.prod γ)) :
    (dormantBaseEmbedding μ γ).toContinuousLinearMap.adjoint
      ((dormantChannel μ γ κ hκ).adjoint f) =
    (dormantBaseEmbedding μ γ).toContinuousLinearMap.adjoint f := by
  apply ext_inner_left ℝ
  intro g
  rw [ContinuousLinearMap.adjoint_inner_right, ContinuousLinearMap.adjoint_inner_right,
    ContinuousLinearMap.adjoint_inner_right]
  change inner ℝ (dormantChannel μ γ κ hκ (dormantBaseEmbedding μ γ g)) f = _
  rw [dormantChannel_base]
  rfl

/-- The ordinary L2 loss of the actual density channel is nonnegative. -/
theorem dormantChannel_loss_nonneg (hκ : ConditionallyInvariant γ κ)
    (f : Lp ℝ 2 (μ.prod γ)) :
    0 ≤ ‖f‖ ^ 2 - ‖(dormantChannel μ γ κ hκ).adjoint f‖ ^ 2 := by
  have h := (dormantChannel μ γ κ hκ).adjoint.le_opNorm f
  have hn := dormantChannel_adjoint_norm_le μ γ κ hκ
  have hle : ‖(dormantChannel μ γ κ hκ).adjoint f‖ ≤ ‖f‖ :=
    h.trans ((mul_le_mul_of_nonneg_right hn (norm_nonneg f)).trans_eq (one_mul _))
  nlinarith [norm_nonneg ((dormantChannel μ γ κ hκ).adjoint f), norm_nonneg f]

end AcceleratedLogConcave.Kinetic.ConditionalContraction
