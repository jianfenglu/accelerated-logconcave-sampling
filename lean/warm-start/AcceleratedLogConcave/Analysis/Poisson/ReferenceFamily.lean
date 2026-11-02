import AcceleratedLogConcave.Analysis.Poisson.ReferenceTransportLaw
import AcceleratedLogConcave.Analysis.Poisson.ReferenceFlow

/-! The actual gradient reference flow, its proved density transport, and its
scalar/vector unitary pullbacks. No measure-preserving map is supplied as data. -/
noncomputable section
open MeasureTheory Set Function InnerProductSpace
open scoped Topology NNReal
namespace AcceleratedLogConcave.Analysis.Poisson
open OAI.LogConcaveSampling.GlobalODE
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable (U : ℝ → E → ℝ) (c : ℝ → ℝ) {a b : ℝ} (hab : a ≤ b)
  (hU : ∀ t, ContDiff ℝ 2 (U t))
  (hG : Continuous (uncurry (fun t => gradient (U t))))
  (hH : Continuous (uncurry (fun t => hessianOperator (U t))))
  (hc : Continuous c) (C : ℝ≥0)
  (hC : ∀ t ∈ Icc a b, |c t| ≤ C)
  (hlo : ∀ t ∈ Icc a b, ∀ x v, 0 ≤ fderiv ℝ (fderiv ℝ (U t)) x v v)
  (hup : ∀ t ∈ Icc a b, ∀ x v, fderiv ℝ (fderiv ℝ (U t)) x v v ≤ ‖v‖ ^ 2)

include hab hH in
omit [MeasurableSpace E] [BorelSpace E] in
/-- Spatial C1 regularity of the genuine gradient flow. -/
theorem referenceFlowHomeomorph_contDiff (s t : Icc a b) :
    ContDiff ℝ 1 (referenceFlowHomeomorph U c (fun t _ => hU t) hG hc C hC hlo hup s t) :=
  flow_contDiff_one (D := fun t x => (-c t) • hessianOperator (U t) x) hab (referenceDrift_continuous U c hG hc)
    (fun t ht => referenceDrift_lipschitz U c t (hU t) (hlo t ht) (hup t ht) C (hC t ht))
    ((hc.comp continuous_fst).neg.smul hH)
    (fun t x => referenceDrift_hasFDerivAt U c t x (hU t)) s t

include hab hH in
omit [MeasurableSpace E] [BorelSpace E] in
/-- Spatial C1 regularity of the genuine inverse flow. -/
theorem referenceFlowHomeomorph_symm_contDiff (s t : Icc a b) :
    ContDiff ℝ 1 (referenceFlowHomeomorph U c (fun t _ => hU t) hG hc C hC hlo hup s t).symm :=
  referenceFlowHomeomorph_contDiff U c hab hU hG hH hc C hC hlo hup t s

omit [MeasurableSpace E] [BorelSpace E] in
/-- Uniform spatial derivative control on the fixed compact time interval. -/
theorem referenceFlowHomeomorph_fderiv_bound (s t : Icc a b) (x : E) :
    ‖fderiv ℝ (referenceFlowHomeomorph U c (fun t _ => hU t) hG hc C hC hlo hup s t) x‖ ≤
      Real.exp ((C : ℝ) * (b - a)) := by
  apply (norm_fderiv_le_of_lipschitz ℝ (flow_lipschitz
    (fun t ht => referenceDrift_lipschitz U c t (hU t) (hlo t ht) (hup t ht) C (hC t ht))
    (referenceDrift_continuous U c hG hc) s t)).trans
  apply Real.exp_le_exp.mpr
  apply mul_le_mul_of_nonneg_left _ C.coe_nonneg
  rw [abs_le]
  constructor <;> linarith [s.2.1, s.2.2, t.2.1, t.2.2]

omit [MeasurableSpace E] [BorelSpace E] in
/-- The same uniform bound applies to the actual inverse derivative. -/
theorem referenceFlowHomeomorph_symm_fderiv_bound (s t : Icc a b) (x : E) :
    ‖fderiv ℝ (referenceFlowHomeomorph U c (fun t _ => hU t) hG hc C hC hlo hup s t).symm x‖ ≤
      Real.exp ((C : ℝ) * (b - a)) :=
  referenceFlowHomeomorph_fderiv_bound U c hU hG hc C hC hlo hup t s x

variable (ρ ρt : ℝ → E → ℝ)
  (hρ : ContinuousOn (uncurry ρ) (Icc a b ×ˢ (univ : Set E)))
  (hρt : ContinuousOn (uncurry ρt) (Ioo a b ×ˢ (univ : Set E)))
  (hdρ : ∀ t ∈ Ioo a b, ∀ x, HasDerivAt (fun s => ρ s x) (ρt t x) t)
  (hρsp : ∀ t ∈ Ioo a b, ContDiff ℝ 1 (ρ t))
  (hPDE : ∀ t ∈ Ioo a b, ∀ x,
    ρt t x + fluxDivergence (fun y => ρ t y • referenceDrift U c t y) x = 0)
  (μ : ℝ → Measure E) [∀ t, IsFiniteMeasure (μ t)]
  (hμ : ∀ t ∈ Icc a b, μ t = volume.withDensity (fun x => ENNReal.ofReal (ρ t x)))
  (hpos : ∀ t ∈ Icc a b, ∀ x, 0 ≤ ρ t x)

include hH ρ ρt hρ hρt hdρ hρsp hPDE hμ hpos in
/-- The potential-generated flow transports the actual density laws at every time. -/
theorem referenceFlowHomeomorph_measurePreserving (t : Icc a b) :
    MeasurePreserving (referenceFlowHomeomorph U c (fun t _ => hU t) hG hc C hC hlo hup
      ⟨a, le_rfl, hab⟩ t) (μ a) (μ t) :=
  measurePreserving_flow_family_of_density_continuity
    (D := fun t x => (-c t) • hessianOperator (U t) x) hab
    (referenceDrift_continuous U c hG hc)
    (fun t ht => referenceDrift_lipschitz U c t (hU t) (hlo t ht) (hup t ht) C (hC t ht))
    ((hc.comp continuous_fst).neg.smul hH)
    (fun t x => referenceDrift_hasFDerivAt U c t x (hU t))
    ρ ρt hρ hρt hdρ hρsp hPDE μ hμ hpos t

/-- The actual reference composition is unitary on both scalar and vector L2. -/
def referenceFlowPullback {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (t : Icc a b) : Lp F 2 (μ t) ≃ₗᵢ[ℝ] Lp F 2 (μ a) :=
  pullback (referenceFlowHomeomorph U c (fun t _ => hU t) hG hc C hC hlo hup
    ⟨a, le_rfl, hab⟩ t).toMeasurableEquiv
    (referenceFlowHomeomorph_measurePreserving U c hab hU hG hH hc C hC hlo hup
      ρ ρt hρ hρt hdρ hρsp hPDE μ hμ hpos t)

end AcceleratedLogConcave.Analysis.Poisson
