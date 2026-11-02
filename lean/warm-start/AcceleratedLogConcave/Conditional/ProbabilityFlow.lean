import AcceleratedLogConcave.Conditional.Flow.Construction
import AcceleratedLogConcave.Conditional.Flow.WeakTransport
import AcceleratedLogConcave.Conditional.Flow.WeightedAdjoint
import AcceleratedLogConcave.Conditional.Flow.MeanIBP
import AcceleratedLogConcave.Conditional.Flow.Current
import AcceleratedLogConcave.Conditional.Flow.Continuity
import AcceleratedLogConcave.Conditional.Flow.Regularity
import AcceleratedLogConcave.Conditional.Flow.MaterialPointwise

/-!
# Actual conditional-mean probability flow

The ODE below uses the actual posterior conditional mean and is constructed
from its analytic continuity and Lipschitz estimates. The transport theorem
derives exact interpolation marginals from the weak continuity equation.

Both continuity equations are proved from the independent-Gaussian law. The
pointwise material identity follows by subtracting their compact tests and
using the positive weighted adjoint. No final flow, marginal identity, or
material identity is assumed.
-/

noncomputable section
open Set Function MeasureTheory
open scoped Topology NNReal

namespace AcceleratedLogConcave.Conditional
open OAI.LogConcaveSampling.GlobalODE

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {a b : ℝ} (hab : a ≤ b) (F : E → ℝ) (x : E) (r : ℝ)
  (hc : ContinuousOn (uncurry (conditionalMean F x r))
    (Icc a b ×ˢ (univ : Set E)))
  {L : ℝ≥0} (hL : ∀ t ∈ Icc a b, LipschitzWith L (conditionalMean F x r t))

/-- Complete probability-time trajectories driven by the actual conditional mean. -/
def probabilityFlow (s : Icc a b) (y : E) : ℝ → E :=
  meanProbabilityFlow hab r (conditionalMean F x r) hc hL s y

theorem probabilityFlow_initial (s : Icc a b) (y : E) :
    probabilityFlow hab F x r hc hL s y s = y :=
  meanProbabilityFlow_initial hab r _ hc hL s y

theorem probabilityFlow_continuous (s : Icc a b) (y : E) :
    Continuous (probabilityFlow hab F x r hc hL s y) :=
  meanProbabilityFlow_continuous hab r _ hc hL s y

/-- The constructed flow solves `Y' = -r M(Y)`, including interval endpoints. -/
theorem probabilityFlow_deriv (s : Icc a b) (y : E) {t : ℝ} (ht : t ∈ Icc a b) :
    HasDerivWithinAt (probabilityFlow hab F x r hc hL s y)
      (probabilityVelocity F x r t (probabilityFlow hab F x r hc hL s y t))
      (Icc a b) t :=
  meanProbabilityFlow_deriv hab r _ hc hL s y ht

/-- The exact flow is invertible between any two times in the chosen interval. -/
def probabilityFlowHomeomorph (s t : Icc a b) : E ≃ₜ E :=
  meanProbabilityFlowHomeomorph hab r (conditionalMean F x r) hc hL s t

theorem probabilityFlowHomeomorph_apply (s t : Icc a b) (y : E) :
    probabilityFlowHomeomorph hab F x r hc hL s t y =
      probabilityFlow hab F x r hc hL s y t := rfl

/-- Exact endpoint marginals follow from the actual interpolation weak equation.
The spatial derivative hypotheses are local analytic regularity, not transport
or material-identity assumptions. -/
theorem probabilityFlow_measurePreserving_of_weak_continuity (hlt : a < b)
    {DM : ℝ → E → E →L[ℝ] E}
    (hDM : ContinuousOn (uncurry DM) (Icc a b ×ˢ (univ : Set E)))
    (hdM : ∀ t ∈ Icc a b, ∀ y, HasFDerivAt (conditionalMean F x r t) (DM t y) y)
    [∀ t, IsFiniteMeasure (interpolationLaw F x r t)]
    (hCE : HasWeakContinuityEquationOn (interpolationLaw F x r)
      (probabilityVelocity F x r) a b) :
    MeasurePreserving
      (probabilityFlowHomeomorph hab F x r hc hL
        ⟨a, le_rfl, hab⟩ ⟨b, hab, le_rfl⟩)
      (interpolationLaw F x r a) (interpolationLaw F x r b) := by
  let D (t : ℝ) (y : E) := (-r) • DM (projIcc a b hab t) y
  have hD : Continuous (uncurry D) := by
    have hp : Continuous (fun q : ℝ × E => ((projIcc a b hab q.1 : ℝ), q.2)) :=
      (continuous_subtype_val.comp ((continuous_projIcc (h := hab)).comp
        continuous_fst)).prodMk continuous_snd
    exact (continuous_const : Continuous (fun _ : ℝ × E => (-r : ℝ))).smul
      (hDM.comp_continuous hp
      (fun q => ⟨(projIcc a b hab q.1).2, mem_univ q.2⟩))
  have hd (t : ℝ) (y : E) :
      HasFDerivAt (clippedProbabilityVelocity hab r (conditionalMean F x r) t)
        (D t y) y :=
    (hdM _ (projIcc a b hab t).2 y).const_smul (-r)
  have hCEclip : HasWeakContinuityEquationOn (interpolationLaw F x r)
      (clippedProbabilityVelocity hab r (conditionalMean F x r)) a b :=
    hCE.congr_velocity fun t ht y =>
      (clippedProbabilityVelocity_eq hab r (conditionalMean F x r)
        ⟨ht.1.le, ht.2.le⟩ y).symm
  exact measurePreserving_flow_of_weak_continuity hlt
    (clippedProbabilityVelocity_continuous hab r hc)
    (fun t _ => clippedProbabilityVelocity_lipschitz hab r hL t) hD hd
    (interpolationLaw F x r) hCEclip

end AcceleratedLogConcave.Conditional

namespace AcceleratedLogConcave.Conditional
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Actual drift Lipschitz constant; the source small-scale assumption bounds
this coefficient by one half. -/
theorem lipschitzWith_probabilityVelocity {F : E → ℝ} (hF : ContDiff ℝ 2 F) {ell : ℝ}
    (hell : 0 ≤ ell)
    (hlo : ∀ z a, 0 ≤ fderiv ℝ (fderiv ℝ F) z a a)
    (hup : ∀ z a, fderiv ℝ (fderiv ℝ F) z a a ≤ ell * ‖a‖ ^ 2)
    (x : E) {r : ℝ} (hr : 0 < r) {ρ : ℝ} (hρlo : -1 < ρ) (hρhi : ρ < 1) :
    LipschitzWith ⟨r ^ 2 * ell, mul_nonneg (sq_nonneg r) hell⟩
      (probabilityVelocity F x r ρ) := by
  apply LipschitzWith.of_dist_le_mul
  intro y z
  have h := (lipschitzWith_conditionalMean hF hell hlo hup x hr hρlo hρhi).dist_le_mul y z
  simp only [dist_eq_norm] at h
  change ‖conditionalMean F x r ρ y - conditionalMean F x r ρ z‖ ≤
    (r * ell) * ‖y - z‖ at h
  simp only [probabilityVelocity, dist_eq_norm, ← smul_sub, norm_smul,
    norm_neg, Real.norm_eq_abs, abs_of_pos hr]
  change r * ‖conditionalMean F x r ρ y - conditionalMean F x r ρ z‖ ≤
    (r ^ 2 * ell) * ‖y - z‖
  exact (mul_le_mul_of_nonneg_left h hr.le).trans_eq (by ring)

/-- The complete flow under the actual C² convex-potential hypotheses. All
continuity and Lipschitz inputs are discharged by Gaussian conditional calculus. -/
def convexProbabilityFlow {F : E → ℝ} (hF : ContDiff ℝ 2 F) {ell : ℝ}
    (hell : 0 ≤ ell)
    (hlo : ∀ z a, 0 ≤ fderiv ℝ (fderiv ℝ F) z a a)
    (hup : ∀ z a, fderiv ℝ (fderiv ℝ F) z a a ≤ ell * ‖a‖ ^ 2)
    (x : E) {r : ℝ} (hr : 0 < r) {a b : ℝ} (hab : a ≤ b)
    (ha : -1 < a) (hb : b < 1) (s : Icc a b) (y : E) : ℝ → E :=
  probabilityFlow hab F x r (continuousOn_conditionalMean hF hlo hup x r ha hb)
    (fun _ ht => lipschitzWith_conditionalMean hF hell hlo hup x hr
      (ha.trans_le ht.1) (ht.2.trans_lt hb)) s y

/-- Initial condition for the flow constructed from the original potential. -/
theorem convexProbabilityFlow_initial {F : E → ℝ} (hF : ContDiff ℝ 2 F) {ell : ℝ}
    (hell : 0 ≤ ell)
    (hlo : ∀ z a, 0 ≤ fderiv ℝ (fderiv ℝ F) z a a)
    (hup : ∀ z a, fderiv ℝ (fderiv ℝ F) z a a ≤ ell * ‖a‖ ^ 2)
    (x : E) {r : ℝ} (hr : 0 < r) {a b : ℝ} (hab : a ≤ b)
    (ha : -1 < a) (hb : b < 1) (s : Icc a b) (y : E) :
    convexProbabilityFlow hF hell hlo hup x hr hab ha hb s y s = y :=
  probabilityFlow_initial _ _ _ _ _ _ _ _

/-- The source ODE is solved by the flow constructed under the original
potential assumptions, without a supplied trajectory. -/
theorem convexProbabilityFlow_deriv {F : E → ℝ} (hF : ContDiff ℝ 2 F) {ell : ℝ}
    (hell : 0 ≤ ell)
    (hlo : ∀ z a, 0 ≤ fderiv ℝ (fderiv ℝ F) z a a)
    (hup : ∀ z a, fderiv ℝ (fderiv ℝ F) z a a ≤ ell * ‖a‖ ^ 2)
    (x : E) {r : ℝ} (hr : 0 < r) {a b : ℝ} (hab : a ≤ b)
    (ha : -1 < a) (hb : b < 1) (s : Icc a b) (y : E) {t : ℝ}
    (ht : t ∈ Icc a b) :
    HasDerivWithinAt (convexProbabilityFlow hF hell hlo hup x hr hab ha hb s y)
      (probabilityVelocity F x r t
        (convexProbabilityFlow hF hell hlo hup x hr hab ha hb s y t)) (Icc a b) t :=
  probabilityFlow_deriv _ _ _ _ _ _ _ _ ht

/-- The constructed source flow gives a homeomorphism between every pair of times. -/
def convexProbabilityFlowHomeomorph {F : E → ℝ} (hF : ContDiff ℝ 2 F) {ell : ℝ}
    (hell : 0 ≤ ell)
    (hlo : ∀ z a, 0 ≤ fderiv ℝ (fderiv ℝ F) z a a)
    (hup : ∀ z a, fderiv ℝ (fderiv ℝ F) z a a ≤ ell * ‖a‖ ^ 2)
    (x : E) {r : ℝ} (hr : 0 < r) {a b : ℝ} (hab : a ≤ b)
    (ha : -1 < a) (hb : b < 1) (s t : Icc a b) : E ≃ₜ E :=
  probabilityFlowHomeomorph hab F x r (continuousOn_conditionalMean hF hlo hup x r ha hb)
    (fun _ hu => lipschitzWith_conditionalMean hF hell hlo hup x hr
      (ha.trans_le hu.1) (hu.2.trans_lt hb)) s t

theorem convexProbabilityFlowHomeomorph_apply {F : E → ℝ} (hF : ContDiff ℝ 2 F) {ell : ℝ}
    (hell : 0 ≤ ell)
    (hlo : ∀ z a, 0 ≤ fderiv ℝ (fderiv ℝ F) z a a)
    (hup : ∀ z a, fderiv ℝ (fderiv ℝ F) z a a ≤ ell * ‖a‖ ^ 2)
    (x : E) {r : ℝ} (hr : 0 < r) {a b : ℝ} (hab : a ≤ b)
    (ha : -1 < a) (hb : b < 1) (s t : Icc a b) (y : E) :
    convexProbabilityFlowHomeomorph hF hell hlo hup x hr hab ha hb s t y =
      convexProbabilityFlow hF hell hlo hup x hr hab ha hb s y t := rfl

/-- Composition between probability times follows from actual ODE uniqueness. -/
theorem convexProbabilityFlow_cocycle {F : E → ℝ} (hF : ContDiff ℝ 2 F) {ell : ℝ}
    (hell : 0 ≤ ell)
    (hlo : ∀ z a, 0 ≤ fderiv ℝ (fderiv ℝ F) z a a)
    (hup : ∀ z a, fderiv ℝ (fderiv ℝ F) z a a ≤ ell * ‖a‖ ^ 2)
    (x : E) {r : ℝ} (hr : 0 < r) {a b : ℝ} (hab : a ≤ b)
    (ha : -1 < a) (hb : b < 1) (s t w : Icc a b) (y : E) :
    convexProbabilityFlow hF hell hlo hup x hr hab ha hb t
      (convexProbabilityFlow hF hell hlo hup x hr hab ha hb s y t) w =
      convexProbabilityFlow hF hell hlo hup x hr hab ha hb s y w :=
  meanProbabilityFlow_cocycle hab r (conditionalMean F x r)
    (continuousOn_conditionalMean hF hlo hup x r ha hb)
    (fun _ ht => lipschitzWith_conditionalMean hF hell hlo hup x hr
      (ha.trans_le ht.1) (ht.2.trans_lt hb)) s t w y

end AcceleratedLogConcave.Conditional

namespace AcceleratedLogConcave.Conditional
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
local notation "E" => EuclideanSpace ℝ ι

/-- Exact interpolation marginals of the complete source flow. The theorem
assumes only C² convexity, an upper Hessian bound, and positive spatial scale;
the source's additional small-scale condition is unnecessary for transport. -/
theorem convexProbabilityFlow_measurePreserving
    {F : E → ℝ} (hF : ContDiff ℝ 2 F) {ell : ℝ} (hell : 0 ≤ ell)
    (hlo : ∀ z a, 0 ≤ fderiv ℝ (fderiv ℝ F) z a a)
    (hup : ∀ z a, fderiv ℝ (fderiv ℝ F) z a a ≤ ell * ‖a‖ ^ 2)
    (x : E) {r : ℝ} (hr : 0 < r) {a b : ℝ} (hab : a ≤ b)
    (ha : -1 < a) (hb : b < 1) (hlt : a < b) :
    MeasurePreserving
      (convexProbabilityFlowHomeomorph hF hell hlo hup x hr hab ha hb
        ⟨a, le_rfl, hab⟩ ⟨b, hab, le_rfl⟩)
      (interpolationLaw F x r a) (interpolationLaw F x r b) := by
  let : ∀ t, IsFiniteMeasure (interpolationLaw F x r t) := fun t => by
    have := interpolationLaw_isProbabilityMeasure hF hlo x r t
    infer_instance
  exact probabilityFlow_measurePreserving_of_weak_continuity hab F x r
    (continuousOn_conditionalMean hF hlo hup x r ha hb)
    (fun _ ht => lipschitzWith_conditionalMean hF hell hlo hup x hr
      (ha.trans_le ht.1) (ht.2.trans_lt hb)) hlt
    (continuousOn_conditionalMeanSpatialDerivative hF hlo hup x r ha hb)
    (fun t ht y => hasFDerivAt_conditionalMeanSpatialDerivative hF hlo hup x r
      (ha.trans_le ht.1) (ht.2.trans_lt hb) y)
    (hasWeakContinuityEquation_interpolation hF hlo hup x r ha hb)


/-- Exact endpoint transport also includes a degenerate time interval. -/
theorem convexProbabilityFlow_measurePreserving_le
    {F : E → ℝ} (hF : ContDiff ℝ 2 F) {ell : ℝ} (hell : 0 ≤ ell)
    (hlo : ∀ z a, 0 ≤ fderiv ℝ (fderiv ℝ F) z a a)
    (hup : ∀ z a, fderiv ℝ (fderiv ℝ F) z a a ≤ ell * ‖a‖ ^ 2)
    (x : E) {r : ℝ} (hr : 0 < r) {a b : ℝ} (hab : a ≤ b)
    (ha : -1 < a) (hb : b < 1) :
    MeasurePreserving
      (convexProbabilityFlowHomeomorph hF hell hlo hup x hr hab ha hb
        ⟨a, le_rfl, hab⟩ ⟨b, hab, le_rfl⟩)
      (interpolationLaw F x r a) (interpolationLaw F x r b) := by
  rcases hab.eq_or_lt with h | h
  · subst b
    have heq : (convexProbabilityFlowHomeomorph hF hell hlo hup x hr hab ha hb
        ⟨a, le_rfl, hab⟩ ⟨a, hab, le_rfl⟩ : E → E) = id := by
      funext y
      exact convexProbabilityFlow_initial hF hell hlo hup x hr hab ha hb ⟨a, le_rfl, hab⟩ y
    rw [heq]
    exact MeasurePreserving.id _
  · exact convexProbabilityFlow_measurePreserving hF hell hlo hup x hr hab ha hb h

end AcceleratedLogConcave.Conditional
