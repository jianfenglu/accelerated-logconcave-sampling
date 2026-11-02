import AcceleratedLogConcave.Conditional.Stein.ReferenceJacobian
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Calculus.Deriv.Prod

/-! Actual-curve adapter. The state is the already constructed
flow together with its actual inverse-flow spatial derivative. No coupled
flow existence or global Lipschitz assumption on the coupled field is used. -/
noncomputable section
open Set Function
open scoped Topology NNReal
namespace OAI.LogConcaveSampling.GlobalODE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [ProperSpace E] {a b : ℝ} (hab : a ≤ b)
  {f : ℝ → E → E} (hc : Continuous (uncurry f))
  {K : ℝ≥0} (hL : ∀ t ∈ Icc a b, LipschitzWith K (f t))
  {D : ℝ → E → E →L[ℝ] E} (hD : Continuous (uncurry D))
  (hf : ∀ t z, HasFDerivAt (f t) (D t z) z)

def flowReferenceState (w : Icc a b) (t : ℝ) (y : E) :
    E × (E →L[ℝ] E) :=
  (flow hL hc w y t, flowReferenceJacobian hab hc hL w t y)

def referenceStateVelocity (f : ℝ → E → E) (D : ℝ → E → E →L[ℝ] E)
    (p : ℝ × (E × (E →L[ℝ] E))) : E × (E →L[ℝ] E) :=
  (f p.1 p.2.1, -(p.2.2).comp (D p.1 p.2.1))

include hD hf in
theorem hasDerivAt_flowReferenceState (w : Icc a b) {t : ℝ}
    (ht : t ∈ Ioo a b) (y : E) :
    HasDerivAt (fun u => flowReferenceState hab hc hL w u y)
      (referenceStateVelocity f D (t, flowReferenceState hab hc hL w t y)) t := by
  have ht' : t ∈ Icc a b := ⟨ht.1.le, ht.2.le⟩
  exact ((flow_deriv hL hc w y t ht').hasDerivAt
    (Icc_mem_nhds ht.1 ht.2)).prodMk
      ((flowReferenceJacobian_deriv hab hc hL hD hf w ht' y).hasDerivAt
        (Icc_mem_nhds ht.1 ht.2))

include hD hf in
theorem flowReferenceState_joint_continuous (w : Icc a b) :
    Continuous (fun p : E × Icc a b => flowReferenceState hab hc hL w p.2 p.1) :=
  (flow_joint_continuous hL hc w).prodMk
    (flowReferenceJacobian_joint_continuous hab hc hL hD hf w)

omit [ProperSpace E] in
/-- Spatial stability and compactness of the zero-input trajectory give
linear growth. No growth estimate for a differentiated state equation is used. -/
theorem exists_flow_linear_bound (w : Icc a b) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Icc a b, ∀ y : E,
      ‖flow hL hc w y t‖ ≤ C * (1 + ‖y‖) := by
  obtain ⟨C₀, hC₀⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (flow_continuous hL hc w (0 : E)).continuousOn
  let A := Real.exp ((K : ℝ) * (b - a))
  have hA : 0 ≤ A := (Real.exp_pos _).le
  refine ⟨A + |C₀|, add_nonneg hA (abs_nonneg _), ?_⟩
  intro t ht y
  have hd : |t - (w : ℝ)| ≤ b - a := by
    rw [abs_le]
    constructor <;> linarith [ht.1, ht.2, w.2.1, w.2.2]
  have hexp : Real.exp ((K : ℝ) * |t - (w : ℝ)|) ≤ A :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hd K.coe_nonneg)
  have hdist := (flow_lipschitz hL hc w ⟨t, ht⟩).dist_le_mul y 0
  simp only [dist_zero_right] at hdist
  have hstep : ‖flow hL hc w y t‖ ≤
      ‖flow hL hc w y t - flow hL hc w 0 t‖ + ‖flow hL hc w 0 t‖ := by
    simpa only [sub_add_cancel] using norm_add_le
      (flow hL hc w y t - flow hL hc w 0 t) (flow hL hc w 0 t)
  rw [← dist_eq_norm] at hstep
  have hb := hC₀ t ht
  have he := mul_le_mul_of_nonneg_right hexp (norm_nonneg y)
  calc
    ‖flow hL hc w y t‖ ≤ A * ‖y‖ + |C₀| :=
      hstep.trans (add_le_add (hdist.trans he) (hb.trans (le_abs_self C₀)))
    _ ≤ (A + |C₀|) * (1 + ‖y‖) := by
      nlinarith [mul_nonneg (abs_nonneg C₀) (norm_nonneg y)]

omit [ProperSpace E] in
/-- The actual backward Jacobian has a uniform zeroth-order bound, so adding
it to the state preserves linear growth in the original spatial input. -/
theorem exists_flowReferenceState_linear_bound (w : Icc a b) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Icc a b, ∀ y : E,
      ‖flowReferenceState hab hc hL w t y‖ ≤ C * (1 + ‖y‖) := by
  obtain ⟨C, hC, hbound⟩ := exists_flow_linear_bound hc hL w
  let A := Real.exp ((K : ℝ) * (b - a))
  have hA : 0 ≤ A := (Real.exp_pos _).le
  refine ⟨C + A, add_nonneg hC hA, ?_⟩
  intro t ht y
  rw [flowReferenceState, Prod.norm_def, max_le_iff]
  constructor
  · exact (hbound t ht y).trans (mul_le_mul_of_nonneg_right
      (le_add_of_nonneg_right hA) (by positivity))
  · have hb := norm_flowReferenceJacobian_uniform_le hab hc hL w t y
    change ‖flowReferenceJacobian hab hc hL w t y‖ ≤ _
    nlinarith [norm_nonneg y, mul_nonneg (add_nonneg hC hA) (norm_nonneg y)]

end OAI.LogConcaveSampling.GlobalODE
