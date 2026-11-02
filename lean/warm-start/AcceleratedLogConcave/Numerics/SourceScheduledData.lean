import AcceleratedLogConcave.Numerics.SourceFiniteOutput
import AcceleratedLogConcave.Numerics.SourceScheduleFeasibility

/-! Literal source schedule applied to original potential data. This file
constructs the actual smooth receiver datum and pays its mesh, order and
finite-iteration scalar facts before exposing the finite output estimate. -/
noncomputable section
open Set MeasureTheory
set_option autoImplicit false
namespace AcceleratedLogConcave.Numerics.SourceScheduledData
open SourceSchedule SourceNumericalData MeanFlowLp MeanResidualBridge MeanCollocationLp
open SmoothQuantitativeAssembly SmoothQuadraturePayments AffineGraph AffineGraph.MeanGeometry
variable {D : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin D)

structure OriginalData (D : ℕ) where
  F : EuclideanSpace ℝ (Fin D) → ℝ
  hF : ContDiff ℝ 2 F
  ell : ℝ
  hell : 0 ≤ ell
  hlo : ∀ z a, 0 ≤ fderiv ℝ (fderiv ℝ F) z a a
  hup : ∀ z a, fderiv ℝ (fderiv ℝ F) z a a ≤ ell * ‖a‖ ^ 2
  x : EuclideanSpace ℝ (Fin D)
  r : ℝ
  hr : 0 < r
  hsmall : r ^ 2 * ell ≤ 1 / 2
  sigma : ℝ
  hsigma : 0 < sigma

/-- A single explicit lower bound on resolution pays both half-caps. -/
def meshResolution (K : ℕ) (c C : ℝ) : ℝ :=
  Real.log 2 / SourceSchedule.w K c C

theorem mesh_resolution_caps (K : ℕ) {c C y : ℝ}
    (hc : 0 < c) (hC : 1 ≤ C)
    (hy : meshResolution K c C ≤ y) :
    0 ≤ y ∧ SourceSchedule.R K c y ≤ 1 / 2 ∧
      SourceSchedule.h₀ K c C y ≤ 1 / 2 := by
  have hw := SourceSchedule.w_pos K hc hC
  have hlog : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hmesh0 : 0 ≤ meshResolution K c C := by
    unfold meshResolution
    positivity
  have hy0 : 0 ≤ y := hmesh0.trans hy
  have hh : Real.log 2 ≤ y * SourceSchedule.w K c C := by
    have h := mul_le_mul_of_nonneg_right hy hw.le
    unfold meshResolution at h
    rw [div_mul_cancel₀ _ hw.ne'] at h
    simpa only [mul_comm] using h
  have hyt : Real.log 2 ≤ y * SourceSchedule.t K c := by
    have hwt := SourceSchedule.w_le_t K hc hC
    have h := mul_le_mul_of_nonneg_left hwt hy0
    nlinarith
  exact ⟨hy0, (SourceSchedule.geometric_caps K hyt hh).1,
    (SourceSchedule.geometric_caps K hyt hh).2⟩

/-- No numerical geometry or order facts are fields of the original input. -/
def inputs (A : OriginalData D) (K : ℕ) (c C y : ℝ)
    (hc : 0 < c) (hC : 1 ≤ C)
    (hy : meshResolution K c C ≤ y) :
    Inputs (Fin D) (SourceSchedule.m K c C) := by
  have hcap := mesh_resolution_caps K hc hC hy
  exact {
    F := A.F
    hF := A.hF
    ell := A.ell
    hell := A.hell
    hlo := A.hlo
    hup := A.hup
    x := A.x
    r := A.r
    hr := A.hr
    hsmall := A.hsmall
    sigma := A.sigma
    hsigma := A.hsigma
    δ := SourceSchedule.δ y
    t := SourceSchedule.t K c
    w := SourceSchedule.w K c C
    hδ := SourceSchedule.delta_pos y
    ht := SourceSchedule.t_pos K hc
    hw := SourceSchedule.w_pos K hc hC
    hRhalf := hcap.2.1 }

theorem scheduled_mesh (A : OriginalData D) (K : ℕ) {c C y : ℝ}
    (hc : 0 < c) (hc80 : c ≤ 1 / 80) (hC : 1 ≤ C)
    (hy : meshResolution K c C ≤ y) :
    MeshConditions (SourceNumericalData.data (inputs A K c C y hc hC hy))
      ((SourceSchedule.δ y) ^ SourceSchedule.w K c C) := by
  let P := inputs A K c C y hc hC hy
  have hcap := mesh_resolution_caps K hc hC hy
  have hm : 2 ≤ SourceSchedule.m K c C :=
    SourceSchedule.m_ge_two K hc (by linarith) hC
  exact SourceNumericalData.data_meshConditions P hm
    (SourceSchedule.delta_le_one hcap.1) hcap.2.2

/-- The literal number of simultaneous layers pays `2K+20` powers of
resolution, while retaining its original factor `2⁻N`. -/
theorem iteration_power (K : ℕ) {C y : ℝ} (hC : 30 ≤ C) (hy : 0 ≤ y) :
    ((SourceSchedule.δ y) ^ ((1 : ℝ) / 3) / 2) ^ SourceSchedule.nP K C ≤
      (SourceSchedule.δ y) ^ (2 * (K : ℝ) + 20) := by
  have hδ := SourceSchedule.delta_pos y
  have hδone := SourceSchedule.delta_le_one hy
  have hexp := SourceSchedule.layer_defect_exponent K hC
  have hpow := Real.rpow_le_rpow_of_exponent_ge hδ hδone hexp
  rw [SourceFiniteOutput.iteration_factor hδ]
  exact (div_le_self (Real.rpow_nonneg hδ.le _) (one_le_pow₀ (by norm_num))).trans hpow

theorem iteration_coefficient (K : ℕ) {C y A : ℝ}
    (hC : 30 ≤ C) (hy : 0 ≤ y) (hA : 0 ≤ A) :
    ((SourceSchedule.δ y) ^ ((1 : ℝ) / 3) / 2) ^ SourceSchedule.nP K C * A ≤
      (SourceSchedule.δ y) ^ (2 * (K : ℝ) + 20) * A :=
  mul_le_mul_of_nonneg_right (iteration_power K hC hy) hA

def datum (A : OriginalData D) (K : ℕ) (c C y : ℝ)
    (hc : 0 < c) (hC : 1 ≤ C)
    (hy : meshResolution K c C ≤ y) :
    Data (Fin D) (SourceSchedule.m K c C) :=
  SourceNumericalData.data (inputs A K c C y hc hC hy)

def seedCoefficient {m : ℕ} (d : Data (Fin D) m) (h₀ : ℝ) : ℝ :=
  2 * (rowMass d h₀ * (d.ell * directBudget d + meanBudget d) +
    residualBudget d h₀ (budget d))

theorem seedCoefficient_nonneg {m : ℕ} (d : Data (Fin D) m) (h₀ : ℝ)
    (hmesh : MeshConditions d h₀) : 0 ≤ seedCoefficient d h₀ := by
  have hr := d.hr.le
  have he := d.hell
  have hrow := rowMass_nonneg d h₀ hmesh
  have hseed := seedBudget_nonneg d
  have hdirect : 0 ≤ directBudget d := by unfold directBudget; positivity
  have hmean : 0 ≤ meanBudget d := by
    unfold meanBudget radiusBudget
    positivity
  have hres : 0 ≤ residualBudget d h₀ (budget d) := norm_nonneg _
  unfold seedCoefficient
  positivity

/-- The finite output on literal source data, with the entire initializer
coefficient retained and the scheduled layer count paid by `δ^(2K+20)`.
The two analytic interfaces are still precisely the velocity and angle bounds
on the smooth common-seed receiver. -/
theorem scheduled_output_bound (A : OriginalData D) (K : ℕ) {c C y S : ℝ}
    (hc : 0 < c) (hc80 : c ≤ 1 / 80) (hC : 30 ≤ C)
    (hy : meshResolution K c C ≤ y) (hS : 1 ≤ S)
    (hsizeR : A.ell * A.r ^ 2 ≤ S * (SourceSchedule.δ y) ^ ((1 : ℝ) / 2))
    (hsizeS : A.ell * A.r / A.sigma ≤ S * (SourceSchedule.δ y) ^ ((1 : ℝ) / 2))
    (hpay : 12 * Real.log
      (520 * (SourceSchedule.m K c C : ℝ) ^ 5 * S) ≤ y)
    (hvelocity : VelocityBounds (datum A K c C y hc (by linarith) hy))
    (hangle : AngleBounds (datum A K c C y hc (by linarith) hy)) :
    let d := datum A K c C y hc (by linarith) hy
    ‖output d (SourceSchedule.nP K C) - terminalTarget d‖ ≤
      A.ell * ((SourceSchedule.δ y) ^ (2 * (K : ℝ) + 20) *
        seedCoefficient d ((SourceSchedule.δ y) ^ SourceSchedule.w K c C) +
        2 * residualBudget d ((SourceSchedule.δ y) ^ SourceSchedule.w K c C) (budget d)) +
      (2 * centerCoefficient d / ((SourceSchedule.m K c C).factorial : ℝ)) *
        (SourceSchedule.δ y) ^ ((SourceSchedule.m K c C : ℝ) / 3) := by
  let hC1 : 1 ≤ C := by linarith
  let P := inputs A K c C y hc hC1 hy
  let d := datum A K c C y hc hC1 hy
  have hcap := mesh_resolution_caps K hc hC1 hy
  have hm : 2 ≤ SourceSchedule.m K c C :=
    SourceSchedule.m_ge_two K hc (by linarith) hC1
  have hmesh := scheduled_mesh A K hc hc80 hC1 hy
  have hδ := SourceSchedule.delta_pos y
  have hδone := SourceSchedule.delta_le_one hcap.1
  have hwt := SourceSchedule.w_le_t K hc hC1
  have ht60 := SourceSchedule.t_le_sixtieth K hc.le (by linarith : c ≤ 1 / 60)
  have hA : 0 < 520 * (SourceSchedule.m K c C : ℝ) ^ 5 * S := by
    have hmpos : (0 : ℝ) < SourceSchedule.m K c C := by
      exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 2) hm)
    positivity
  have hres := SourceSchedule.delta_le_resolution hA hpay
  have ho := SourceFiniteOutput.output_bound P hm hδone hcap.2.2 hwt ht60
    (by norm_num : (1 : ℝ) / 2 ≤ 1 / 2) hS hsizeR hsizeS hres
    hvelocity hangle (SourceSchedule.nP K C)
  change ‖output d (SourceSchedule.nP K C) - terminalTarget d‖ ≤
    A.ell * (((SourceSchedule.δ y ^ ((1 : ℝ) / 3) / 2) ^ SourceSchedule.nP K C) *
      seedCoefficient d (SourceSchedule.δ y ^ SourceSchedule.w K c C) +
      2 * residualBudget d (SourceSchedule.δ y ^ SourceSchedule.w K c C) (budget d)) +
    (2 * centerCoefficient d / ((SourceSchedule.m K c C).factorial : ℝ)) *
      SourceSchedule.δ y ^ ((SourceSchedule.m K c C : ℝ) / 3) at ho
  have hseed := seedCoefficient_nonneg d _ hmesh
  have hiter := iteration_coefficient K hC hcap.1 hseed
  exact ho.trans (add_le_add
    (mul_le_mul_of_nonneg_left (add_le_add hiter le_rfl) A.hell) le_rfl)

end AcceleratedLogConcave.Numerics.SourceScheduledData
