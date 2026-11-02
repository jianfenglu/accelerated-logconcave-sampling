import AcceleratedLogConcave.Numerics.SourceContractedOutput

/-! Literal scheduled finite numerical convergence. All three error powers
are paid at 2K+20 and the initializer contains no inverse-mesh row mass. This
is an analytic common-seed receiver theorem, not an executable retained-law
identification or a warm-start sampling theorem. -/
noncomputable section
set_option autoImplicit false
namespace AcceleratedLogConcave.Numerics.SourceScheduledConvergence
open MeanFlowLp MeanResidualBridge MeanCollocationLp SourceScheduledData
open SmoothQuantitativeAssembly SmoothQuadraturePayments
variable {D : ℕ}

def coefficient {m : ℕ} (d : Data (Fin D) m) : ℝ :=
  d.ell*directBudget d+meanBudget d+
    4*d.ell*d.r*Real.sqrt (D:ℝ)*SmoothInventoryDimension.A m+
    2*centerCoefficient d/(m.factorial:ℝ)

theorem scheduled_output_bound (A : OriginalData D) (K : ℕ) {c C y S : ℝ}
    (hc : 0 < c) (hc80 : c ≤ 1/80) (hC : 30 ≤ C)
    (hy : meshResolution K c C ≤ y) (hS : 1 ≤ S)
    (hsizeR : A.ell*A.r^2 ≤ S*(SourceSchedule.δ y)^((1:ℝ)/2))
    (hsizeS : A.ell*A.r/A.sigma ≤ S*(SourceSchedule.δ y)^((1:ℝ)/2))
    (hpay : 12*Real.log (520*(SourceSchedule.m K c C:ℝ)^5*S) ≤ y)
    (hvelocity : VelocityBounds (datum A K c C y hc (by linarith) hy))
    (hangle : AngleBounds (datum A K c C y hc (by linarith) hy)) :
    let d := datum A K c C y hc (by linarith) hy
    ‖output d (SourceSchedule.nP K C)-terminalTarget d‖ ≤
      coefficient d*(SourceSchedule.δ y)^(2*(K:ℝ)+20) := by
  let hC1 : 1 ≤ C := by linarith
  let P := inputs A K c C y hc hC1 hy
  let d := datum A K c C y hc hC1 hy
  let mm := SourceSchedule.m K c C
  let nn := SourceSchedule.nP K C
  have hcap := mesh_resolution_caps K hc hC1 hy
  have hm : 2 ≤ mm := SourceSchedule.m_ge_two K hc (by linarith) hC1
  have hδ := SourceSchedule.delta_pos y
  have hδone := SourceSchedule.delta_le_one hcap.1
  have hw := SourceSchedule.w_pos K hc hC1
  have hwt := SourceSchedule.w_le_t K hc hC1
  have ht := SourceSchedule.t_le_sixtieth K hc.le (by linarith : c ≤ 1/60)
  have hcoefpos : 0 < 520*(mm:ℝ)^5*S := by
    have hmr : (0:ℝ) < mm := by exact_mod_cast (show 0 < mm by omega)
    have hS0 : 0 < S := by linarith
    positivity
  have hres := SourceSchedule.delta_le_resolution hcoefpos hpay
  have ho := SourceContractedOutput.output_bound P hm hδone hcap.2.2 hwt ht
    (by norm_num : (1:ℝ)/2 ≤ 1/2) hS hsizeR hsizeS hres hvelocity hangle nn
  have hiExp := SourceSchedule.layer_defect_exponent K hC
  have hqExp := SourceSchedule.mesh_defect_exponent K hc (by linarith : c ≤ 1) hC
  have hi : (SourceSchedule.δ y)^(((nn:ℝ)+1)/3) ≤ (SourceSchedule.δ y)^(2*(K:ℝ)+20) :=
    Real.rpow_le_rpow_of_exponent_ge hδ hδone (by dsimp [nn]; linarith)
  have hq : (SourceSchedule.δ y)^(SmoothRowPayments.exponent mm (SourceSchedule.w K c C) (SourceSchedule.t K c)) ≤
      (SourceSchedule.δ y)^(2*(K:ℝ)+20) :=
    Real.rpow_le_rpow_of_exponent_ge hδ hδone (by
      simpa only [SmoothRowPayments.exponent, Nat.cast_sub (by omega : 1 ≤ mm), Nat.cast_one]
        using hqExp)
  have hcenter := (SmoothRowPayments.power_center (m := mm) hδ hδone hw.le hwt ht).trans hq
  have hM : 0 ≤ d.ell*directBudget d+meanBudget d := by
    unfold directBudget meanBudget radiusBudget seedBudget
    have := d.hr.le
    have := d.hell
    positivity
  have hQ : 0 ≤ 4*d.ell*d.r*Real.sqrt (D:ℝ)*SmoothInventoryDimension.A mm := by
    have := d.hr.le
    have := d.hell
    have := SmoothInventoryDimension.A_nonneg mm
    positivity
  have hCe : 0 ≤ 2*centerCoefficient d/(mm.factorial:ℝ) := by
    have := centerCoefficient_nonneg d
    positivity
  apply ho.trans
  have hsum := add_le_add (add_le_add (mul_le_mul_of_nonneg_left hi hM)
    (mul_le_mul_of_nonneg_left hq hQ)) (mul_le_mul_of_nonneg_left hcenter hCe)
  exact hsum.trans_eq (by unfold coefficient; ring)

end AcceleratedLogConcave.Numerics.SourceScheduledConvergence
