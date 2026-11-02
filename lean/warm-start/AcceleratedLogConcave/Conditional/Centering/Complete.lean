import AcceleratedLogConcave.External.OAI.GlobalODE
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-!
# Finite-horizon completeness from linear growth

A smooth compact cutoff gives a globally Lipschitz auxiliary field. Grönwall
keeps its solution inside the region where the cutoff is one, so the resulting
trajectory solves the original locally Lipschitz field on the entire prescribed
interval. The original field is never assumed globally Lipschitz.
-/
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Metric
open scoped Topology NNReal

namespace AcceleratedLogConcave.Conditional.Centering
open OAI.LogConcaveSampling.GlobalODE

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [FiniteDimensional ℝ H]

/-- Every finite forward horizon is reached by a C1 field of linear growth. -/
theorem exists_curve_of_contDiff_linear_growth {f : H → H}
    (hf : ContDiff ℝ 1 f) {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hgrowth : ∀ z, ‖f z‖ ≤ C * ‖z‖ + D)
    {a b : ℝ} (hab : a ≤ b) (x : H) :
    ∃ α : ℝ → H, Continuous α ∧ α a = x ∧
      ∀ t ∈ Icc a b, HasDerivWithinAt α (f (α t)) (Icc a b) t := by
  let R := gronwallBound ‖x‖ C D (b-a) + 1
  have hbase : ‖x‖ ≤ gronwallBound ‖x‖ C D (b-a) := by
    simpa only [gronwallBound_x0] using
      gronwallBound_mono (norm_nonneg x) hD hC (sub_nonneg.mpr hab)
  have hR : 0 < R := by dsimp [R]; linarith [norm_nonneg x]
  let χ : ContDiffBump (0 : H) :=
    { rIn := R, rOut := R + 1, rIn_pos := hR, rIn_lt_rOut := by linarith }
  let g : H → H := fun z => χ z • f z
  have hg : ContDiff ℝ 1 g := χ.contDiff.smul hf
  have hgcompact : HasCompactSupport g := χ.hasCompactSupport.smul_right
  obtain ⟨K, hK⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hgcompact hg (by norm_num)
  have hgrowthg (z : H) : ‖g z‖ ≤ C * ‖z‖ + D := by
    calc
      _ = χ z * ‖f z‖ := by simp only [g, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg χ.nonneg]
      _ ≤ 1 * ‖f z‖ := mul_le_mul_of_nonneg_right χ.le_one (norm_nonneg _)
      _ ≤ _ := by simpa only [one_mul] using hgrowth z
  let α := flow (fun _ _ => hK) (hg.continuous.comp continuous_snd)
    (⟨a, le_rfl, hab⟩ : Icc a b) x
  have hα : Continuous α := flow_continuous _ _ _ _
  have hα0 : α a = x := flow_initial _ _ _ _
  have hdα (t : ℝ) (ht : t ∈ Icc a b) :
      HasDerivWithinAt α (g (α t)) (Icc a b) t := flow_deriv _ _ _ _ t ht
  have hbound (t : ℝ) (ht : t ∈ Icc a b) : ‖α t‖ < R := by
    have h := norm_le_gronwallBound_of_norm_deriv_right_le hα.continuousOn
      (right_deriv hdα) (by rw [hα0]) (fun τ _ => hgrowthg (α τ)) t ht
    have hmono := gronwallBound_mono (norm_nonneg x) hD hC
      (show t-a ≤ b-a by linarith [ht.2])
    dsimp [R]
    linarith
  refine ⟨α, hα, hα0, fun t ht => ?_⟩
  have heq : g (α t) = f (α t) := by
    have hχ : χ (α t) = 1 := χ.one_of_mem_closedBall
      (by simpa only [mem_closedBall_zero_iff] using (hbound t ht).le)
    simp only [g, hχ, one_smul]
  rw [← heq]
  exact hdα t ht

/-- The same hypotheses reach every finite backward horizon. -/
theorem exists_curve_backward_of_contDiff_linear_growth {f : H → H}
    (hf : ContDiff ℝ 1 f) {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hgrowth : ∀ z, ‖f z‖ ≤ C * ‖z‖ + D)
    {a b : ℝ} (hab : a ≤ b) (x : H) :
    ∃ α : ℝ → H, Continuous α ∧ α b = x ∧
      ∀ t ∈ Icc a b, HasDerivWithinAt α (f (α t)) (Icc a b) t := by
  obtain ⟨β, hβ, hβ0, hdβ⟩ := exists_curve_of_contDiff_linear_growth hf.neg hC hD
    (fun z => by simpa only [norm_neg] using hgrowth z)
    (a := -b) (b := -a) (neg_le_neg hab) x
  refine ⟨fun t => β (-t), hβ.comp continuous_neg, by simpa using hβ0, ?_⟩
  intro t ht
  have hh := (hdβ (-t) ⟨neg_le_neg ht.2, neg_le_neg ht.1⟩).hasFDerivWithinAt.comp_hasDerivWithinAt t
    (hasDerivAt_neg t).hasDerivWithinAt
    (fun (τ : ℝ) (hτ : τ ∈ Icc a b) => ⟨neg_le_neg hτ.2, neg_le_neg hτ.1⟩)
  simpa [Function.comp_def] using hh

end AcceleratedLogConcave.Conditional.Centering
