import AcceleratedLogConcave.Conditional.Centering.WholeFlow

/-! Local agreement of the canonical complete flow with a smooth globally
Lipschitz cutoff flow. The agreement is uniform on a neighborhood of the
initial point and on the entire chosen time interval. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric Filter
open scoped Topology NNReal

namespace AcceleratedLogConcave.Conditional.Centering
open OAI.LogConcaveSampling.GlobalODE
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [FiniteDimensional ℝ H]

/-- Smooth local cutoff representation of the actual complete flow. -/
theorem exists_local_cutoff_flow {f : H → H} (hf : ContDiff ℝ 1 f)
    {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hgrowth : ∀ z, ‖f z‖ ≤ C * ‖z‖ + D) (x : H) {T : ℝ} (hT : 0 < T) :
    ∃ g : H → H, ContDiff ℝ 1 g ∧ ∃ K : ℝ≥0, ∃ hK : LipschitzWith K g,
      (∀ y ∈ ball x 1, ∀ t ∈ Icc (-T) T,
        completeCurve hf hC hD hgrowth y t =
          flow (fun _ _ => hK) (hK.continuous.comp continuous_snd)
            (⟨0, by linarith, hT.le⟩ : Icc (-T) T) y t) ∧
      (∀ y ∈ ball x 1, ∀ t ∈ Icc (-T) T,
        g (completeCurve hf hC hD hgrowth y t) = f (completeCurve hf hC hD hgrowth y t) ∧
        fderiv ℝ g (completeCurve hf hC hD hgrowth y t) =
          fderiv ℝ f (completeCurve hf hC hD hgrowth y t)) ∧
      (∀ n : ℕ∞, ContDiff ℝ n f → ContDiff ℝ n g) := by
  let δ := ‖x‖+1
  have hδ : 0 ≤ δ := by dsimp [δ]; positivity
  let R := gronwallBound δ C D T + 1
  have hbase : δ ≤ gronwallBound δ C D T := by
    simpa only [gronwallBound_x0] using gronwallBound_mono hδ hD hC hT.le
  have hR : 0 < R := by dsimp [R]; linarith
  let χ : ContDiffBump (0 : H) :=
    { rIn := R, rOut := R+1, rIn_pos := hR, rIn_lt_rOut := by linarith }
  let g : H → H := fun z => χ z • f z
  have hg : ContDiff ℝ 1 g := χ.contDiff.smul hf
  obtain ⟨K, hK⟩ := ContDiff.lipschitzWith_of_hasCompactSupport
    χ.hasCompactSupport.smul_right hg (by norm_num)
  have hnorm (y : H) (hy : y ∈ ball x 1) (t : ℝ) (ht : t ∈ Icc (-T) T) :
      ‖completeCurve hf hC hD hgrowth y t‖ < R := by
    have hybound : ‖y‖ ≤ δ := by
      have hnorm := norm_le_norm_sub_add y x
      have hdist : ‖y - x‖ < 1 := by simpa only [mem_ball, dist_eq_norm] using hy
      dsimp [δ]
      linarith
    have h := completeCurve_norm_bound hf hC hD hgrowth hδ hybound hT.le
      (abs_le.mpr ht)
    dsimp [R]
    linarith
  have hloc (y : H) (hy : y ∈ ball x 1) (t : ℝ) (ht : t ∈ Icc (-T) T) :
      g =ᶠ[𝓝 (completeCurve hf hC hD hgrowth y t)] f := by
    have hχ := χ.eventuallyEq_one_of_mem_ball
      (by simpa only [mem_ball_zero_iff] using hnorm y hy t ht)
    filter_upwards [hχ] with z hz
    simp only [g, hz, Pi.one_apply, one_smul]
  refine ⟨g, hg, K, hK, ?_, ?_, ?_⟩
  · intro y hy t ht
    have hd (τ : ℝ) (hτ : τ ∈ Icc (-T) T) :
        HasDerivWithinAt (completeCurve hf hC hD hgrowth y)
          (g (completeCurve hf hC hD hgrowth y τ)) (Icc (-T) T) τ := by
      rw [(hloc y hy τ hτ).eq_of_nhds]
      exact (completeCurve_deriv hf hC hD hgrowth y τ).hasDerivWithinAt
    have hh := trajectory_dist (fun _ _ => hK)
      (completeCurve_continuous hf hC hD hgrowth y).continuousOn hd
      (flow_continuous (fun _ _ => hK) (hK.continuous.comp continuous_snd)
        (⟨0, by linarith, hT.le⟩ : Icc (-T) T) y).continuousOn
      (flow_deriv (fun _ _ => hK) (hK.continuous.comp continuous_snd)
        (⟨0, by linarith, hT.le⟩ : Icc (-T) T) y)
      (⟨0, by linarith, hT.le⟩ : Icc (-T) T) ⟨t, ht⟩
    rw [completeCurve_initial, flow_initial, dist_self, zero_mul, dist_le_zero] at hh
    exact hh
  · intro y hy t ht
    exact ⟨(hloc y hy t ht).eq_of_nhds, (hloc y hy t ht).fderiv_eq⟩
  · intro n hnf
    exact χ.contDiff.smul hnf

/-- Local cutoff agreement gives spatial C1 regularity of the actual complete
flow, even though the original field need not be globally Lipschitz. -/
theorem completeCurve_contDiff_one {f : H → H} (hf : ContDiff ℝ 1 f)
    {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hgrowth : ∀ z, ‖f z‖ ≤ C * ‖z‖ + D) (t : ℝ) :
    ContDiff ℝ 1 (fun x => completeCurve hf hC hD hgrowth x t) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  let T := |t|+1
  have hT : 0 < T := by dsimp [T]; positivity
  obtain ⟨g, hg, K, hK, heq, _⟩ := exists_local_cutoff_flow hf hC hD hgrowth x hT
  have hDg : Continuous (fun q : ℝ × H => fderiv ℝ g q.2) :=
    (hg.continuous_fderiv (by norm_num)).comp continuous_snd
  have hdg (τ : ℝ) (z : H) : HasFDerivAt g (fderiv ℝ g z) z :=
    (hg.differentiable_one z).hasFDerivAt
  have ht : t ∈ Icc (-T) T := by
    constructor <;> dsimp [T] <;> linarith [le_abs_self t, neg_abs_le t]
  have hflow := flow_contDiff_one (a := -T) (b := T)
    (f := fun (_ : ℝ) z => g z) (D := fun (_ : ℝ) z => fderiv ℝ g z) (by linarith)
    (hK.continuous.comp continuous_snd) (fun _ _ => hK) hDg hdg
    (⟨0, by linarith, hT.le⟩ : Icc (-T) T) ⟨t, ht⟩
  have he : (fun y => completeCurve hf hC hD hgrowth y t) =ᶠ[𝓝 x]
      (fun y => flow (fun _ _ => hK) (hK.continuous.comp continuous_snd)
        (⟨0, by linarith, hT.le⟩ : Icc (-T) T) y t) := by
    filter_upwards [ball_mem_nhds x (by norm_num : (0 : ℝ) < 1)] with y hy
    exact heq y hy t ht
  exact hflow.contDiffAt.congr_of_eventuallyEq he

/-- Joint time/initial-state continuity follows from the same uniform cutoff
representation used to prove spatial differentiability. -/
theorem completeCurve_joint_continuous {f : H → H} (hf : ContDiff ℝ 1 f)
    {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hgrowth : ∀ z, ‖f z‖ ≤ C * ‖z‖ + D) :
    Continuous (fun q : ℝ × H => completeCurve hf hC hD hgrowth q.2 q.1) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  let T := |p.1|+1
  have hT : 0 < T := by dsimp [T]; positivity
  have hp : p.1 ∈ Ioo (-T) T := by
    constructor <;> dsimp [T] <;> linarith [le_abs_self p.1, neg_abs_le p.1]
  obtain ⟨g, hg, K, hK, heq, _⟩ := exists_local_cutoff_flow hf hC hD hgrowth p.2 hT
  let hab : -T ≤ T := by linarith
  let s : Icc (-T) T := ⟨0, by linarith, hT.le⟩
  let F (q : ℝ × H) := flow (fun _ _ => hK) (hK.continuous.comp continuous_snd)
    s q.2 (projIcc (-T) T hab q.1)
  have hF : Continuous F := (flow_joint_continuous (fun _ _ => hK)
    (hK.continuous.comp continuous_snd) s).comp
    (continuous_snd.prodMk ((continuous_projIcc (h := hab)).comp continuous_fst))
  have he : (fun q : ℝ × H => completeCurve hf hC hD hgrowth q.2 q.1) =ᶠ[𝓝 p] F := by
    filter_upwards [(isOpen_Ioo.prod isOpen_ball).mem_nhds
      (show p ∈ Ioo (-T) T ×ˢ ball p.2 1 from ⟨hp, mem_ball_self (by norm_num)⟩)] with q hq
    dsimp [F]
    rw [projIcc_of_mem hab ⟨hq.1.1.le, hq.1.2.le⟩]
    exact heq q.2 hq.2 q.1 ⟨hq.1.1.le, hq.1.2.le⟩
  exact hF.continuousAt.congr he.symm

/-- The complete actual flow is a C1 homeomorphism at each real time. -/
def completeFlowHomeomorph {f : H → H} (hf : ContDiff ℝ 1 f)
    {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hgrowth : ∀ z, ‖f z‖ ≤ C * ‖z‖ + D) (t : ℝ) : H ≃ₜ H where
  toFun x := completeCurve hf hC hD hgrowth x t
  invFun x := completeCurve hf hC hD hgrowth x (-t)
  left_inv x := completeCurve_inverse hf hC hD hgrowth x t
  right_inv x := by simpa only [neg_neg] using completeCurve_inverse hf hC hD hgrowth x (-t)
  continuous_toFun := (completeCurve_contDiff_one hf hC hD hgrowth t).continuous
  continuous_invFun := (completeCurve_contDiff_one hf hC hD hgrowth (-t)).continuous

end AcceleratedLogConcave.Conditional.Centering
