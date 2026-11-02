import AcceleratedLogConcave.Conditional.Centering.Complete
import Mathlib.Topology.Order.ProjIcc

/-! Parameter continuity for complete nonlinear trajectories. A common ball
comes from linear growth. Only the limiting field supplies a spatial Lipschitz
constant; no uniform parameter bound on spatial derivatives is used. -/

noncomputable section
open Set Filter Metric
open scoped Topology NNReal ContDiff

namespace AcceleratedLogConcave.Conditional.Centering
open OAI.LogConcaveSampling.GlobalODE

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [FiniteDimensional ℝ H] {X : Type*} [TopologicalSpace X]

omit [FiniteDimensional ℝ H] [TopologicalSpace X] in
/-- A fixed limiting field controls two curves on a common ball, in both time
directions. The defect is measured on that ball. -/
theorem centered_trajectory_parameter_bound
    {f : X → H → H} {γ : X → ℝ → H} {R T : ℝ} (_hT : 0 ≤ T)
    (hγ : ∀ x, Continuous (γ x))
    (hdγ : ∀ x t, HasDerivAt (γ x) (f x (γ x t)) t)
    (hball : ∀ x t, |t| ≤ T → γ x t ∈ closedBall (0 : H) R)
    {x y : X} {K : ℝ≥0} (hK : LipschitzOnWith K (f y) (closedBall (0 : H) R))
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hdefect : ∀ z ∈ closedBall (0 : H) R, dist (f x z) (f y z) ≤ δ)
    {t : ℝ} (ht : |t| ≤ T) :
    dist (γ x t) (γ y t) ≤
      gronwallBound (dist (γ x 0) (γ y 0)) K δ T := by
  have hb (x : X) (u : ℝ) (hu : u ∈ Ico 0 T) :
      γ x u ∈ closedBall (0 : H) R := hball x u (by rw [abs_of_nonneg hu.1]; exact hu.2.le)
  by_cases ht0 : 0 ≤ t
  · have hh := dist_le_of_approx_trajectories_ODE_of_mem
      (v := fun _ => f y) (s := fun _ => closedBall (0 : H) R)
      (fun _ _ => hK) (hγ x).continuousOn
      (fun u _ => (hdγ x u).hasDerivWithinAt)
      (fun u hu => hdefect _ (hb x u hu)) (hb x)
      (hγ y).continuousOn (fun u _ => (hdγ y u).hasDerivWithinAt)
      (fun _ _ => by simp : ∀ u ∈ Ico 0 T,
        dist (f y (γ y u)) (f y (γ y u)) ≤ (0 : ℝ)) (hb y)
      (le_refl (dist (γ x 0) (γ y 0))) t ⟨ht0, (le_abs_self t).trans ht⟩
    simp only [add_zero, sub_zero] at hh
    exact hh.trans (gronwallBound_mono dist_nonneg hδ K.coe_nonneg ((le_abs_self t).trans ht))
  · have hd (x : X) (u : ℝ) :
        HasDerivAt (fun v => γ x (-v)) (-f x (γ x (-u))) u := by
      convert! (hdγ x (-u)).hasFDerivAt.comp_hasDerivAt u (hasDerivAt_neg u) using 1
      simp
    have hb' (x : X) (u : ℝ) (hu : u ∈ Ico 0 T) :
        γ x (-u) ∈ closedBall (0 : H) R :=
      hball x (-u) (by rw [abs_neg, abs_of_nonneg hu.1]; exact hu.2.le)
    have hh := dist_le_of_approx_trajectories_ODE_of_mem
      (v := fun _ z => -f y z) (s := fun _ => closedBall (0 : H) R)
      (f := fun u => γ x (-u)) (g := fun u => γ y (-u))
      (δ := dist (γ x 0) (γ y 0))
      (fun _ _ => hK.neg) ((hγ x).comp continuous_neg).continuousOn
      (fun u _ => (hd x u).hasDerivWithinAt)
      (fun u hu => by simpa only [dist_neg_neg] using hdefect _ (hb' x u hu)) (hb' x)
      ((hγ y).comp continuous_neg).continuousOn (fun u _ => (hd y u).hasDerivWithinAt)
      (fun _ _ => by simp : ∀ u ∈ Ico 0 T,
        dist (-f y (γ y (-u))) (-f y (γ y (-u))) ≤ (0 : ℝ)) (hb' y)
      (by simp) (-t)
      ⟨by linarith, (neg_le_abs t).trans ht⟩
    simp only [neg_neg, add_zero, sub_zero] at hh
    exact hh.trans (gronwallBound_mono dist_nonneg hδ K.coe_nonneg ((neg_le_abs t).trans ht))

/-- Joint field continuity becomes a uniform defect on a common compact
trajectory ball. Smoothness is needed separately at each limiting parameter. -/
theorem continuous_parameter_trajectory_of_common_ball
    {f : X → H → H} {γ : X → ℝ → H} {R T : ℝ} (hT : 0 ≤ T)
    (hf : Continuous (fun p : X × H => f p.1 p.2))
    (hfx : ∀ x, ContDiff ℝ 1 (f x))
    (hγ : ∀ x, Continuous (γ x))
    (hdγ : ∀ x t, HasDerivAt (γ x) (f x (γ x t)) t)
    (hball : ∀ x t, |t| ≤ T → γ x t ∈ closedBall (0 : H) R)
    (hinit : Continuous (fun x => γ x 0)) :
    Continuous (fun x => (⟨fun t : Icc (-T) T => γ x t,
      (hγ x).comp continuous_subtype_val⟩ : C(Icc (-T) T, H))) := by
  let Γ (x : X) : C(Icc (-T) T, H) :=
    ⟨fun t => γ x t, (hγ x).comp continuous_subtype_val⟩
  let P (x : X) : C(closedBall (0 : H) R, H) :=
    ⟨fun z => f x z, hf.comp (continuous_const.prodMk continuous_subtype_val)⟩
  have hP : Continuous P := ContinuousMap.continuous_of_continuous_uncurry P
    (hf.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)))
  change Continuous Γ
  rw [continuous_iff_continuousAt]
  intro x
  obtain ⟨K, hK⟩ := (hfx x).contDiffOn.exists_lipschitzOnWith
    one_ne_zero (convex_closedBall (0 : H) R) (isCompact_closedBall (0 : H) R)
  let B (y : X) := gronwallBound (dist (γ y 0) (γ x 0)) K (dist (P y) (P x)) T
  have hB : Continuous B := by
    dsimp [B]
    by_cases hK0 : (K : ℝ) = 0
    · simp only [gronwallBound, ite_eq_left hK0]
      exact (hinit.dist continuous_const).add ((hP.dist continuous_const).mul continuous_const)
    · simp only [gronwallBound, ite_eq_right hK0]
      exact ((hinit.dist continuous_const).mul continuous_const).add
        (((hP.dist continuous_const).div_const _).mul continuous_const)
  have hBx : B x = 0 := by simp [B, gronwallBound_ε0_δ0]
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [hB.continuousAt.preimage_mem_nhds
    (Iio_mem_nhds (by simpa [hBx] using hε))] with y hy
  apply lt_of_le_of_lt _ (show B y < ε from hy)
  apply (ContinuousMap.dist_le (by
    have hh := gronwallBound_mono (dist_nonneg (x := γ y 0) (y := γ x 0))
      (dist_nonneg (x := P y) (y := P x)) K.coe_nonneg hT
    rw [gronwallBound_x0] at hh
    exact (dist_nonneg (x := γ y 0) (y := γ x 0)).trans hh)).mpr
  intro t
  exact centered_trajectory_parameter_bound hT hγ hdγ hball hK dist_nonneg
    (fun z hz => ContinuousMap.dist_apply_le_dist (f := P y) (g := P x) ⟨z, hz⟩)
    (abs_le.mpr ⟨t.2.1, t.2.2⟩)

omit [FiniteDimensional ℝ H] [TopologicalSpace X] in
/-- A uniform linear-growth bound controls any genuine complete trajectory,
with either sign of time. -/
theorem centered_trajectory_norm_bound
    {f : H → H} {γ : ℝ → H} (hγ : Continuous γ)
    (hdγ : ∀ t, HasDerivAt γ (f (γ t)) t)
    {C D δ T : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D) (hδ : 0 ≤ δ)
    (hgrowth : ∀ z, ‖f z‖ ≤ C * ‖z‖ + D) (hinit : ‖γ 0‖ ≤ δ)
    {t : ℝ} (ht : |t| ≤ T) :
    ‖γ t‖ ≤ gronwallBound δ C D T := by
  by_cases ht0 : 0 ≤ t
  · have hh := norm_le_gronwallBound_of_norm_deriv_right_le
      (hγ.continuousOn : ContinuousOn γ (Icc 0 T))
      (fun u _ => (hdγ u).hasDerivWithinAt) hinit
      (fun u _ => hgrowth (γ u)) t ⟨ht0, (le_abs_self t).trans ht⟩
    simp only [sub_zero] at hh
    exact hh.trans (gronwallBound_mono hδ hD hC ((le_abs_self t).trans ht))
  · have hd (u : ℝ) : HasDerivAt (fun v => γ (-v)) (-f (γ (-u))) u := by
      convert! (hdγ (-u)).hasFDerivAt.comp_hasDerivAt u (hasDerivAt_neg u) using 1
      simp
    have hh := norm_le_gronwallBound_of_norm_deriv_right_le
      (f := fun u => γ (-u))
      ((hγ.comp continuous_neg).continuousOn : ContinuousOn (fun u => γ (-u)) (Icc 0 T))
      (fun u _ => (hd u).hasDerivWithinAt) (by simpa using hinit)
      (fun u _ => by simpa only [norm_neg] using hgrowth (γ (-u))) (-t)
      ⟨by linarith, (neg_le_abs t).trans ht⟩
    simp only [neg_neg, sub_zero] at hh
    exact hh.trans (gronwallBound_mono hδ hD hC ((neg_le_abs t).trans ht))

/-- Continuous local linear-growth coefficients give uniform-norm continuity
of actual complete trajectories on every compact time interval. -/
theorem continuous_parameter_trajectory_of_linear_growth
    {f : X → H → H} {γ : X → ℝ → H} {C D : X → ℝ}
    (hf : Continuous (fun p : X × H => f p.1 p.2))
    (hfx : ∀ x, ContDiff ℝ 1 (f x)) (hC : Continuous C) (hD : Continuous D)
    (hC0 : ∀ x, 0 ≤ C x) (hD0 : ∀ x, 0 ≤ D x)
    (hgrowth : ∀ x z, ‖f x z‖ ≤ C x * ‖z‖ + D x)
    (hγ : ∀ x, Continuous (γ x))
    (hdγ : ∀ x t, HasDerivAt (γ x) (f x (γ x t)) t)
    (hinit : Continuous (fun x => γ x 0)) {T : ℝ} (hT : 0 ≤ T) :
    Continuous (fun x => (⟨fun t : Icc (-T) T => γ x t,
      (hγ x).comp continuous_subtype_val⟩ : C(Icc (-T) T, H))) := by
  let Γ (x : X) : C(Icc (-T) T, H) :=
    ⟨fun t => γ x t, (hγ x).comp continuous_subtype_val⟩
  change Continuous Γ
  rw [continuous_iff_continuousAt]
  intro x
  let Cmax := C x + 1
  let Dmax := D x + 1
  let δ := ‖γ x 0‖ + 1
  let U : Set X := {y | C y < Cmax ∧ D y < Dmax ∧ ‖γ y 0‖ < δ}
  have hU : IsOpen U :=
    (isOpen_lt hC continuous_const).inter
      ((isOpen_lt hD continuous_const).inter (isOpen_lt hinit.norm continuous_const))
  have hx : x ∈ U := by simp [U, Cmax, Dmax, δ]
  have hCmax : 0 ≤ Cmax := by dsimp [Cmax]; linarith [hC0 x]
  have hDmax : 0 ≤ Dmax := by dsimp [Dmax]; linarith [hD0 x]
  have hδ : 0 ≤ δ := by dsimp [δ]; positivity
  have hball (y : U) (t : ℝ) (ht : |t| ≤ T) :
      γ y t ∈ closedBall (0 : H) (gronwallBound δ Cmax Dmax T) := by
    rw [mem_closedBall_zero_iff]
    apply centered_trajectory_norm_bound (hγ y) (hdγ y) hCmax hDmax hδ
      (fun z => (hgrowth y z).trans ?_) y.property.2.2.le ht
    gcongr
    · exact y.property.1.le
    · exact y.property.2.1.le
  have hu : Continuous (fun y : U => Γ y) :=
    continuous_parameter_trajectory_of_common_ball (X := U)
      (f := fun y : U => f y) (γ := fun y : U => γ y) hT
      (hf.comp ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd))
      (fun y => hfx y) (fun y => hγ y) (fun y => hdγ y) hball
      (hinit.comp continuous_subtype_val)
  exact (continuousOn_iff_continuous_domRestrict.mpr hu).continuousAt (hU.mem_nhds hx)

/-- Evaluation at a varying time preserves the parameter continuity, including
negative times and zero. -/
theorem continuous_parameter_trajectory_joint_of_linear_growth
    {f : X → H → H} {γ : X → ℝ → H} {C D : X → ℝ}
    (hf : Continuous (fun p : X × H => f p.1 p.2))
    (hfx : ∀ x, ContDiff ℝ 1 (f x)) (hC : Continuous C) (hD : Continuous D)
    (hC0 : ∀ x, 0 ≤ C x) (hD0 : ∀ x, 0 ≤ D x)
    (hgrowth : ∀ x z, ‖f x z‖ ≤ C x * ‖z‖ + D x)
    (hγ : ∀ x, Continuous (γ x))
    (hdγ : ∀ x t, HasDerivAt (γ x) (f x (γ x t)) t)
    (hinit : Continuous (fun x => γ x 0)) :
    Continuous (fun p : X × ℝ => γ p.1 p.2) := by
  rw [continuous_iff_continuousAt]
  intro p
  let T := |p.2| + 1
  have hT : 0 ≤ T := by dsimp [T]; positivity
  let Γ (x : X) : C(Icc (-T) T, H) :=
    ⟨fun t => γ x t, (hγ x).comp continuous_subtype_val⟩
  have hΓ : Continuous Γ := continuous_parameter_trajectory_of_linear_growth
    hf hfx hC hD hC0 hD0 hgrowth hγ hdγ hinit hT
  let τ : ℝ → Icc (-T) T := projIcc (-T) T (by linarith)
  have hτ : Continuous τ := continuous_projIcc
  have hc : Continuous (fun q : X × ℝ => Γ q.1 (τ q.2)) :=
    (hΓ.comp continuous_fst).eval (hτ.comp continuous_snd)
  have hp : p.2 ∈ Ioo (-T) T := by
    constructor <;> dsimp [T] <;> linarith [neg_le_abs p.2, le_abs_self p.2]
  apply hc.continuousAt.congr_of_eventuallyEq
  filter_upwards [continuous_snd.continuousAt.preimage_mem_nhds (isOpen_Ioo.mem_nhds hp)] with q hq
  dsimp [Γ, τ]
  rw [projIcc_of_mem _ ⟨hq.1.le, hq.2.le⟩]

end AcceleratedLogConcave.Conditional.Centering
