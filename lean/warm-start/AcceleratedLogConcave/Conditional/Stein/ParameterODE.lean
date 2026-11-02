import AcceleratedLogConcave.External.OAI.GlobalODE

/-! # Genuine parameter dependence of globally Lipschitz ODE trajectories

The field is compared only along the limiting trajectory. Compactness of the
time interval upgrades joint continuity to a uniform defect, and Gronwall then
controls the full trajectory in the uniform norm.
-/

noncomputable section
open Set Function Filter Metric
open scoped Topology NNReal

namespace OAI.LogConcaveSampling.GlobalODE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {X : Type*} [TopologicalSpace X] {a b : ℝ} (hab : a ≤ b)
  {K : ℝ≥0} {f : X → ℝ → E → E} {γ : X → ℝ → E}
  (hL : ∀ x t, t ∈ Icc a b → LipschitzWith K (f x t))
  (hγ : ∀ x, ContinuousOn (γ x) (Icc a b))
  (hdγ : ∀ x t, t ∈ Icc a b →
    HasDerivWithinAt (γ x) (f x t (γ x t)) (Icc a b) t)

include hab hL hγ hdγ

omit [TopologicalSpace X] hab in
/-- The defect on one reference trajectory suffices for a uniform perturbation
estimate. The fields need not be uniformly close on the whole state space. -/
theorem trajectory_parameter_bound (x y : X) {δ : ℝ} (hδ : 0 ≤ δ)
    (hdefect : ∀ t ∈ Icc a b, dist (f x t (γ y t)) (f y t (γ y t)) ≤ δ)
    (t : Icc a b) :
    dist (γ x t) (γ y t) ≤
      gronwallBound (dist (γ x a) (γ y a)) K δ (b - a) := by
  have hh := dist_le_of_approx_trajectories_ODE_of_mem (s := fun _ => univ)
    (fun u hu => (hL x u ⟨hu.1, hu.2.le⟩).lipschitzOnWith)
    (hγ x) (right_deriv (hdγ x))
    (fun u hu => by simp : ∀ u ∈ Ico a b,
      dist (f x u (γ x u)) (f x u (γ x u)) ≤ (0 : ℝ))
    (fun _ _ => mem_univ _) (hγ y) (right_deriv (hdγ y))
    (fun u hu => (dist_comm _ _).trans_le (hdefect u ⟨hu.1, hu.2.le⟩))
    (fun _ _ => mem_univ _) (le_refl (dist (γ x a) (γ y a))) t t.2
  simp only [zero_add] at hh
  exact hh.trans (gronwallBound_mono dist_nonneg hδ K.coe_nonneg (by linarith [t.2.2]))

/-- Jointly continuous fields and continuous initial data give continuity into
the space of trajectories with its uniform norm. This is an actual ODE estimate,
not a continuity premise for the unknown flow. -/
theorem continuous_parameter_trajectory
    (hf : Continuous (fun p : X × Icc a b × E => f p.1 p.2.1 p.2.2))
    (hinit : Continuous (fun x => γ x a)) :
    Continuous (fun x => (⟨fun t : Icc a b => γ x t,
      (hγ x).comp_continuous continuous_subtype_val (fun t => t.2)⟩ : C(Icc a b, E))) := by
  let Γ (x : X) : C(Icc a b, E) :=
    ⟨fun t => γ x t, (hγ x).comp_continuous continuous_subtype_val (fun t => t.2)⟩
  change Continuous Γ
  rw [continuous_iff_continuousAt]
  intro x
  let P (y : X) : C(Icc a b, E) :=
    ⟨fun t => f y t (γ x t),
      hf.comp (continuous_const.prodMk (continuous_id.prodMk (Γ x).continuous))⟩
  have hP : Continuous P := ContinuousMap.continuous_of_continuous_uncurry P
    (hf.comp (continuous_fst.prodMk
      (continuous_snd.prodMk ((Γ x).continuous.comp continuous_snd))))
  let B (y : X) := gronwallBound (dist (γ y a) (γ x a)) K (dist (P y) (P x)) (b - a)
  have hB : Continuous B := by
    dsimp [B]
    by_cases hK : (K : ℝ) = 0
    · simp only [gronwallBound, ite_eq_left hK]
      exact (hinit.dist continuous_const).add ((hP.dist continuous_const).mul continuous_const)
    · simp only [gronwallBound, ite_eq_right hK]
      exact ((hinit.dist continuous_const).mul continuous_const).add
        (((hP.dist continuous_const).div_const _).mul continuous_const)
  have hBx : B x = 0 := by simp [B, gronwallBound_ε0_δ0]
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [hB.continuousAt.preimage_mem_nhds (Iio_mem_nhds (by simpa [hBx] using hε))]
    with y hy
  have hy' : B y < ε := hy
  apply lt_of_le_of_lt _ hy'
  apply (ContinuousMap.dist_le (by
    have hh := gronwallBound_mono (dist_nonneg (x := γ y a) (y := γ x a))
      (dist_nonneg (x := P y) (y := P x)) K.coe_nonneg
      (sub_nonneg.mpr hab)
    rw [gronwallBound_x0] at hh
    exact (dist_nonneg (x := γ y a) (y := γ x a)).trans hh)).mpr
  intro t
  exact trajectory_parameter_bound hL hγ hdγ y x dist_nonneg
    (fun u hu => ContinuousMap.dist_apply_le_dist (f := P y) (g := P x) ⟨u, hu⟩) t

/-- Joint dependence on parameters and evaluation time, from continuous
initial data at the left endpoint. -/
theorem continuous_parameter_trajectory_joint
    (hf : Continuous (fun p : X × Icc a b × E => f p.1 p.2.1 p.2.2))
    (hinit : Continuous (fun x => γ x a)) :
    Continuous (fun p : X × Icc a b => γ p.1 p.2) :=
  ((continuous_parameter_trajectory hab hL hγ hdγ hf hinit).comp continuous_fst).eval
    continuous_snd

/-- Terminal data are treated by reversing time. This preserves the actual
right-composition matrix equation when it is used for transported Jacobians. -/
theorem continuous_parameter_terminal_trajectory_joint
    (hf : Continuous (fun p : X × Icc a b × E => f p.1 p.2.1 p.2.2))
    (hterminal : Continuous (fun x => γ x b)) :
    Continuous (fun p : X × Icc a b => γ p.1 p.2) := by
  let T (t : Icc (-b) (-a)) : Icc a b :=
    ⟨-(t : ℝ), le_neg.mp t.2.2, neg_le.mp t.2.1⟩
  have hT : Continuous T := continuous_subtype_val.neg.subtype_mk _
  have hmap : MapsTo Neg.neg (Icc (-b) (-a)) (Icc a b) :=
    fun _ h => ⟨le_neg.mp h.2, neg_le.mp h.1⟩
  have hd (x : X) (u : ℝ) (hu : u ∈ Icc (-b) (-a)) :
      HasDerivWithinAt (fun t => γ x (-t))
        (-f x (-u) (γ x (-u))) (Icc (-b) (-a)) u := by
    convert! HasFDerivWithinAt.comp_hasDerivWithinAt u (hdγ x (-u) (hmap hu))
      (hasDerivAt_neg u).hasDerivWithinAt hmap using 1
    simp
  have hh := continuous_parameter_trajectory_joint (neg_le_neg hab)
    (f := fun x t z => -f x (-t) z) (γ := fun x t => γ x (-t))
    (fun x t ht => (hL x (-t) (hmap ht)).neg)
    (fun x => (hγ x).comp continuousOn_neg hmap) hd
    ((hf.comp (continuous_fst.prodMk
      ((hT.comp continuous_snd.fst).prodMk continuous_snd.snd))).neg)
    (by simpa using hterminal)
  let S (t : Icc a b) : Icc (-b) (-a) :=
    ⟨-(t : ℝ), neg_le_neg t.2.2, neg_le_neg t.2.1⟩
  have hS : Continuous S := continuous_subtype_val.neg.subtype_mk _
  convert hh.comp (continuous_fst.prodMk (hS.comp continuous_snd)) using 1
  funext p
  simp [S]

end OAI.LogConcaveSampling.GlobalODE
