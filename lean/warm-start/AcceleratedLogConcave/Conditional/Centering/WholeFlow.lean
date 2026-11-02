import AcceleratedLogConcave.Conditional.Centering.Complete

/-! A canonical two-sided trajectory for smooth fields with linear growth. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric Filter
open scoped Topology NNReal

namespace AcceleratedLogConcave.Conditional.Centering
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [FiniteDimensional ℝ H]

/-- Compact ranges turn local spatial regularity into a uniform uniqueness
constant. No global Lipschitz hypothesis on the vector field is imposed. -/
theorem trajectory_unique_of_contDiff {f : H → H} (hf : ContDiff ℝ 1 f)
    {α β : ℝ → H} (hα : Continuous α) (hβ : Continuous β) {a b s : ℝ}
    (hs : s ∈ Ioo a b)
    (hdα : ∀ t ∈ Ioo a b, HasDerivAt α (f (α t)) t)
    (hdβ : ∀ t ∈ Ioo a b, HasDerivAt β (f (β t)) t)
    (hinit : α s = β s) : EqOn α β (Ioo a b) := by
  obtain ⟨A, hA⟩ := isCompact_Icc.exists_bound_of_continuousOn hα.continuousOn
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hβ.continuousOn
  let R := max A B
  have hαmem (t : ℝ) (ht : t ∈ Ioo a b) : α t ∈ closedBall 0 R := by
    simpa only [mem_closedBall_zero_iff] using (hA t (mem_Icc_of_Ioo ht)).trans (le_max_left A B)
  have hβmem (t : ℝ) (ht : t ∈ Ioo a b) : β t ∈ closedBall 0 R := by
    simpa only [mem_closedBall_zero_iff] using (hB t (mem_Icc_of_Ioo ht)).trans (le_max_right A B)
  obtain ⟨K, hK⟩ := hf.contDiffOn.exists_lipschitzOnWith (by norm_num : (1 : WithTop ℕ∞) ≠ 0)
    (convex_closedBall (0 : H) R) (isCompact_closedBall (0 : H) R)
  exact ODE_solution_unique_of_mem_Ioo (fun _ _ => hK) hs
    (fun t ht => ⟨hdα t ht, hαmem t ht⟩)
    (fun t ht => ⟨hdβ t ht, hβmem t ht⟩) hinit

/-- A centered finite trajectory, differentiable on the whole open interval,
including the time at which the forward and backward constructions meet. -/
theorem exists_centered_curve {f : H → H} (hf : ContDiff ℝ 1 f)
    {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hgrowth : ∀ z, ‖f z‖ ≤ C * ‖z‖ + D) {T : ℝ} (hT : 0 < T) (x : H) :
    ∃ α : ℝ → H, Continuous α ∧ α 0 = x ∧
      ∀ t ∈ Ioo (-T) T, HasDerivAt α (f (α t)) t := by
  obtain ⟨α, hα, hα0, hdα⟩ := exists_curve_of_contDiff_linear_growth hf hC hD hgrowth hT.le x
  obtain ⟨β, hβ, hβ0, hdβ⟩ := exists_curve_backward_of_contDiff_linear_growth hf hC hD hgrowth
    (a := -T) (b := 0) (by linarith) x
  let Z : ℝ → H := fun t => if t ≤ 0 then β t else α t
  have hZ0 : Z 0 = x := by simp only [Z, le_refl, ite_true, hβ0]
  have hleft : EqOn Z β (Icc (-T) 0) := fun t ht => ite_eq_left ht.2
  have hright : EqOn Z α (Icc 0 T) := by
    intro t ht
    rcases eq_or_lt_of_le ht.1 with he | he
    · subst t; simp only [Z, le_refl, ite_true, hβ0, hα0]
    · exact ite_eq_right (not_le.mpr he)
  refine ⟨Z, Continuous.if_le hβ hα continuous_id continuous_const
    (fun t ht => by change t = 0 at ht; subst t; exact hβ0.trans hα0.symm), hZ0, ?_⟩
  intro t ht
  by_cases ht0 : t = 0
  · subst t
    have hl : HasDerivWithinAt Z (f x) (Icc (-T) 0) 0 := by
      convert! (hdβ 0 ⟨by linarith, le_rfl⟩).congr hleft (hleft ⟨by linarith, le_rfl⟩) using 1
      rw [hβ0]
    have hr : HasDerivWithinAt Z (f x) (Icc 0 T) 0 := by
      convert! (hdα 0 ⟨le_rfl, hT.le⟩).congr hright (hright ⟨le_rfl, hT.le⟩) using 1
      rw [hα0]
    have hu := hl.union hr
    have hUnion : Icc (-T) 0 ∪ Icc 0 T = Icc (-T) T := by
      ext τ
      constructor
      · rintro (h | h) <;> constructor <;> linarith [h.1, h.2]
      · intro h
        by_cases hτ : τ ≤ 0
        · exact Or.inl ⟨h.1, hτ⟩
        · exact Or.inr ⟨(lt_of_not_ge hτ).le, h.2⟩
    rw [hUnion] at hu
    rw [hZ0]
    exact hu.hasDerivAt (Icc_mem_nhds (by linarith) hT)
  · rcases lt_or_gt_of_ne ht0 with hn | hp
    · have he : Z =ᶠ[𝓝 t] β := by
        filter_upwards [Iio_mem_nhds hn] with τ hτ
        exact ite_eq_left hτ.le
      rw [he.eq_of_nhds]
      exact ((hdβ t ⟨ht.1.le, hn.le⟩).hasDerivAt (Icc_mem_nhds ht.1 hn)).congr_of_eventuallyEq he
    · have he : Z =ᶠ[𝓝 t] α := by
        filter_upwards [Ioi_mem_nhds hp] with τ hτ
        exact ite_eq_right (not_le.mpr hτ)
      rw [he.eq_of_nhds]
      exact ((hdα t ⟨hp.le, ht.2.le⟩).hasDerivAt (Icc_mem_nhds hp ht.2)).congr_of_eventuallyEq he

section Canonical
variable {f : H → H} (hf : ContDiff ℝ 1 f)
    {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hgrowth : ∀ z, ‖f z‖ ≤ C * ‖z‖ + D)

/-- The finite trajectory is chosen only after existence is proved. -/
def finiteCurve (T : ℝ) (hT : 0 < T) (x : H) : ℝ → H :=
  (exists_centered_curve hf hC hD hgrowth hT x).choose

theorem finiteCurve_continuous (T : ℝ) (hT : 0 < T) (x : H) :
    Continuous (finiteCurve hf hC hD hgrowth T hT x) :=
  (exists_centered_curve hf hC hD hgrowth hT x).choose_spec.1

theorem finiteCurve_initial (T : ℝ) (hT : 0 < T) (x : H) :
    finiteCurve hf hC hD hgrowth T hT x 0 = x :=
  (exists_centered_curve hf hC hD hgrowth hT x).choose_spec.2.1

theorem finiteCurve_deriv (T : ℝ) (hT : 0 < T) (x : H) {t : ℝ}
    (ht : t ∈ Ioo (-T) T) :
    HasDerivAt (finiteCurve hf hC hD hgrowth T hT x)
      (f (finiteCurve hf hC hD hgrowth T hT x t)) t :=
  (exists_centered_curve hf hC hD hgrowth hT x).choose_spec.2.2 t ht

/-- A single trajectory on all real times, obtained by uniqueness on overlaps. -/
def completeCurve (x : H) (t : ℝ) : H :=
  finiteCurve hf hC hD hgrowth (|t| + 1) (by positivity) x t

/-- The complete trajectory agrees with each finite construction throughout
its interval. This is the gluing argument, rather than a supplied global flow. -/
theorem completeCurve_eq_finiteCurve (T : ℝ) (hT : 0 < T) (x : H) {t : ℝ}
    (ht : |t| < T) :
    completeCurve hf hC hD hgrowth x t = finiteCurve hf hC hD hgrowth T hT x t := by
  let S := min (|t|+1) T
  have hS : 0 < S := lt_min (by positivity) hT
  have hS₁ : S ≤ |t|+1 := min_le_left _ _
  have hS₂ : S ≤ T := min_le_right _ _
  have hrestrict₁ : Ioo (-S) S ⊆ Ioo (-(|t|+1)) (|t|+1) :=
    fun τ hτ => ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
  have hrestrict₂ : Ioo (-S) S ⊆ Ioo (-T) T :=
    fun τ hτ => ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
  have huniq := trajectory_unique_of_contDiff hf
    (finiteCurve_continuous hf hC hD hgrowth (|t|+1) (by positivity) x)
    (finiteCurve_continuous hf hC hD hgrowth T hT x)
    (s := 0) (a := -S) (b := S) ⟨by linarith, hS⟩
    (fun τ hτ => finiteCurve_deriv hf hC hD hgrowth _ _ x (hrestrict₁ hτ))
    (fun τ hτ => finiteCurve_deriv hf hC hD hgrowth _ _ x (hrestrict₂ hτ))
    (by rw [finiteCurve_initial, finiteCurve_initial])
  apply huniq
  have hst : |t| < S := lt_min (by linarith) ht
  exact ⟨(neg_lt_of_abs_lt hst), lt_of_abs_lt hst⟩

/-- The glued trajectory solves the original ODE at every real time. -/
theorem completeCurve_deriv (x : H) (t : ℝ) :
    HasDerivAt (completeCurve hf hC hD hgrowth x)
      (f (completeCurve hf hC hD hgrowth x t)) t := by
  let T := |t|+1
  have hT : 0 < T := by dsimp [T]; positivity
  have ht : |t| < T := by dsimp [T]; linarith
  have he : completeCurve hf hC hD hgrowth x =ᶠ[𝓝 t]
      finiteCurve hf hC hD hgrowth T hT x := by
    filter_upwards [(isOpen_lt continuous_abs continuous_const).mem_nhds ht] with τ hτ
    exact completeCurve_eq_finiteCurve hf hC hD hgrowth T hT x hτ
  rw [he.eq_of_nhds]
  exact (finiteCurve_deriv hf hC hD hgrowth T hT x
    ⟨neg_lt_of_abs_lt ht, lt_of_abs_lt ht⟩).congr_of_eventuallyEq he

theorem completeCurve_continuous (x : H) :
    Continuous (completeCurve hf hC hD hgrowth x) :=
  continuous_iff_continuousAt.mpr fun t => (completeCurve_deriv hf hC hD hgrowth x t).continuousAt

theorem completeCurve_initial (x : H) : completeCurve hf hC hD hgrowth x 0 = x := by
  exact finiteCurve_initial hf hC hD hgrowth _ _ x

/-- Time translation is compatible with the autonomous flow, by local uniqueness. -/
theorem completeCurve_add (x : H) (s t : ℝ) :
    completeCurve hf hC hD hgrowth (completeCurve hf hC hD hgrowth x s) t =
      completeCurve hf hC hD hgrowth x (s+t) := by
  let T := |t|+1
  have hT : 0 < T := by dsimp [T]; positivity
  let α := completeCurve hf hC hD hgrowth (completeCurve hf hC hD hgrowth x s)
  let β := fun τ => completeCurve hf hC hD hgrowth x (s+τ)
  have hdβ (τ : ℝ) : HasDerivAt β (f (β τ)) τ := by
    convert! (completeCurve_deriv hf hC hD hgrowth x (s+τ)).hasFDerivAt.comp_hasDerivAt τ
      ((hasDerivAt_id τ).const_add s) using 1
    simp [β]
  have huniq := trajectory_unique_of_contDiff hf (α := α) (β := β)
    (completeCurve_continuous hf hC hD hgrowth _)
    ((completeCurve_continuous hf hC hD hgrowth x).comp (continuous_const.add continuous_id))
    (a := -T) (b := T) (s := 0) ⟨by linarith, hT⟩
    (fun τ _ => completeCurve_deriv hf hC hD hgrowth _ τ)
    (fun τ _ => hdβ τ)
    (by simp [α, β, completeCurve_initial])
  apply huniq
  constructor <;> dsimp [T] <;> linarith [le_abs_self t, neg_abs_le t]

/-- Reversing time gives the inverse map, with no additional growth hypothesis. -/
theorem completeCurve_inverse (x : H) (t : ℝ) :
    completeCurve hf hC hD hgrowth (completeCurve hf hC hD hgrowth x t) (-t) = x := by
  rw [completeCurve_add, add_neg_cancel, completeCurve_initial]

/-- A uniform Grönwall estimate on a positive horizon, permitting a larger
initial norm bound for use in spatial neighborhoods. -/
theorem completeCurve_norm_bound {δ : ℝ} (hδ : 0 ≤ δ) {x : H} (hx : ‖x‖ ≤ δ)
    {T : ℝ} (_hT : 0 ≤ T) {t : ℝ} (ht : |t| ≤ T) :
    ‖completeCurve hf hC hD hgrowth x t‖ ≤ gronwallBound δ C D T := by
  let α := completeCurve hf hC hD hgrowth x
  have hα := completeCurve_continuous hf hC hD hgrowth x
  have hα0 : ‖α 0‖ ≤ δ := by simpa only [α, completeCurve_initial] using hx
  by_cases ht0 : 0 ≤ t
  · have hh := norm_le_gronwallBound_of_norm_deriv_right_le
      (hα.continuousOn : ContinuousOn α (Icc 0 T))
      (fun τ _ => (completeCurve_deriv hf hC hD hgrowth x τ).hasDerivWithinAt)
      hα0 (fun τ _ => hgrowth (α τ)) t
      ⟨ht0, (le_abs_self t).trans ht⟩
    exact hh.trans (gronwallBound_mono hδ hD hC (by simpa only [sub_zero] using (le_abs_self t).trans ht))
  · have hβ : Continuous (fun τ => α (-τ)) := hα.comp continuous_neg
    have hdβ (τ : ℝ) : HasDerivAt (fun v => α (-v)) (-f (α (-τ))) τ := by
      convert! (completeCurve_deriv hf hC hD hgrowth x (-τ)).hasFDerivAt.comp_hasDerivAt τ
        (hasDerivAt_neg τ) using 1
      simp [α]
    have hh := norm_le_gronwallBound_of_norm_deriv_right_le
      (hβ.continuousOn : ContinuousOn (fun τ => α (-τ)) (Icc 0 T))
      (fun τ _ => (hdβ τ).hasDerivWithinAt) (by simpa using hα0)
      (fun τ _ => by simpa only [norm_neg] using hgrowth (α (-τ))) (-t)
      ⟨by linarith, (neg_le_abs t).trans ht⟩
    simp only [neg_neg, sub_zero] at hh
    exact hh.trans (gronwallBound_mono hδ hD hC (by simpa only [sub_zero] using (neg_le_abs t).trans ht))

end Canonical

end AcceleratedLogConcave.Conditional.Centering
