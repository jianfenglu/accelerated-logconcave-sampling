import AcceleratedLogConcave.External.OAI.GlobalODE
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-! Higher spatial regularity obtained from compactly cut off tangent fields. -/

noncomputable section
open Set Metric Function
open scoped Topology NNReal ContDiff
namespace AcceleratedLogConcave.Conditional.Transport
open OAI.LogConcaveSampling.GlobalODE

section Autonomous
variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [FiniteDimensional ℝ H]
  {f : H → H} (hf : ContDiff ℝ ∞ f) {K : ℝ≥0} (hK : LipschitzWith K f)
  {a b : ℝ} (hab : a ≤ b)

def autonomousFlow (x : H) : ℝ → H :=
  flow (fun _ _ => hK) (hf.continuous.comp continuous_snd) ⟨a,le_rfl,hab⟩ x

def autonomousLinearization (x : H) : ℝ → H →L[ℝ] H :=
  flowLinearization (f := fun _ => f) (D := fun _ => fderiv ℝ f) hab (hf.continuous.comp continuous_snd) (fun _ _ => hK)
    ((hf.continuous_fderiv (by simp)).comp continuous_snd)
    (fun _ z => (hf.differentiable (by simp) z).hasFDerivAt) x

theorem autonomousFlow_continuous (x : H) : Continuous (autonomousFlow hf hK hab x) :=
  flow_continuous _ _ _ _

theorem autonomousFlow_initial (x : H) : autonomousFlow hf hK hab x a = x :=
  flow_initial _ _ _ _

theorem autonomousFlow_deriv (x : H) {t : ℝ} (ht : t ∈ Icc a b) :
    HasDerivWithinAt (autonomousFlow hf hK hab x)
      (f (autonomousFlow hf hK hab x t)) (Icc a b) t := flow_deriv _ _ _ _ t ht

theorem autonomousLinearization_initial (x : H) :
    autonomousLinearization hf hK hab x a = ContinuousLinearMap.id ℝ H := by
  unfold autonomousLinearization flowLinearization
  exact fundamental_initial _ _ _

theorem autonomousLinearization_continuous (x : H) :
    Continuous (autonomousLinearization hf hK hab x) := by
  unfold autonomousLinearization flowLinearization
  exact fundamental_continuous _ _ _

theorem autonomousLinearization_deriv (x : H) {t : ℝ} (ht : t ∈ Icc a b) :
    HasDerivWithinAt (autonomousLinearization hf hK hab x)
      ((fderiv ℝ f (autonomousFlow hf hK hab x t)).comp
        (autonomousLinearization hf hK hab x t)) (Icc a b) t := by
  unfold autonomousLinearization flowLinearization autonomousFlow
  exact fundamental_deriv _ _ _ t ht

theorem autonomousLinearization_norm_le (x : H) (t : Icc a b) :
    ‖autonomousLinearization hf hK hab x t‖ ≤ Real.exp ((K:ℝ)*|(t:ℝ)-a|) := by
  unfold autonomousLinearization flowLinearization
  exact fundamental_norm_bound _ _ _ t

theorem autonomousFlow_hasFDerivAt (x : H) (t : Icc a b) :
    HasFDerivAt (fun z => autonomousFlow hf hK hab z t)
      (autonomousLinearization hf hK hab x t) x :=
  flow_hasFDerivAt_left (f := fun _ => f) (D := fun _ => fderiv ℝ f) hab (hf.continuous.comp continuous_snd) (fun _ _ => hK)
    ((hf.continuous_fderiv (by simp)).comp continuous_snd)
    (fun _ z => (hf.differentiable (by simp) z).hasFDerivAt) x t

theorem autonomousFlow_lipschitz (t : Icc a b) :
    LipschitzWith ⟨Real.exp ((K:ℝ)*|(t:ℝ)-a|), (Real.exp_pos _).le⟩
      (fun z => autonomousFlow hf hK hab z t) := flow_lipschitz _ _ _ _

/-- On a neighborhood of each initial point, the actual derivative is the
second component of a globally Lipschitz smooth tangent flow. The cutoff is
justified by uniform base-trajectory and fundamental-operator bounds. -/
theorem exists_tangent_cutoff (x : H) (t : Icc a b) :
    ∃ (g : (H × (H →L[ℝ] H)) → (H × (H →L[ℝ] H)))
      (hg : ContDiff ℝ ∞ g) (L : ℝ≥0) (hL : LipschitzWith L g),
      ∀ y ∈ ball x 1,
        fderiv ℝ (fun z => autonomousFlow hf hK hab z t) y =
          (autonomousFlow hg hL hab (y,ContinuousLinearMap.id ℝ H) t).2 := by
  let V := H × (H →L[ℝ] H)
  let F : V → V := fun p => (f p.1,(fderiv ℝ f p.1).comp p.2)
  have hdf : ContDiff ℝ ∞ (fderiv ℝ f) := hf.fderiv_right (by simp)
  have hF : ContDiff ℝ ∞ F :=
    (hf.comp contDiff_fst).prodMk ((hdf.comp contDiff_fst).clm_comp contDiff_snd)
  obtain ⟨A,hA⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (autonomousFlow_continuous hf hK hab x).continuousOn
  let B := Real.exp ((K:ℝ)*(b-a))
  have hB : 0 < B := Real.exp_pos _
  let R := |A|+B+1
  have hR : 0 < R := by dsimp [R]; positivity
  let χ : ContDiffBump (0:V) :=
    {rIn := R, rOut := R+1, rIn_pos := hR, rIn_lt_rOut := by linarith}
  let g : V → V := fun p => χ p • F p
  have hg : ContDiff ℝ ∞ g := χ.contDiff.smul hF
  have hcompact : HasCompactSupport g := χ.hasCompactSupport.smul_right
  obtain ⟨L,hL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hcompact hg (by simp)
  refine ⟨g,hg,L,hL,fun y hy => ?_⟩
  let α : ℝ → V := fun u =>
    (autonomousFlow hf hK hab y u,autonomousLinearization hf hK hab y u)
  have hα : Continuous α := (autonomousFlow_continuous hf hK hab y).prodMk
    (autonomousLinearization_continuous hf hK hab y)
  have hα0 : α a = (y,ContinuousLinearMap.id ℝ H) := by
    simp only [α,autonomousFlow_initial,autonomousLinearization_initial]
  have hExp (u : ℝ) (hu : u ∈ Icc a b) : Real.exp ((K:ℝ)*|u-a|) ≤ B := by
    apply Real.exp_le_exp.mpr
    apply mul_le_mul_of_nonneg_left _ K.coe_nonneg
    rw [abs_of_nonneg (sub_nonneg.mpr hu.1)]
    linarith [hu.2]
  have hnorm (u : ℝ) (hu : u ∈ Icc a b) : ‖α u‖ < R := by
    have hJ := (autonomousLinearization_norm_le hf hK hab y ⟨u,hu⟩).trans (hExp u hu)
    change ‖autonomousLinearization hf hK hab y u‖ ≤ B at hJ
    have hdist := (autonomousFlow_lipschitz hf hK hab ⟨u,hu⟩).dist_le_mul y x
    have hy' : ‖y-x‖ < 1 := by simpa only [mem_ball,dist_eq_norm] using hy
    have hdiff : ‖autonomousFlow hf hK hab y u-autonomousFlow hf hK hab x u‖ ≤ B := by
      simp only [dist_eq_norm] at hdist
      exact hdist.trans ((mul_le_mul (hExp u hu) hy'.le (norm_nonneg _) hB.le).trans_eq (by ring))
    have hbase := norm_add_le
      (autonomousFlow hf hK hab y u-autonomousFlow hf hK hab x u)
      (autonomousFlow hf hK hab x u)
    rw [sub_add_cancel] at hbase
    have hA' := hA u hu
    change max ‖autonomousFlow hf hK hab y u‖ ‖autonomousLinearization hf hK hab y u‖ < R
    apply max_lt_iff.mpr
    constructor <;> dsimp [R] <;> linarith [le_abs_self A,abs_nonneg A]
  have hdα (u : ℝ) (hu : u ∈ Icc a b) :
      HasDerivWithinAt α (g (α u)) (Icc a b) u := by
    have hχ : χ (α u) = 1 := χ.one_of_mem_closedBall
      (by simpa only [mem_closedBall_zero_iff] using (hnorm u hu).le)
    have hgα : g (α u) = F (α u) := by simp only [g,hχ,one_smul]
    rw [hgα]
    exact (autonomousFlow_deriv hf hK hab y hu).prodMk
      (autonomousLinearization_deriv hf hK hab y hu)
  have hh := trajectory_dist (fun _ _ => hL) hα.continuousOn hdα
    (autonomousFlow_continuous hg hL hab (y,ContinuousLinearMap.id ℝ H)).continuousOn
    (fun u hu => autonomousFlow_deriv hg hL hab (y,ContinuousLinearMap.id ℝ H) hu)
    (⟨a,le_rfl,hab⟩ : Icc a b) t
  rw [hα0,autonomousFlow_initial,dist_self,zero_mul,dist_le_zero] at hh
  have hs := congrArg Prod.snd hh
  rw [(autonomousFlow_hasFDerivAt hf hK hab y t).fderiv]
  exact hs

end Autonomous

/-- Smoothness of the actual endpoint map, obtained by induction using the
cutoff tangent representation. The auxiliary tangent field is allowed to
live in any finite-dimensional real normed space, including operator spaces
with their operator norm. -/
theorem contDiff_autonomousFlow_left (n : ℕ) :
    ∀ {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [FiniteDimensional ℝ H]
      {f : H → H} (hf : ContDiff ℝ ∞ f) {K : ℝ≥0} (hK : LipschitzWith K f)
      {a b : ℝ} (hab : a ≤ b) (t : Icc a b),
      ContDiff ℝ n (fun x => autonomousFlow hf hK hab x t) := by
  induction n with
  | zero =>
    intro H _ _ _ f hf K hK a b hab t
    exact contDiff_zero.mpr (autonomousFlow_lipschitz hf hK hab t).continuous
  | succ n ih =>
    intro H _ _ _ f hf K hK a b hab t
    rw [show ((n+1:ℕ) : WithTop ℕ∞) = (n : WithTop ℕ∞)+1 by simp]
    apply contDiff_succ_iff_fderiv.mpr
    refine ⟨fun x => (autonomousFlow_hasFDerivAt hf hK hab x t).differentiableAt, by simp, ?_⟩
    apply contDiff_iff_contDiffAt.mpr
    intro x
    obtain ⟨g,hg,L,hL,heq⟩ := exists_tangent_cutoff hf hK hab x t
    have hcomp : ContDiff ℝ n (fun y : H =>
        (autonomousFlow hg hL hab (y,ContinuousLinearMap.id ℝ H) t).2) :=
      contDiff_snd.comp ((ih hg hL hab t).comp (contDiff_id.prodMk contDiff_const))
    apply hcomp.contDiffAt.congr_of_eventuallyEq
    filter_upwards [Metric.ball_mem_nhds x (by norm_num : (0:ℝ) < 1)] with y hy
    exact heq y hy

theorem contDiff_infty_autonomousFlow_left
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [FiniteDimensional ℝ H]
    {f : H → H} (hf : ContDiff ℝ ∞ f) {K : ℝ≥0} (hK : LipschitzWith K f)
    {a b : ℝ} (hab : a ≤ b) (t : Icc a b) :
    ContDiff ℝ ∞ (fun x => autonomousFlow hf hK hab x t) :=
  contDiff_infty.mpr (fun n => contDiff_autonomousFlow_left n hf hK hab t)

/-- Inverse endpoint maps are smooth because their genuine fundamental
operators are continuous linear equivalences. -/
theorem contDiff_infty_autonomousFlow_reverse
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [FiniteDimensional ℝ H]
    {f : H → H} (hf : ContDiff ℝ ∞ f) {K : ℝ≥0} (hK : LipschitzWith K f)
    {a b : ℝ} (hab : a ≤ b) (t : Icc a b) :
    ContDiff ℝ ∞ (fun x => flow (fun _ _ => hK) (hf.continuous.comp continuous_snd) t x a) := by
  let hc := hf.continuous.comp (continuous_snd : Continuous (Prod.snd : ℝ × H → H))
  let hL : ∀ u ∈ Icc a b, LipschitzWith K ((fun _ => f) u) := fun _ _ => hK
  let D : ℝ → H → H →L[ℝ] H := fun _ => fderiv ℝ f
  have hD : Continuous (uncurry D) := (hf.continuous_fderiv (by simp)).comp continuous_snd
  have hd : ∀ u z, HasFDerivAt ((fun _ => f) u) (D u z) z :=
    fun _ z => (hf.differentiable (by simp) z).hasFDerivAt
  let Hm := flowHomeomorph hL hc ⟨a,le_rfl,hab⟩ t
  let J (x : H) := fundamentalEquiv
    (flowSpatialCoefficient_continuous (f := fun _ => f) (D := D) hab hc hL hD x)
    (flowSpatialCoefficient_bound (f := fun _ => f) (D := D) hab hc hL hd x) ⟨a,le_rfl,hab⟩ t
  have hJ (x : H) : HasFDerivAt Hm (J x : H →L[ℝ] H) x :=
    flow_hasFDerivAt_left (f := fun _ => f) (D := D) hab hc hL hD hd x t
  exact Hm.contDiff_symm hJ (contDiff_infty_autonomousFlow_left hf hK hab t)

/-- Both orientations, and every pair of times, have the proved smoothness. -/
theorem contDiff_infty_autonomousFlow
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [FiniteDimensional ℝ H]
    {f : H → H} (hf : ContDiff ℝ ∞ f) {K : ℝ≥0} (hK : LipschitzWith K f)
    {a b : ℝ} (hab : a ≤ b) (s t : Icc a b) :
    ContDiff ℝ ∞ (fun x => flow (fun _ _ => hK) (hf.continuous.comp continuous_snd) s x t) := by
  have hh := (contDiff_infty_autonomousFlow_left hf hK hab t).comp
    (contDiff_infty_autonomousFlow_reverse hf hK hab s)
  convert hh using 1
  funext x
  exact (flow_cocycle (fun _ _ => hK) (hf.continuous.comp continuous_snd) s
    ⟨a,le_rfl,hab⟩ t x).symm

end AcceleratedLogConcave.Conditional.Transport
