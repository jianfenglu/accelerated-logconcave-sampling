import AcceleratedLogConcave.Numerics.RmsQuadrature
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Inv

/-!
# Regularized singular-kernel value quadrature
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology BigOperators ContDiff
namespace AcceleratedLogConcave.Numerics.SingularKernel

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- The actual regularized second divided difference, including its endpoint. -/
def regularizedValue (f : ℝ → E) (ρ : ℝ) : E :=
  ∫ v : ℝ in 0..1, (1-v) • iteratedDeriv 2 f (v*ρ)

/-- The literal finite value formula, with the source boundary coefficient. -/
def kernelValueRule {ι : Type*} [Fintype ι]
    (f : ℝ → E) (b : ℝ) (z w : ι → ℝ) : E :=
  -(b⁻¹) • f 0 + ∑ j, (w j / (z j)^2) • (f (z j)-f 0)

private theorem integral_one_sub : (∫ v : ℝ in 0..1, (1-v)) = 1/2 := by
  have hc : IntervalIntegrable (fun _ : ℝ => (1:ℝ)) volume 0 1 := intervalIntegrable_const
  have hd : IntervalIntegrable (fun v : ℝ => v) volume 0 1 := continuous_id.intervalIntegrable 0 1
  rw [intervalIntegral.integral_sub hc hd]
  norm_num [integral_id]

@[simp] theorem regularizedValue_zero (f : ℝ → E) :
    regularizedValue f 0 = (1/2:ℝ) • iteratedDeriv 2 f 0 := by
  simp only [regularizedValue, mul_zero]
  rw [intervalIntegral.integral_smul_const, integral_one_sub]

/-- The exact second-order Taylor identity, before division by the physical time. -/
theorem sub_eq_sq_smul_regularizedValue {f : ℝ → E} {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hf : ∀ x ∈ Icc (0:ℝ) ρ, ContDiffAt ℝ 2 f x) (hzero : deriv f 0 = 0) :
    f ρ-f 0 = ρ^2 • regularizedValue f ρ := by
  have hseg (v : ℝ) (hv : v ∈ Icc (0:ℝ) 1) : v*ρ ∈ Icc (0:ℝ) ρ := by
    constructor
    · exact mul_nonneg hv.1 hρ
    · simpa using mul_le_mul_of_nonneg_right hv.2 hρ
  have h := map_add_eq_sum_add_integral_iteratedFDeriv
    (f := f) (x := 0) (y := ρ) (n := 1)
    (fun v hv => hf _ (by simpa [smul_eq_mul] using hseg v hv))
  simp only [zero_add, Nat.factorial_one, Nat.cast_one, inv_one, one_smul,
    Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    Nat.factorial_zero, pow_zero, iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod,
    Fin.prod_const, iteratedDeriv_zero, iteratedDeriv_one,
    hzero, smul_zero, add_zero, pow_one] at h
  change f ρ = f 0 + ∫ v : ℝ in 0..1, (1-v) • (ρ^2 • iteratedDeriv 2 f (v*ρ)) at h
  have hi : (∫ v : ℝ in 0..1, (1-v) • (ρ^2 • iteratedDeriv 2 f (v*ρ))) =
      ρ^2 • regularizedValue f ρ := by
    calc
      _ = ∫ v : ℝ in 0..1, ρ^2 • ((1-v) • iteratedDeriv 2 f (v*ρ)) := by
        apply intervalIntegral.integral_congr
        intro v _
        exact smul_comm (1-v) (ρ^2) _
      _ = _ := by rw [intervalIntegral.integral_smul]; rfl
  rw [hi] at h
  exact sub_eq_iff_eq_add.mpr (by simpa [add_comm] using h)

theorem regularizedValue_eq_div {f : ℝ → E} {ρ : ℝ} (hρ : 0 < ρ)
    (hf : ∀ x ∈ Icc (0:ℝ) ρ, ContDiffAt ℝ 2 f x) (hzero : deriv f 0 = 0) :
    regularizedValue f ρ = (ρ^2)⁻¹ • (f ρ-f 0) := by
  rw [sub_eq_sq_smul_regularizedValue hρ.le hf hzero, smul_smul,
    inv_mul_cancel₀ (pow_ne_zero 2 hρ.ne'), one_smul]


/-- The literal value rule is exactly the ordinary weighted rule on the actual
regularized curve, with the source origin coefficient retained. -/
theorem kernelValueRule_eq_weighted_regularized {ι : Type*} [Fintype ι]
    {f : ℝ → E} (b : ℝ) (z w : ι → ℝ) (hz : ∀ j, 0 < z j)
    (hf : ∀ j, ∀ x ∈ Icc (0:ℝ) (z j), ContDiffAt ℝ 2 f x)
    (hzero : deriv f 0 = 0) :
    kernelValueRule f b z w = -(b⁻¹) • f 0 + ∑ j, w j • regularizedValue f (z j) := by
  unfold kernelValueRule
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [regularizedValue_eq_div (hz j) (hf j) hzero, smul_smul, div_eq_mul_inv]

private def primitive (n : ℕ) (a u : ℝ) : ℝ :=
  -((a+u)^(n+1))⁻¹/(n+1:ℝ) + a*((a+u)^(n+2))⁻¹/(n+2:ℝ)

private theorem primitive_deriv (n : ℕ) {a u : ℝ} (h : 0 < a+u) :
    HasDerivAt (primitive n a) (u/(a+u)^(n+3)) u := by
  have hd := (hasDerivAt_id u).const_add a
  have h1 : (n:ℝ)+1 ≠ 0 := by positivity
  have h2 : (n:ℝ)+2 ≠ 0 := by positivity
  convert ((((hd.pow (n+1)).inv (pow_ne_zero _ h.ne')).neg.div_const ((n:ℝ)+1)).add
    ((((hd.pow (n+2)).inv (pow_ne_zero _ h.ne')).const_mul a).div_const ((n:ℝ)+2))) using 1
  · rfl
  · simp only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, Pi.pow_apply, id_eq,
      show n+1-1=n by omega, show n+2-1=n+1 by omega, mul_one]
    field_simp
    simp only [pow_succ]
    ring

theorem integral_u_div_add_pow_le (m : ℕ) (hm : 1 ≤ m) (a : ℝ) (ha : 0 < a) :
    (∫ u : ℝ in 0..1, u/(a+u)^(m+2)) ≤ (a^m)⁻¹/((m:ℝ)*(m+1)) := by
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
  have hd (u : ℝ) (hu : u ∈ uIcc (0:ℝ) 1) := primitive_deriv n (a:=a) (u:=u)
    (by rw [uIcc_of_le zero_le_one] at hu; linarith [hu.1])
  have hi : IntervalIntegrable (fun u : ℝ => u/(a+u)^(n+3)) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    apply continuousOn_id.div (by fun_prop)
    intro u hu
    rw [uIcc_of_le zero_le_one] at hu
    exact pow_ne_zero _ (by linarith [hu.1])
  have heq := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi
  change (∫ u : ℝ in 0..1, u/(a+u)^(n+3)) ≤ _
  rw [heq]
  have hzero : primitive n a 0 = -(a^(n+1))⁻¹/(((n:ℝ)+1)*(n+2)) := by
    simp only [primitive, add_zero]
    field_simp
    simp only [pow_succ]
    ring
  have hone : primitive n a 1 ≤ 0 := by
    have hineq : a/(((n:ℝ)+2)*(a+1)^(n+2)) ≤
        1/(((n:ℝ)+1)*(a+1)^(n+1)) := by
      apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
      have hlin : ((n:ℝ)+1)*a ≤ ((n:ℝ)+2)*(a+1) := by nlinarith
      have hmul := mul_le_mul_of_nonneg_right hlin (pow_nonneg (by linarith : 0 ≤ a+1) (n+1))
      rw [pow_succ (a+1) (n+1)]
      nlinarith [hmul]
    have hsub := sub_nonpos.mpr hineq
    convert hsub using 1
    all_goals
      simp [primitive, div_eq_mul_inv, mul_inv_rev]
      ring
  rw [hzero]
  have hh := add_le_add_right hone ((a^(n+1))⁻¹/(((n:ℝ)+1)*(n+2)))
  convert hh using 1
  all_goals
    push_cast
    simp only [pow_succ]
    ring


private theorem mul_mem_interval {l r x v : ℝ} (hl : l < 0) (hr : 0 < r)
    (hx : x ∈ Ioo l r) (hv : v ∈ Icc (0:ℝ) 1) : v*x ∈ Ioo l r := by
  by_cases h : 0 ≤ x
  · have h1 := mul_nonneg hv.1 h
    have h2 := mul_nonneg (sub_nonneg.mpr hv.2) h
    constructor <;> nlinarith [hx.1, hx.2]
  · have h1 := mul_nonpos_of_nonneg_of_nonpos hv.1 (le_of_not_ge h)
    have h2 := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hv.2) (le_of_not_ge h)
    constructor <;> nlinarith [hx.1, hx.2]

omit [CompleteSpace E] in
/-- Local compact domination is derived from actual continuous derivatives. -/
private theorem hasDerivAt_weighted_average {l r ρ : ℝ} (hl : l < 0) (hr : 0 < r) (hρ : ρ ∈ Ioo l r)
    {G H : ℝ → E} {w : ℝ → ℝ}
    (hG : ContinuousOn G (Icc l r)) (hH : ContinuousOn H (Icc l r))
    (hw : ContinuousOn w (Icc (0:ℝ) 1))
    (hd : ∀ x ∈ Ioo l r, HasDerivAt G (H x) x) :
    HasDerivAt (fun x => ∫ v : ℝ in 0..1, w v • G (v*x))
      (∫ v : ℝ in 0..1, (w v*v) • H (v*ρ)) ρ := by
  have hi {F : ℝ → E} (hF : ContinuousOn F (Icc l r))
      {q : ℝ → ℝ} (hq : ContinuousOn q (Icc (0:ℝ) 1))
      (x : ℝ) (hx : x ∈ Ioo l r) :
      IntervalIntegrable (fun v => q v • F (v*x)) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le zero_le_one]
    exact hq.smul (hF.comp (continuous_id.mul_const x).continuousOn
      (fun v hv => (mul_mem_interval hl hr hx hv).1.le |> fun h =>
        ⟨h, (mul_mem_interval hl hr hx hv).2.le⟩))
  obtain ⟨M,hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hH
  have hwv : ContinuousOn (fun v => w v*v) (Icc (0:ℝ) 1) := hw.mul continuousOn_id
  refine (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F' := fun x v => (w v*v) • H (v*x))
    (bound := fun v => ‖w v‖*‖v‖*M)
    (Ioo_mem_nhds hρ.1 hρ.2) ?_ (hi hG hw ρ hρ) ?_ ?_ ?_ ?_).2
  · filter_upwards [Ioo_mem_nhds hρ.1 hρ.2] with x hx
    exact (intervalIntegrable_iff.mp (hi hG hw x hx)).aestronglyMeasurable
  · exact (intervalIntegrable_iff.mp (hi hH hwv ρ hρ)).aestronglyMeasurable
  · filter_upwards [] with v hv x hx
    rw [uIoc_of_le zero_le_one] at hv
    rw [norm_smul, norm_mul]
    exact mul_le_mul_of_nonneg_left
      (hM (v*x) ⟨(mul_mem_interval hl hr hx ⟨hv.1.le,hv.2⟩).1.le,
        (mul_mem_interval hl hr hx ⟨hv.1.le,hv.2⟩).2.le⟩)
      (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  · apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le zero_le_one]
    exact (hw.norm.mul continuousOn_id.norm).mul_const M
  · filter_upwards [] with v hv x hx
    rw [uIoc_of_le zero_le_one] at hv
    convert ((hd (v*x) (mul_mem_interval hl hr hx ⟨hv.1.le,hv.2⟩)).scomp x
      ((hasDerivAt_id x).const_mul v)).const_smul (w v) using 1
    · funext y
      rfl
    · simp only [mul_one, smul_smul]


omit [CompleteSpace E] in
private theorem continuousAt_weighted_average {l r ρ : ℝ} (hl : l < 0) (hr : 0 < r)
    (hρ : ρ ∈ Ioo l r) {G : ℝ → E} {w : ℝ → ℝ}
    (hG : ContinuousOn G (Icc l r)) (hw : ContinuousOn w (Icc (0:ℝ) 1)) :
    ContinuousAt (fun x => ∫ v : ℝ in 0..1, w v • G (v*x)) ρ := by
  obtain ⟨M,hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hG
  have hi (x : ℝ) (hx : x ∈ Ioo l r) :
      IntervalIntegrable (fun v => w v • G (v*x)) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le zero_le_one]
    exact hw.smul (hG.comp (continuous_id.mul_const x).continuousOn
      (fun v hv => ⟨(mul_mem_interval hl hr hx hv).1.le,
        (mul_mem_interval hl hr hx hv).2.le⟩))
  refine intervalIntegral.continuousAt_of_dominated_interval
    (bound := fun v => ‖w v‖*M) ?_ ?_ ?_ ?_
  · filter_upwards [Ioo_mem_nhds hρ.1 hρ.2] with x hx
    exact (intervalIntegrable_iff.mp (hi x hx)).aestronglyMeasurable
  · filter_upwards [Ioo_mem_nhds hρ.1 hρ.2] with x hx
    filter_upwards [] with v hv
    rw [uIoc_of_le zero_le_one] at hv
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left
      (hM (v*x) ⟨(mul_mem_interval hl hr hx ⟨hv.1.le,hv.2⟩).1.le,
        (mul_mem_interval hl hr hx ⟨hv.1.le,hv.2⟩).2.le⟩) (norm_nonneg _)
  · apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le zero_le_one]
    exact hw.norm.mul_const M
  · filter_upwards [] with v hv
    rw [uIoc_of_le zero_le_one] at hv
    have ht := mul_mem_interval hl hr hρ ⟨hv.1.le,hv.2⟩
    exact (hG.continuousAt (Icc_mem_nhds ht.1 ht.2)).comp
      (continuousAt_id.const_mul v) |>.const_smul (w v)


omit [CompleteSpace E] in
section

private def weightedAverage (w : ℝ → ℝ) (G : ℝ → E) (x : ℝ) : E :=
  ∫ v : ℝ in 0..1, w v • G (v*x)

private theorem inner_interval {l r ρ : ℝ} (hl : l < 0) (hr : 0 < r)
    (hρ : ρ ∈ Ioo l r) :
    ∃ L R, l < L ∧ L < 0 ∧ 0 < R ∧ R < r ∧ ρ ∈ Ioo L R := by
  obtain ⟨L,hL1,hL2⟩ := exists_between (lt_min hρ.1 hl)
  obtain ⟨R,hR1,hR2⟩ := exists_between (max_lt hρ.2 hr)
  exact ⟨L,R,hL1,(lt_min_iff.mp hL2).2,(max_lt_iff.mp hR1).2,hR2,
    (lt_min_iff.mp hL2).1,(max_lt_iff.mp hR1).1⟩

private theorem continuousOn_weightedAverage {l r : ℝ} (hl : l < 0) (hr : 0 < r)
    {G : ℝ → E} {w : ℝ → ℝ} (hG : ContinuousOn G (Ioo l r))
    (hw : ContinuousOn w (Icc (0:ℝ) 1)) :
    ContinuousOn (weightedAverage w G) (Ioo l r) := by
  intro ρ hρ
  obtain ⟨L,R,hlL,hL,hR,hRr,hρ'⟩ := inner_interval hl hr hρ
  have hsub : Icc L R ⊆ Ioo l r := fun x hx => ⟨hlL.trans_le hx.1,hx.2.trans_lt hRr⟩
  exact (continuousAt_weighted_average hL hR hρ' (hG.mono hsub) hw).continuousWithinAt

private theorem hasDerivAt_weightedAverage {l r ρ : ℝ} (hl : l < 0) (hr : 0 < r)
    (hρ : ρ ∈ Ioo l r) {G : ℝ → E} {w : ℝ → ℝ}
    (hG : ContDiffOn ℝ 1 G (Ioo l r)) (hw : ContinuousOn w (Icc (0:ℝ) 1)) :
    HasDerivAt (weightedAverage w G) (weightedAverage (fun v => w v*v) (deriv G) ρ) ρ := by
  obtain ⟨L,R,hlL,hL,hR,hRr,hρ'⟩ := inner_interval hl hr hρ
  have hsub : Icc L R ⊆ Ioo l r := fun x hx => ⟨hlL.trans_le hx.1,hx.2.trans_lt hRr⟩
  apply hasDerivAt_weighted_average hL hR hρ' (hG.continuousOn.mono hsub)
    ((hG.continuousOn_deriv_of_isOpen isOpen_Ioo (by norm_num)).mono hsub) hw
  intro x hx
  exact ((hG.contDiffAt (isOpen_Ioo.mem_nhds (hsub ⟨hx.1.le,hx.2.le⟩))).differentiableAt
    (by norm_num)).hasDerivAt

private theorem contDiffOn_weightedAverage (n : ℕ) {l r : ℝ} (hl : l < 0) (hr : 0 < r)
    {G : ℝ → E} {w : ℝ → ℝ} (hG : ContDiffOn ℝ n G (Ioo l r))
    (hw : ContinuousOn w (Icc (0:ℝ) 1)) :
    ContDiffOn ℝ n (weightedAverage w G) (Ioo l r) := by
  induction n generalizing G w with
  | zero => exact contDiffOn_zero.mpr (continuousOn_weightedAverage hl hr hG.continuousOn hw)
  | succ n ih =>
    have h1 : ContDiffOn ℝ 1 G (Ioo l r) := hG.of_le (by simp)
    have hd (x : ℝ) (hx : x ∈ Ioo l r) := hasDerivAt_weightedAverage hl hr hx h1 hw
    rw [show ((n+1:ℕ):ℕ∞ω) = (n:ℕ∞ω)+1 by simp,
      contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioo]
    refine ⟨fun x hx => (hd x hx).differentiableAt.differentiableWithinAt, ?_, ?_⟩
    · intro h; simp at h
    · have hc := ih (G := deriv G) (w := fun v => w v*v) (hG.deriv_of_isOpen isOpen_Ioo (by simp)) (hw.mul continuousOn_id)
      exact hc.congr (fun x hx => (hd x hx).deriv)

private theorem iteratedDeriv_weightedAverage (n : ℕ) {l r ρ : ℝ} (hl : l < 0) (hr : 0 < r)
    (hρ : ρ ∈ Ioo l r) {G : ℝ → E} {w : ℝ → ℝ}
    (hG : ContDiffOn ℝ n G (Ioo l r)) (hw : ContinuousOn w (Icc (0:ℝ) 1)) :
    iteratedDeriv n (weightedAverage w G) ρ =
      ∫ v : ℝ in 0..1, (w v*v^n) • iteratedDeriv n G (v*ρ) := by
  induction n generalizing G w with
  | zero => simp [weightedAverage]
  | succ n ih =>
    have h1 : ContDiffOn ℝ 1 G (Ioo l r) := hG.of_le (by simp)
    have he : deriv (weightedAverage w G) =ᶠ[𝓝 ρ]
        weightedAverage (fun v => w v*v) (deriv G) := by
      filter_upwards [isOpen_Ioo.mem_nhds hρ] with x hx
      exact (hasDerivAt_weightedAverage hl hr hx h1 hw).deriv
    rw [iteratedDeriv_succ', he.iteratedDeriv_eq n,
      ih (G := deriv G) (w := fun v => w v*v) (hG.deriv_of_isOpen isOpen_Ioo (by simp)) (hw.mul continuousOn_id)]
    simp only [iteratedDeriv_succ']
    apply intervalIntegral.integral_congr
    intro v _
    dsimp only
    congr 1
    rw [pow_succ]
    ring

end


omit [CompleteSpace E] in
private theorem iteratedDeriv_comp_order (n k : ℕ) (f : ℝ → E) :
    iteratedDeriv n (iteratedDeriv k f) = iteratedDeriv (n+k) f := by
  simp only [iteratedDeriv_eq_iterate, Function.iterate_add_apply]

omit [CompleteSpace E] in
private theorem contDiffOn_second {n : ℕ} {l r : ℝ} {f : ℝ → E}
    (hf : ContDiffOn ℝ (n+2) f (Ioo l r)) :
    ContDiffOn ℝ n (iteratedDeriv 2 f) (Ioo l r) := by
  have h1 : ContDiffOn ℝ (n+1) (deriv f) (Ioo l r) :=
    hf.deriv_of_isOpen isOpen_Ioo (by norm_num [add_assoc])
  have h2 : ContDiffOn ℝ n (deriv (deriv f)) (Ioo l r) :=
    h1.deriv_of_isOpen isOpen_Ioo (by simp)
  simpa only [show 2 = 1+1 from rfl, iteratedDeriv_succ, iteratedDeriv_one, iteratedDeriv_zero] using h2

omit [CompleteSpace E] in
/-- Local regularity is obtained by actual differentiation under the compact integral. -/
theorem contDiffOn_regularizedValue (n : ℕ) {l r : ℝ} (hl : l < 0) (hr : 0 < r)
    {f : ℝ → E} (hf : ContDiffOn ℝ (n+2) f (Ioo l r)) :
    ContDiffOn ℝ n (regularizedValue f) (Ioo l r) := by
  exact contDiffOn_weightedAverage n hl hr (contDiffOn_second hf)
    (continuous_const.sub continuous_id).continuousOn

omit [CompleteSpace E] in
/-- The actual all-order derivative of the regularized curve. -/
theorem iteratedDeriv_regularizedValue (n : ℕ) {l r ρ : ℝ}
    (hl : l < 0) (hr : 0 < r) (hρ : ρ ∈ Ioo l r)
    {f : ℝ → E} (hf : ContDiffOn ℝ (n+2) f (Ioo l r)) :
    iteratedDeriv n (regularizedValue f) ρ =
      ∫ v : ℝ in 0..1, ((1-v)*v^n) • iteratedDeriv (n+2) f (v*ρ) := by
  change iteratedDeriv n (weightedAverage (fun v => 1-v) (iteratedDeriv 2 f)) ρ = _
  rw [iteratedDeriv_weightedAverage n hl hr hρ (w := fun v => 1-v) (contDiffOn_second hf)
    (continuous_const.sub continuous_id).continuousOn, iteratedDeriv_comp_order]

private theorem sub_eq_smul_average_deriv {f : ℝ → E} {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hf : ∀ x ∈ Icc (0:ℝ) ρ, ContDiffAt ℝ 1 f x) :
    f ρ-f 0 = ρ • weightedAverage (fun _ => 1) (deriv f) ρ := by
  have hseg (v : ℝ) (hv : v ∈ Icc (0:ℝ) 1) : v*ρ ∈ Icc (0:ℝ) ρ :=
    ⟨mul_nonneg hv.1 hρ, by simpa using mul_le_mul_of_nonneg_right hv.2 hρ⟩
  have h := map_add_eq_sum_add_integral_iteratedFDeriv
    (f := f) (x := 0) (y := ρ) (n := 0)
    (fun v hv => hf _ (by simpa [smul_eq_mul] using hseg v hv))
  simp only [zero_add, Nat.factorial_zero, Nat.cast_one, inv_one, one_smul,
    Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero,
    iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod, Fin.prod_const,
    iteratedDeriv_zero, iteratedDeriv_one, pow_one] at h
  rw [intervalIntegral.integral_smul] at h
  simpa [weightedAverage, one_smul, eq_comm, sub_eq_iff_eq_add, add_comm] using h

theorem kernel_value_identity_general {l r b : ℝ} (hl : l < 0) (hb : 0 < b) (hbr : b < r)
    {f : ℝ → E} (hf : ContDiffOn ℝ 2 f (Ioo l r)) (hf0 : deriv f 0 = 0) :
    IntervalIntegrable (fun x => x⁻¹ • deriv f x) volume 0 b ∧
      (∫ x : ℝ in 0..b, x⁻¹ • deriv f x) =
        b⁻¹ • (f b-f 0) + ∫ x : ℝ in 0..b, regularizedValue f x := by
  have hr : 0 < r := hb.trans hbr
  have hsub : Icc (0:ℝ) b ⊆ Ioo l r := fun x hx => ⟨hl.trans_le hx.1,hx.2.trans_lt hbr⟩
  have hdf : ContDiffOn ℝ 1 (deriv f) (Ioo l r) := hf.deriv_of_isOpen isOpen_Ioo (by norm_num)
  have hd2 : ContinuousOn (iteratedDeriv 2 f) (Ioo l r) := (contDiffOn_second (n := 0) hf).continuousOn
  have htwo : deriv (deriv f) = iteratedDeriv 2 f := by
    simp only [show 2 = 1+1 from rfl, iteratedDeriv_succ, iteratedDeriv_zero]
  let H := weightedAverage (fun _ : ℝ => 1) (deriv f)
  let K := weightedAverage (fun _ : ℝ => 1) (iteratedDeriv 2 f)
  let D := weightedAverage (fun v : ℝ => v) (iteratedDeriv 2 f)
  have hcK : ContinuousOn K (Ioo l r) := continuousOn_weightedAverage hl hr hd2 continuousOn_const
  have hcD : ContinuousOn D (Ioo l r) := continuousOn_weightedAverage hl hr hd2 continuousOn_id
  have hcG : ContinuousOn (regularizedValue f) (Ioo l r) :=
    (contDiffOn_regularizedValue 0 hl hr hf).continuousOn
  have hiK : IntervalIntegrable K volume 0 b :=
    ContinuousOn.intervalIntegrable (by simpa only [uIcc_of_le hb.le] using hcK.mono hsub)
  have hiD : IntervalIntegrable D volume 0 b :=
    ContinuousOn.intervalIntegrable (by simpa only [uIcc_of_le hb.le] using hcD.mono hsub)
  have hiG : IntervalIntegrable (regularizedValue f) volume 0 b :=
    ContinuousOn.intervalIntegrable (by simpa only [uIcc_of_le hb.le] using hcG.mono hsub)
  have he (x : ℝ) (hx : x ∈ Icc (0:ℝ) b) : K x = D x + regularizedValue f x := by
    have hmul : ContinuousOn (fun v : ℝ => iteratedDeriv 2 f (v*x)) (Icc (0:ℝ) 1) := by
      apply hd2.comp (continuous_id.mul_const x).continuousOn
      intro v hv
      exact hsub ⟨mul_nonneg hv.1 hx.1, (mul_le_mul_of_nonneg_right hv.2 hx.1).trans (by simpa using hx.2)⟩
    have hi1 : IntervalIntegrable (fun v : ℝ => v • iteratedDeriv 2 f (v*x)) volume 0 1 :=
      ContinuousOn.intervalIntegrable (by simpa only [uIcc_of_le zero_le_one] using (show ContinuousOn (fun v => v • iteratedDeriv 2 f (v*x)) (Icc (0:ℝ) 1) from continuousOn_id.smul hmul))
    have hi2 : IntervalIntegrable (fun v : ℝ => (1-v) • iteratedDeriv 2 f (v*x)) volume 0 1 :=
      ContinuousOn.intervalIntegrable (by simpa only [uIcc_of_le zero_le_one] using
        (show ContinuousOn (fun v => (1-v) • iteratedDeriv 2 f (v*x)) (Icc (0:ℝ) 1) from (continuousOn_const.sub continuousOn_id).smul hmul))
    dsimp only [K,D,weightedAverage,regularizedValue]
    rw [← intervalIntegral.integral_add hi1 hi2]
    apply intervalIntegral.integral_congr
    intro v _
    simp only [← add_smul, add_sub_cancel, one_smul]
  have hHD (x : ℝ) (hx : x ∈ uIcc (0:ℝ) b) : HasDerivAt H (D x) x := by
    rw [uIcc_of_le hb.le] at hx
    simpa only [one_mul, htwo] using hasDerivAt_weightedAverage hl hr (hsub hx)
      (w := fun _ : ℝ => 1) hdf continuousOn_const
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hHD hiD
  have hHb : H b = b⁻¹ • (f b-f 0) := by
    have hh := sub_eq_smul_average_deriv hb.le (fun x hx =>
      (hf.contDiffAt (isOpen_Ioo.mem_nhds (hsub hx))).of_le (by norm_num))
    rw [hh, smul_smul, inv_mul_cancel₀ hb.ne', one_smul]
  have hH0 : H 0 = 0 := by simp [H,weightedAverage,hf0]
  have heK : ∀ x ∈ Ioo (0:ℝ) b, x⁻¹ • deriv f x = K x := by
    intro x hx
    have hh := sub_eq_smul_average_deriv hx.1.le (f := deriv f) (fun y hy =>
      hdf.contDiffAt (isOpen_Ioo.mem_nhds (hsub ⟨hy.1,hy.2.trans hx.2.le⟩)))
    rw [hf0, sub_zero] at hh
    rw [hh, smul_smul, inv_mul_cancel₀ hx.1.ne', one_smul]
    simp only [htwo]
    rfl
  have hcongr : EqOn (fun x => x⁻¹ • deriv f x) K (uIoo (0:ℝ) b) := by
    rw [uIoo_of_le hb.le]
    exact fun x hx => heK x hx
  refine ⟨(intervalIntegrable_congr_uIoo hcongr).mpr hiK, ?_⟩
  rw [intervalIntegral.integral_congr_uIoo hcongr]
  calc
    (∫ x : ℝ in 0..b, K x) = ∫ x : ℝ in 0..b, D x + regularizedValue f x :=
      intervalIntegral.integral_congr (by
        rw [uIcc_of_le hb.le]
        exact fun x hx => he x hx)
    _ = _ := by rw [intervalIntegral.integral_add hiD hiG,hFTC,hHb,hH0,sub_zero]


private theorem denominator_compare {ρ v : ℝ} (hρ : ρ ∈ Icc (0:ℝ) 1)
    (hv : v ∈ Icc (0:ℝ) 1) :
    (1-ρ^2)+(1-v) ≤ 2*(1-(v*ρ)^2) := by
  have hv2 : v^2 ≤ 1 := by nlinarith [hv.1,hv.2]
  have hvv : v^2 ≤ v := by nlinarith [mul_nonneg hv.1 (sub_nonneg.mpr hv.2)]
  have hr2 : ρ^2 ≤ 1 := by nlinarith [hρ.1,hρ.2]
  have h1 := mul_le_mul_of_nonneg_right hv2 (sq_nonneg ρ)
  have h2 := (mul_le_mul_of_nonneg_left hr2 (sq_nonneg v)).trans (by simpa using hvv)
  nlinarith [sq_nonneg (v*ρ)]

private theorem reciprocal_power_bound (q : ℕ) {A ρ v : ℝ} (hA : 0 ≤ A)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hv : v ∈ Icc (0:ℝ) 1) :
    A/(1-(v*ρ)^2)^q ≤ (2:ℝ)^q*A/((1-ρ^2)+(1-v))^q := by
  have hprod : 0 ≤ v*ρ ∧ v*ρ < 1 :=
    ⟨mul_nonneg hv.1 hρ0, (mul_le_mul_of_nonneg_right hv.2 hρ0).trans_lt (by simpa using hρ1)⟩
  have hd : 0 < 1-(v*ρ)^2 := by nlinarith [hprod.1,hprod.2]
  have hs : 0 < (1-ρ^2)+(1-v) := by nlinarith [hv.2]
  apply (div_le_div_iff₀ (pow_pos hd _) (pow_pos hs _)).mpr
  calc
    A * ((1-ρ^2)+(1-v))^q ≤ A*(2*(1-(v*ρ)^2))^q :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hs.le (denominator_compare ⟨hρ0,hρ1.le⟩ hv) q) hA
    _ = _ := by rw [mul_pow]; ring

omit [CompleteSpace E] in
/-- The compact integral yields the source gain m(m+1), including order one. -/
theorem norm_iteratedDeriv_regularizedValue_le (m : ℕ) (hm : 1 ≤ m) {l r b A ρ : ℝ}
    (hl : l < 0) (hb : 0 < b) (hb1 : b < 1) (hbr : b < r)
    (hA : 0 ≤ A) (hρ : ρ ∈ Icc (0:ℝ) b) {f : ℝ → E}
    (hf : ContDiffOn ℝ (m+2) f (Ioo l r))
    (hD : ∀ t ∈ Icc (0:ℝ) b, ‖iteratedDeriv (m+2) f t‖ ≤ A/(1-t^2)^(m+2)) :
    ‖iteratedDeriv m (regularizedValue f) ρ‖ ≤
      (2:ℝ)^(m+2)*A / ((m:ℝ)*(m+1)*(1-ρ^2)^m) := by
  have hr : 0 < r := hb.trans hbr
  have hρ1 : ρ < 1 := hρ.2.trans_lt hb1
  have ha : 0 < 1-ρ^2 := by nlinarith [hρ.1]
  have hρopen : ρ ∈ Ioo l r := ⟨hl.trans_le hρ.1,hρ.2.trans_lt hbr⟩
  rw [iteratedDeriv_regularizedValue m hl hr hρopen hf]
  have hpoint (v : ℝ) (hv : v ∈ Icc (0:ℝ) 1) :
      ‖((1-v)*v^m) • iteratedDeriv (m+2) f (v*ρ)‖ ≤
        ((2:ℝ)^(m+2)*A) * ((1-v)/((1-ρ^2)+(1-v))^(m+2)) := by
    have hnode : v*ρ ∈ Icc (0:ℝ) b :=
      ⟨mul_nonneg hv.1 hρ.1, (mul_le_mul_of_nonneg_right hv.2 hρ.1).trans (by simpa using hρ.2)⟩
    have hvpow : v^m ≤ 1 := pow_le_one₀ hv.1 hv.2
    have hu : 0 ≤ 1-v := sub_nonneg.mpr hv.2
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hu (pow_nonneg hv.1 _))]
    calc
      (1-v)*v^m*‖iteratedDeriv (m+2) f (v*ρ)‖ ≤ (1-v)*‖iteratedDeriv (m+2) f (v*ρ)‖ :=
        mul_le_mul_of_nonneg_right (by nlinarith) (norm_nonneg _)
      _ ≤ (1-v)*(A/(1-(v*ρ)^2)^(m+2)) := mul_le_mul_of_nonneg_left (hD _ hnode) hu
      _ ≤ (1-v)*((2:ℝ)^(m+2)*A/((1-ρ^2)+(1-v))^(m+2)) :=
        mul_le_mul_of_nonneg_left (reciprocal_power_bound (m+2) hA hρ.1 hρ1 hv) hu
      _ = _ := by ring
  have hi : IntervalIntegrable (fun v : ℝ =>
      ((2:ℝ)^(m+2)*A)*((1-v)/((1-ρ^2)+(1-v))^(m+2))) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le zero_le_one]
    apply continuousOn_const.mul
    apply (continuousOn_const.sub continuousOn_id).div (by fun_prop)
    intro v hv
    exact pow_ne_zero _ (by linarith [hv.2])
  have hn := intervalIntegral.norm_integral_le_of_norm_le zero_le_one
    (by filter_upwards [] with v hv; exact hpoint v ⟨hv.1.le,hv.2⟩) hi
  have he : (∫ v : ℝ in 0..1, (1-v)/((1-ρ^2)+(1-v))^(m+2)) =
      ∫ u : ℝ in 0..1, u/((1-ρ^2)+u)^(m+2) := by
    rw [intervalIntegral.integral_comp_sub_left (fun u : ℝ => u/((1-ρ^2)+u)^(m+2)) 1]
    norm_num
  rw [intervalIntegral.integral_const_mul,he] at hn
  refine hn.trans ((mul_le_mul_of_nonneg_left (integral_u_div_add_pow_le m hm (1-ρ^2) ha)
    (mul_nonneg (pow_nonneg (by norm_num) _) hA)).trans_eq ?_)
  simp only [div_eq_mul_inv, mul_inv_rev]


private theorem cancel_geometric_powers (m : ℕ) (hm : 1 ≤ m)
    {ell h d A : ℝ} (hell : 0 ≤ ell) (_hh : 0 ≤ h) (hd : 0 < d) (hA : 0 ≤ A)
    (hgeom : ell ≤ 2*h*d) :
    2*ell^(m+1)*((2:ℝ)^(m+2)*A/((m:ℝ)*(m+1)*d^m))/(m.factorial:ℝ) ≤
      (2:ℝ)^(2*m+3)*A*ell*h^m/((m:ℝ)*(m+1)*(m.factorial:ℝ)) := by
  have hm0 : (0:ℝ)<m := Nat.cast_pos.mpr (by omega)
  have hc : 0 ≤ 2*ell*(2:ℝ)^(m+2)*A/((m:ℝ)*(m+1)*(m.factorial:ℝ)) := by positivity
  calc
    _ = (2*ell*(2:ℝ)^(m+2)*A/((m:ℝ)*(m+1)*(m.factorial:ℝ)))*(ell/d)^m := by
      rw [div_pow,pow_succ]
      field_simp
    _ ≤ (2*ell*(2:ℝ)^(m+2)*A/((m:ℝ)*(m+1)*(m.factorial:ℝ)))*(2*h)^m :=
      mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (div_nonneg hell hd.le) ((div_le_iff₀ hd).mpr hgeom) m) hc
    _ = _ := by
      rw [mul_pow]
      have hp : (2:ℝ)^(2*m+3) = 2 * 2^(m+2) * 2^m := by
        rw [← pow_succ',← pow_add]
        congr 1
        omega
      rw [hp]
      ring

/-- Oriented or partial rows use the entire physical cell for both Taylor remainders. -/
theorem norm_cell_defect_le (m : ℕ) (hm : 1 ≤ m) {l r b a c A h₀ : ℝ}
    (hl : l < 0) (hb : 0 < b) (hb1 : b < 1) (hbr : b < r)
    (ha : 0 ≤ a) (hac : a < c) (hcb : c ≤ b) (hA : 0 ≤ A) (hh : 0 ≤ h₀)
    (hgeom : c-a ≤ 2*h₀*(1-c^2))
    {f : ℝ → E} (hf : ContDiffOn ℝ (m+2) f (Ioo l r))
    (hD : ∀ t ∈ Icc (0:ℝ) b, ‖iteratedDeriv (m+2) f t‖ ≤ A/(1-t^2)^(m+2))
    {ι : Type*} [Fintype ι] (row : ValueRow ι)
    (hu : row.start ∈ Icc a c) (hv : row.finish ∈ Icc a c)
    (hn : ∀ j, row.node j ∈ Icc a c) (hmass : row.mass ≤ c-a)
    (hex : row.Exact (fun _ => 1) a m) :
    ‖(∫ t : ℝ in row.start..row.finish, regularizedValue f t) - row.evaluate (regularizedValue f)‖ ≤
      (2:ℝ)^(2*m+3)*A*(c-a)*h₀^m/((m:ℝ)*(m+1)*(m.factorial:ℝ)) := by
  have hc0 : 0 ≤ c := ha.trans hac.le
  have hc1 : c < 1 := hcb.trans_lt hb1
  have hden : 0 < 1-c^2 := by nlinarith
  have hm0 : (0:ℝ)<m := Nat.cast_pos.mpr (by omega)
  let D := (2:ℝ)^(m+2)*A/((m:ℝ)*(m+1)*(1-c^2)^m)
  have hD0 : 0 ≤ D := by dsimp [D]; positivity
  have hgSmooth (t : ℝ) (ht : t ∈ Icc a c) : ContDiffAt ℝ m (regularizedValue f) t :=
    (contDiffOn_regularizedValue m hl (hb.trans hbr) hf).contDiffAt
      (isOpen_Ioo.mem_nhds ⟨hl.trans_le (ha.trans ht.1),(ht.2.trans hcb).trans_lt hbr⟩)
  have hgBound (t : ℝ) (ht : t ∈ Icc a c) : ‖iteratedDeriv m (regularizedValue f) t‖ ≤ D := by
    have ht0 := ha.trans ht.1
    have htB := ht.2.trans hcb
    refine (norm_iteratedDeriv_regularizedValue_le m hm hl hb hb1 hbr hA ⟨ht0,htB⟩ hf hD).trans ?_
    apply div_le_div_of_nonneg_left (by positivity) (by positivity : 0 < (m:ℝ)*(m+1)*(1-c^2)^m)
    apply mul_le_mul_of_nonneg_left _ (by positivity : 0 ≤ (m:ℝ)*(m+1))
    exact pow_le_pow_left₀ hden.le (by nlinarith [pow_le_pow_left₀ ht0 ht.2 2]) m
  have hrow := row.norm_defect_le hm hD0 hu hv hn
    (by intro t ht; norm_num : ∀ t ∈ uIcc row.start row.finish, |(1:ℝ)| ≤ 1)
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (1:ℝ)) volume row.start row.finish)
    hmass hex hgSmooth hgBound
  simp only [one_smul] at hrow
  exact hrow.trans (cancel_geometric_powers m hm (sub_nonneg.mpr hac.le) hh hden hA hgeom)

theorem exponential_constant_bound (m : ℕ) (hm : 1 ≤ m) :
    (2:ℝ)^(2*m+3)/((m:ℝ)*(m+1)) ≤ (16:ℝ)^m := by
  have hm0 : (0:ℝ)<m := Nat.cast_pos.mpr (by omega)
  have hm1 : (1:ℝ)≤m := Nat.one_le_cast.mpr hm
  apply (div_le_iff₀ (by positivity : 0 < (m:ℝ)*(m+1))).mpr
  have hp := pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) (show 2*m+3 ≤ 4*m+1 by omega)
  have he : (2:ℝ)^(4*m+1) = 2*16^m := by rw [pow_add,pow_mul]; norm_num; ring
  rw [he] at hp
  have hd2 : (2:ℝ) ≤ (m:ℝ)*(m+1) := by nlinarith
  apply hp.trans
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left hd2 (show (0:ℝ) ≤ 16^m by positivity)


omit [CompleteSpace E] [NormedSpace ℝ E] in
private theorem finite_telescoping {N : ℕ} (q : Fin (N+1) → E) :
    (∑ i : Fin N, (q i.succ-q i.castSucc)) = q (Fin.last N)-q 0 := by
  apply eq_sub_iff_add_eq.mpr
  rw [Finset.sum_sub_distrib]
  calc
    (∑ i : Fin N, q i.succ) - (∑ i : Fin N, q i.castSucc) + q 0 =
      (q 0 + ∑ i : Fin N, q i.succ) - ∑ i : Fin N, q i.castSucc := by abel
    _ = (∑ i : Fin (N+1), q i) - ∑ i : Fin N, q i.castSucc := by rw [Fin.sum_univ_succ]
    _ = _ := by rw [Fin.sum_univ_castSucc]; abel

omit [CompleteSpace E] in
private theorem finite_integral_telescope {N : ℕ} {p : Fin (N+1) → ℝ} {b : ℝ}
    (hp : StrictMono p) (hp0 : p 0 = 0) (hpN : p (Fin.last N) = b)
    {g : ℝ → E} (hg : ContinuousOn g (Icc (0:ℝ) b)) :
    (∑ i : Fin N, ∫ t : ℝ in p i.castSucc..p i.succ, g t) = ∫ t : ℝ in 0..b, g t := by
  have hpB (i : Fin (N+1)) : p i ∈ Icc (0:ℝ) b := by
    constructor
    · rw [←hp0]; exact hp.monotone (Fin.zero_le i)
    · rw [←hpN]; exact hp.monotone (Fin.le_last i)
  have hi (i : Fin (N+1)) : IntervalIntegrable g volume 0 (p i) := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le (hpB i).1]
    exact hg.mono (Icc_subset_Icc le_rfl (hpB i).2)
  calc
    _ = ∑ i : Fin N, ((∫ t : ℝ in 0..p i.succ, g t) - ∫ t : ℝ in 0..p i.castSucc, g t) := by
      apply Finset.sum_congr rfl
      intro i _
      exact (intervalIntegral.integral_interval_sub_left (hi i.succ) (hi i.castSucc)).symm
    _ = _ := by rw [finite_telescoping (fun i => ∫ t : ℝ in 0..p i, g t),hpN,hp0,intervalIntegral.integral_same,sub_zero]

/-- The actual singular integral and the flattened positive-node value rule on a finite partition. -/
theorem norm_kernel_value_defect_le (m : ℕ) (hm : 1 ≤ m) {l r b A h₀ : ℝ}
    (hl : l < 0) (hb : 0 < b) (hb1 : b < 1) (hbr : b < r) (hA : 0 ≤ A) (hh : 0 ≤ h₀)
    {f : ℝ → E} (hf : ContDiffOn ℝ (m+2) f (Ioo l r)) (hf0 : deriv f 0 = 0) (hfb : f b = 0)
    (hD : ∀ t ∈ Icc (0:ℝ) b, ‖iteratedDeriv (m+2) f t‖ ≤ A/(1-t^2)^(m+2))
    {N : ℕ} (p : Fin (N+1) → ℝ) (hp : StrictMono p) (hp0 : p 0 = 0) (hpN : p (Fin.last N) = b)
    {ι : Type*} [Fintype ι] (rows : Fin N → ValueRow ι)
    (hu : ∀ i, (rows i).start = p i.castSucc) (hv : ∀ i, (rows i).finish = p i.succ)
    (hn : ∀ i j, (rows i).node j ∈ Icc (p i.castSucc) (p i.succ))
    (hn0 : ∀ i j, 0 < (rows i).node j)
    (hmass : ∀ i, (rows i).mass ≤ p i.succ-p i.castSucc)
    (hex : ∀ i, (rows i).Exact (fun _ => 1) (p i.castSucc) m)
    (hgeom : ∀ i : Fin N, p i.succ-p i.castSucc ≤ 2*h₀*(1-(p i.succ)^2)) :
    ‖(∫ t : ℝ in 0..b, t⁻¹ • deriv f t) -
        kernelValueRule f b (fun ij : Fin N × ι => (rows ij.1).node ij.2)
          (fun ij => (rows ij.1).weight ij.2)‖ ≤ (16:ℝ)^m*A*h₀^m/(m.factorial:ℝ) := by
  have hpB (i : Fin (N+1)) : p i ∈ Icc (0:ℝ) b := by
    constructor
    · rw [←hp0]; exact hp.monotone (Fin.zero_le i)
    · rw [←hpN]; exact hp.monotone (Fin.le_last i)
  have hsub : Icc (0:ℝ) b ⊆ Ioo l r := fun t ht => ⟨hl.trans_le ht.1,ht.2.trans_lt hbr⟩
  have hf2 : ContDiffOn ℝ 2 f (Ioo l r) := hf.of_le (by norm_cast; omega)
  have hg : ContinuousOn (regularizedValue f) (Icc (0:ℝ) b) :=
    ((contDiffOn_regularizedValue m hl (hb.trans hbr) hf).continuousOn).mono hsub
  have hId := (kernel_value_identity_general hl hb hbr hf2 hf0).2
  have hRule := kernelValueRule_eq_weighted_regularized (f := f) (b := b)
    (z := fun ij : Fin N × ι => (rows ij.1).node ij.2)
    (w := fun ij => (rows ij.1).weight ij.2) (fun ij => hn0 ij.1 ij.2)
    (fun ij t ht => hf2.contDiffAt (isOpen_Ioo.mem_nhds (hsub
      ⟨ht.1,ht.2.trans ((hn ij.1 ij.2).2.trans (hpB ij.1.succ).2)⟩))) hf0
  rw [hId,hfb,zero_sub,smul_neg,hRule]
  simp only [neg_smul]
  rw [add_sub_add_left_eq_sub]
  have htel := finite_integral_telescope hp hp0 hpN hg
  have hsum : (∑ ij : Fin N × ι, (rows ij.1).weight ij.2 • regularizedValue f ((rows ij.1).node ij.2)) =
      ∑ i : Fin N, (rows i).evaluate (regularizedValue f) := by
    rw [Fintype.sum_prod_type]
    rfl
  rw [hsum,←htel,←Finset.sum_sub_distrib]
  let C := (2:ℝ)^(2*m+3)*A*h₀^m/((m:ℝ)*(m+1)*(m.factorial:ℝ))
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hlocal (i : Fin N) :
      ‖(∫ t : ℝ in p i.castSucc..p i.succ, regularizedValue f t) -
        (rows i).evaluate (regularizedValue f)‖ ≤ C*(p i.succ-p i.castSucc) := by
    have hac := hp i.castSucc_lt_succ
    have h := norm_cell_defect_le m hm hl hb hb1 hbr (hpB i.castSucc).1 hac (hpB i.succ).2
      hA hh (hgeom i) hf hD (rows i)
      (by rw [hu]; exact ⟨le_rfl,hac.le⟩) (by rw [hv]; exact ⟨hac.le,le_rfl⟩)
      (hn i) (hmass i) (hex i)
    rw [hu,hv] at h
    convert h using 1; dsimp [C]; ring
  calc
    _ ≤ ∑ i : Fin N, ‖(∫ t : ℝ in p i.castSucc..p i.succ, regularizedValue f t) -
        (rows i).evaluate (regularizedValue f)‖ := norm_sum_le _ _
    _ ≤ ∑ i : Fin N, C*(p i.succ-p i.castSucc) := Finset.sum_le_sum (fun i _ => hlocal i)
    _ = C*b := by rw [←Finset.mul_sum,finite_telescoping,hpN,hp0,sub_zero]
    _ ≤ C := by simpa using mul_le_mul_of_nonneg_left hb1.le hC
    _ ≤ _ := by
      have hc := mul_le_mul_of_nonneg_right (exponential_constant_bound m hm)
        (show 0 ≤ A*h₀^m/(m.factorial:ℝ) by positivity)
      convert hc using 1 <;> simp only [C, div_eq_mul_inv, mul_inv_rev] <;> ring


/-- A deterministic maximum of genuine RMS norms. No norm of a random maximum
or row-count factor is introduced. Local Lp differentiability remains explicit. -/
theorem max_rms_kernel_value_defect_le {Ω J : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (s : Finset J) (hs : s.Nonempty) (m : ℕ) (hm : 1 ≤ m) {l r b A h₀ : ℝ}
    (hl : l < 0) (hb : 0 < b) (hb1 : b < 1) (hbr : b < r) (hA : 0 ≤ A) (hh : 0 ≤ h₀)
    (f : J → ℝ → Lp E 2 μ)
    (hf : ∀ j ∈ s, ContDiffOn ℝ (m+2) (f j) (Ioo l r))
    (hf0 : ∀ j ∈ s, deriv (f j) 0 = 0) (hfb : ∀ j ∈ s, f j b = 0)
    (hD : ∀ j ∈ s, ∀ t ∈ Icc (0:ℝ) b, ‖iteratedDeriv (m+2) (f j) t‖ ≤ A/(1-t^2)^(m+2))
    {N : ℕ} (p : Fin (N+1) → ℝ) (hp : StrictMono p) (hp0 : p 0 = 0) (hpN : p (Fin.last N) = b)
    {ι : Type*} [Fintype ι] (rows : Fin N → ValueRow ι)
    (hu : ∀ i, (rows i).start = p i.castSucc) (hv : ∀ i, (rows i).finish = p i.succ)
    (hn : ∀ i j, (rows i).node j ∈ Icc (p i.castSucc) (p i.succ))
    (hn0 : ∀ i j, 0 < (rows i).node j)
    (hmass : ∀ i, (rows i).mass ≤ p i.succ-p i.castSucc)
    (hex : ∀ i, (rows i).Exact (fun _ => 1) (p i.castSucc) m)
    (hgeom : ∀ i : Fin N, p i.succ-p i.castSucc ≤ 2*h₀*(1-(p i.succ)^2)) :
    s.sup' hs (fun j => ‖(∫ t : ℝ in 0..b, t⁻¹ • deriv (f j) t) -
        kernelValueRule (f j) b (fun ij : Fin N × ι => (rows ij.1).node ij.2)
          (fun ij => (rows ij.1).weight ij.2)‖) ≤ (16:ℝ)^m*A*h₀^m/(m.factorial:ℝ) := by
  apply Finset.sup'_le
  intro j hj
  exact norm_kernel_value_defect_le m hm hl hb hb1 hbr hA hh (hf j hj)
    (hf0 j hj) (hfb j hj) (hD j hj) p hp hp0 hpN rows hu hv hn hn0 hmass hex hgeom

end AcceleratedLogConcave.Numerics.SingularKernel
