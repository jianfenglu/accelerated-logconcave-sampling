import AcceleratedLogConcave.Conditional.Transport.SmoothFlow
import AcceleratedLogConcave.Conditional.Transport.TimeClamp
import AcceleratedLogConcave.Conditional.Stein.Transport

/-! Smooth local representatives uniform in both transport endpoints. -/
set_option maxHeartbeats 300000
noncomputable section
open Set Metric Function
open scoped Topology ContDiff NNReal
namespace AcceleratedLogConcave.Conditional.Transport
open OAI.LogConcaveSampling.GlobalODE

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- A globally smooth representative agrees locally in space with every
actual transport between two times of the interval, simultaneously. This
also gives continuous spatial derivatives of every order at time endpoints. -/
theorem exists_smooth_convexProbabilityFlow_extension_ball {F : E → ℝ} (hF : ContDiff ℝ 2 F)
    {ell : ℝ} (hell : 0 ≤ ell)
    (hlo : ∀ z a, 0 ≤ fderiv ℝ (fderiv ℝ F) z a a)
    (hup : ∀ z a, fderiv ℝ (fderiv ℝ F) z a a ≤ ell * ‖a‖ ^ 2)
    (x : E) {r : ℝ} (hr : 0 < r) {b : ℝ} (hb : 0 ≤ b) (hb1 : b < 1)
    (hsmall : r^2*ell ≤ 1/2) (z : E) {ε : ℝ} (hε : 0 < ε) :
    ∃ S : (ℝ × ℝ) × E → E, ContDiff ℝ ∞ S ∧
      ∀ s t : Icc 0 b, ∀ y ∈ ball z ε,
        S (((s:ℝ),(t:ℝ)),y) =
          convexProbabilityFlow hF hell hlo hup x hr hb (by norm_num) hb1 s y t := by
  let Z := convexProbabilityFlow hF hell hlo hup x hr hb (by norm_num) hb1
    (⟨0,le_rfl,hb⟩ : Icc 0 b) (0:E)
  have hZc : Continuous Z := probabilityFlow_continuous hb F x r
    (continuousOn_conditionalMean hF hlo hup x r (by norm_num) hb1)
    (fun _ ht => lipschitzWith_conditionalMean hF hell hlo hup x hr
      (by linarith [ht.1]) (ht.2.trans_lt hb1)) ⟨0,le_rfl,hb⟩ (0:E)
  obtain ⟨A,hA⟩ := isCompact_Icc.exists_bound_of_continuousOn hZc.continuousOn
  have hZ (u : ℝ) (hu : u ∈ Icc 0 b) : ‖Z u‖ ≤ |A| := (hA u hu).trans (le_abs_self A)
  obtain ⟨ψ,hψ,hψrange,hψeq⟩ := exists_smooth_timeClamp hb (by norm_num) hb1
  have hC : ContDiff ℝ ∞ (fun p : ℝ × E => (ψ p.1,p.2)) :=
    (hψ.comp contDiff_fst).prodMk contDiff_snd
  have hms := (contDiffOn_conditionalMean hF hlo hup x r).comp_contDiff hC
    (fun p => hψrange p.1)
  have hM : ContDiff ℝ ∞ (fun p : ℝ × E => conditionalMean F x r (ψ p.1) p.2) := by
    exact hms
  have hv : ContDiff ℝ ∞ (fun p : ℝ × E => probabilityVelocity F x r (ψ p.1) p.2) :=
    hM.const_smul (-r)
  let H := (ℝ × ℝ) × (ℝ × E)
  let V : H → H := fun p => (0,(p.1.2-p.1.1,
    (p.1.2-p.1.1) • probabilityVelocity F x r (ψ p.2.1) p.2.2))
  have hΔ : ContDiff ℝ ∞ (fun p : H => p.1.2-p.1.1) := contDiff_fst.snd.sub contDiff_fst.fst
  have hV : ContDiff ℝ ∞ V :=
    contDiff_const.prodMk (hΔ.prodMk (hΔ.smul (hv.comp contDiff_snd)))
  let M := ‖z‖+ε+|A|
  have hMpos : 0 < M := by dsimp [M]; positivity
  let R := Real.exp 1*M+|A|+|b|+1
  have hR : 0 < R := by dsimp [R]; positivity
  let χ : ContDiffBump (0:H) :=
    {rIn := R,rOut := R+1,rIn_pos := hR,rIn_lt_rOut := by linarith}
  let g : H → H := fun p => χ p • V p
  have hg : ContDiff ℝ ∞ g := χ.contDiff.smul hV
  have hcompact : HasCompactSupport g := χ.hasCompactSupport.smul_right
  obtain ⟨L,hL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hcompact hg (by simp)
  let S : (ℝ × ℝ) × E → E := fun p =>
    (autonomousFlow hg hL (show (0:ℝ) ≤ 1 by norm_num)
      (p.1,(p.1.1,p.2)) 1).2.2
  have hS : ContDiff ℝ ∞ S :=
    contDiff_snd.comp (contDiff_snd.comp
      ((contDiff_infty_autonomousFlow_left hg hL (by norm_num : (0:ℝ) ≤ 1)
        ⟨1,by norm_num,le_rfl⟩).comp
        (contDiff_fst.prodMk (contDiff_fst.fst.prodMk contDiff_snd))))
  refine ⟨S,hS,fun s t y hy => ?_⟩
  let X := convexProbabilityFlow hF hell hlo hup x hr hb (by norm_num) hb1 s y
  have hXc : Continuous X := probabilityFlow_continuous hb F x r
    (continuousOn_conditionalMean hF hlo hup x r (by norm_num) hb1)
    (fun _ ht => lipschitzWith_conditionalMean hF hell hlo hup x hr
      (by linarith [ht.1]) (ht.2.trans_lt hb1)) s y
  let u : ℝ → ℝ := fun τ => (s:ℝ)+τ*((t:ℝ)-(s:ℝ))
  have hu (τ : ℝ) (hτ : τ ∈ Icc (0:ℝ) 1) : u τ ∈ Icc 0 b := by
    have hlo1 := mul_nonneg (sub_nonneg.mpr hτ.2) s.2.1
    have hlo2 := mul_nonneg hτ.1 t.2.1
    have hup1 := mul_nonneg (sub_nonneg.mpr hτ.2) (sub_nonneg.mpr s.2.2)
    have hup2 := mul_nonneg hτ.1 (sub_nonneg.mpr t.2.2)
    dsimp [u]
    constructor <;> nlinarith

  let α : ℝ → H := fun τ => (((s:ℝ),(t:ℝ)),(u τ,X (u τ)))
  have huc : Continuous u := by dsimp [u]; fun_prop
  have hα : Continuous α := continuous_const.prodMk (huc.prodMk (hXc.comp huc))
  have hα0 : α 0 = (((s:ℝ),(t:ℝ)),((s:ℝ),y)) := by
    dsimp [α,u,X]
    simp only [zero_mul,add_zero,convexProbabilityFlow_initial]
  have hnorm (τ : ℝ) (hτ : τ ∈ Icc (0:ℝ) 1) : ‖α τ‖ < R := by
    have hut := hu τ hτ
    have hdist := (lipschitzWith_convexProbabilityFlow_exp_one hF hell hlo hup x hr hb hb1
      hsmall s ⟨u τ,hut⟩).dist_le_mul y (Z s)
    have hcoc := convexProbabilityFlow_cocycle hF hell hlo hup x hr hb (by norm_num) hb1
      (⟨0,le_rfl,hb⟩ : Icc 0 b) s ⟨u τ,hut⟩ (0:E)
    change convexProbabilityFlow hF hell hlo hup x hr hb (by norm_num) hb1 s (Z s) (u τ) = Z (u τ) at hcoc
    rw [hcoc] at hdist
    have hyy : ‖y‖ ≤ ‖z‖+ε := by
      have hh := norm_le_norm_sub_add y z
      have hy' : ‖y-z‖ < ε := by simpa only [mem_ball,dist_eq_norm] using hy
      linarith
    have hdiff : ‖X (u τ)-Z (u τ)‖ ≤ Real.exp 1*M := by
      simp only [dist_eq_norm] at hdist
      apply hdist.trans
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos 1).le
      have hh := norm_sub_le y (Z s)
      have hz := hZ s s.2
      dsimp [M]
      linarith
    have hbase := norm_add_le (X (u τ)-Z (u τ)) (Z (u τ))
    rw [sub_add_cancel] at hbase
    have hZu := hZ (u τ) hut
    have hsabs : |(s:ℝ)| ≤ |b| := by rw [abs_of_nonneg s.2.1,abs_of_nonneg hb]; exact s.2.2
    have htabs : |(t:ℝ)| ≤ |b| := by rw [abs_of_nonneg t.2.1,abs_of_nonneg hb]; exact t.2.2
    have huabs : |u τ| ≤ |b| := by rw [abs_of_nonneg hut.1,abs_of_nonneg hb]; exact hut.2
    change max (max ‖(s:ℝ)‖ ‖(t:ℝ)‖) (max ‖u τ‖ ‖X (u τ)‖) < R
    simp only [Real.norm_eq_abs,max_lt_iff]
    constructor <;> constructor <;> dsimp [R] <;>
      nlinarith [Real.exp_pos 1,abs_nonneg A,abs_nonneg b,mul_pos (Real.exp_pos 1) hMpos]
  have hdα (τ : ℝ) (hτ : τ ∈ Icc (0:ℝ) 1) :
      HasDerivWithinAt α (g (α τ)) (Icc 0 1) τ := by
    have hχ : χ (α τ) = 1 := χ.one_of_mem_closedBall
      (by simpa only [mem_closedBall_zero_iff] using (hnorm τ hτ).le)
    have heq : g (α τ) = (0,((t:ℝ)-(s:ℝ),
        ((t:ℝ)-(s:ℝ)) • probabilityVelocity F x r (u τ) (X (u τ)))) := by
      simp only [g,hχ,one_smul,V,α,hψeq (hu τ hτ),id_eq]
    rw [heq]
    have hdu : HasDerivAt u ((t:ℝ)-(s:ℝ)) τ := by
      simpa [u] using ((hasDerivAt_id τ).mul_const ((t:ℝ)-(s:ℝ))).const_add (s:ℝ)
    have hdx := (convexProbabilityFlow_deriv hF hell hlo hup x hr hb (by norm_num) hb1 s y
      (hu τ hτ)).hasFDerivWithinAt.comp_hasDerivWithinAt τ hdu.hasDerivWithinAt hu
    exact (hasDerivWithinAt_const τ (Icc 0 1) ((s:ℝ),(t:ℝ))).prodMk
      (hdu.hasDerivWithinAt.prodMk hdx)
  have hh := trajectory_dist (fun _ _ => hL) hα.continuousOn hdα
    (autonomousFlow_continuous hg hL (by norm_num : (0:ℝ) ≤ 1)
      (((s:ℝ),(t:ℝ)),((s:ℝ),y))).continuousOn
    (fun τ hτ => autonomousFlow_deriv hg hL (by norm_num : (0:ℝ) ≤ 1)
      (((s:ℝ),(t:ℝ)),((s:ℝ),y)) hτ)
    (⟨0,le_rfl,by norm_num⟩ : Icc (0:ℝ) 1) ⟨1,by norm_num,le_rfl⟩
  rw [hα0,autonomousFlow_initial,dist_self,zero_mul,dist_le_zero] at hh
  have hlast := congrArg (fun q : H => q.2.2) hh
  have hu1 : u 1 = (t:ℝ) := by dsimp [u]; ring
  simpa only [S,α,hu1,X] using hlast.symm

/-- Unit-neighborhood specialization of the uniform smooth representative. -/
theorem exists_smooth_convexProbabilityFlow_extension {F : E → ℝ} (hF : ContDiff ℝ 2 F)
    {ell : ℝ} (hell : 0 ≤ ell)
    (hlo : ∀ z a, 0 ≤ fderiv ℝ (fderiv ℝ F) z a a)
    (hup : ∀ z a, fderiv ℝ (fderiv ℝ F) z a a ≤ ell * ‖a‖ ^ 2)
    (x : E) {r : ℝ} (hr : 0 < r) {b : ℝ} (hb : 0 ≤ b) (hb1 : b < 1)
    (hsmall : r^2*ell ≤ 1/2) (z : E) :
    ∃ S : (ℝ × ℝ) × E → E, ContDiff ℝ ∞ S ∧
      ∀ s t : Icc 0 b, ∀ y ∈ ball z 1,
        S (((s:ℝ),(t:ℝ)),y) =
          convexProbabilityFlow hF hell hlo hup x hr hb (by norm_num) hb1 s y t :=
  exists_smooth_convexProbabilityFlow_extension_ball hF hell hlo hup x hr hb hb1 hsmall z (by norm_num)

end AcceleratedLogConcave.Conditional.Transport
