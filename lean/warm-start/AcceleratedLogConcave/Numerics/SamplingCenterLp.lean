import AcceleratedLogConcave.Numerics.CenteringFlowLp
/-! Actual center dependence of the probability flow and canonical L² composition.

The two-center ODE estimate supplies joint continuity and affine envelopes. These
are used to lift correlated square-integrable centers and initial inputs on an
arbitrary probability space. Signed integral identities retain the initial mean.
No conditional Gaussian law, common exceptional set or endpoint derivative is claimed.
-/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory AcceleratedLogConcave Conditional
open scoped NNReal
set_option maxHeartbeats 1000000
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace AcceleratedLogConcave.Numerics.SamplingCenterLp
variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι
structure Data (ι : Type*) [Fintype ι] where
  F : EuclideanSpace ℝ ι → ℝ
  hF : ContDiff ℝ 2 F
  ell : ℝ
  hell : 0 ≤ ell
  hlo : ∀ z a, 0 ≤ fderiv ℝ (fderiv ℝ F) z a a
  hup : ∀ z a, fderiv ℝ (fderiv ℝ F) z a a ≤ ell*‖a‖^2
  r : ℝ
  hr : 0 < r
  b : ℝ
  hb : 0 ≤ b
  hb1 : b < 1

def path (d : Data ι) (x : E) (t : ℝ) (p : E) : E :=
  Numerics.SamplingFlowLp.sourcePath d.hF d.hell d.hlo d.hup x d.hr d.hb d.hb1 t p
def reply (d : Data ι) (x : E) (t : ℝ) (p : E) : E :=
  Numerics.SamplingFlowLp.centeredReply d.hF d.hell d.hlo d.hup x d.hr d.hb d.hb1 t p
def amplification (d : Data ι) : ℝ := Real.exp (d.r^2*d.ell*d.b)
def initialMean (d : Data ι) (x : E) : E := Gibbs.primitiveMean d.F x d.r


private theorem norm_conditionalMean_center_sub_le (d : Data ι) (x y z : E)
    {t : ℝ} (ht : t ∈ Icc 0 d.b) :
    ‖conditionalMean d.F x d.r t z-conditionalMean d.F y d.r t z‖ ≤ d.ell*‖x-y‖ := by
  have htlo : -1 < t := by linarith [ht.1]
  have hthi : t < 1 := ht.2.trans_lt d.hb1
  rw [Numerics.AffineFlowIdentities.conditionalMean_eq_primitiveMean d.hF d.hell d.hlo d.hup x d.hr htlo hthi,
    Numerics.AffineFlowIdentities.conditionalMean_eq_primitiveMean d.hF d.hell d.hlo d.hup y d.hr htlo hthi]
  have hrad : 0 < d.r*Real.sqrt (1-t^2) := mul_pos d.hr (Real.sqrt_pos.mpr (by nlinarith))
  have h := (Gibbs.primitive_mean_lipschitz d.hF d.hell d.hlo d.hup hrad).dist_le_mul
    (x+(d.r*t) • z) (y+(d.r*t) • z)
  simp only [dist_eq_norm,add_sub_add_right_eq_sub] at h
  exact h

private theorem norm_velocity_center_sub_le (d : Data ι) (x y z : E)
    {t : ℝ} (ht : t ∈ Icc 0 d.b) :
    ‖probabilityVelocity d.F x d.r t z-probabilityVelocity d.F y d.r t z‖ ≤
      d.r*d.ell*‖x-y‖ := by
  change ‖(-d.r) • conditionalMean d.F x d.r t z-(-d.r) • conditionalMean d.F y d.r t z‖ ≤ _
  rw [← smul_sub,norm_smul,Real.norm_eq_abs,abs_neg,abs_of_pos d.hr]
  have h := mul_le_mul_of_nonneg_left (norm_conditionalMean_center_sub_le d x y z ht) d.hr.le
  simpa only [mul_assoc] using h

private def rawPath (d : Data ι) (x p : E) : ℝ → E :=
  convexProbabilityFlow d.hF d.hell d.hlo d.hup x d.hr d.hb
    (by norm_num) d.hb1 ⟨0,le_rfl,d.hb⟩ p

private theorem rawPath_initial (d : Data ι) (x p : E) : rawPath d x p 0=p :=
  convexProbabilityFlow_initial d.hF d.hell d.hlo d.hup x d.hr d.hb
    (by norm_num) d.hb1 ⟨0,le_rfl,d.hb⟩ p

private theorem rawPath_continuous (d : Data ι) (x p : E) : Continuous (rawPath d x p) :=
  Numerics.AffineFlowIdentities.convexProbabilityFlow_continuous d.hF d.hell d.hlo d.hup
    x d.hr d.hb (by norm_num) d.hb1 _ _

private theorem rawPath_deriv_right (d : Data ι) (x p : E) {t : ℝ} (ht : t ∈ Ico 0 d.b) :
    HasDerivWithinAt (rawPath d x p)
      (probabilityVelocity d.F x d.r t (rawPath d x p t)) (Ici t) t := by
  apply (convexProbabilityFlow_deriv d.hF d.hell d.hlo d.hup x d.hr d.hb
    (by norm_num) d.hb1 ⟨0,le_rfl,d.hb⟩ p ⟨ht.1,ht.2.le⟩).mono_of_mem_nhdsWithin
  exact inter_mem (Filter.mem_of_superset self_mem_nhdsWithin (Ici_subset_Ici.mpr ht.1))
    (mem_nhdsWithin_of_mem_nhds (Iic_mem_nhds ht.2))

private theorem rawPath_stability_gronwall (d : Data ι) (x y p q : E)
    {t : ℝ} (ht : t ∈ Icc 0 d.b) :
    ‖rawPath d x p t-rawPath d y q t‖ ≤
      gronwallBound ‖p-q‖ (d.r^2*d.ell) (d.r*d.ell*‖x-y‖) t := by
  let K : ℝ≥0 := ⟨d.r^2*d.ell,mul_nonneg (sq_nonneg _) d.hell⟩
  have hL (u : ℝ) (hu : u ∈ Ico 0 d.b) :
      LipschitzWith K (probabilityVelocity d.F x d.r u) := by
    have hh := meanVelocity_lipschitz d.r (lipschitzWith_conditionalMean d.hF d.hell d.hlo
      d.hup x d.hr (by linarith [hu.1]) (hu.2.trans d.hb1))
    convert! hh using 1
    ext
    simp only [NNReal.coe_mul,coe_nnnorm,Real.norm_eq_abs,abs_of_pos d.hr]
    change d.r^2*d.ell=d.r*(d.r*d.ell)
    ring
  have hh := dist_le_of_approx_trajectories_ODE_of_mem
    (s := fun _ => Set.univ) (K := K) (δ := ‖p-q‖)
    (fun u hu => (hL u hu).lipschitzOnWith)
    (rawPath_continuous d x p).continuousOn (fun u hu => rawPath_deriv_right d x p hu)
    (fun u _ => (show dist (probabilityVelocity d.F x d.r u (rawPath d x p u))
      (probabilityVelocity d.F x d.r u (rawPath d x p u)) ≤ (0:ℝ) by simp))
    (fun _ _ => Set.mem_univ _)
    (rawPath_continuous d y q).continuousOn (fun u hu => rawPath_deriv_right d y q hu)
    (fun u hu => by
      rw [dist_eq_norm,norm_sub_rev]
      exact norm_velocity_center_sub_le d x y _ ⟨hu.1,hu.2.le⟩)
    (fun _ _ => Set.mem_univ _) (by simp only [rawPath_initial,dist_eq_norm,le_refl]) t ht
  simp only [dist_eq_norm,zero_add,sub_zero] at hh
  exact hh

private theorem gronwall_le_exp {δ C D T : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D) :
    gronwallBound δ C D T ≤ (δ+D*T)*Real.exp (C*T) := by
  by_cases h : C=0
  · simp [gronwallBound,h]
  · have hpos : 0 < C := lt_of_le_of_ne hC (Ne.symm h)
    rw [gronwallBound_of_K_ne_0 h]
    have he := Real.add_one_le_exp (-(C*T))
    have hh := mul_le_mul_of_nonneg_right he (Real.exp_pos (C*T)).le
    rw [← Real.exp_add] at hh
    have hzero : -(C*T)+(C*T)=0 := by ring
    rw [hzero,Real.exp_zero] at hh
    have he' : Real.exp (C*T)-1 ≤ C*T*Real.exp (C*T) := by nlinarith
    have hm := mul_le_mul_of_nonneg_left he' (div_nonneg hD hC)
    have hc : D/C*(C*T*Real.exp (C*T)) = D*T*Real.exp (C*T) := by field_simp
    rw [hc] at hm
    nlinarith

theorem path_stability (d : Data ι) (x y p q : E) (t : ℝ) :
    ‖path d x t p-path d y t q‖ ≤
      amplification d*(‖p-q‖+d.r*d.ell*d.b*‖x-y‖) := by
  let τ := Numerics.SamplingFlowLp.sourceTime d.hb t
  have hτ := Numerics.SamplingFlowLp.sourceTime_mem d.hb t
  have hK : 0 ≤ d.r^2*d.ell := mul_nonneg (sq_nonneg _) d.hell
  have hD : 0 ≤ d.r*d.ell*‖x-y‖ := mul_nonneg (mul_nonneg d.hr.le d.hell) (norm_nonneg _)
  have hh := (rawPath_stability_gronwall d x y p q hτ).trans (gronwall_le_exp hK hD)
  have he := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hτ.2 hK)
  have hsum := add_le_add_right (mul_le_mul_of_nonneg_left hτ.2 hD) ‖p-q‖
  have hmul := mul_le_mul hsum he (Real.exp_pos _).le
    (add_nonneg (norm_nonneg _) (mul_nonneg hD d.hb))
  change ‖rawPath d x p τ-rawPath d y q τ‖ ≤ _
  exact hh.trans (by simpa only [amplification,mul_comm,mul_left_comm,mul_assoc] using hmul)

theorem reply_stability (d : Data ι) (x y p q : E) (t : ℝ) :
    ‖reply d x t p-reply d y t q‖ ≤ 2*d.ell*‖x-y‖ +
      d.r*d.b*d.ell*amplification d*(‖p-q‖+d.r*d.ell*d.b*‖x-y‖) := by
  let τ := Numerics.SamplingFlowLp.sourceTime d.hb t
  have hτ := Numerics.SamplingFlowLp.sourceTime_mem d.hb t
  have htlo : -1 < τ := by linarith [hτ.1]
  have hthi : τ < 1 := hτ.2.trans_lt d.hb1
  have hrad : 0 < d.r*Real.sqrt (1-τ^2) := mul_pos d.hr (Real.sqrt_pos.mpr (by nlinarith))
  have hu := (Gibbs.primitive_mean_lipschitz d.hF d.hell d.hlo d.hup hrad).dist_le_mul
    (x+(d.r*τ) • path d x t p) (y+(d.r*τ) • path d y t q)
  have hv := (Gibbs.primitive_mean_lipschitz d.hF d.hell d.hlo d.hup d.hr).dist_le_mul x y
  simp only [dist_eq_norm] at hu hv
  change _ ≤ d.ell*‖_‖ at hu
  change _ ≤ d.ell*‖x-y‖ at hv
  have he : (x+(d.r*τ) • path d x t p)-(y+(d.r*τ) • path d y t q) =
      (x-y)+(d.r*τ) • (path d x t p-path d y t q) := by module
  rw [he] at hu
  have hp := norm_add_le (x-y) ((d.r*τ) • (path d x t p-path d y t q))
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (mul_nonneg d.hr.le hτ.1)] at hp
  have hpu := mul_le_mul_of_nonneg_left hp d.hell
  have hd := path_stability d x y p q t
  have hcoef : d.r*τ ≤ d.r*d.b := mul_le_mul_of_nonneg_left hτ.2 d.hr.le
  have hpu' := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right hcoef (norm_nonneg (path d x t p-path d y t q))) d.hell
  have hdd := mul_le_mul_of_nonneg_left hd
    (mul_nonneg (mul_nonneg d.hr.le d.hb) d.hell)
  have heq : reply d x t p-reply d y t q =
      (Gibbs.primitiveMean d.F (x+(d.r*τ) • path d x t p) (d.r*Real.sqrt (1-τ^2)) -
       Gibbs.primitiveMean d.F (y+(d.r*τ) • path d y t q) (d.r*Real.sqrt (1-τ^2))) -
      (Gibbs.primitiveMean d.F x d.r-Gibbs.primitiveMean d.F y d.r) := by
    unfold reply Numerics.SamplingFlowLp.centeredReply path
    dsimp only [τ]
    abel
  rw [heq]
  have hh := norm_sub_le
    (Gibbs.primitiveMean d.F (x+(d.r*τ) • path d x t p) (d.r*Real.sqrt (1-τ^2)) -
       Gibbs.primitiveMean d.F (y+(d.r*τ) • path d y t q) (d.r*Real.sqrt (1-τ^2)))
    (Gibbs.primitiveMean d.F x d.r-Gibbs.primitiveMean d.F y d.r)
  nlinarith

private theorem continuous_of_param_bound (g : ℝ → E × E → E) (A B : ℝ)
    (hT : ∀ z, Continuous (fun t => g t z))
    (hB : ∀ t x y, ‖g t x-g t y‖ ≤ A*‖x.1-y.1‖+B*‖x.2-y.2‖) :
    Continuous (fun v : ℝ × (E × E) => g v.1 v.2) := by
  rw [continuous_iff_continuousAt]
  rintro ⟨t,z⟩
  have hb : Tendsto (fun v : ℝ × (E × E) => A*‖v.2.1-z.1‖+B*‖v.2.2-z.2‖)
      (nhds (t,z)) (nhds 0) := by
    have hc : Continuous (fun v : ℝ × (E × E) => A*‖v.2.1-z.1‖+B*‖v.2.2-z.2‖) := by fun_prop
    simpa using hc.tendsto (t,z)
  have hd : Tendsto (fun v : ℝ × (E × E) => g v.1 v.2-g v.1 z)
      (nhds (t,z)) (nhds 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    exact squeeze_zero (fun v => norm_nonneg _) (fun v => hB v.1 v.2 z) hb
  have hf := hd.add ((hT z).continuousAt.tendsto.comp continuous_fst.continuousAt.tendsto)
  simpa only [ContinuousAt,Function.comp_def,sub_add_cancel,zero_add] using hf

theorem continuous_path (d : Data ι) :
    Continuous (fun v : ℝ × (E × E) => path d v.2.1 v.1 v.2.2) := by
  apply continuous_of_param_bound (fun t z => path d z.1 t z.2)
    (amplification d*d.r*d.ell*d.b) (amplification d)
  · intro z
    simpa only [path,Function.comp_def,Function.uncurry_def,id_eq] using
      (Numerics.SamplingFlowLp.continuous_sourcePath d.hF d.hell d.hlo d.hup
        z.1 d.hr d.hb d.hb1).comp (continuous_id.prodMk continuous_const)
  · intro t x y
    have hh := path_stability d x.1 y.1 x.2 y.2 t
    nlinarith

theorem continuous_reply (d : Data ι) :
    Continuous (fun v : ℝ × (E × E) => reply d v.2.1 v.1 v.2.2) := by
  apply continuous_of_param_bound (fun t z => reply d z.1 t z.2)
    (2*d.ell+d.r*d.b*d.ell*amplification d*(d.r*d.ell*d.b))
    (d.r*d.b*d.ell*amplification d)
  · intro z
    simpa only [reply,Function.comp_def,Function.uncurry_def,id_eq] using
      (Numerics.SamplingFlowLp.continuous_centeredReply d.hF d.hell d.hlo d.hup
        z.1 d.hr d.hb d.hb1).comp (continuous_id.prodMk continuous_const)
  · intro t x y
    have hh := reply_stability d x.1 y.1 x.2 y.2 t
    nlinarith

theorem uniform_affine_envelopes (d : Data ι) :
    ∃ A B C : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ 0 ≤ C ∧ ∀ x t p,
      ‖path d x t p‖ ≤ A+C*(‖x‖+‖p‖) ∧
      ‖reply d x t p‖ ≤ B+C*(‖x‖+‖p‖) := by
  obtain ⟨_,A,B,_,hA,hB,_,hY,hQ⟩ := Numerics.SamplingFlowLp.uniform_affine_envelopes
    d.hF d.hell d.hlo d.hup (0:E) d.hr d.hb d.hb1
  have ha : 0 ≤ amplification d := (Real.exp_pos _).le
  have hR : 0 ≤ d.r*d.ell*d.b := mul_nonneg (mul_nonneg d.hr.le d.hell) d.hb
  have hS : 0 ≤ d.r*d.b*d.ell*amplification d :=
    mul_nonneg (mul_nonneg (mul_nonneg d.hr.le d.hb) d.hell) ha
  let C₁ := amplification d*(1+d.r*d.ell*d.b)
  let C₂ := 2*d.ell+(d.r*d.b*d.ell*amplification d)*(1+d.r*d.ell*d.b)
  have hC₁ : 0 ≤ C₁ := mul_nonneg ha (by linarith)
  have hC₂ : 0 ≤ C₂ := add_nonneg (mul_nonneg (by norm_num) d.hell) (mul_nonneg hS (by linarith))
  refine ⟨A,B,C₁+C₂,hA,hB,add_nonneg hC₁ hC₂,?_⟩
  intro x t p
  have hY0 : ‖path d 0 t 0‖ ≤ A := by simpa only [norm_zero,mul_zero,zero_add,path] using hY t 0
  have hQ0 : ‖reply d 0 t 0‖ ≤ B := by simpa only [norm_zero,mul_zero,zero_add,reply] using hQ t 0
  have hYY := path_stability d x 0 p 0 t
  have hQQ := reply_stability d x 0 p 0 t
  simp only [sub_zero] at hYY hQQ
  have hYtri := norm_add_le (path d x t p-path d 0 t 0) (path d 0 t 0)
  have hQtri := norm_add_le (reply d x t p-reply d 0 t 0) (reply d 0 t 0)
  rw [sub_add_cancel] at hYtri hQtri
  have hnx := norm_nonneg x
  have hnp := norm_nonneg p
  have hYcoef : ‖path d x t p-path d 0 t 0‖ ≤ C₁*(‖x‖+‖p‖) := by
    dsimp only [C₁]
    nlinarith [mul_nonneg ha hnx,mul_nonneg (mul_nonneg ha hR) hnp]
  have hQcoef : ‖reply d x t p-reply d 0 t 0‖ ≤ C₂*(‖x‖+‖p‖) := by
    dsimp only [C₂]
    nlinarith [mul_nonneg (mul_nonneg (by norm_num : (0:ℝ)≤2) d.hell) hnp,
      mul_nonneg hS hnx,mul_nonneg (mul_nonneg hS hR) hnp]
  constructor
  · nlinarith [mul_nonneg hC₂ (add_nonneg hnx hnp)]
  · nlinarith [mul_nonneg hC₁ (add_nonneg hnx hnp)]

section LiftHelpers
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
omit [IsFiniteMeasure μ] in
private theorem norm_sq_toLp {g : Ω → E}
    (hg : MemLp g 2 μ) :
    ‖hg.toLp g‖ ^ 2 = ∫ p, ‖g p‖ ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hg.coeFn_toLp] with p hp
  rw [hp, real_inner_self_eq_norm_sq]

omit [IsFiniteMeasure μ] in
/-- Pointwise time continuity and one genuine L² envelope give continuity of the canonical L² classes. -/
private theorem continuous_toLp_of_dominated
    (g : ℝ → Ω → E)
    (ht : ∀ ω, Continuous (fun t => g t ω))
    (B : Ω → ℝ)
    (hB : MemLp B 2 μ)
    (hbound : ∀ t p, ‖g t p‖ ≤ B p)
    (hm : ∀ t, MemLp (g t) 2 μ) :
    Continuous (fun t => (hm t).toLp (g t)) := by
  rw [continuous_iff_continuousAt]
  intro s
  have hc : Continuous (fun t => ∫ p, ‖g t p - g s p‖ ^ 2
      ∂μ) := by
    apply continuous_of_dominated (bound := fun p => (2 * B p)^2)
    · intro t
      exact ((hm t).aestronglyMeasurable.sub (hm s).aestronglyMeasurable).norm.pow 2
    · intro t
      filter_upwards [] with p
      have hn : ‖g t p - g s p‖ ≤ 2 * B p :=
        (norm_sub_le _ _).trans (by linarith [hbound t p, hbound s p])
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖g t p - g s p‖)]
      exact pow_le_pow_left₀ (norm_nonneg _) hn 2
    · exact (hB.const_mul 2).integrable_sq
    · filter_upwards [] with p
      exact ((ht p).sub continuous_const).norm.pow 2
  have heq (t : ℝ) :
      dist ((hm t).toLp (g t)) ((hm s).toLp (g s)) =
        Real.sqrt (∫ p, ‖g t p - g s p‖ ^ 2 ∂μ) := by
    rw [dist_eq_norm, ← MemLp.toLp_sub, ← norm_sq_toLp]
    exact (Real.sqrt_sq (norm_nonneg _)).symm
  rw [ContinuousAt, tendsto_iff_dist_tendsto_zero]
  simp_rw [heq]
  simpa [Function.comp_def] using ((Real.continuous_sqrt.comp hc).continuousAt (x := s)).tendsto

/-- Signed pointwise integration commutes with the canonical L² lift under genuine
joint a.e. strong measurability, time continuity and a common L² envelope. The proof uses scalar pairings and Fubini. -/
private theorem toLp_intervalIntegral_of_dominated
    (g : ℝ → Ω → E)
    (ht : ∀ ω, Continuous (fun t => g t ω))
    (hg : ∀ ν : Measure ℝ, AEStronglyMeasurable (Function.uncurry g) (ν.prod μ))
    (B : Ω → ℝ)
    (hB : MemLp B 2 μ)
    (hbound : ∀ t p, ‖g t p‖ ≤ B p)
    (hm : ∀ t, MemLp (g t) 2 μ)
    (a b : ℝ) :
    ∃ hi : MemLp (fun p => ∫ t in a..b, g t p) 2
        μ,
      hi.toLp (fun p => ∫ t in a..b, g t p) = ∫ t in a..b, (hm t).toLp (g t) := by
  have hmeas : AEStronglyMeasurable (fun p => ∫ t in a..b, g t p) μ := by
    unfold intervalIntegral
    exact (hg (volume.restrict (Ioc a b))).prod_swap.integral_prod_right'.sub
      (hg (volume.restrict (Ioc b a))).prod_swap.integral_prod_right'
  have hi : MemLp (fun p => ∫ t in a..b, g t p) 2 μ := by
    apply (hB.const_mul |b-a|).mono' hmeas
    filter_upwards [] with p
    simpa only [mul_comm] using
      intervalIntegral.norm_integral_le_of_norm_le_const (fun t _ => hbound t p)
  refine ⟨hi, ?_⟩
  have hgi (p) : IntervalIntegrable (fun t => g t p) volume a b :=
    (ht p).intervalIntegrable a b
  have hli : IntervalIntegrable (fun t => (hm t).toLp (g t)) volume a b :=
    (continuous_toLp_of_dominated g ht B hB hbound hm).intervalIntegrable a b
  apply ext_inner_left ℝ
  intro w
  have : IsFiniteMeasure (volume.restrict (uIoc a b)) := by
    unfold uIoc
    infer_instance
  have hprod : Integrable (fun q : ℝ × Ω =>
      inner ℝ (w q.2) (g q.1 q.2)) ((volume.restrict (uIoc a b)).prod μ) := by
    apply (((Lp.memLp w).norm.integrable_mul hB).comp_snd _).mono'
      ((Lp.aestronglyMeasurable w).comp_snd.inner (hg _))
    filter_upwards [] with q
    exact (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left (hbound q.1 q.2) (norm_nonneg _))
  calc
    inner ℝ w (hi.toLp (fun p => ∫ t in a..b, g t p)) =
        ∫ p, inner ℝ (w p) (∫ t in a..b, g t p) ∂μ := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [hi.coeFn_toLp] with p hp
      rw [hp]
    _ = ∫ p, (∫ t in a..b, inner ℝ (w p) (g t p)) ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with p
      exact ((innerSL ℝ (w p)).intervalIntegral_comp_comm (hgi p)).symm
    _ = ∫ t in a..b, ∫ p, inner ℝ (w p) (g t p) ∂μ :=
      (intervalIntegral_integral_swap hprod).symm
    _ = ∫ t in a..b, inner ℝ w ((hm t).toLp (g t)) := by
      apply intervalIntegral.integral_congr
      intro t _
      dsimp only
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [(hm t).coeFn_toLp] with p hp
      rw [hp]
    _ = inner ℝ w (∫ t in a..b, (hm t).toLp (g t)) :=
      (innerSL ℝ w).intervalIntegral_comp_comm hli

end LiftHelpers

set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency true
section RandomCenters
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable (d : Data ι) (X P : Ω → EuclideanSpace ℝ ι) (hX : MemLp X 2 μ) (hP : MemLp P 2 μ)
include hX hP

/-- Joint measurability is derived for every time measure from actual joint continuity. -/
theorem path_joint_aestronglyMeasurable (ν : Measure ℝ) :
    AEStronglyMeasurable (fun v : ℝ × Ω => path d (X v.2) v.1 (P v.2)) (ν.prod μ) := by
  have h0 : AEStronglyMeasurable (fun v : ℝ × Ω => v.1) (ν.prod μ) :=
    measurable_fst.aestronglyMeasurable
  have h1 : AEStronglyMeasurable (fun v : ℝ × Ω => X v.2) (ν.prod μ) :=
    hX.aestronglyMeasurable.comp_snd
  have h2 : AEStronglyMeasurable (fun v : ℝ × Ω => P v.2) (ν.prod μ) :=
    hP.aestronglyMeasurable.comp_snd
  have hm : AEStronglyMeasurable (fun v : ℝ × Ω => (v.1,(X v.2,P v.2))) (ν.prod μ) :=
    h0.prodMk (h1.prodMk h2)
  exact (continuous_path d).comp_aestronglyMeasurable (f := fun v : ℝ × Ω => (v.1,(X v.2,P v.2))) hm

theorem reply_joint_aestronglyMeasurable (ν : Measure ℝ) :
    AEStronglyMeasurable (fun v : ℝ × Ω => reply d (X v.2) v.1 (P v.2)) (ν.prod μ) := by
  have h0 : AEStronglyMeasurable (fun v : ℝ × Ω => v.1) (ν.prod μ) :=
    measurable_fst.aestronglyMeasurable
  have h1 : AEStronglyMeasurable (fun v : ℝ × Ω => X v.2) (ν.prod μ) :=
    hX.aestronglyMeasurable.comp_snd
  have h2 : AEStronglyMeasurable (fun v : ℝ × Ω => P v.2) (ν.prod μ) :=
    hP.aestronglyMeasurable.comp_snd
  have hm : AEStronglyMeasurable (fun v : ℝ × Ω => (v.1,(X v.2,P v.2))) (ν.prod μ) :=
    h0.prodMk (h1.prodMk h2)
  exact (continuous_reply d).comp_aestronglyMeasurable (f := fun v : ℝ × Ω => (v.1,(X v.2,P v.2))) hm

theorem path_memLp (t : ℝ) : MemLp (fun ω => path d (X ω) t (P ω)) 2 μ := by
  obtain ⟨A,B,C,hA,hB,hC,hbound⟩ := uniform_affine_envelopes d
  apply ((memLp_const A).add ((hX.norm.add hP.norm).const_mul C)).mono'
    ((continuous_path d).comp_aestronglyMeasurable
      (show AEStronglyMeasurable (fun ω => (t,(X ω,P ω))) μ from
        aestronglyMeasurable_const.prodMk (hX.aestronglyMeasurable.prodMk hP.aestronglyMeasurable)))
  filter_upwards [] with ω
  exact (hbound (X ω) t (P ω)).1

theorem reply_memLp (t : ℝ) : MemLp (fun ω => reply d (X ω) t (P ω)) 2 μ := by
  obtain ⟨A,B,C,hA,hB,hC,hbound⟩ := uniform_affine_envelopes d
  apply ((memLp_const B).add ((hX.norm.add hP.norm).const_mul C)).mono'
    ((continuous_reply d).comp_aestronglyMeasurable
      (show AEStronglyMeasurable (fun ω => (t,(X ω,P ω))) μ from
        aestronglyMeasurable_const.prodMk (hX.aestronglyMeasurable.prodMk hP.aestronglyMeasurable)))
  filter_upwards [] with ω
  exact (hbound (X ω) t (P ω)).2

omit P hP in
theorem initialMean_memLp : MemLp (fun ω => initialMean d (X ω)) 2 μ := by
  have hL := Gibbs.primitive_mean_lipschitz d.hF d.hell d.hlo d.hup d.hr
  apply ((hX.norm.const_mul d.ell).add (memLp_const ‖initialMean d 0‖)).mono'
    (hL.continuous.comp_aestronglyMeasurable hX.aestronglyMeasurable)
  filter_upwards [] with ω
  have h := hL.dist_le_mul (X ω) 0
  simp only [dist_eq_norm,sub_zero] at h
  have htri := norm_add_le (initialMean d (X ω)-initialMean d 0) (initialMean d 0)
  rw [sub_add_cancel] at htri
  have hh : ‖initialMean d (X ω)-initialMean d 0‖ ≤ d.ell*‖X ω‖ := h
  change ‖initialMean d (X ω)‖ ≤ d.ell*‖X ω‖+‖initialMean d 0‖
  linarith

/-- The canonical class of the actual path for correlated random center and initial input. -/
def pathLp (t : ℝ) : Lp E 2 μ := (path_memLp d X P hX hP t).toLp _
def replyLp (t : ℝ) : Lp E 2 μ := (reply_memLp d X P hX hP t).toLp _
omit P hP in
def initialMeanLp : Lp E 2 μ := (initialMean_memLp d X hX).toLp _

theorem continuous_pathLp : Continuous (pathLp d X P hX hP) := by
  obtain ⟨A,B,C,hA,hB,hC,hbound⟩ := uniform_affine_envelopes d
  exact continuous_toLp_of_dominated (fun t ω => path d (X ω) t (P ω))
    (fun ω => (continuous_path d).comp (f := fun t : ℝ => (t,(X ω,P ω)))
      (continuous_id.prodMk continuous_const))
    (fun ω => A+C*(‖X ω‖+‖P ω‖))
    ((memLp_const A).add ((hX.norm.add hP.norm).const_mul C))
    (fun t ω => (hbound (X ω) t (P ω)).1) (path_memLp d X P hX hP)

theorem continuous_replyLp : Continuous (replyLp d X P hX hP) := by
  obtain ⟨A,B,C,hA,hB,hC,hbound⟩ := uniform_affine_envelopes d
  exact continuous_toLp_of_dominated (fun t ω => reply d (X ω) t (P ω))
    (fun ω => (continuous_reply d).comp (f := fun t : ℝ => (t,(X ω,P ω)))
      (continuous_id.prodMk continuous_const))
    (fun ω => B+C*(‖X ω‖+‖P ω‖))
    ((memLp_const B).add ((hX.norm.add hP.norm).const_mul C))
    (fun t ω => (hbound (X ω) t (P ω)).2) (reply_memLp d X P hX hP)

/-- The signed Bochner integral commutes with the actual random-center L² lift. -/
theorem reply_integral_lift (a b : ℝ) :
    ∃ hi : MemLp (fun ω => ∫ t in a..b, reply d (X ω) t (P ω)) 2 μ,
      hi.toLp _ = ∫ t in a..b, replyLp d X P hX hP t := by
  obtain ⟨A,B,C,hA,hB,hC,hbound⟩ := uniform_affine_envelopes d
  exact toLp_intervalIntegral_of_dominated (fun t ω => reply d (X ω) t (P ω))
    (fun ω => (continuous_reply d).comp (f := fun t : ℝ => (t,(X ω,P ω)))
      (continuous_id.prodMk continuous_const))
    (reply_joint_aestronglyMeasurable d X P hX hP)
    (fun ω => B+C*(‖X ω‖+‖P ω‖))
    ((memLp_const B).add ((hX.norm.add hP.norm).const_mul C))
    (fun t ω => (hbound (X ω) t (P ω)).2) (reply_memLp d X P hX hP) a b

/-- The source signed sampling equation retains the random initial mean term. -/
theorem pathLp_eq_sub_integral (a b : ℝ) (ha : a ∈ Icc 0 d.b) (hb : b ∈ Icc 0 d.b) :
    pathLp d X P hX hP b = pathLp d X P hX hP a -
      d.r • ((b-a) • initialMeanLp d X hX + ∫ t in a..b, replyLp d X P hX hP t) := by
  obtain ⟨hi,heq⟩ := reply_integral_lift d X P hX hP a b
  rw [← heq]
  unfold pathLp initialMeanLp
  rw [← MemLp.toLp_const_smul, ← MemLp.toLp_add, ← MemLp.toLp_const_smul,
    ← MemLp.toLp_sub]
  apply MemLp.toLp_congr
  filter_upwards [] with ω
  exact Numerics.SamplingFlowLp.sourcePath_eq_sub_integral d.hF d.hell d.hlo d.hup
    (X ω) d.hr d.hb d.hb1 a b ha hb (P ω)

end RandomCenters

end AcceleratedLogConcave.Numerics.SamplingCenterLp
