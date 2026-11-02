import AcceleratedLogConcave.Analysis.DominatedLp

/-! L² fundamental theorem transfer using a uniform energy bound, not a
pointwise L² envelope. Stationarity supplies that energy for source jets. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory
open scoped Topology
namespace AcceleratedLogConcave.Analysis.StationaryLpFTC
variable {Ω E : Type*} [MeasurableSpace Ω] [TopologicalSpace Ω]
  [SecondCountableTopology Ω] [BorelSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [SecondCountableTopology E] {μ : Measure Ω} [IsFiniteMeasure μ]

omit [CompleteSpace E] in
/-- Finite-time Fubini is justified by the stationary energy, with no
pointwise-in-time dominating observable assumption. -/
theorem integrable_inner_prod_of_energy
    (g : ℝ → Ω → E) (hc : Continuous (Function.uncurry g))
    (hm : ∀ t, MemLp (g t) 2 μ) {C : ℝ} (_hC : 0 ≤ C)
    (hb : ∀ t, (∫ z, ‖g t z‖^2 ∂μ) ≤ C)
    (w : Lp E 2 μ) (a b : ℝ) :
    Integrable (fun q : ℝ × Ω => inner ℝ (w q.2) (g q.1 q.2))
      ((volume.restrict (uIoc a b)).prod μ) := by
  have hmeas : AEStronglyMeasurable (fun q : ℝ × Ω => inner ℝ (w q.2) (g q.1 q.2))
      ((volume.restrict (uIoc a b)).prod μ) :=
    (Lp.aestronglyMeasurable w).comp_snd.inner hc.aestronglyMeasurable
  apply (integrable_prod_iff hmeas).mpr
  have hi (t : ℝ) : Integrable (fun z => inner ℝ (w z) (g t z)) μ := by
    apply (((Lp.memLp w).norm.integrable_mul (hm t).norm)).mono'
      ((Lp.aestronglyMeasurable w).inner (hm t).aestronglyMeasurable)
    filter_upwards [] with z
    exact norm_inner_le_norm _ _
  refine ⟨Filter.Eventually.of_forall hi, ?_⟩
  have : IsFiniteMeasure (volume.restrict (uIoc a b)) := by
    unfold uIoc
    infer_instance
  apply (integrable_const ((∫ z, ‖w z‖^2 ∂μ) + C)).mono'
    hmeas.norm.integral_prod_right'
  filter_upwards [] with t
  rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun z => norm_nonneg _))]
  calc
    _ ≤ ∫ z, ‖w z‖^2 + ‖g t z‖^2 ∂μ := by
      apply integral_mono (hi t).norm
        (((Lp.memLp w).norm.integrable_sq).add ((hm t).norm.integrable_sq))
      intro z
      change ‖inner ℝ (w z) (g t z)‖ ≤ ‖w z‖^2 + ‖g t z‖^2
      have hh : ‖inner ℝ (w z) (g t z)‖ ≤ ‖w z‖ * ‖g t z‖ :=
        norm_inner_le_norm _ _
      nlinarith [sq_nonneg (‖w z‖-‖g t z‖)]
    _ = (∫ z, ‖w z‖^2 ∂μ) + ∫ z, ‖g t z‖^2 ∂μ :=
      integral_add ((Lp.memLp w).norm.integrable_sq) ((hm t).norm.integrable_sq)
    _ ≤ _ := by linarith [hb t]

/-- Given an actual pointwise primitive identity and continuous L² derivative
orbit, the same identity holds in L². No higher jet is used. -/
theorem toLp_sub_eq_integral_of_energy
    (f g : ℝ → Ω → E) (hc : Continuous (Function.uncurry g))
    (hf : ∀ t, MemLp (f t) 2 μ) (hg : ∀ t, MemLp (g t) 2 μ)
    (hlp : Continuous (fun t => (hg t).toLp (g t)))
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ t, (∫ z, ‖g t z‖^2 ∂μ) ≤ C)
    (a b : ℝ) (hp : ∀ z, f b z - f a z = ∫ t in a..b, g t z) :
    (hf b).toLp (f b) - (hf a).toLp (f a) =
      ∫ t in a..b, (hg t).toLp (g t) := by
  have hgi (z : Ω) : IntervalIntegrable (fun t => g t z) volume a b :=
    (hc.comp (continuous_id.prodMk continuous_const)).intervalIntegrable a b
  apply ext_inner_left ℝ
  intro w
  have hprod := integrable_inner_prod_of_energy g hc hg hC hb w a b
  calc
    inner ℝ w ((hf b).toLp (f b) - (hf a).toLp (f a)) =
        ∫ z, inner ℝ (w z) (∫ t in a..b, g t z) ∂μ := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_sub ((hf b).toLp (f b)) ((hf a).toLp (f a)),
        (hf b).coeFn_toLp, (hf a).coeFn_toLp] with z hz hzb hza
      rw [hz, Pi.sub_apply, hzb, hza, hp z]
    _ = ∫ z, (∫ t in a..b, inner ℝ (w z) (g t z)) ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with z
      exact ((innerSL ℝ (w z)).intervalIntegral_comp_comm (hgi z)).symm
    _ = ∫ t in a..b, ∫ z, inner ℝ (w z) (g t z) ∂μ :=
      (intervalIntegral_integral_swap hprod).symm
    _ = ∫ t in a..b, inner ℝ w ((hg t).toLp (g t)) := by
      apply intervalIntegral.integral_congr
      intro t _
      dsimp only
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [(hg t).coeFn_toLp] with z hz
      rw [hz]
    _ = inner ℝ w (∫ t in a..b, (hg t).toLp (g t)) :=
      (innerSL ℝ w).intervalIntegral_comp_comm (hlp.intervalIntegrable a b)


/-- Lift a pointwise derivative using stationary finite energy and the continuous
L² orbit of the derivative. No pointwise common envelope is assumed. -/
theorem hasDerivAt_toLp_of_energy
    (f g : ℝ → Ω → E) (hc : Continuous (Function.uncurry g))
    (hf : ∀ t, MemLp (f t) 2 μ) (hg : ∀ t, MemLp (g t) 2 μ)
    (hlp : Continuous (fun t => (hg t).toLp (g t)))
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ t, (∫ z, ‖g t z‖^2 ∂μ) ≤ C)
    (hd : ∀ t z, HasDerivAt (fun a => f a z) (g t z) t) (t : ℝ) :
    HasDerivAt (fun a => (hf a).toLp (f a)) ((hg t).toLp (g t)) t := by
  have he : (fun a => (hf a).toLp (f a)) =
      fun a => (hf 0).toLp (f 0) + ∫ u in 0..a, (hg u).toLp (g u) := by
    funext a
    have hh := toLp_sub_eq_integral_of_energy f g hc hf hg hlp hC hb 0 a (fun z => by
      symm
      exact intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hd u z)
        ((hc.comp (continuous_id.prodMk continuous_const)).intervalIntegrable 0 a))
    exact (sub_eq_iff_eq_add.mp hh).trans (add_comm _ _)
  rw [he]
  exact (intervalIntegral.integral_hasDerivAt_right (hlp.intervalIntegrable 0 t)
    hlp.aestronglyMeasurable.stronglyMeasurableAtFilter hlp.continuousAt).const_add _

end AcceleratedLogConcave.Analysis.StationaryLpFTC
