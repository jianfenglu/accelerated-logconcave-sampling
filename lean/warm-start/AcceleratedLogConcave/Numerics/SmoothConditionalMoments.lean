import AcceleratedLogConcave.Numerics.MeanFlowLp
import AcceleratedLogConcave.Conditional.PolynomialMoments

/-! Polynomial moments of the literal conditional center and its shared input.
The center is allowed to be correlated with the input. No independence is used.
-/
noncomputable section
open Set MeasureTheory ProbabilityTheory
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
namespace AcceleratedLogConcave.Numerics.ConditionalSmoothing
open MeanFlowLp AffineGraph AffineGraph.MeanGeometry

private theorem integrable_norm_pow_of_affine_bound
    {Ω X Y : Type*} [MeasurableSpace Ω] [NormedAddCommGroup X] [NormedAddCommGroup Y]
    {μ : Measure Ω} [IsFiniteMeasure μ] {f : Ω → X} {g : Ω → Y}
    (hf : AEStronglyMeasurable f μ) (n : ℕ)
    (hg : Integrable (fun ω => ‖g ω‖^n) μ)
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hb : ∀ ω, ‖f ω‖ ≤ A+B*‖g ω‖) :
    Integrable (fun ω => ‖f ω‖^n) μ := by
  apply (((integrable_const (A^n)).add (hg.const_mul (B^n))).const_mul (2^(n-1))).mono'
    (hf.norm.pow n)
  filter_upwards [] with ω
  simp only [Pi.pow_apply, Pi.add_apply, Real.norm_eq_abs]
  rw [abs_of_nonneg (pow_nonneg (norm_nonneg _) _)]
  calc
    _ ≤ (A+B*‖g ω‖)^n := pow_le_pow_left₀ (norm_nonneg _) (hb ω) n
    _ ≤ 2^(n-1)*(A^n+(B*‖g ω‖)^n) :=
      add_pow_le hA (mul_nonneg hB (norm_nonneg _)) n
    _ = _ := by simp only [mul_pow]

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ}
local notation "E" => EuclideanSpace ℝ ι
variable (d : MeanFlowLp.Data ι m)

theorem continuous_seedPosition (t : ℝ) : Continuous (position d t) :=
  (WithLp.prod_continuous_ofLp 2 E E).fst.comp
    ((CenteringFlowLp.continuous_phase (kernelData d) _ _).comp
      (continuous_const.prodMk continuous_fst))

theorem continuous_seedBackward (j : Fin m) (t : ℝ) : Continuous (backward d j t) :=
  (TransportFlowLp.continuous_flow (transportData d) d.x _).comp
    (continuous_const.prodMk (continuous_seedPosition d (centerNode j)))

theorem continuous_seedCenter (j : Fin m) (ρ : d.G.Kernel) :
    Continuous (conditionalCenter d j ρ) := by
  unfold conditionalCenter
  have hc : Continuous (fun ω : Seed d =>
      (d.r*d.G.rho ρ) • backward d j (d.G.rho ρ) ω) :=
    (continuous_seedBackward d j (d.G.rho ρ)).const_smul (d.r*d.G.rho ρ)
  exact continuous_const.add hc

def conditionalInput (j : Fin m) (ρ : d.G.Kernel) (ω : Seed d) : E × E :=
  (conditionalCenter d j ρ ω, ω.2 j ρ)

theorem continuous_conditionalInput (j : Fin m) (ρ : d.G.Kernel) :
    Continuous (conditionalInput d j ρ) := by
  apply (continuous_seedCenter d j ρ).prodMk
  fun_prop

theorem seedPosition_integrable_norm_pow (t : ℝ) (n : ℕ) :
    Integrable (fun ω => ‖position d t ω‖^n) (seedMeasure d) :=
  ((CenteringFlowLp.position_preserving (kernelData d)).comp
    (kernel_phase_preserving d t)).integrable_comp_of_integrable
      (Conditional.interpolationLaw_integrable_norm_pow d.hF d.hlo d.x d.r
        (backwardEnd d.G.R) n)

theorem seedBackward_integrable_norm_pow (j : Fin m) (t : ℝ) (n : ℕ) :
    Integrable (fun ω => ‖backward d j t ω‖^n) (seedMeasure d) := by
  obtain ⟨A,B,hA,_,hb⟩ := TransportFlowLp.uniform_affine_envelopes
    (transportData d) d.x ⟨backwardEnd d.G.R,d.G.backwardEnd_pos.le,le_rfl⟩
  exact integrable_norm_pow_of_affine_bound
    (continuous_seedBackward d j t).aestronglyMeasurable n
    (seedPosition_integrable_norm_pow d (centerNode j) n)
    hA (Real.exp_pos _).le (fun ω => (hb t (position d (centerNode j) ω)).1)

theorem seedCenter_integrable_norm_pow (j : Fin m) (ρ : d.G.Kernel) (n : ℕ) :
    Integrable (fun ω => ‖conditionalCenter d j ρ ω‖^n) (seedMeasure d) := by
  apply integrable_norm_pow_of_affine_bound
    (continuous_seedCenter d j ρ).aestronglyMeasurable n
    (seedBackward_integrable_norm_pow d j (d.G.rho ρ) n)
    (norm_nonneg d.x) (abs_nonneg (d.r*d.G.rho ρ))
  intro ω
  simpa only [conditionalCenter, norm_smul, Real.norm_eq_abs] using
    norm_add_le d.x ((d.r*d.G.rho ρ) • backward d j (d.G.rho ρ) ω)

omit [DecidableEq ι] in
theorem seedNoise_integrable_norm_pow (j : Fin m) (ρ : d.G.Kernel) (n : ℕ) :
    Integrable (fun ω : Seed d => ‖ω.2 j ρ‖^n) (seedMeasure d) := by
  have h : Integrable (fun z : E => ‖z‖^n) (stdGaussian E) := by
    simpa only [id_eq] using
      (IsGaussian.memLp_id (stdGaussian E) n (by simp)).integrable_norm_pow'
  exact (noise_projection_preserving d j ρ).integrable_comp_of_integrable h

/-- The joint input has every finite norm moment on the original common seed. -/
theorem conditionalInput_integrable_norm_pow (j : Fin m) (ρ : d.G.Kernel) (n : ℕ) :
    Integrable (fun ω => ‖conditionalInput d j ρ ω‖^n) (seedMeasure d) := by
  apply (((seedCenter_integrable_norm_pow d j ρ n).add
    (seedNoise_integrable_norm_pow d j ρ n)).const_mul (2^(n-1))).mono'
    ((continuous_conditionalInput d j ρ).norm.pow n).aestronglyMeasurable
  filter_upwards [] with ω
  simp only [Pi.pow_apply, Pi.add_apply, Real.norm_eq_abs]
  rw [abs_of_nonneg (pow_nonneg (norm_nonneg _) _)]
  have hnorm : ‖conditionalInput d j ρ ω‖ ≤ ‖conditionalCenter d j ρ ω‖+‖ω.2 j ρ‖ := by
    rw [conditionalInput, Prod.norm_def]
    exact max_le (le_add_of_nonneg_right (norm_nonneg _))
      (le_add_of_nonneg_left (norm_nonneg _))
  exact (pow_le_pow_left₀ (norm_nonneg _) hnorm n).trans
    (add_pow_le (norm_nonneg _) (norm_nonneg _) n)

theorem conditionalInput_polynomial_memLp (j : Fin m) (ρ : d.G.Kernel) (N : ℕ) :
    MemLp (fun ω => (1+‖conditionalInput d j ρ ω‖)^N) 2 (seedMeasure d) := by
  have hc := continuous_conditionalInput d j ρ
  have hm : Integrable (fun p : E × E => ‖p‖^(2*N))
      ((seedMeasure d).map (conditionalInput d j ρ)) :=
    (integrable_map_measure (by fun_prop) hc.aemeasurable).mpr
      (conditionalInput_integrable_norm_pow d j ρ (2*N))
  exact (memLp_map_measure_iff (by fun_prop) hc.aemeasurable).mp
    (Analysis.PolynomialLp.memLp_two_one_add_norm_pow N hm)

end AcceleratedLogConcave.Numerics.ConditionalSmoothing
