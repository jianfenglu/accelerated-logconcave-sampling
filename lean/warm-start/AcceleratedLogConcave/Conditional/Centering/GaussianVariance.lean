import AcceleratedLogConcave.Gibbs.PrimitiveMoments

/-! Dimension-explicit Gaussian variance bounds for a Lipschitz transported
observable. These require no new Poincaré theorem for the transported law. -/
noncomputable section
open MeasureTheory ProbabilityTheory InnerProductSpace
open scoped RealInnerProductSpace NNReal
namespace AcceleratedLogConcave.Conditional.Centering
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Centering at the true mean cannot increase the quadratic moment. -/
theorem integral_centered_norm_sq_le {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {f : Ω → E} (hf : MemLp f 2 μ) :
    (∫ z, ‖f z - ∫ w, f w ∂μ‖ ^ 2 ∂μ) ≤ ∫ z, ‖f z‖ ^ 2 ∂μ := by
  let m := ∫ w, f w ∂μ
  have hi := hf.integrable (by norm_num : (1 : ENNReal) ≤ 2)
  have hinner := (innerSL ℝ m).integrable_comp hi
  have he := (innerSL ℝ m).integral_comp_comm hi
  change Integrable (fun z => inner ℝ m (f z)) μ at hinner
  have his : Integrable (fun z => ‖f z‖ ^ 2 - 2 * inner ℝ m (f z)) μ :=
    hf.norm.integrable_sq.sub (hinner.const_mul 2)
  have hnorm := hf.norm.integrable_sq
  have hpoint (z : Ω) : ‖f z - m‖ ^ 2 = ‖f z‖ ^ 2 - 2 * inner ℝ m (f z) + ‖m‖ ^ 2 := by
    rw [norm_sub_sq_real, real_inner_comm m (f z)]
  change (∫ z, ‖f z - m‖ ^ 2 ∂μ) ≤ _
  simp_rw [hpoint]
  rw [integral_add his (integrable_const _),
    integral_sub hnorm (hinner.const_mul 2), integral_const_mul,
    integral_const, probReal_univ, one_smul]
  have he' : (∫ z, inner ℝ m (f z) ∂μ) = ‖m‖ ^ 2 := by
    simpa only [innerSL_apply_apply, m, real_inner_self_eq_norm_sq] using he
  rw [he']
  nlinarith [sq_nonneg ‖m‖]

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The dimension factor for a Lipschitz Gaussian observable is explicit. -/
theorem gaussian_centered_norm_sq_le {f : E → E} {C : ℝ≥0}
    (hf : LipschitzWith C f) :
    (∫ z, ‖f z - ∫ w, f w ∂stdGaussian E‖ ^ 2 ∂stdGaussian E) ≤
      (C : ℝ)^2 * (Module.finrank ℝ E : ℝ) := by
  let μ := stdGaussian E
  let g : E → E := fun z => f z - f 0
  have hg : Continuous g := hf.continuous.sub continuous_const
  have hb (z : E) : ‖g z‖ ≤ (C : ℝ) * ‖z‖ := by
    simpa only [g, dist_eq_norm, sub_zero] using hf.dist_le_mul z 0
  have hgm : MemLp g 2 μ := Gibbs.memLp_two_stdGaussian_of_affine_bound hg C 0
    (fun z => by simpa using hb z)
  have hfm : MemLp f 2 μ := by
    convert hgm.add (memLp_const (f 0)) using 1
    ext z
    simp [g]
  have hgi := hgm.integrable (by norm_num : (1 : ENNReal) ≤ 2)
  have hfi := hfm.integrable (by norm_num : (1 : ENNReal) ≤ 2)
  have hmean : (∫ w, g w ∂μ) = (∫ w, f w ∂μ) - f 0 := by
    simp only [g, integral_sub hfi (integrable_const _), integral_const,
      probReal_univ, one_smul]
  have hc := integral_centered_norm_sq_le hgm
  have he (z : E) : g z - ∫ w, g w ∂μ = f z - ∫ w, f w ∂μ := by
    rw [hmean]
    dsimp [g]
    abel
  simp_rw [he] at hc
  refine hc.trans ?_
  have hz : Integrable (fun z : E => ‖z‖^2) μ :=
    (IsGaussian.memLp_two_id (μ := μ)).norm.integrable_sq
  have hm := integral_mono hgm.norm.integrable_sq (hz.const_mul ((C : ℝ)^2))
    (fun z => show ‖g z‖^2 ≤ (C : ℝ)^2 * ‖z‖^2 by
      nlinarith [sq_le_sq₀ (norm_nonneg (g z)) (by positivity : 0 ≤ (C : ℝ)*‖z‖) |>.mpr (hb z)])
  simpa only [integral_const_mul, μ, Gibbs.integral_norm_sq_stdGaussian] using hm

end AcceleratedLogConcave.Conditional.Centering