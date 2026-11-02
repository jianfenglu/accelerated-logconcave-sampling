import AcceleratedLogConcave.Oracle.MeanAllNodeMoments

/-! Dimension-free reductions of the literal mean benchmark scale budgets.
The only residual input is a deterministic payment for the explicit original
smooth budget. No executed-output or current-call accuracy is assumed. -/
noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
namespace AcceleratedLogConcave.Oracle.MeanSourceScaleMoments
open Numerics Numerics.MeanFlowLp Numerics.MeanCollocationLp Numerics.AffineGraph
variable {D m : ℕ} (d : MeanFlowLp.Data (Fin D) m)
local notation "B" => Gibbs.primitiveScale d.F d.x
local notation "s" => Real.sqrt (Module.finrank ℝ (Point D))
local notation "g" => ‖gradient d.F d.x‖

/-- Literal seed scale at radius at most one. -/
theorem seedBudget_le (hr : d.r≤1) : seedBudget d≤2*B := by
  have hg := norm_nonneg (gradient d.F d.x)
  have hs := Real.sqrt_nonneg (Module.finrank ℝ (Point D) : ℝ)
  unfold seedBudget Gibbs.primitiveScale
  nlinarith [mul_le_mul_of_nonneg_right hr hg]

/-- Multiplying the actual direct-vector budget by curvature cancels the
radius under the source slope guard. -/
theorem directBudget_curvature_le (hr : d.r≤1) (hslope : d.ell*d.r≤1) :
    d.ell*directBudget d≤16*B := by
  have hseed := seedBudget_le d hr
  have hseed0 := seedBudget_nonneg d
  calc
    d.ell*directBudget d = 8*(d.ell*d.r)*seedBudget d := by unfold directBudget; ring
    _ ≤ 8*1*seedBudget d := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hslope (by norm_num)) hseed0
    _ ≤ 16*B := by linarith

/-- The primitive mean payment is at most twice the original source scale. -/
theorem meanBudget_le (hr : d.r≤1) (hslope : d.ell*d.r≤1) : meanBudget d≤2*B := by
  have hg := norm_nonneg (gradient d.F d.x)
  have hs := Real.sqrt_nonneg (Module.finrank ℝ (Point D) : ℝ)
  have hinner : s+d.r*g≤B := by
    change _≤s+g
    nlinarith [mul_le_mul_of_nonneg_right hr hg]
  have hi0 : 0≤s+d.r*g := add_nonneg hs (mul_nonneg d.hr.le hg)
  calc
    meanBudget d = g+(d.ell*d.r)*(s+d.r*g) := rfl
    _ ≤ g+1*(s+d.r*g) := add_le_add_right (mul_le_mul_of_nonneg_right hslope hi0) g
    _ ≤ 2*B := by
      change s+d.r*g≤s+g at hinner
      change _≤2*(s+g)
      linarith

/-- The curvature-weighted original initializer is bounded without dividing
by curvature or by the source scale. Zero curvature and dimension are kept. -/
theorem initializer_curvature_le (h₀ : ℝ) (hr : d.r≤1) (hslope : d.ell*d.r≤1)
    (hhalf : contraction d h₀≤1/2)
    (hres : d.ell*MeanOriginalBounds.residualBudget d h₀≤B) :
    d.ell*MeanOriginalBounds.initializerBudget d h₀≤20*B := by
  have hd := directBudget_curvature_le d hr hslope
  have hm := meanBudget_le d hr hslope
  have hrow : d.ell*rowMass d h₀≤1/2 := hhalf
  have hd0 : 0≤d.ell*directBudget d := mul_nonneg d.hell
    (mul_nonneg (mul_nonneg (by norm_num) d.hr.le) (seedBudget_nonneg d))
  have hm0 : 0≤meanBudget d := by
    unfold meanBudget radiusBudget
    positivity [d.hell,d.hr.le]
  have hmul := mul_le_mul_of_nonneg_right hrow (add_nonneg hd0 hm0)
  unfold MeanOriginalBounds.initializerBudget
  nlinarith

/-- Actual main-node displacement payment, still using the literal original
smooth initializer and its explicit residual budget. -/
theorem displacement_curvature_le (h₀ : ℝ) (hr : d.r≤1) (hslope : d.ell*d.r≤1)
    (hhalf : contraction d h₀≤1/2)
    (hres : d.ell*MeanOriginalBounds.residualBudget d h₀≤B) :
    d.ell*MeanAllNodeMoments.displacementBudget d h₀≤36*B := by
  have hd := directBudget_curvature_le d hr hslope
  have hi := initializer_curvature_le d h₀ hr hslope hhalf hres
  unfold MeanAllNodeMoments.displacementBudget
  nlinarith

/-- Constant 64 pays the actual all-node squared scale moment in the source
units required by lower-child error averaging. -/
theorem main_scale_square_le (h₀ : ℝ) (hr : d.r≤1) (hslope : d.ell*d.r≤1)
    (hmesh : MeshConditions d h₀) (hhalf : contraction d h₀≤1/2)
    (hres : d.ell*MeanOriginalBounds.residualBudget d h₀≤B) :
    MeanAllNodeMoments.scaleSquareBudget d h₀≤(64*B)^2 := by
  have hb := Gibbs.primitiveScale_nonneg d.F d.x
  have hd := displacement_curvature_le d h₀ hr hslope hhalf hres
  have hd0 := mul_nonneg d.hell (MeanAllNodeMoments.displacementBudget_nonneg d h₀ hmesh hhalf)
  have hsq := (sq_le_sq₀ hd0 (mul_nonneg (by norm_num) hb)).2 hd
  unfold MeanAllNodeMoments.scaleSquareBudget
  nlinarith [sq_nonneg B]

theorem main_scale_sqrt_le (h₀ : ℝ) (hr : d.r≤1) (hslope : d.ell*d.r≤1)
    (hmesh : MeshConditions d h₀) (hhalf : contraction d h₀≤1/2)
    (hres : d.ell*MeanOriginalBounds.residualBudget d h₀≤B) :
    Real.sqrt (MeanAllNodeMoments.scaleSquareBudget d h₀)≤64*B := by
  apply Real.sqrt_le_iff.mpr
  exact ⟨mul_nonneg (by norm_num) (Gibbs.primitiveScale_nonneg _ _),
    main_scale_square_le d h₀ hr hslope hmesh hhalf hres⟩

/-- Original posterior/interpolation position moment at radius at most one. -/
theorem position_square_le (hr : d.r≤1) : MeanBenchmarkMoments.positionSquareBudget d≤4*B^2 := by
  have hg := norm_nonneg (gradient d.F d.x)
  have hs := Real.sqrt_nonneg (Module.finrank ℝ (Point D) : ℝ)
  have hb := Gibbs.primitiveScale_nonneg d.F d.x
  have hinner : s+d.r*g≤B := by
    change _≤s+g
    nlinarith [mul_le_mul_of_nonneg_right hr hg]
  have hi0 : 0≤s+d.r*g := add_nonneg hs (mul_nonneg d.hr.le hg)
  have hsq := (sq_le_sq₀ hi0 hb).2 hinner
  have hsB : s≤B := by change s≤s+g; linarith
  have hs2 := (sq_le_sq₀ hs hb).2 hsB
  have hdim := Real.sq_sqrt (Nat.cast_nonneg (Module.finrank ℝ (Point D)))
  unfold MeanBenchmarkMoments.positionSquareBudget
  nlinarith

/-- The designated paid-final scale uses its exact stationary position law;
no smooth residual payment enters this sharper constant four bound. -/
theorem final_scale_square_le (hr : d.r≤1) (hslope : d.ell*d.r≤1) :
    MeanBenchmarkMoments.finalScaleSquareBudget d≤(4*B)^2 := by
  have hp := position_square_le d hr
  have hp0 : 0≤MeanBenchmarkMoments.positionSquareBudget d := by
    unfold MeanBenchmarkMoments.positionSquareBudget
    positivity
  have ha0 : 0≤d.ell*d.r*backwardEnd d.G.R := mul_nonneg (mul_nonneg d.hell d.hr.le) d.G.backwardEnd_pos.le
  have ha1 : d.ell*d.r*backwardEnd d.G.R≤1 :=
    (mul_le_mul_of_nonneg_right hslope d.G.backwardEnd_pos.le).trans (by simpa using d.G.backwardEnd_lt_one.le)
  have ha2 := (sq_le_sq₀ ha0 (by norm_num : (0:ℝ)≤1)).2 ha1
  have hmul := mul_le_mul_of_nonneg_right ha2 hp0
  unfold MeanBenchmarkMoments.finalScaleSquareBudget
  nlinarith [sq_nonneg B]

theorem final_scale_sqrt_le (hr : d.r≤1) (hslope : d.ell*d.r≤1) :
    Real.sqrt (MeanBenchmarkMoments.finalScaleSquareBudget d)≤4*B := by
  apply Real.sqrt_le_iff.mpr
  exact ⟨mul_nonneg (by norm_num) (Gibbs.primitiveScale_nonneg _ _),final_scale_square_le d hr hslope⟩

end AcceleratedLogConcave.Oracle.MeanSourceScaleMoments
