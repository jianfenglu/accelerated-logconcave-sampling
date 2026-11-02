import AcceleratedLogConcave.Oracle.MeanOriginalBounds
import AcceleratedLogConcave.Oracle.MeanBenchmarkMoments

/-! Quantitative scale moments at every actual main benchmark node. The
reference displacement is paid by the original direct-vector and one-step
residual bounds; no moment or current-call accuracy is assumed. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
namespace AcceleratedLogConcave.Oracle.MeanAllNodeMoments
open Numerics Numerics.MeanFlowLp Numerics.MeanResidualBridge Numerics.MeanCollocationLp
variable {D m : ℕ} (d : MeanFlowLp.Data (Fin D) m)

def displacementBudget (h₀ : ℝ) : ℝ :=
  directBudget d + MeanOriginalBounds.initializerBudget d h₀

def scaleSquareBudget (h₀ : ℝ) : ℝ :=
  2*(Gibbs.primitiveScale d.F d.x)^2+2*d.ell^2*(displacementBudget d h₀)^2

theorem reference_norm_le (h₀ : ℝ) (hmesh : MeshConditions d h₀)
    (hhalf : contraction d h₀≤1/2) (i : d.G.MeanNode) :
    ‖reference d i‖≤displacementBudget d h₀ := by
  have he := MeanOriginalBounds.initializer_norm_le d h₀ hmesh hhalf i
  unfold MeanOriginalBounds.initializerError at he
  rw [AffineResidual.toLp_eq_of_ae _ (raw_error_ae d 0 i)] at he
  have hd := (norm_le_pi_norm (lpGraph d).direct i).trans (norm_direct_le d)
  have hh := norm_sub_le ((lpGraph d).direct i) ((lpGraph d).direct i-reference d i)
  rw [sub_sub_cancel] at hh
  exact hh.trans (add_le_add hd he)

theorem displacementBudget_nonneg (h₀ : ℝ) (hmesh : MeshConditions d h₀)
    (hhalf : contraction d h₀≤1/2) : 0≤displacementBudget d h₀ :=
  add_nonneg ((norm_nonneg _).trans (norm_direct_le d))
    (MeanOriginalBounds.initializerBudget_nonneg d h₀ hmesh hhalf)

private theorem integral_reference_norm_sq (i : d.G.MeanNode) :
    (∫ ω : Seed d, ‖reference d i ω‖^2 ∂seedMeasure d)=‖reference d i‖^2 := by
  rw [← real_inner_self_eq_norm_sq,L2.inner_def]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun ω => (real_inner_self_eq_norm_sq _).symm

/-- Every literal main-node scale has an explicit squared moment, including
zero curvature and dimension. Mesh and half-contraction restrictions remain
visible and are the same ones used by the actual receiver. -/
theorem node_scale_square_le (h₀ : ℝ) (hmesh : MeshConditions d h₀)
    (hhalf : contraction d h₀≤1/2) (i : d.G.MeanNode) :
    (∫ ω, MeanBenchmarkMoments.nodeScale d i ω ^ 2 ∂seedMeasure d)≤scaleSquareBudget d h₀ := by
  let B := Gibbs.primitiveScale d.F d.x
  have hB : 0≤B := Gibbs.primitiveScale_nonneg _ _
  have hpt : ∀ᵐ ω ∂seedMeasure d,
      MeanBenchmarkMoments.nodeScale d i ω ^ 2 ≤ 2*B^2+2*d.ell^2*‖reference d i ω‖^2 := by
    filter_upwards [MeanResidualBridge.rawReference_ae d i] with ω hω
    change rawReference d i ω = d.x + reference d i ω at hω
    have hg := Gibbs.gradient_lipschitz_of_hessian_bounds d.hF d.hell d.hlo d.hup
    have hb := hg.dist_le_mul (d.x+reference d i ω) d.x
    simp only [dist_eq_norm,add_sub_cancel_left] at hb
    change ‖gradient d.F (d.x+reference d i ω)-gradient d.F d.x‖ ≤ d.ell*‖reference d i ω‖ at hb
    have hn := norm_add_le (gradient d.F (d.x+reference d i ω)-gradient d.F d.x) (gradient d.F d.x)
    rw [sub_add_cancel] at hn
    have hs : MeanBenchmarkMoments.nodeScale d i ω≤B+d.ell*‖reference d i ω‖ := by
      dsimp [MeanBenchmarkMoments.nodeScale,Gibbs.primitiveScale,B]
      rw [hω]
      linarith
    have hn0 : 0≤MeanBenchmarkMoments.nodeScale d i ω := Gibbs.primitiveScale_nonneg _ _
    have hs2 := (sq_le_sq₀ hn0 (add_nonneg hB (mul_nonneg d.hell (norm_nonneg _)))).2 hs
    nlinarith [sq_nonneg (B-d.ell*‖reference d i ω‖)]
  have href := (Lp.memLp (reference d i)).norm.integrable_sq
  have hi := integral_mono_ae (MeanBenchmarkMoments.node_scale_square_integrable d i)
    ((integrable_const _).add (href.const_mul (2*d.ell^2))) hpt
  simp only [Pi.add_apply] at hi
  rw [integral_add (integrable_const _) (href.const_mul (2*d.ell^2)),
    integral_const,probReal_univ,one_smul,integral_const_mul,integral_reference_norm_sq] at hi
  exact hi.trans (add_le_add_right (mul_le_mul_of_nonneg_left
    ((sq_le_sq₀ (norm_nonneg _) (displacementBudget_nonneg d h₀ hmesh hhalf)).2
      (reference_norm_le d h₀ hmesh hhalf i)) (show (0:ℝ)≤2*d.ell^2 from mul_nonneg (by norm_num) (sq_nonneg d.ell))) _)

end AcceleratedLogConcave.Oracle.MeanAllNodeMoments
