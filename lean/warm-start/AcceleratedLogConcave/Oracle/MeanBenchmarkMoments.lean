import AcceleratedLogConcave.Numerics.MeanBenchmarkCoupling
import AcceleratedLogConcave.Oracle.PrivateBenchmarkMoments

/-! Primitive-scale payments at the actual common-seed mean benchmark centers.
The active-final bound uses the genuine stationary source position law and
its posterior second moment; no absolute compiler-output moment is assumed. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open MeasureTheory ProbabilityTheory Set
namespace AcceleratedLogConcave.Oracle.MeanBenchmarkMoments
open Numerics Numerics.MeanFlowLp Numerics.MeanResidualBridge Conditional
variable {D m : ℕ} (d : MeanFlowLp.Data (Fin D) m)
local notation "E" => EuclideanSpace ℝ (Fin D)

/-- Primitive scale at any literal benchmark inventory node. -/
def nodeScale (i : d.G.MeanNode) (ω : Seed d) : ℝ :=
  Gibbs.primitiveScale d.F (rawReference d i ω)

private theorem primitive_scale_memLp {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → E) (hf : MemLp f 2 μ) :
    MemLp (fun ω => Gibbs.primitiveScale d.F (f ω)) 2 μ := by
  have hg := Gibbs.gradient_lipschitz_of_hessian_bounds d.hF d.hell d.hlo d.hup
  have hl : LipschitzWith ⟨d.ell,d.hell⟩ (fun y : E => gradient d.F y-gradient d.F 0) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [dist_sub_right] using hg.dist_le_mul x y
  have hz := hl.comp_memLp (sub_self (gradient d.F 0)) hf
  have hgrad : MemLp (fun ω => gradient d.F (f ω)) 2 μ := by
    convert hz.add (memLp_const (gradient d.F 0)) using 1
    funext ω
    simp [Function.comp_def]
  exact (memLp_const (Real.sqrt (Module.finrank ℝ E))).add hgrad.norm

theorem node_scale_memLp (i : d.G.MeanNode) : MemLp (nodeScale d i) 2 (seedMeasure d) :=
  primitive_scale_memLp d (seedMeasure d) (rawReference d i) (rawReference_memLp d i)

theorem node_scale_square_integrable (i : d.G.MeanNode) :
    Integrable (fun ω => nodeScale d i ω ^ 2) (seedMeasure d) :=
  (node_scale_memLp d i).integrable_sq

private theorem norm_square_transport {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {ν : Measure E} {f : X → E} (hp : MeasurePreserving f μ ν) :
    (∫ z, ‖f z‖^2 ∂μ) = ∫ y, ‖y‖^2 ∂ν := by
  have hg : StronglyMeasurable (fun y : E => ‖y‖^2) := by fun_prop
  have hgmap : AEStronglyMeasurable (fun y : E => ‖y‖^2) (μ.map f) := hg.aestronglyMeasurable
  have hi := integral_map hp.aemeasurable hgmap
  rw [hp.map_eq] at hi
  exact hi.symm

/-- Explicit posterior/interpolation position budget from the original F,x,r. -/
def positionSquareBudget : ℝ :=
  2*(Real.sqrt (Module.finrank ℝ E)+d.r*‖gradient d.F d.x‖)^2 +
    2*(Module.finrank ℝ E)

private theorem interpolation_square_integral_le :
    (∫ y : E, ‖y‖^2 ∂interpolationLaw d.F d.x d.r (AffineGraph.backwardEnd d.G.R)) ≤
      positionSquareBudget d := by
  let μ := baseLaw d.F d.x d.r
  let γ := stdGaussian E
  let b := AffineGraph.backwardEnd d.G.R
  let : IsProbabilityMeasure μ := baseLaw_isProbabilityMeasure d.hF d.hlo d.x d.r
  have hz0 : MemLp (id : E → E) 2 μ := Gibbs.primitive_memLp_two_id d.hF d.hlo d.x d.r
  have hz : MemLp (Prod.fst : E × E → E) 2 (μ.prod γ) :=
    hz0.comp_measurePreserving measurePreserving_fst
  have hn : MemLp (Prod.snd : E × E → E) 2 (μ.prod γ) :=
    (IsGaussian.memLp_two_id (μ := γ)).comp_measurePreserving measurePreserving_snd
  have hi : MemLp (interpolationMap b : E × E → E) 2 (μ.prod γ) :=
    (hz.const_smul b).add (hn.const_smul (Real.sqrt (conditionalVariance b)))
  have hb0 : 0 ≤ b := d.G.backwardEnd_pos.le
  have hb1 : b ≤ 1 := d.G.backwardEnd_lt_one.le
  have hs0 := Real.sqrt_nonneg (conditionalVariance b)
  have hs1 : Real.sqrt (conditionalVariance b) ≤ 1 :=
    Real.sqrt_le_one.mpr (by dsimp [conditionalVariance]; nlinarith [sq_nonneg b])
  have hpt (z : E × E) : ‖interpolationMap b z‖^2 ≤ 2*‖z.1‖^2+2*‖z.2‖^2 := by
    have hh : ‖interpolationMap b z‖ ≤ ‖z.1‖+‖z.2‖ := by
      calc
        _ ≤ ‖b • z.1‖+‖Real.sqrt (conditionalVariance b) • z.2‖ := norm_add_le _ _
        _ = b*‖z.1‖+Real.sqrt (conditionalVariance b)*‖z.2‖ := by
          rw [norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs,
            abs_of_nonneg hb0,abs_of_nonneg hs0]
        _ ≤ _ := add_le_add (mul_le_of_le_one_left (norm_nonneg _) hb1)
          (mul_le_of_le_one_left (norm_nonneg _) hs1)
    nlinarith [norm_nonneg (interpolationMap b z),norm_nonneg z.1,norm_nonneg z.2,
      sq_nonneg (‖z.1‖-‖z.2‖)]
  have hh := integral_mono hi.norm.integrable_sq
    ((hz.norm.integrable_sq.const_mul 2).add (hn.norm.integrable_sq.const_mul 2)) hpt
  simp only [Pi.add_apply] at hh
  rw [integral_add (hz.norm.integrable_sq.const_mul 2) (hn.norm.integrable_sq.const_mul 2),
    integral_const_mul,integral_const_mul] at hh
  have hzint : (∫ z : E × E, ‖z.1‖^2 ∂μ.prod γ) = ∫ z : E, ‖z‖^2 ∂μ :=
    norm_square_transport measurePreserving_fst
  have hnint : (∫ z : E × E, ‖z.2‖^2 ∂μ.prod γ) = (Module.finrank ℝ E : ℝ) := by
    rw [norm_square_transport measurePreserving_snd,Gibbs.integral_norm_sq_stdGaussian]
  rw [hzint,hnint] at hh
  have hp := Gibbs.primitive_second_moment_le d.hF d.hell d.hlo d.hup d.hr d.x
  have hs := Real.sq_sqrt (integral_nonneg (fun z : E => sq_nonneg ‖z‖) (μ := μ))
  have hbp : (∫ z : E, ‖z‖^2 ∂μ) ≤
      (Real.sqrt (Module.finrank ℝ E)+d.r*‖gradient d.F d.x‖)^2 := by
    change Real.sqrt (∫ z : E, ‖z‖^2 ∂μ) ≤ _ at hp
    nlinarith [Real.sqrt_nonneg (∫ z : E, ‖z‖^2 ∂μ),
      Real.sqrt_nonneg (Module.finrank ℝ E),mul_nonneg d.hr.le (norm_nonneg (gradient d.F d.x))]
  have hmap : (∫ y : E, ‖y‖^2 ∂interpolationLaw d.F d.x d.r b) =
      ∫ z : E × E, ‖interpolationMap b z‖^2 ∂μ.prod γ := by
    rw [interpolationLaw,integral_map (by unfold interpolationMap; fun_prop) (by fun_prop)]
  rw [hmap]
  unfold positionSquareBudget
  linarith

/-- The genuine stationary centering law fixes every final-time position
moment; no conditional statement given original parent P is used. -/
theorem position_square_integral_le (t : ℝ) :
    (∫ ω : Seed d, ‖position d t ω‖^2 ∂seedMeasure d) ≤ positionSquareBudget d := by
  have hp : MeasurePreserving (position d t) (seedMeasure d)
      (interpolationLaw d.F d.x d.r (AffineGraph.backwardEnd d.G.R)) :=
    (CenteringFlowLp.position_preserving (kernelData d)).comp
      ((CenteringFlowLp.phase_preserving (kernelData d) (d.sigma/2) (half_pos d.hsigma) t).comp
        (phase_projection_preserving d))
  rw [norm_square_transport hp]
  exact interpolation_square_integral_le d

/-- The exact active-final benchmark center, with its actual stationary phase. -/
def finalCenter (i : Fin m) (ω : Seed d) : E := rawReference d (.center d.G i) ω

theorem finalCenter_measurable (i : Fin m) : Measurable (finalCenter d i) := by
  have hp : Continuous (fun ω : Seed d => position d (AffineGraph.MeanGeometry.centerNode i) ω) :=
    (CenteringFlowLp.continuous_position (kernelData d) (d.sigma/2) (half_pos d.hsigma)).comp
      (continuous_const.prodMk continuous_fst)
  exact (continuous_const.add (hp.const_smul (d.r*AffineGraph.backwardEnd d.G.R))).measurable

/-- Primitive mean at the exact radius rR used by each active-final child. -/
def finalMean (i : Fin m) (ω : Seed d) : E :=
  Gibbs.primitiveMean d.F (finalCenter d i ω) (d.r*d.G.R)

theorem finalMean_measurable (i : Fin m) : Measurable (finalMean d i) :=
  (Gibbs.primitive_mean_lipschitz d.hF d.hell d.hlo d.hup
    (mul_pos d.hr d.G.R_pos)).continuous.measurable.comp (finalCenter_measurable d i)

/-- Quantitative squared scale budget for all actual active-final benchmark
centers. The parent potential and its original center gradient remain visible. -/
def finalScaleSquareBudget : ℝ :=
  2*(Gibbs.primitiveScale d.F d.x)^2 +
    2*(d.ell*d.r*AffineGraph.backwardEnd d.G.R)^2*positionSquareBudget d

theorem final_scale_square_integral_le (i : Fin m) :
    (∫ ω : Seed d, nodeScale d (.center d.G i) ω ^ 2 ∂seedMeasure d) ≤
      finalScaleSquareBudget d := by
  let a := d.ell*d.r*AffineGraph.backwardEnd d.G.R
  let B := Gibbs.primitiveScale d.F d.x
  have ha : 0 ≤ a := mul_nonneg (mul_nonneg d.hell d.hr.le) d.G.backwardEnd_pos.le
  have hb : 0 ≤ B := Gibbs.primitiveScale_nonneg _ _
  have hpt (ω : Seed d) : nodeScale d (.center d.G i) ω ^ 2 ≤
      2*B^2+2*a^2*‖position d (AffineGraph.MeanGeometry.centerNode i) ω‖^2 := by
    have hh := Gibbs.norm_primitive_score_sub_gradient_le d.hF d.hell d.hlo d.hup
      (mul_nonneg d.hr.le d.G.backwardEnd_pos.le) d.x (position d (AffineGraph.MeanGeometry.centerNode i) ω)
    have hn := norm_add_le
      (gradient d.F (d.x+(d.r*AffineGraph.backwardEnd d.G.R) • position d (AffineGraph.MeanGeometry.centerNode i) ω)-
        gradient d.F d.x) (gradient d.F d.x)
    rw [sub_add_cancel] at hn
    have hs0 : 0 ≤ nodeScale d (.center d.G i) ω := Gibbs.primitiveScale_nonneg _ _
    have hs : nodeScale d (.center d.G i) ω ≤ B+a*‖position d (AffineGraph.MeanGeometry.centerNode i) ω‖ := by
      dsimp [nodeScale,rawReference,rawCurves,AffineResidual.Mean.Curves.reference,
        AffineGraph.MeanGeometry.MeanNode.center,Gibbs.primitiveScale,B,a]
      nlinarith
    have hsq := (sq_le_sq₀ hs0 (add_nonneg hb (mul_nonneg ha (norm_nonneg _)))).2 hs
    nlinarith [sq_nonneg (B-a*‖position d (AffineGraph.MeanGeometry.centerNode i) ω‖)]
  have hy := (position_memLp d (AffineGraph.MeanGeometry.centerNode i)).norm.integrable_sq
  have hh := integral_mono (node_scale_square_integrable d (.center d.G i))
    ((integrable_const _).add (hy.const_mul (2*a^2))) hpt
  simp only [Pi.add_apply] at hh
  rw [integral_add (integrable_const _) (hy.const_mul (2*a^2)),
    integral_const,probReal_univ,one_smul,integral_const_mul] at hh
  exact hh.trans (add_le_add_right (mul_le_mul_of_nonneg_left
    (position_square_integral_le d (AffineGraph.MeanGeometry.centerNode i)) (by positivity : 0 ≤ 2*a^2)) _)

end AcceleratedLogConcave.Oracle.MeanBenchmarkMoments
