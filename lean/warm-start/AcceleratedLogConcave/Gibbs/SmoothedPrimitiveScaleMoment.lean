import AcceleratedLogConcave.Channels.TerminalHeatBias
import AcceleratedLogConcave.Oracle.TerminalMean

/-! Original-data second moments of the physical primitive scale under a
Gaussian-smoothed Gibbs law. Normalization, position and score moments are
derived from the original C2 Hessian bounds; zero noise and dimension are allowed. -/
noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
open scoped NNReal RealInnerProductSpace
namespace AcceleratedLogConcave.Gibbs.SmoothedPrimitiveScaleMoment
variable {d : ℕ} {V : EuclideanSpace ℝ (Fin d) → ℝ} {m : ℝ}
  (hV : ContDiff ℝ 2 V) (hm : 0<m)
  (hlo : ∀ x w,m*‖w‖^2≤fderiv ℝ (fderiv ℝ V) x w w)
  (hup : ∀ x w,fderiv ℝ (fderiv ℝ V) x w w≤‖w‖^2)
local notation "piV" => (volume.tilted (fun x => -V x))
local notation "E" => EuclideanSpace ℝ (Fin d)

include hV hm hlo hup in
/-- The original Gibbs law has a genuine integrable score square and the
sharp dimension payment, with all tail assumptions derived internally. -/
theorem gibbs_score_square :
    Integrable (fun x => ‖gradient V x‖^2) piV ∧
      (∫ x,‖gradient V x‖^2 ∂piV)≤(d:ℝ) := by
  have hZ := integrable_exp_neg_of_hessian_lower hV hm hlo
  have hp : Integrable (fun x : E => ‖x‖^2) piV := by
    apply (integrable_tilted_iff hZ _).mpr
    simpa only [smul_eq_mul,mul_comm] using
      integrable_norm_pow_mul_exp_neg_of_hessian_lower hV hm hlo 2
  have hu : ∀ x w,fderiv ℝ (fderiv ℝ V) x w w≤(1:ℝ)*‖w‖^2 := by
    simpa only [one_mul] using hup
  refine ⟨integrable_tilted_gradient_norm_sq_of_hessian_bounds hV hlo hu hp,?_⟩
  simpa only [finrank_euclideanSpace_fin,mul_one] using
    integral_tilted_gradient_norm_sq_le_finrank_mul hV hZ hlo hu hp

include hV in
private theorem gradient_continuous : Continuous (gradient V) :=
  (InnerProductSpace.toDual ℝ E).symm.continuous.comp (hV.continuous_fderiv (by norm_num))

include hV hm hlo hup in
/-- Gaussian smoothing at covariance v<=1 costs at most four dimension units
in the original score second moment. -/
theorem smoothed_score_square (v : ℝ≥0) (hv : (v:ℝ)≤1) :
    Integrable (fun x => ‖gradient V x‖^2) (Channels.forward piV v) ∧
      (∫ x,‖gradient V x‖^2 ∂Channels.forward piV v)≤4*(d:ℝ) := by
  have hZ := integrable_exp_neg_of_hessian_lower hV hm hlo
  let _ : IsProbabilityMeasure piV := isProbabilityMeasure_tilted hZ
  obtain ⟨hg,hgBound⟩ := gibbs_score_square hV hm hlo hup
  have hn := Channels.TerminalHeatBiasAux.integrable_norm_sq_noise (d := d) v
  have hzero : ∀ x w,0≤fderiv ℝ (fderiv ℝ V) x w w := by
    intro x w
    exact (mul_nonneg hm.le (sq_nonneg _)).trans (hlo x w)
  have hLip : LipschitzWith 1 (gradient V) := gradient_lipschitz_of_hessian_bounds hV (by norm_num : (0:ℝ)≤1)
    hzero (by simpa only [one_mul] using hup)
  have hpoint (z : E × E) : ‖gradient V (z.1+z.2)‖^2≤2*‖gradient V z.1‖^2+2*‖z.2‖^2 := by
    have hd : ‖gradient V (z.1+z.2)-gradient V z.1‖≤‖z.2‖ := by
      simpa only [dist_eq_norm,NNReal.coe_one,one_mul,add_sub_cancel_left] using hLip.dist_le_mul (z.1+z.2) z.1
    have ht : ‖gradient V (z.1+z.2)‖≤‖gradient V z.1‖+‖z.2‖ := by
      calc
        _ = ‖(gradient V (z.1+z.2)-gradient V z.1)+gradient V z.1‖ := by congr 1; module
        _ ≤ ‖gradient V (z.1+z.2)-gradient V z.1‖+‖gradient V z.1‖ := norm_add_le _ _
        _ ≤ _ := by linarith
    nlinarith [norm_nonneg (gradient V (z.1+z.2)),norm_nonneg (gradient V z.1),norm_nonneg z.2,
      sq_nonneg (‖gradient V z.1‖-‖z.2‖)]
  have hdom : Integrable (fun z : E × E => 2*‖gradient V z.1‖^2+2*‖z.2‖^2)
      ((piV).prod (Channels.noise v)) :=
    ((hg.comp_fst (Channels.noise v)).const_mul 2).add ((hn.comp_snd piV).const_mul 2)
  have hscoreCont : Continuous (fun x : E => ‖gradient V x‖^2) := (gradient_continuous hV).norm.pow 2
  have hprod : Integrable (fun z : E × E => ‖gradient V (z.1+z.2)‖^2)
      ((piV).prod (Channels.noise v)) := by
    refine hdom.mono' (hscoreCont.comp (continuous_fst.add continuous_snd)).aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall (fun z => by simpa only [Real.norm_eq_abs,abs_sq] using hpoint z)
  have hforward : Integrable (fun x => ‖gradient V x‖^2) (Channels.forward piV v) := by
    change Integrable (fun x => ‖gradient V x‖^2) (((piV).prod (Channels.noise v)).map (fun z => z.1+z.2))
    exact (integrable_map_measure hscoreCont.aestronglyMeasurable (by fun_prop)).mpr hprod
  refine ⟨hforward,?_⟩
  change (∫ x,‖gradient V x‖^2 ∂(((piV).prod (Channels.noise v)).map (fun z => z.1+z.2)))≤_
  rw [integral_map (by fun_prop) hscoreCont.aestronglyMeasurable]
  have hi := integral_mono hprod hdom hpoint
  have hf : (∫ z : E × E,‖gradient V z.1‖^2 ∂(piV).prod (Channels.noise v)) = ∫ x,‖gradient V x‖^2 ∂piV := by
    rw [integral_prod _ (hg.comp_fst (Channels.noise v))]
    simp
  have hs : (∫ z : E × E,‖z.2‖^2 ∂(piV).prod (Channels.noise v)) = ∫ x : E,‖x‖^2 ∂Channels.noise v := by
    rw [integral_prod _ (hn.comp_snd piV)]
    simp
  rw [integral_add ((hg.comp_fst (Channels.noise v)).const_mul 2) ((hn.comp_snd piV).const_mul 2),
    integral_const_mul,integral_const_mul,hf,hs,Channels.TerminalHeatBiasAux.integral_norm_sq_noise] at hi
  have hvd := mul_le_mul_of_nonneg_left hv (Nat.cast_nonneg d : (0:ℝ)≤d)
  nlinarith

include hV in
/-- The actual inverse input scaling cancels in the original gradient query. -/
theorem primitiveScale_eq (h : ℝ) (hh : 0<h) (x : E) :
    primitiveScale (Oracle.scaledPotential V (Real.sqrt h)) ((Real.sqrt h)⁻¹ • x)=
      Real.sqrt (d:ℝ)+Real.sqrt h*‖gradient V x‖ := by
  unfold primitiveScale
  rw [Oracle.gradient_scaled_potential (hV.of_le (by norm_num))]
  rw [smul_smul,mul_inv_cancel₀ (Real.sqrt_pos.mpr hh).ne',one_smul,norm_smul,
    Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg h)]
  simp only [finrank_euclideanSpace_fin]

include hV hm hlo hup in
/-- The physical primitive scale has an integrable square bounded by 10d
under every covariance-v smoothed original Gibbs law with v<=1 and 0<h<=1. -/
theorem primitiveScale_square (h : ℝ) (hh : 0<h) (hh1 : h≤1) (v : ℝ≥0) (hv : (v:ℝ)≤1) :
    Integrable (fun x => (primitiveScale (Oracle.scaledPotential V (Real.sqrt h))
      ((Real.sqrt h)⁻¹ • x))^2) (Channels.forward piV v) ∧
    (∫ x,(primitiveScale (Oracle.scaledPotential V (Real.sqrt h))
      ((Real.sqrt h)⁻¹ • x))^2 ∂Channels.forward piV v)≤10*(d:ℝ) := by
  have hZ := integrable_exp_neg_of_hessian_lower hV hm hlo
  let _ : IsProbabilityMeasure piV := isProbabilityMeasure_tilted hZ
  let _ : IsProbabilityMeasure (Channels.forward piV v) := by unfold Channels.forward; infer_instance
  obtain ⟨hg,hgBound⟩ := smoothed_score_square hV hm hlo hup v hv
  have hpoint (x : E) : (primitiveScale (Oracle.scaledPotential V (Real.sqrt h))
      ((Real.sqrt h)⁻¹ • x))^2≤2*(d:ℝ)+2*h*‖gradient V x‖^2 := by
    rw [primitiveScale_eq hV h hh]
    have hd := Real.sq_sqrt (Nat.cast_nonneg d : (0:ℝ)≤d)
    have hs := Real.sq_sqrt hh.le
    nlinarith [sq_nonneg (Real.sqrt (d:ℝ)-Real.sqrt h*‖gradient V x‖)]
  have hdom : Integrable (fun x => 2*(d:ℝ)+2*h*‖gradient V x‖^2) (Channels.forward piV v) :=
    (integrable_const _).add (hg.const_mul (2*h))
  have hint : Integrable (fun x => (primitiveScale (Oracle.scaledPotential V (Real.sqrt h))
      ((Real.sqrt h)⁻¹ • x))^2) (Channels.forward piV v) := by
    refine hdom.mono' ?_ (Filter.Eventually.of_forall (fun x => by
      simpa only [Real.norm_eq_abs,abs_sq] using hpoint x))
    simp_rw [primitiveScale_eq hV h hh]
    exact ((continuous_const.add ((gradient_continuous hV).norm.const_mul (Real.sqrt h))).pow 2).aestronglyMeasurable
  refine ⟨hint,?_⟩
  have hi := integral_mono hint hdom hpoint
  simp only [integral_add (integrable_const _) (hg.const_mul (2*h)),integral_const_mul,integral_const,
    probReal_univ,one_smul] at hi
  have hscore := mul_le_mul_of_nonneg_left hgBound (show 0≤2*h by positivity)
  have hdim := mul_le_mul_of_nonneg_right hh1 (Nat.cast_nonneg d : (0:ℝ)≤d)
  nlinarith

end AcceleratedLogConcave.Gibbs.SmoothedPrimitiveScaleMoment
