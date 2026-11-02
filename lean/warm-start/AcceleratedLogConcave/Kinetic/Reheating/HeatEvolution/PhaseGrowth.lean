import AcceleratedLogConcave.Kinetic.Reheating.HeatEvolution.PhaseJoint
import AcceleratedLogConcave.Kinetic.Reheating.HeatEvolution.Growth

/-! Uniform polynomial bounds and actual product-L2 integrability for the
position gradient and weighted generator of the joint compact phase heat core. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace
open scoped RealInnerProductSpace
namespace AcceleratedLogConcave.Kinetic.Reheating
open Analysis.Poisson AcceleratedLogConcave.HeatCalculus
variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι

/-- The position gradient of the actual phase quotient. -/
def compactPhaseHeatGradient {a b : ℝ} (F : ReferencePoissonFamily E a b)
    (f : E×E → ℝ) (t : ℝ) (z : E×E) : E :=
  gradient (fun x => compactPhaseHeatQuotient F f t (x,z.2)) z.1

/-- The actual negative weighted position Laplacian. -/
def compactPhaseHeatGenerator {a b : ℝ} (F : ReferencePoissonFamily E a b)
    (f : E×E → ℝ) (t : ℝ) (z : E×E) : ℝ :=
  weightedHeatGenerator (F.potential t) (fun x => compactPhaseHeatQuotient F f t (x,z.2)) z.1

theorem compactPhaseHeatQuotient_growth {a b : ℝ} (F : ReferencePoissonFamily E a b)
    {f : E×E → ℝ} (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f)
    (hheat : ∀ t ∈ Icc a b, F.law t = heatedLaw (F.law a) (t-a)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Icc a b, ∀ z,
      ‖compactPhaseHeatQuotient F f t z‖ ≤ C ∧
      ‖compactPhaseHeatGradient F f t z‖ ≤ C*(1+‖z.1‖) ∧
      ‖compactPhaseHeatGenerator F f t z‖ ≤ C*(1+‖z.1‖^2) := by
  obtain ⟨C₀,C₁,C₂,h₀,h₁,h₂,hn⟩ := compactPhaseHeatNumerator_derivative_bounds F hf hc hheat
  obtain ⟨C,hC,hb⟩ := compactHeatQuotient_growth_of_numerator_bounds F
    (fun p x => f (x,p)) (phase_position_slice_C2 hf) (phase_position_slice_compact hc)
    C₀ C₁ C₂ h₀ h₁ h₂ (fun p t ht x => hn t ht x p)
  exact ⟨C,hC,fun t ht z => hb z.2 t ht z.1⟩

theorem compactPhaseHeatGradient_continuous {a b : ℝ} (F : ReferencePoissonFamily E a b)
    {f : E×E → ℝ} (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f)
    (t : ℝ) (ht : t ∈ Icc a b) : Continuous (compactPhaseHeatGradient F f t) := by
  have hn := (compactPhaseHeatNumerator_fderiv_continuous F hf hc).comp
    ((continuous_const (y := t)).prodMk (continuous_id : Continuous (id : E×E → E×E)))
  have hng : Continuous (fun z : E×E => gradient (compactHeatNumerator F (fun y => f (y,z.2)) t) z.1) :=
    (toDual ℝ E).symm.continuous.comp hn
  have hp : Continuous (fun z : E×E => (F.density t z.1)⁻¹) :=
    ((reference_density_C2 F t ht).continuous.comp continuous_fst).inv₀
      (fun z => (reference_density_pos F t ht z.1).ne')
  have hq := compactPhaseHeatQuotient_continuous F hf.continuous hc t ht
  have hV : Continuous (fun z : E×E => gradient (F.potential t) z.1) :=
    F.gradient_continuous.comp (continuous_const.prodMk continuous_fst)
  have hh := (hp.smul hng).add (hq.smul hV)
  convert hh using 1
  funext z
  exact compactHeatQuotient_gradient F (phase_position_slice_C2 hf z.2)
    (phase_position_slice_compact hc z.2) t ht z.1

theorem compactPhaseHeatGenerator_continuous {a b : ℝ} (F : ReferencePoissonFamily E a b)
    {f : E×E → ℝ} (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f)
    (t : ℝ) (ht : t ∈ Icc a b) : Continuous (compactPhaseHeatGenerator F f t) := by
  have hn := (compactPhaseHeatNumerator_laplacian_continuous F hf hc).comp
    ((continuous_const (y := t)).prodMk (continuous_id : Continuous (id : E×E → E×E)))
  have hp := (reference_density_C2 F t ht).continuous.comp (continuous_fst : Continuous (Prod.fst : E×E → E))
  have hq := compactPhaseHeatQuotient_continuous F hf.continuous hc t ht
  have hG := compactPhaseHeatGradient_continuous F hf hc t ht
  have hV : Continuous (fun z : E×E => gradient (F.potential t) z.1) :=
    F.gradient_continuous.comp (continuous_const.prodMk continuous_fst)
  have hLap := (continuous_compactTestLaplacian (F.potential_C2 t)).comp
    (continuous_fst : Continuous (Prod.fst : E×E → E))
  have hh := ((hn.neg.div hp (fun z => (reference_density_pos F t ht z.1).ne')).add
    (hq.mul ((hV.norm.pow 2).sub hLap))).sub (hV.inner hG)
  convert hh using 1
  funext z
  exact compactHeatQuotient_generator F (phase_position_slice_C2 hf z.2)
    (phase_position_slice_compact hc z.2) t ht z.1

/-- The source Hessian supplies joint continuity of its genuine trace. -/
theorem reference_phase_potential_laplacian_continuous {a b : ℝ}
    (F : ReferencePoissonFamily E a b) :
    Continuous (fun z : ℝ×(E×E) => compactTestLaplacian (F.potential z.1) z.2.1) := by
  have hH : Continuous (fun z : ℝ×(E×E) => hessianOperator (F.potential z.1) z.2.1) :=
    F.hessian_continuous.comp (continuous_fst.prodMk (continuous_fst.comp continuous_snd))
  have hh : Continuous (fun z : ℝ×(E×E) => ∑ i, inner ℝ
      (hessianOperator (F.potential z.1) z.2.1 (EuclideanSpace.basisFun ι ℝ i))
      (EuclideanSpace.basisFun ι ℝ i)) := by fun_prop
  simpa only [inner_hessianOperator, compactTestLaplacian] using hh

/-- Joint continuity of the actual position gradient on the whole source strip. -/
theorem compactPhaseHeatGradient_continuousOn {a b : ℝ} (F : ReferencePoissonFamily E a b)
    {f : E×E → ℝ} (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f) :
    ContinuousOn (fun z : ℝ×(E×E) => compactPhaseHeatGradient F f z.1 z.2) (Icc a b ×ˢ univ) := by
  have hng : Continuous (fun z : ℝ×(E×E) =>
      gradient (compactHeatNumerator F (fun y => f (y,z.2.2)) z.1) z.2.1) :=
    (toDual ℝ E).symm.continuous.comp (compactPhaseHeatNumerator_fderiv_continuous F hf hc)
  have hp : ContinuousOn (fun z : ℝ×(E×E) => (F.density z.1 z.2.1)⁻¹) (Icc a b ×ˢ univ) :=
    (F.density_continuous.comp
      (show ContinuousOn (fun z : ℝ×(E×E) => (z.1,z.2.1)) (Icc a b ×ˢ univ) from
        (continuous_fst.prodMk (continuous_fst.comp continuous_snd)).continuousOn)
      (fun z hz => ⟨hz.1, mem_univ _⟩)).inv₀
      (fun z hz => (reference_density_pos F z.1 hz.1 z.2.1).ne')
  have hq := compactPhaseHeatQuotient_continuousOn F hf.continuous hc
  have hV : Continuous (fun z : ℝ×(E×E) => gradient (F.potential z.1) z.2.1) :=
    F.gradient_continuous.comp (continuous_fst.prodMk (continuous_fst.comp continuous_snd))
  apply ((hp.smul hng.continuousOn).add (hq.smul hV.continuousOn)).congr
  intro z hz
  exact compactHeatQuotient_gradient F (phase_position_slice_C2 hf z.2.2)
    (phase_position_slice_compact hc z.2.2) z.1 hz.1 z.2.1

/-- Joint continuity of the genuine weighted position generator. -/
theorem compactPhaseHeatGenerator_continuousOn {a b : ℝ} (F : ReferencePoissonFamily E a b)
    {f : E×E → ℝ} (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f) :
    ContinuousOn (fun z : ℝ×(E×E) => compactPhaseHeatGenerator F f z.1 z.2) (Icc a b ×ˢ univ) := by
  have hn := (compactPhaseHeatNumerator_laplacian_continuous F hf hc).continuousOn
    (s := Icc a b ×ˢ (univ : Set (E×E)))
  have hp : ContinuousOn (fun z : ℝ×(E×E) => F.density z.1 z.2.1) (Icc a b ×ˢ univ) :=
    F.density_continuous.comp
      (show ContinuousOn (fun z : ℝ×(E×E) => (z.1,z.2.1)) (Icc a b ×ˢ univ) from
        (continuous_fst.prodMk (continuous_fst.comp continuous_snd)).continuousOn)
      (fun z hz => ⟨hz.1, mem_univ _⟩)
  have hq := compactPhaseHeatQuotient_continuousOn F hf.continuous hc
  have hG := compactPhaseHeatGradient_continuousOn F hf hc
  have hV : Continuous (fun z : ℝ×(E×E) => gradient (F.potential z.1) z.2.1) :=
    F.gradient_continuous.comp (continuous_fst.prodMk (continuous_fst.comp continuous_snd))
  have hLap := (reference_phase_potential_laplacian_continuous F).continuousOn
    (s := Icc a b ×ˢ (univ : Set (E×E)))
  apply (((hn.neg.div hp (fun z hz => (reference_density_pos F z.1 hz.1 z.2.1).ne')).add
    (hq.mul ((hV.continuousOn.norm.pow 2).sub hLap))).sub (hV.continuousOn.inner hG)).congr
  intro z hz
  exact compactHeatQuotient_generator F (phase_position_slice_C2 hf z.2.2)
    (phase_position_slice_compact hc z.2.2) z.1 hz.1 z.2.1

/-- The product moment required here is an actual Gibbs moment, uniformly over
all retained momentum; no conditional moment hypothesis is imposed. -/
theorem reference_phase_memLp_of_quadratic_bound {K : Type*} [NormedAddCommGroup K]
    [NormedSpace ℝ K] {a b : ℝ} (F : ReferencePoissonFamily E a b)
    (t : ℝ) (ht : t ∈ Icc a b) {h : E×E → K} (hh : Continuous h)
    (C : ℝ) (hC : ∀ z, ‖h z‖ ≤ C*(1+‖z.1‖^2)) :
    MemLp h 2 ((F.law t).prod (stdGaussian E)) := by
  have hm := (((memLp_const (1:ℝ) (μ := F.law t) (p := 2)).add
    (reference_memLp_norm_pow F t ht 2)).const_mul C).comp_fst (stdGaussian E)
  apply hm.mono hh.aestronglyMeasurable
  filter_upwards [] with z
  exact (hC z).trans (le_abs_self _)

/-- Value, genuine position gradient and generator all belong to product L2. -/
theorem compactPhaseHeatQuotient_memLp {a b : ℝ} (F : ReferencePoissonFamily E a b)
    {f : E×E → ℝ} (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f)
    (hheat : ∀ t ∈ Icc a b, F.law t = heatedLaw (F.law a) (t-a))
    (t : ℝ) (ht : t ∈ Icc a b) :
    MemLp (compactPhaseHeatQuotient F f t) 2 ((F.law t).prod (stdGaussian E)) ∧
    MemLp (compactPhaseHeatGradient F f t) 2 ((F.law t).prod (stdGaussian E)) ∧
    MemLp (compactPhaseHeatGenerator F f t) 2 ((F.law t).prod (stdGaussian E)) := by
  obtain ⟨C,hC,hb⟩ := compactPhaseHeatQuotient_growth F hf hc hheat
  refine ⟨MemLp.of_bound (compactPhaseHeatQuotient_continuous F hf.continuous hc t ht).aestronglyMeasurable
    C (Eventually.of_forall fun z => (hb t ht z).1), ?_, ?_⟩
  · apply reference_phase_memLp_of_quadratic_bound F t ht
      (compactPhaseHeatGradient_continuous F hf hc t ht) (2*C)
    intro z
    have hh := (hb t ht z).2.1
    have hn : ‖z.1‖ ≤ 1+‖z.1‖^2 := by nlinarith [sq_nonneg (‖z.1‖-1)]
    nlinarith [mul_le_mul_of_nonneg_left hn hC, mul_nonneg hC (sq_nonneg ‖z.1‖)]
  · exact reference_phase_memLp_of_quadratic_bound F t ht
      (compactPhaseHeatGenerator_continuous F hf hc t ht) C (fun z => (hb t ht z).2.2)

end AcceleratedLogConcave.Kinetic.Reheating
