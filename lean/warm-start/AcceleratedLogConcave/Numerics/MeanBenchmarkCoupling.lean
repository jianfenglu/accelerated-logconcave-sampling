import AcceleratedLogConcave.Numerics.MeanCollocationLp
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
/-! Actual centering-factor retained kernel and same-seed finite numerical coupling.
The retained input is G0; the full compiler Q^q on the assembled original P remains separate. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory AcceleratedLogConcave
open Numerics Numerics.MeanFlowLp Numerics.MeanCollocationLp
open scoped ENNReal
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
namespace AcceleratedLogConcave.Numerics.MeanBenchmarkCoupling
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ}
local notation "E" => EuclideanSpace ℝ ι

def positionLaw (d : Data ι m) : Measure E :=
  Conditional.interpolationLaw d.F d.x d.r (AffineGraph.backwardEnd d.G.R)
def endpoint (d : Data ι m) (t : ℝ) (y g : E) : E :=
  (CenteringFlowLp.phase (kernelData d) (d.sigma/2) (half_pos d.hsigma) t
    (WithLp.toLp 2 (y,g))).snd
/-- Fresh initial position, fixed initial centering momentum G0. No conditional choice. -/
def referenceKernel (d : Data ι m) (t : ℝ) : Kernel E E :=
  ((Kernel.id : Kernel E E) ×ₖ Kernel.const E (positionLaw d)).map
    (fun gy : E × E=>endpoint d t gy.2 gy.1)
def momentumPair (d : Data ι m) (t : ℝ) (ω : Seed d) : E × E :=
  (ω.1.snd,score d t ω)
def actualRetained (d : Data ι m) (N : ℕ) (ω : Seed d) : E × E :=
  (rawOutput d N ω,ω.1.snd)
def benchmarkRetained (d : Data ι m) (ω : Seed d) : E × E :=
  (rawTerminalTarget d ω,ω.1.snd)
def actualLaw (d : Data ι m) (N : ℕ) : Measure (E × E) :=
  (seedMeasure d).map (actualRetained d N)
def referenceLaw (d : Data ι m) : Measure (E × E) :=
  ((stdGaussian E) ⊗ₘ referenceKernel d 1).map
    (fun gg : E × E=>(Gibbs.primitiveMean d.F d.x d.r+(d.sigma/2) • gg.2,gg.1))
def coupling (d : Data ι m) (N : ℕ) : Measure ((E × E) × (E × E)) :=
  (seedMeasure d).map (fun ω=>(actualRetained d N ω,benchmarkRetained d ω))
def errorBound (d : Data ι m) (h₀ : ℝ) (D : AffineResidual.Mean.DerivativeBudget d.G) (N : ℕ) : ℝ :=
  d.ell*finiteError d h₀ D N+2*D.center/(m.factorial:ℝ)

/-- Actual Borel kernel, its pointwise fresh-position formula, and its true complete joint law. -/
def KernelTarget (d : Data ι m) : Prop := ∀ t : ℝ,
  IsMarkovKernel (referenceKernel d t) ∧
  (∀ g,referenceKernel d t g=(positionLaw d).map (fun y=>endpoint d t y g)) ∧
  (seedMeasure d).map (momentumPair d t)=(stdGaussian E) ⊗ₘ referenceKernel d t ∧
  referenceKernel d t ∘ₘ (stdGaussian E)=stdGaussian E

/-- Measurability is a conclusion about the literal finite raw computation, not its L2 representative. -/
def MeasurabilityTarget (d : Data ι m) : Prop :=
  (∀ N,Measurable (actualRetained d N)) ∧ Measurable (benchmarkRetained d)

/-- Both marginals identify G0 and the actual centering-factor reference transition. -/
def CouplingTarget (d : Data ι m) : Prop := ∀ N : ℕ,
  IsProbabilityMeasure (actualLaw d N) ∧ IsProbabilityMeasure (referenceLaw d) ∧
  IsProbabilityMeasure (coupling d N) ∧
  (coupling d N).map Prod.fst=actualLaw d N ∧
  (coupling d N).map Prod.snd=referenceLaw d ∧
  (∀ᵐ z ∂coupling d N,z.1.2=z.2.2) ∧
  (actualLaw d N).map Prod.snd=stdGaussian E ∧
  (referenceLaw d).map Prod.snd=stdGaussian E ∧
  (referenceLaw d).map Prod.fst=(stdGaussian E).map
    (fun g=>Gibbs.primitiveMean d.F d.x d.r+(d.sigma/2) • g)

/-- The literal raw benchmark has the explicit prescribed reference law. -/
def BenchmarkTarget (d : Data ι m) : Prop :=
  (seedMeasure d).map (benchmarkRetained d)=referenceLaw d ∧
  (seedMeasure d).map (rawTerminalTarget d)=(stdGaussian E).map
    (fun g=>Gibbs.primitiveMean d.F d.x d.r+(d.sigma/2) • g)

/-- Unconditional actual quadratic cost identity, with no high-order regularity premise. -/
def QuadraticIdentityTarget (d : Data ι m) : Prop := ∀ N : ℕ,
  Integrable (fun z : (E × E) × (E × E)=>‖z.1.1-z.2.1‖^2) (coupling d N) ∧
  (∫ z,‖z.1.1-z.2.1‖^2 ∂coupling d N)=‖output d N-terminalTarget d‖^2

/-- The numerical error controls this actual cost, after its law is independently identified. -/
def CostTarget (d : Data ι m) (h₀ : ℝ) : Prop := MeshConditions d h₀ →
  ∀ K l v D,Regularity d K l v D →∀ N : ℕ,
  (∫ z,‖z.1.1-z.2.1‖^2 ∂coupling d N)≤(errorBound d h₀ D N)^2

/-- At time zero the transition is a Dirac kernel, not a fixed-input Gaussian sampler. -/
def ZeroTimeTarget (d : Data ι m) : Prop := referenceKernel d 0=Kernel.id


instance position_probability (d : Data ι m) : IsProbabilityMeasure (positionLaw d) :=
  Conditional.interpolationLaw_isProbabilityMeasure d.hF d.hlo d.x d.r _

theorem continuous_endpoint (d : Data ι m) (t : ℝ) :
    Continuous (fun gy : E × E=>endpoint d t gy.2 gy.1) := by
  exact (WithLp.prod_continuous_ofLp 2 E E).snd.comp
    ((CenteringFlowLp.continuous_phase (kernelData d) (d.sigma/2) (half_pos d.hsigma)).comp
      (continuous_const.prodMk ((WithLp.prod_continuous_toLp 2 E E).comp
        (continuous_snd.prodMk continuous_fst))))

instance referenceKernel_markov (d : Data ι m) (t : ℝ) : IsMarkovKernel (referenceKernel d t) := by
  unfold referenceKernel
  exact Kernel.IsMarkovKernel.map _ (continuous_endpoint d t).measurable

theorem referenceKernel_apply (d : Data ι m) (t : ℝ) (g : E) :
    referenceKernel d t g=(positionLaw d).map (fun y=>endpoint d t y g) := by
  rw [referenceKernel,Kernel.map_apply _ (continuous_endpoint d t).measurable,
    Kernel.prod_apply,Kernel.id_apply,Kernel.const_apply,Measure.dirac_prod,
    Measure.map_map (continuous_endpoint d t).measurable measurable_prodMk_left]
  rfl

theorem reference_joint_eq (d : Data ι m) (t : ℝ) :
    (stdGaussian E) ⊗ₘ referenceKernel d t=
      ((stdGaussian E).prod (positionLaw d)).map (fun gy=>(gy.1,endpoint d t gy.2 gy.1)) := by
  have hm := (continuous_fst.prodMk (continuous_endpoint d t)).measurable
  apply Measure.ext_of_lintegral
  intro f hf
  rw [Measure.lintegral_compProd hf,lintegral_map hf hm]
  rw [lintegral_prod (fun gy : E × E=>f (gy.1,endpoint d t gy.2 gy.1)) (by fun_prop)]
  apply lintegral_congr
  intro g
  rw [referenceKernel_apply]
  have hf' : Measurable (fun b : E=>f (g,b)) := hf.comp measurable_prodMk_left
  have he : Measurable (fun y : E=>endpoint d t y g) :=
    ((continuous_endpoint d t).comp (continuous_const.prodMk continuous_id)).measurable
  exact lintegral_map hf' he

theorem momentumPair_law (d : Data ι m) (t : ℝ) :
    (seedMeasure d).map (momentumPair d t)=(stdGaussian E) ⊗ₘ referenceKernel d t := by
  let f : Conditional.Centering.Phase E → E × E := fun z=>
    (z.snd,(CenteringFlowLp.phase (kernelData d) (d.sigma/2) (half_pos d.hsigma) t z).snd)
  have hf : Measurable f := (WithLp.prod_continuous_ofLp 2 E E).snd.measurable.prodMk
    ((WithLp.prod_continuous_ofLp 2 E E).snd.comp
      ((CenteringFlowLp.continuous_phase (kernelData d) (d.sigma/2) (half_pos d.hsigma)).comp
        (continuous_const.prodMk continuous_id))).measurable
  change (seedMeasure d).map (f ∘ Prod.fst)=_
  rw [← Measure.map_map hf (phase_projection_preserving d).measurable,
    (phase_projection_preserving d).map_eq]
  change (((positionLaw d).prod (stdGaussian E)).map (WithLp.toLp 2)).map f = _
  rw [Measure.map_map hf (WithLp.prod_continuous_toLp 2 E E).measurable,reference_joint_eq,
    ← Measure.prod_swap (μ:=positionLaw d) (ν:=stdGaussian E),
    Measure.map_map (continuous_fst.prodMk (continuous_endpoint d t)).measurable measurable_swap]
  rfl

theorem score_preserving (d : Data ι m) (t : ℝ) :
    MeasurePreserving (score d t) (seedMeasure d) (stdGaussian E) :=
  (KernelFlowLp.momentum_preserving (kernelData d)).comp (kernel_phase_preserving d t)

theorem referenceKernel_invariant (d : Data ι m) (t : ℝ) :
    referenceKernel d t ∘ₘ (stdGaussian E)=stdGaussian E := by
  rw [← Measure.snd_compProd,← momentumPair_law]
  change ((seedMeasure d).map (momentumPair d t)).map Prod.snd=_
  have hi := (KernelFlowLp.momentum_preserving (kernelData d)).comp (phase_projection_preserving d)
  have hm : Measurable (momentumPair d t) := hi.measurable.prodMk (score_preserving d t).measurable
  rw [Measure.map_map measurable_snd hm]
  exact (score_preserving d t).map_eq

theorem kernel_target (d : Data ι m) : KernelTarget d :=
  fun t=>⟨inferInstance,referenceKernel_apply d t,momentumPair_law d t,referenceKernel_invariant d t⟩

theorem referenceKernel_zero (d : Data ι m) : referenceKernel d 0=Kernel.id := by
  ext g : 1
  rw [referenceKernel_apply,Kernel.id_apply]
  have he (y : E) : endpoint d 0 y g=g := by
    unfold endpoint
    rw [CenteringFlowLp.phase_initial]
    rfl
  simp only [he,Measure.map_const,measure_univ,one_smul]

theorem zeroTime_target (d : Data ι m) : ZeroTimeTarget d := referenceKernel_zero d


open AffineGraph

omit [DecidableEq ι] in
theorem continuous_raw_direct (d : Data ι m) (i : d.G.MeanNode) :
    Continuous (fun ω : Seed d=>(rawGraph d ω).direct i) := by
  have ha (a : d.G.Anchor) : Continuous (fun ω : Seed d=>d.G.anchorValues ω.1.fst ω.1.snd ω.2 a) := by
    rcases a with _ | _ | ⟨j,k⟩
    · exact (WithLp.prod_continuous_ofLp 2 E E).fst.comp continuous_fst
    · exact (WithLp.prod_continuous_ofLp 2 E E).snd.comp continuous_fst
    · exact (continuous_apply k).comp ((continuous_apply j).comp continuous_snd)
  change Continuous (fun ω : Seed d=>d.x+∑ a,d.G.centerForm d.r d.sigma i (.inl a) •
    d.G.anchorValues ω.1.fst ω.1.snd ω.2 a)
  exact continuous_const.add (continuous_finsetSum _ fun a _=>(ha a).const_smul (d.G.centerForm d.r d.sigma i (.inl a)))

omit [DecidableEq ι] in
theorem continuous_rawIterate (d : Data ι m) (N : ℕ) (i : d.G.MeanNode) :
    Continuous (rawIterate d N i) := by
  induction N generalizing i with
  | zero => exact continuous_raw_direct d i
  | succ N ih =>
    change Continuous (fun ω : Seed d=>(rawGraph d ω).direct i+
      ∑ j,d.G.matrix d.r d.sigma i j • Gibbs.primitiveMean d.F (rawIterate d N j ω) (d.G.radius d.r j))
    exact (continuous_raw_direct d i).add (continuous_finsetSum _ fun j _=>
      ((Gibbs.primitive_mean_lipschitz d.hF d.hell d.hlo d.hup (d.G.radius_pos d.r d.hr j)).continuous.comp
        (ih j)).const_smul (d.G.matrix d.r d.sigma i j))

omit [DecidableEq ι] in
theorem continuous_rawOutput (d : Data ι m) (N : ℕ) : Continuous (rawOutput d N) := by
  change Continuous (fun ω : Seed d=>(d.sigma/2) • ω.1.snd+
    ∑ j : Fin m,GaussLegendre.weight m j • Gibbs.primitiveMean d.F
      (rawIterate d N (.center d.G j) ω) (d.r*d.G.R))
  exact (((WithLp.prod_continuous_ofLp 2 E E).snd.comp continuous_fst).const_smul (d.sigma/2)).add
    (continuous_finsetSum _ fun j _=>
      ((Gibbs.primitive_mean_lipschitz d.hF d.hell d.hlo d.hup (mul_pos d.hr d.G.R_pos)).continuous.comp
        (continuous_rawIterate d N (.center d.G j))).const_smul (GaussLegendre.weight m j))

omit [DecidableEq ι] in
theorem initial_preserving (d : Data ι m) :
    MeasurePreserving (fun ω : Seed d=>ω.1.snd) (seedMeasure d) (stdGaussian E) :=
  (KernelFlowLp.momentum_preserving (kernelData d)).comp (phase_projection_preserving d)

omit [DecidableEq ι] in
theorem measurable_actualRetained (d : Data ι m) (N : ℕ) : Measurable (actualRetained d N) :=
  (continuous_rawOutput d N).measurable.prodMk (initial_preserving d).measurable

theorem measurable_rawTerminalTarget (d : Data ι m) : Measurable (rawTerminalTarget d) :=
  measurable_const.add ((score_preserving d 1).measurable.const_smul (d.sigma/2))

theorem measurable_benchmarkRetained (d : Data ι m) : Measurable (benchmarkRetained d) :=
  (measurable_rawTerminalTarget d).prodMk (initial_preserving d).measurable

theorem measurability_target (d : Data ι m) : MeasurabilityTarget d :=
  ⟨measurable_actualRetained d,measurable_benchmarkRetained d⟩

theorem benchmarkRetained_law (d : Data ι m) :
    (seedMeasure d).map (benchmarkRetained d)=referenceLaw d := by
  rw [referenceLaw,← momentumPair_law]
  have hm : Measurable (momentumPair d 1) := (initial_preserving d).measurable.prodMk
    (score_preserving d 1).measurable
  rw [Measure.map_map (by fun_prop) hm]
  rfl

theorem rawTerminalTarget_law (d : Data ι m) :
    (seedMeasure d).map (rawTerminalTarget d)=(stdGaussian E).map
      (fun g=>Gibbs.primitiveMean d.F d.x d.r+(d.sigma/2) • g) := by
  rw [← (score_preserving d 1).map_eq,Measure.map_map (by fun_prop) (score_preserving d 1).measurable]
  rfl

theorem benchmark_target (d : Data ι m) : BenchmarkTarget d :=
  ⟨benchmarkRetained_law d,rawTerminalTarget_law d⟩

instance actualLaw_probability (d : Data ι m) (N : ℕ) : IsProbabilityMeasure (actualLaw d N) := by
  unfold actualLaw
  exact (Measure.isProbabilityMeasure_map_iff (measurable_actualRetained d N).aemeasurable).mpr inferInstance

instance referenceLaw_probability (d : Data ι m) : IsProbabilityMeasure (referenceLaw d) := by
  rw [← benchmarkRetained_law]
  exact (Measure.isProbabilityMeasure_map_iff (measurable_benchmarkRetained d).aemeasurable).mpr inferInstance

theorem measurable_coupling_map (d : Data ι m) (N : ℕ) :
    Measurable (fun ω=>(actualRetained d N ω,benchmarkRetained d ω)) :=
  (measurable_actualRetained d N).prodMk (measurable_benchmarkRetained d)

instance coupling_probability (d : Data ι m) (N : ℕ) : IsProbabilityMeasure (coupling d N) := by
  unfold coupling
  exact (Measure.isProbabilityMeasure_map_iff (measurable_coupling_map d N).aemeasurable).mpr inferInstance

theorem coupling_first (d : Data ι m) (N : ℕ) : (coupling d N).map Prod.fst=actualLaw d N := by
  rw [coupling,Measure.map_map measurable_fst (measurable_coupling_map d N)]
  rfl

theorem coupling_second (d : Data ι m) (N : ℕ) : (coupling d N).map Prod.snd=referenceLaw d := by
  rw [coupling,Measure.map_map measurable_snd (measurable_coupling_map d N)]
  exact benchmarkRetained_law d

theorem coupling_same_input (d : Data ι m) (N : ℕ) :
    ∀ᵐ z ∂coupling d N,z.1.2=z.2.2 := by
  unfold coupling
  apply (ae_map_iff (measurable_coupling_map d N).aemeasurable ((isClosed_eq (by fun_prop) (by fun_prop)).measurableSet)).mpr
  exact Filter.Eventually.of_forall fun _=>rfl

omit [DecidableEq ι] in
theorem actualLaw_input (d : Data ι m) (N : ℕ) : (actualLaw d N).map Prod.snd=stdGaussian E := by
  rw [actualLaw,Measure.map_map measurable_snd (measurable_actualRetained d N)]
  exact (initial_preserving d).map_eq

theorem referenceLaw_input (d : Data ι m) : (referenceLaw d).map Prod.snd=stdGaussian E := by
  rw [← benchmarkRetained_law,Measure.map_map measurable_snd (measurable_benchmarkRetained d)]
  exact (initial_preserving d).map_eq

theorem referenceLaw_output (d : Data ι m) : (referenceLaw d).map Prod.fst=
    (stdGaussian E).map (fun g=>Gibbs.primitiveMean d.F d.x d.r+(d.sigma/2) • g) := by
  rw [← benchmarkRetained_law,Measure.map_map measurable_fst (measurable_benchmarkRetained d)]
  exact rawTerminalTarget_law d

theorem coupling_target (d : Data ι m) : CouplingTarget d :=
  fun N=>⟨inferInstance,inferInstance,inferInstance,coupling_first d N,coupling_second d N,
    coupling_same_input d N,actualLaw_input d N,referenceLaw_input d,referenceLaw_output d⟩


/-- Exact representative identity used only under integration. -/
theorem raw_output_error_ae (d : Data ι m) (N : ℕ) :
    (fun ω=>rawOutput d N ω-rawTerminalTarget d ω)=ᵐ[seedMeasure d]
      ((output d N-terminalTarget d : MeanResidualBridge.H d) : Seed d → E) := by
  filter_upwards [rawOutput_ae d N,rawTerminalTarget_ae d,
    Lp.coeFn_sub (output d N) (terminalTarget d)] with ω ho ht hs
  simpa only [ho,ht,Pi.sub_apply] using hs.symm

theorem raw_output_error_memLp (d : Data ι m) (N : ℕ) :
    MemLp (fun ω=>rawOutput d N ω-rawTerminalTarget d ω) 2 (seedMeasure d) :=
  (Lp.memLp (output d N-terminalTarget d)).ae_eq (raw_output_error_ae d N).symm

theorem coupling_cost_integrable (d : Data ι m) (N : ℕ) :
    Integrable (fun z : (E × E) × (E × E)=>‖z.1.1-z.2.1‖^2) (coupling d N) := by
  unfold coupling
  apply (integrable_map_measure (by fun_prop) (measurable_coupling_map d N).aemeasurable).mpr
  exact (memLp_two_iff_integrable_sq_norm (raw_output_error_memLp d N).aestronglyMeasurable).mp
    (raw_output_error_memLp d N)

theorem coupling_cost_eq (d : Data ι m) (N : ℕ) :
    (∫ z,‖z.1.1-z.2.1‖^2 ∂coupling d N)=‖output d N-terminalTarget d‖^2 := by
  rw [coupling,integral_map (measurable_coupling_map d N).aemeasurable (by fun_prop)]
  change (∫ ω,‖rawOutput d N ω-rawTerminalTarget d ω‖^2 ∂seedMeasure d)=_
  calc
    _ = ∫ ω,‖(output d N-terminalTarget d : MeanResidualBridge.H d) ω‖^2 ∂seedMeasure d := by
      apply integral_congr_ae
      filter_upwards [raw_output_error_ae d N] with ω hω
      rw [hω]
    _ = ‖output d N-terminalTarget d‖^2 := by
      have h := real_inner_self_eq_norm_sq (output d N-terminalTarget d)
      rw [L2.inner_def] at h
      simpa only [real_inner_self_eq_norm_sq] using h

theorem quadraticIdentity_target (d : Data ι m) : QuadraticIdentityTarget d :=
  fun N=>⟨coupling_cost_integrable d N,coupling_cost_eq d N⟩

theorem cost_target (d : Data ι m) (h₀ : ℝ) : CostTarget d h₀ := by
  intro h K l v D hreg N
  rw [coupling_cost_eq]
  have hb := final_bound d h₀ h K l v D hreg N
  have h0 := norm_nonneg (output d N-terminalTarget d)
  change ‖output d N-terminalTarget d‖^2≤(d.ell*finiteError d h₀ D N+2*D.center/(m.factorial:ℝ))^2
  nlinarith

end AcceleratedLogConcave.Numerics.MeanBenchmarkCoupling
