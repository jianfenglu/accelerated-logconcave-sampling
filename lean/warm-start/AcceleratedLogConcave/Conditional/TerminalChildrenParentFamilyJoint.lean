import AcceleratedLogConcave.Conditional.TerminalChildrenParentFamily
import AcceleratedLogConcave.Conditional.Centering.SourceParameterRegularity

/-! The jointly measurable retained transition on the actual source parameters.
The original parent input remains in the readout. Its sections equal the
actual parent kernel with actual terminal references at every final slot. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory ProbabilityTheory
open scoped ContDiff ENNReal
namespace AcceleratedLogConcave.Conditional.TerminalChildrenParentFamily
open Numerics Numerics.MeanFlowLp Numerics.AffineGraph MeanReferenceLayer
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ}
local notation "E" => EuclideanSpace ℝ ι

/-- The source centering width is half the actual parent width. -/
def halfParameters {ell : ℝ} (theta : SourceParameters E ell) : SourceParameters E ell :=
  ⟨(theta.center,theta.radius,theta.width / 2),theta.radius_pos,
    half_pos theta.width_pos,theta.small⟩

omit [Fintype ι] [DecidableEq ι] in
theorem continuous_halfParameters {ell : ℝ} :
    Continuous (halfParameters (ι := ι) (ell := ell)) := by
  apply Continuous.subtype_mk
  exact SourceParameters.continuous_center.prodMk
    (SourceParameters.continuous_radius.prodMk (SourceParameters.continuous_width.div_const 2))

variable {F : EuclideanSpace ℝ ι → ℝ} {ell : ℝ} (hF : ContDiff ℝ 2 F) (hell : 0 ≤ ell)
  (hlo : ∀ z a, 0 ≤ fderiv ℝ (fderiv ℝ F) z a a)
  (hup : ∀ z a, fderiv ℝ (fderiv ℝ F) z a a ≤ ell * ‖a‖ ^ 2)
  (G : MeanGeometry m)

omit [DecidableEq ι] in
/-- Actual source regularity makes the literal readout jointly continuous. -/
theorem continuous_sourceReadout :
    Continuous (fun z : (SourceParameters E ell × E) × Fresh ι m ↦
      sourceReadout hF hell hlo hup G z.1.1 z.1.2 z.2) := by
  have hg : Continuous (fun z : (SourceParameters E ell × E) × Fresh ι m ↦
      GaussianAssembly.active (normalizedCoefficients G) z.1.2 z.2.2 none) := by
    unfold GaussianAssembly.active GaussianAssembly.noiseSum
    fun_prop
  have hz : Continuous (fun z : (SourceParameters E ell × E) × Fresh ι m ↦
      WithLp.toLp 2 (z.2.1, GaussianAssembly.active (normalizedCoefficients G) z.1.2 z.2.2 none)) :=
    (WithLp.prod_continuous_toLp 2 E E).comp (continuous_snd.fst.prodMk hg)
  have hp : Continuous (fun z : (SourceParameters E ell × E) × Fresh ι m ↦
      halfParameters z.1.1) :=
    (continuous_halfParameters (ι := ι) (ell := ell)).comp continuous_fst.fst
  have hi := (Centering.continuous_sourceCenteringFlow_increment_parameters hF hell hlo hup
    G.backwardEnd_pos.le G.backwardEnd_lt_one).comp (hp.prodMk hz)
  have hc := continuous_fst.snd.add (hi.const_smul (1 / 2 : ℝ))
  apply hc.congr
  intro z
  rfl


/-- The exact source position kernel and independent literal Gaussian array. -/
def familyFreshKernel : Kernel (SourceParameters E ell × E) (Fresh ι m) :=
  ((SourcePositionFamily.positionKernel hF hlo (backwardEnd G.R)
    SourceParameters.continuous_center.measurable SourceParameters.continuous_radius.measurable).comap
      Prod.fst measurable_fst) ×ₖ
    Kernel.const (SourceParameters E ell × E)
      (Measure.pi (fun _ : Option (Fin m) ↦ stdGaussian E))

omit [DecidableEq ι] in
instance familyFreshKernel_markov : IsMarkovKernel (familyFreshKernel (ell := ell) hF hlo G) := by
  let := SourcePositionFamily.positionKernel_markov (A := SourceParameters E ell) hF hlo (backwardEnd G.R)
    SourceParameters.continuous_center.measurable SourceParameters.continuous_radius.measurable
  unfold familyFreshKernel
  infer_instance

/-- The source retained transition, jointly measurable in center, radius,
parent width and the original parent input. -/
def familyKernel : Kernel (SourceParameters E ell × E) E :=
  ((Kernel.id : Kernel (SourceParameters E ell × E) (SourceParameters E ell × E)) ×ₖ
    familyFreshKernel (ell := ell) hF hlo G).map
      (fun z ↦ sourceReadout hF hell hlo hup G z.1.1 z.1.2 z.2)

instance familyKernel_markov : IsMarkovKernel (familyKernel hF hell hlo hup G) :=
  Kernel.IsMarkovKernel.map _ (continuous_sourceReadout hF hell hlo hup G).measurable

omit [DecidableEq ι] in
/-- The fresh law is the literal source interpolation law times the independent
finite Gaussian auxiliary array. -/
theorem familyFreshKernel_apply (theta : SourceParameters E ell) (p : E) :
    familyFreshKernel (ell := ell) hF hlo G (theta,p) =
      freshLaw (data hF hell hlo hup G theta) := by
  let := SourcePositionFamily.positionKernel_markov (A := SourceParameters E ell) hF hlo
    (backwardEnd G.R) SourceParameters.continuous_center.measurable
    SourceParameters.continuous_radius.measurable
  rw [familyFreshKernel, Kernel.prod_apply, Kernel.comap_apply,
    SourcePositionFamily.positionKernel_apply, Kernel.const_apply]
  rfl

omit [DecidableEq ι] in
/-- Pointwise readout formula at each retained input, prior to averaging it. -/
theorem familyKernel_apply (theta : SourceParameters E ell) (p : E) :
    familyKernel hF hell hlo hup G (theta,p) =
      (freshLaw (data hF hell hlo hup G theta)).map
        (sourceReadout hF hell hlo hup G theta p) := by
  rw [familyKernel, Kernel.map_apply _ (continuous_sourceReadout hF hell hlo hup G).measurable,
    Kernel.prod_apply, Kernel.id_apply, familyFreshKernel_apply hF hell hlo hup G,
    Measure.dirac_prod, Measure.map_map
      (continuous_sourceReadout hF hell hlo hup G).measurable measurable_prodMk_left]
  rfl

/-- Equality of fixed-input kernel sections with the actual source parent
having its actual terminal identity child references. -/
theorem familyKernel_section (hm : 0 < m) (theta : SourceParameters E ell) :
    (familyKernel hF hell hlo hup G).comap (fun p ↦ (theta,p)) measurable_prodMk_left =
      parentKernel (data hF hell hlo hup G theta)
        (terminalChildren (data hF hell hlo hup G theta) hm) := by
  rw [parentKernel_eq_retainedKernel]
  ext p : 1
  rw [Kernel.comap_apply, familyKernel_apply, retainedKernel,
    Kernel.map_apply _ (continuous_readout _ hm).measurable, freshKernel,
    Kernel.prod_apply, Kernel.id_apply, Kernel.const_apply, Measure.dirac_prod,
    Measure.map_map (continuous_readout _ hm).measurable measurable_prodMk_left]
  congr 1
  funext fresh
  exact (readout_data_eq_sourceReadout hF hell hlo hup G hm theta p fresh).symm

/-- Gaussian stationarity of every parameter section follows from equality
with the source parent kernel. -/
theorem familyKernel_invariant (hm : 0 < m) (theta : SourceParameters E ell) :
    (familyKernel hF hell hlo hup G).comap (fun p ↦ (theta,p)) measurable_prodMk_left ∘ₘ
      stdGaussian E = stdGaussian E := by
  rw [familyKernel_section hF hell hlo hup G hm theta]
  exact parentKernel_invariant _ _

/-- On the actual first nonterminal precision band, every active-final source
edge is terminal and the retained source transition has the stated parent
kernel section and Gaussian stationarity. Main/private edges remain separate. -/
theorem familyKernel_firstBand (hm : 0 < m) (theta : SourceParameters E ell)
    (q t : ℝ) (hq : (1 / 2 : ℝ) < q) (hband : q ≤ 1 / 2 + t) :
    (∀ _i : Fin m, Oracle.Precision.CallEdge t .activeFinal (.mean (q - t)) (.mean q) ∧
      Oracle.Precision.terminal (q - t)) ∧
    (familyKernel hF hell hlo hup G).comap (fun p ↦ (theta,p)) measurable_prodMk_left =
      parentKernel (data hF hell hlo hup G theta)
        (terminalChildren (data hF hell hlo hup G theta) hm) ∧
    (familyKernel hF hell hlo hup G).comap (fun p ↦ (theta,p)) measurable_prodMk_left ∘ₘ
      stdGaussian E = stdGaussian E := by
  refine ⟨?_, familyKernel_section hF hell hlo hup G hm theta,
    familyKernel_invariant hF hell hlo hup G hm theta⟩
  intro i
  exact ⟨source_final_edge q t hq i,
    ((all_final_terminal_iff hm q t).mpr ⟨hq,hband⟩).2 i⟩

end AcceleratedLogConcave.Conditional.TerminalChildrenParentFamily
