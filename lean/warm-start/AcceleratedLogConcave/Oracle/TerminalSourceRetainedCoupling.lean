import AcceleratedLogConcave.Oracle.FreshChildRetainedCoupling
import AcceleratedLogConcave.Probability.TerminalRetainedCoupling
import AcceleratedLogConcave.Probability.CanonicalNativeTapeLaw

/-! The terminal lower-depth joint in the exact canonical full-seed format
required by fresh-child retention. Its reference is the original designated
Gaussian. Literal interpreter errors transfer to the existing native terminal
coupling; no terminal analysis or quantitative premise is replaced. The existing
RecursiveExecutable.mean_terminal supplies the exact precision-branch rewrite. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
namespace AcceleratedLogConcave.Oracle.TerminalSourceRetainedCoupling
open TapeLowering CanonicalTapeLaw CanonicalTapeMeasurability
open AcceleratedLogConcave.Probability
variable {d c : ℕ} {Γ : Ctx} {τ : Ty}

local instance canonicalTapeSpace (p : Prog c Γ τ) : MeasurableSpace (Tape d p) := tapeSpace d p

abbrev Seed (d : ℕ) (origin : Origin) := Point d × Tape d (terminalMeanProgram origin)

@[instance_reducible] def nativeSeedSpace (d : ℕ) (origin : Origin) : MeasurableSpace (Seed d origin) :=
  let pointSpace : MeasurableSpace (Point d) := inferInstance
  pointSpace.prod (MixedResidualTape.tapeMeasurableSpace d (terminalMeanProgram origin))

@[instance_reducible] def nativeRetainedSpace (d : ℕ) (origin : Origin) :
    MeasurableSpace ((Point d × Point d) × Seed d origin) :=
  let pairSpace : MeasurableSpace (Point d × Point d) := inferInstance
  pairSpace.prod (nativeSeedSpace d origin)

/-- Complete original source seed and the same designated Gaussian reference. -/
def joint (origin : Origin) : Kernel (Point d) (Seed d origin × Point d) :=
  (Kernel.const (Point d)
    (FreshChildRetainedCoupling.sourceLaw (CanonicalNativeTapeLaw.primitiveLaws d)
      (terminalMeanProgram origin))).map (fun pw => (pw,pw.1))

instance joint_markov (origin : Origin) : IsMarkovKernel (joint (d := d) origin) :=
  Kernel.IsMarkovKernel.map _ (measurable_id.prodMk measurable_fst)

theorem joint_apply (origin : Origin) (x : Point d) :
    joint origin x =
      (FreshChildRetainedCoupling.sourceLaw (CanonicalNativeTapeLaw.primitiveLaws d)
        (terminalMeanProgram origin)).map (fun pw => (pw,pw.1)) := by
  have hm : Measurable (fun pw : Seed d origin => (pw,pw.1)) :=
    measurable_id.prodMk measurable_fst
  rw [joint, Kernel.map_apply _ hm, Kernel.const_apply]

theorem source_marginal (origin : Origin) :
    (joint (d := d) origin).fst = Kernel.const (Point d)
      (FreshChildRetainedCoupling.sourceLaw (CanonicalNativeTapeLaw.primitiveLaws d)
        (terminalMeanProgram origin)) := by
  have hm : Measurable (fun pw : Seed d origin => (pw,pw.1)) :=
    measurable_id.prodMk measurable_fst
  ext x : 1
  rw [Kernel.fst_apply, joint_apply, Measure.map_map measurable_fst hm, Kernel.const_apply]
  exact Measure.map_id

/-- The identity changes only presentation of the same entire source seed. -/
theorem source_identity (origin : Origin) :
    @MeasurePreserving (Seed d origin) (Seed d origin) _ (nativeSeedSpace d origin) id
      (FreshChildRetainedCoupling.sourceLaw (CanonicalNativeTapeLaw.primitiveLaws d)
        (terminalMeanProgram origin))
      (MixedResidualTape.standaloneLaw d (terminalMeanProgram origin)) := by
  let : IsProbabilityMeasure (tapeLaw (CanonicalNativeTapeLaw.primitiveLaws d)
    (terminalMeanProgram origin)) := tapeLaw_probability _ _
  have h := (MeasurePreserving.id (stdGaussian (Point d))).prod
    (CanonicalNativeTapeLaw.identity_preserving d (terminalMeanProgram origin))
  convert h using 1 <;> rfl

theorem reference_joint (origin : Origin) (x : Point d) :
    (joint origin x).map (fun z => (z.1.1,z.2)) =
      stdGaussian (Point d) ⊗ₘ (Kernel.id : Kernel (Point d) (Point d)) := by
  have hm : Measurable (fun pw : Seed d origin => (pw,pw.1)) :=
    measurable_id.prodMk measurable_fst
  rw [joint_apply, Measure.map_map (by fun_prop) hm]
  let : IsProbabilityMeasure (tapeLaw (CanonicalNativeTapeLaw.primitiveLaws d)
    (terminalMeanProgram origin)) := tapeLaw_probability _ _
  have hf : MeasurePreserving (Prod.fst : Seed d origin → Point d)
      (FreshChildRetainedCoupling.sourceLaw (CanonicalNativeTapeLaw.primitiveLaws d)
        (terminalMeanProgram origin)) (stdGaussian (Point d)) :=
    measurePreserving_fst
  have hh := congrArg (fun μ : Measure (Point d) => μ.map (fun P => (P,P))) hf.map_eq
  rw [Measure.map_map (by fun_prop) measurable_fst] at hh
  exact hh.trans (Measure.compProd_deterministic measurable_id).symm

/-- Read the actual terminal value at the full original source seed. -/
def evaluate (origin : Origin) (G : Point d → Point d) (a r σ : ℝ) (x : Point d)
    (z : Seed d origin × Point d) : (Point d × Point d) × Seed d origin :=
  (((run (terminalMeanProgram origin) G (terminalMeanInputs a r σ x z.1.1)
    Env.empty z.1.2).value,z.2),z.1)

theorem evaluate_measurable (origin : Origin) {G : Point d → Point d}
    (hG : Measurable G) (a r σ : ℝ) (x : Point d) :
    @Measurable (Seed d origin × Point d) ((Point d × Point d) × Seed d origin)
      _ (nativeRetainedSpace d origin) (evaluate origin G a r σ x) := by
  have hseed := (source_identity (d := d) origin).measurable
  have hret := (TerminalRetainedCoupling.measurable_retained_section origin hG
    ((x,a),(r,σ))).comp hseed
  exact ((hret.fst.fst.comp measurable_fst).prodMk measurable_snd).prodMk
    (hseed.comp measurable_fst)

/-- This canonical lower joint evaluates to the existing actual native terminal
coupling, retaining every unit and Gaussian instruction coordinate. -/
theorem evaluate_preserving (origin : Origin) {G : Point d → Point d}
    (hG : Measurable G) (a r σ : ℝ) (x : Point d) :
    @MeasurePreserving (Seed d origin × Point d) ((Point d × Point d) × Seed d origin)
      _ (nativeRetainedSpace d origin) (evaluate origin G a r σ x)
      (joint origin x) (TerminalRetainedCoupling.kernel origin G ((x,a),(r,σ))) := by
  refine ⟨evaluate_measurable origin hG a r σ x,?_⟩
  have hdiag : Measurable (fun pw : Seed d origin => (pw,pw.1)) :=
    measurable_id.prodMk measurable_fst
  rw [joint_apply, Measure.map_map (evaluate_measurable origin hG a r σ x) hdiag]
  have hp := source_identity (d := d) origin
  have hm := TerminalRetainedCoupling.measurable_retained_section origin hG ((x,a),(r,σ))
  have he := congrArg (@Measure.map (Seed d origin) ((Point d × Point d) × Seed d origin)
    (nativeSeedSpace d origin) (nativeRetainedSpace d origin)
    (TerminalRetainedCoupling.retained origin G ((x,a),(r,σ)))) hp.map_eq
  rw [Measure.map_map hm hp.measurable,
    ← TerminalRetainedCoupling.kernel_apply origin hG] at he
  exact he



theorem actual_marginal (origin : Origin) {G : Point d → Point d}
    (hG : Continuous G) (a r σ : ℝ) (x : Point d) :
    (joint origin x).map (fun z : Seed d origin × Point d =>
      ((run (terminalMeanProgram origin) G (terminalMeanInputs a r σ x z.1.1)
        Env.empty z.1.2).value,z.2)) = terminalMeanActualLaw origin G a r σ x := by
  have hp := evaluate_preserving origin hG.measurable a r σ x
  have hh := congrArg (@Measure.map ((Point d × Point d) × Seed d origin) (Point d × Point d)
    (nativeRetainedSpace d origin) _ Prod.fst) hp.map_eq
  rw [Measure.map_map measurable_fst hp.measurable,
    TerminalRetainedCoupling.actual_marginal origin hG] at hh
  exact hh

/-- Literal terminal interpreter error, with the adjoined reference coordinate. -/
def error (origin : Origin) (G : Point d → Point d) (a r σ : ℝ)
    (x u : Point d) (z : Seed d origin × Point d) : Point d :=
  (show Point d from (run (terminalMeanProgram origin) G (terminalMeanInputs a r σ x z.1.1)
    Env.empty z.1.2).value) - (u+σ • z.2)

/-- Exact squared-error transport to the existing native full-seed coupling. -/
theorem error_square_integral (origin : Origin) {G : Point d → Point d}
    (hG : Measurable G) (a r σ : ℝ) (x u : Point d) :
    (∫ z, ‖error origin G a r σ x u z‖^2 ∂joint origin x) =
      ∫ z, ‖z.1.1-(u+σ • z.1.2)‖^2
        ∂TerminalRetainedCoupling.kernel origin G ((x,a),(r,σ)) := by
  have hp := evaluate_preserving origin hG a r σ x
  have hf : @Measurable ((Point d × Point d) × Seed d origin) ℝ
      (nativeRetainedSpace d origin) _ (fun z => ‖z.1.1-(u+σ • z.1.2)‖^2) := by
    fun_prop
  have hg := hf.aestronglyMeasurable (μ := TerminalRetainedCoupling.kernel origin G ((x,a),(r,σ)))
  have hi := integral_map hp.aemeasurable (hp.map_eq.symm ▸ hg)
  rw [hp.map_eq] at hi
  exact hi.symm

/-- Transfer a native full-seed error moment through literal terminal evaluation. -/
theorem error_memLp_of_native (origin : Origin) {G : Point d → Point d}
    (hG : Measurable G) (a r σ : ℝ) (x u : Point d)
    (herr : MemLp (fun z => z.1.1-(u+σ • z.1.2)) 2
      (TerminalRetainedCoupling.kernel origin G ((x,a),(r,σ)))) :
    MemLp (error origin G a r σ x u) 2 (joint origin x) := by
  have hp := evaluate_preserving origin hG a r σ x
  have hh := herr.comp_measurePreserving hp
  have he : error origin G a r σ x u =
      (fun z => (evaluate origin G a r σ x z).1.1-
        (u+σ • (evaluate origin G a r σ x z).1.2)) := by
    funext z
    rfl
  rw [he]
  exact hh

open Gibbs

/-- The actual terminal lower joint has finite error second moment without
requiring positive radius, width, or a terminal precision guard. -/
theorem scaled_error_memLp_two {V : Point d → ℝ} {a L : ℝ}
    (hV : ContDiff ℝ 2 V) (hL : 0 ≤ L)
    (hlo : ∀ y v, 0 ≤ fderiv ℝ (fderiv ℝ (scaledPotential V a)) y v v)
    (hup : ∀ y v, fderiv ℝ (fderiv ℝ (scaledPotential V a)) y v v ≤ L*‖v‖^2)
    (origin : Origin) (r σ : ℝ) (x : Point d) :
    MemLp (error origin (gradient V) a r σ x (primitiveMean (scaledPotential V a) x r))
      2 (joint origin x) := by
  have hG : Measurable (gradient V) :=
    ((InnerProductSpace.toDual ℝ (Point d)).symm.continuous.comp
      (hV.continuous_fderiv (by norm_num))).measurable
  exact error_memLp_of_native origin hG a r σ x _
    (TerminalRetainedCoupling.scaled_residual_memLp_two hV hL hlo hup origin r σ x)

/-- The existing guarded terminal RMS estimate on the exact canonical lower
joint required by the fresh-child producer. -/
theorem scaled_accuracy {V : Point d → ℝ} {a L r σ δ q b S : ℝ}
    (hV : ContDiff ℝ 2 V) (hL : 0 ≤ L)
    (hlo : ∀ y v, 0 ≤ fderiv ℝ (fderiv ℝ (scaledPotential V a)) y v v)
    (hup : ∀ y v, fderiv ℝ (fderiv ℝ (scaledPotential V a)) y v v ≤ L*‖v‖^2)
    (hr : 0 < r) (hr1 : r ≤ 1) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hσ : 0 < σ)
    (hS : 0 ≤ S) (hq : q ≤ 1/2) (hb : 3/4 < b)
    (hsize : (L*r)/σ ≤ S*δ^b) (hsmall : 3*S*δ^((1:ℝ)/4) ≤ 1)
    (origin : Origin) (x : Point d) :
    Real.sqrt (∫ z,
      ‖error origin (gradient V) a r σ x (primitiveMean (scaledPotential V a) x r) z‖^2
        ∂joint origin x) ≤ σ*δ^q*primitiveScale (scaledPotential V a) x := by
  have hG : Measurable (gradient V) :=
    ((InnerProductSpace.toDual ℝ (Point d)).symm.continuous.comp
      (hV.continuous_fderiv (by norm_num))).measurable
  rw [error_square_integral origin hG]
  exact TerminalRetainedCoupling.scaled_accuracy hV hL hlo hup hr hr1 hδ hδ1 hσ hS hq hb
    hsize hsmall origin x

/-- Squared form of the same guarded estimate, with the complete original
source seed still present in the lower-depth joint. -/
theorem scaled_square_error_le {V : Point d → ℝ} {a L r σ δ q b S : ℝ}
    (hV : ContDiff ℝ 2 V) (hL : 0 ≤ L)
    (hlo : ∀ y v, 0 ≤ fderiv ℝ (fderiv ℝ (scaledPotential V a)) y v v)
    (hup : ∀ y v, fderiv ℝ (fderiv ℝ (scaledPotential V a)) y v v ≤ L*‖v‖^2)
    (hr : 0 < r) (hr1 : r ≤ 1) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hσ : 0 < σ)
    (hS : 0 ≤ S) (hq : q ≤ 1/2) (hb : 3/4 < b)
    (hsize : (L*r)/σ ≤ S*δ^b) (hsmall : 3*S*δ^((1:ℝ)/4) ≤ 1)
    (origin : Origin) (x : Point d) :
    (∫ z, ‖error origin (gradient V) a r σ x (primitiveMean (scaledPotential V a) x r) z‖^2
      ∂joint origin x) ≤ (σ*δ^q*primitiveScale (scaledPotential V a) x)^2 := by
  have hc := scaled_accuracy hV hL hlo hup hr hr1 hδ hδ1 hσ hS hq hb hsize hsmall origin x
  have hi : 0 ≤ ∫ z,
      ‖error origin (gradient V) a r σ x (primitiveMean (scaledPotential V a) x r) z‖^2
        ∂joint origin x := integral_nonneg (fun _ => sq_nonneg _)
  have hn := Real.sqrt_nonneg (∫ z,
    ‖error origin (gradient V) a r σ x (primitiveMean (scaledPotential V a) x r) z‖^2
      ∂joint origin x)
  have hbnd := hn.trans hc
  have hp := mul_nonneg (sub_nonneg.mpr hc) (add_nonneg hbnd hn)
  nlinarith [Real.sq_sqrt hi]

end AcceleratedLogConcave.Oracle.TerminalSourceRetainedCoupling
