import AcceleratedLogConcave.Oracle.DesignatedChildAbsorbedLaw
import AcceleratedLogConcave.Probability.CausalRetainedExtension
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! Realization of a lower-depth child coupling on an actual designated-child
occurrence. Disintegration is pulled back at the SAME completed source seed.
The extension retains the original comparison draw and complete execution tape;
it does not replace them by the completed tape or resample a reference marginal.
The first-marginal premise concerns the supplied LOWER-depth joint coupling,
not accuracy or a desired retained law for the current parent. -/

noncomputable section
open MeasureTheory ProbabilityTheory MeasurableSpace
namespace AcceleratedLogConcave.Oracle.DesignatedChildRetainedCoupling
open TapeLowering NoisyLayer CanonicalTapeLaw CanonicalTapeMeasurability
open DesignatedChildAbsorbedLaw
open AcceleratedLogConcave.Probability.CausalRetainedExtension

private theorem instr_standardBorel (d : ℕ) (i : Instr c Γ τ) :
    @StandardBorelSpace (i.Tape d) (instrSpace d i) := by
  cases i with
  | gaussian => change StandardBorelSpace (Point d); infer_instance
  | uniform => change StandardBorelSpace UniformValue; infer_instance
  | pure _ => change StandardBorelSpace PUnit; infer_instance
  | center => change StandardBorelSpace PUnit; infer_instance
  | momentum => change StandardBorelSpace PUnit; infer_instance
  | grad _ => change StandardBorelSpace PUnit; infer_instance

/-- Countable generation follows from the actual finite syntax, with its
canonical instruction spaces; it is not a supplier hypothesis. -/
private theorem tape_standardBorel (d : ℕ) (p : Prog c Γ τ) :
    @StandardBorelSpace (Tape d p) (tapeSpace d p) := by
  induction p with
  | ret r => change StandardBorelSpace PUnit; infer_instance
  | step o i next ih =>
      let : MeasurableSpace (i.Tape d) := instrSpace d i
      let : MeasurableSpace (Tape d next) := tapeSpace d next
      let : StandardBorelSpace (i.Tape d) := instr_standardBorel d i
      let : StandardBorelSpace (Tape d next) := ih
      change StandardBorelSpace (i.Tape d × Tape d next)
      infer_instance
  | batch o children next ihc ihn =>
      let : ∀ j, MeasurableSpace (Tape d (children j)) := fun j => tapeSpace d (children j)
      let : MeasurableSpace (Tape d next) := tapeSpace d next
      let : ∀ j, StandardBorelSpace (Tape d (children j)) := ihc
      let : StandardBorelSpace (Tape d next) := ihn
      change StandardBorelSpace ((∀ j, Tape d (children j)) × Tape d next)
      infer_instance

local instance canonicalTapeSpace (d : ℕ) (p : Prog c Γ τ) :
    MeasurableSpace (Tape d p) := tapeSpace d p
local instance canonicalTapeStandardBorel (d : ℕ) (p : Prog c Γ τ) :
    StandardBorelSpace (Tape d p) := tape_standardBorel d p

private theorem map_pullback_compProd {W B C : Type*}
    [MeasurableSpace W] [MeasurableSpace B] [MeasurableSpace C]
    (μ : Measure W) [SFinite μ] (ν : Measure B) [SFinite ν]
    (f : W → B) (hf : MeasurePreserving f μ ν)
    (k : Kernel B C) [IsSFiniteKernel k] :
    (μ ⊗ₘ k.comap f hf.measurable).map (Prod.map f id) = ν ⊗ₘ k := by
  ext s hs
  rw [Measure.map_apply (hf.measurable.prodMap measurable_id) hs,
    Measure.compProd_apply (hs.preimage (hf.measurable.prodMap measurable_id)),
    Measure.compProd_apply hs]
  exact hf.lintegral_comp (Kernel.measurable_kernel_prodMk_left hs)

variable {c c' d n : ℕ} {Δ : Ctx}
    (L : PrimitiveLaws d) (hL : L.pointDraw = stdGaussian (Point d))
    (p : Program c .point) (e : GaussianSlot p ≃ Fin n)
    (κ : Fin (n*n+c) → Fin c') (old : Ref Δ .point)
    (P : Ref Δ .point) (auxiliary : Fin n → Origin)
    (rho radius Ds : ℝ) (shift : Fin n → ℝ)
    (hrho : 0 ≤ rho) (hr : 0 < radius) (hDs : 0 < Ds)
    (hv : CovarianceSetup.shiftSq shift ≤ Ds^2) (hsmall : rho ≤ radius/(2*Ds))

/-- Exact actual occurrence law before adjoining a reference output. -/
def originalLaw : Measure (Raw d p e κ old P auxiliary) :=
  (stdGaussian (Point d)).prod (L.pointDraw.prod
    (tapeLaw L (RetainedMeanFinalBatch.designatedChild p e κ old P auxiliary)))

instance originalLaw_probability :
    IsProbabilityMeasure (originalLaw L p e κ old P auxiliary) := by
  let : IsProbabilityMeasure (tapeLaw L (RetainedMeanFinalBatch.designatedChild p e κ old P auxiliary)) :=
    tapeLaw_probability L _
  let : IsProbabilityMeasure L.pointDraw := L.point_probability
  unfold originalLaw
  infer_instance

/-- Source seed law required as the first marginal of the lower-depth coupling. -/
def sourceLaw : Measure (Point d × Tape d p) := L.pointDraw.prod (tapeLaw L p)

instance sourceLaw_probability : IsProbabilityMeasure (sourceLaw L p) := by
  let : IsProbabilityMeasure L.pointDraw := L.point_probability
  let : IsProbabilityMeasure (tapeLaw L p) := tapeLaw_probability L _
  unfold sourceLaw
  infer_instance

/-- Reference conditional evaluated at the actual completed source seed. -/
def conditional
    (joint : Kernel (Point d) ((Point d × Tape d p) × Point d)) [IsMarkovKernel joint] :
    Kernel (Point d × (Raw d p e κ old P auxiliary))
      (Point d) :=
  (childConditional joint).comap
    (fun z => (z.1,completedSource p e κ old P auxiliary rho radius shift z.2))
    (measurable_fst.prodMk
      ((completedSource_preserving L hL p e κ old P auxiliary rho radius Ds shift
        hrho hr hDs hv hsmall).measurable.comp measurable_snd))

instance conditional_markov
    (joint : Kernel (Point d) ((Point d × Tape d p) × Point d)) [IsMarkovKernel joint] :
    IsMarkovKernel (conditional L hL p e κ old P auxiliary rho radius Ds shift
      hrho hr hDs hv hsmall joint) := by
  unfold conditional
  infer_instance

/-- The actual center and ENTIRE original occurrence seed remain in the output. -/
def retainedKernel
    (joint : Kernel (Point d) ((Point d × Tape d p) × Point d)) [IsMarkovKernel joint] :=
  (Kernel.id : Kernel
    (Point d × (Raw d p e κ old P auxiliary)) _) ×ₖ
      conditional L hL p e κ old P auxiliary rho radius Ds shift
        hrho hr hDs hv hsmall joint

instance retainedKernel_markov
    (joint : Kernel (Point d) ((Point d × Tape d p) × Point d)) [IsMarkovKernel joint] :
    IsMarkovKernel (retainedKernel L hL p e κ old P auxiliary rho radius Ds shift
      hrho hr hDs hv hsmall joint) := by
  unfold retainedKernel
  infer_instance

/-- At every input, forgetting only the new child output gives the identity
kernel on the original center, comparison draw and complete actual child tape. -/
theorem retainedKernel_original
    (joint : Kernel (Point d) ((Point d × Tape d p) × Point d)) [IsMarkovKernel joint] :
    (retainedKernel L hL p e κ old P auxiliary rho radius Ds shift
      hrho hr hDs hv hsmall joint).fst = Kernel.id := by
  unfold retainedKernel
  exact Kernel.fst_prod _ _

theorem conditional_measurable
    (joint : Kernel (Point d) ((Point d × Tape d p) × Point d)) [IsMarkovKernel joint] :
    Measurable (conditional L hL p e κ old P auxiliary rho radius Ds shift
      hrho hr hDs hv hsmall joint) := Kernel.measurable _

/-- The canonical extension contains the original comparison and full child
tape as its first coordinate; its conditional never discards that sample. -/
def occurrenceLaw
    (joint : Kernel (Point d) ((Point d × Tape d p) × Point d)) [IsMarkovKernel joint]
    (center : Point d) :=
  originalLaw L p e κ old P auxiliary ⊗ₘ
    (conditional L hL p e κ old P auxiliary rho radius Ds shift
      hrho hr hDs hv hsmall joint).comap (fun w => (center,w)) measurable_prodMk_left

theorem original_projection
    (joint : Kernel (Point d) ((Point d × Tape d p) × Point d)) [IsMarkovKernel joint]
    (center : Point d) :
    (occurrenceLaw L hL p e κ old P auxiliary rho radius Ds shift
      hrho hr hDs hv hsmall joint center).map Prod.fst =
      originalLaw L p e κ old P auxiliary :=
  Measure.fst_compProd _ _

/-- Source-specific pullback of the LOWER child joint coupling. The reference
is adjoined conditionally at the completed seed of this exact actual occurrence. -/
theorem projected_joint
    (joint : Kernel (Point d) ((Point d × Tape d p) × Point d)) [IsMarkovKernel joint]
    (hsource : joint.fst = Kernel.const (Point d) (sourceLaw L p)) (center : Point d) :
    (occurrenceLaw L hL p e κ old P auxiliary rho radius Ds shift
      hrho hr hDs hv hsmall joint center).map
        (Prod.map (completedSource p e κ old P auxiliary rho radius shift) id) =
      joint center := by
  have hp : MeasurePreserving
      (completedSource p e κ old P auxiliary rho radius shift)
      (originalLaw L p e κ old P auxiliary) (sourceLaw L p) :=
    completedSource_preserving L hL p e κ old P auxiliary rho radius Ds shift
      hrho hr hDs hv hsmall
  let k := (childConditional joint).comap (fun b => (center,b)) measurable_prodMk_left
  have hdis := disintegrate_source joint (Kernel.const (Point d) (sourceLaw L p)) hsource
  change (originalLaw L p e κ old P auxiliary ⊗ₘ
      k.comap (completedSource p e κ old P auxiliary rho radius shift) hp.measurable).map _ = _
  rw [map_pullback_compProd _ (sourceLaw L p) _ hp k]
  ext s hs
  rw [Measure.compProd_apply hs, ← hdis, Kernel.compProd_apply hs]
  rfl

/-- The completed-seed/reference projection is measure preserving onto the
given lower-depth coupling, not merely onto one of its marginals. -/
theorem projected_preserving
    (joint : Kernel (Point d) ((Point d × Tape d p) × Point d)) [IsMarkovKernel joint]
    (hsource : joint.fst = Kernel.const (Point d) (sourceLaw L p)) (center : Point d) :
    MeasurePreserving
      (Prod.map (completedSource p e κ old P auxiliary rho radius shift) id)
      (occurrenceLaw L hL p e κ old P auxiliary rho radius Ds shift
        hrho hr hDs hv hsmall joint center) (joint center) := by
  refine ⟨?_, projected_joint L hL p e κ old P auxiliary rho radius Ds shift
    hrho hr hDs hv hsmall joint hsource center⟩
  exact (completedSource_preserving L hL p e κ old P auxiliary rho radius Ds shift
    hrho hr hDs hv hsmall).measurable.prodMap measurable_id

/-- The retained designated input is the existing stored value, not
the comparison Gaussian. Its joint law with the reference is inherited exactly. -/
theorem designated_reference_law
    (joint : Kernel (Point d) ((Point d × Tape d p) × Point d)) [IsMarkovKernel joint]
    (hsource : joint.fst = Kernel.const (Point d) (sourceLaw L p)) (center : Point d) :
    (occurrenceLaw L hL p e κ old P auxiliary rho radius Ds shift
      hrho hr hDs hv hsmall joint center).map
        (fun z => (z.1.2.1,z.2)) =
      (joint center).map (fun z => (z.1.1,z.2)) := by
  have hp := projected_preserving L hL p e κ old P auxiliary rho radius Ds shift
    hrho hr hDs hv hsmall joint hsource center
  have h := congrArg (fun μ : Measure ((Point d × Tape d p) × Point d) =>
    μ.map (fun z => (z.1.1,z.2))) hp.map_eq
  rw [Measure.map_map (by fun_prop) hp.measurable] at h
  exact h

/-- A finite lower-child error moment transfers to this exact original
occurrence extension. The error may inspect the full source tape and reference. -/
theorem error_memLp
    (joint : Kernel (Point d) ((Point d × Tape d p) × Point d)) [IsMarkovKernel joint]
    (hsource : joint.fst = Kernel.const (Point d) (sourceLaw L p)) (center : Point d)
    (err : ((Point d × Tape d p) × Point d) → Point d)
    (herr : MemLp err 2 (joint center)) :
    MemLp (fun z => err
      (completedSource p e κ old P auxiliary rho radius shift z.1,z.2)) 2
      (occurrenceLaw L hL p e κ old P auxiliary rho radius Ds shift
        hrho hr hDs hv hsmall joint center) :=
  herr.comp_measurePreserving (projected_preserving L hL p e κ old P auxiliary
    rho radius Ds shift hrho hr hDs hv hsmall joint hsource center)

/-- The same coupling preserves the entire squared-error integral exactly.
Any lower-depth RMS bound therefore transfers without a new parent estimate. -/
theorem error_square_integral
    (joint : Kernel (Point d) ((Point d × Tape d p) × Point d)) [IsMarkovKernel joint]
    (hsource : joint.fst = Kernel.const (Point d) (sourceLaw L p)) (center : Point d)
    (err : ((Point d × Tape d p) × Point d) → Point d)
    (herr : MemLp err 2 (joint center)) :
    (∫ z, ‖err (completedSource p e κ old P auxiliary rho radius shift z.1,z.2)‖^2
      ∂occurrenceLaw L hL p e κ old P auxiliary rho radius Ds shift
        hrho hr hDs hv hsmall joint center) =
      ∫ z, ‖err z‖^2 ∂joint center := by
  have hp := projected_preserving L hL p e κ old P auxiliary rho radius Ds shift
    hrho hr hDs hv hsmall joint hsource center
  have hg : AEStronglyMeasurable (fun z => ‖err z‖^2) (joint center) :=
    herr.aestronglyMeasurable.norm.pow 2
  have hi := integral_map hp.aemeasurable (hp.map_eq.symm ▸ hg)
  rw [hp.map_eq] at hi
  exact hi.symm

end AcceleratedLogConcave.Oracle.DesignatedChildRetainedCoupling
