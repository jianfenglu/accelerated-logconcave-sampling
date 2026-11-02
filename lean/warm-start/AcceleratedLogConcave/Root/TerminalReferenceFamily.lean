import AcceleratedLogConcave.Root.ClockBackwardKernel
import AcceleratedLogConcave.Oracle.TerminalMean
import AcceleratedLogConcave.Oracle.TapeLowering

/-! The manuscript's actual terminal (q ≤ 1/2) reference family.
The reference is the unchanged designated input of the existing terminalMeanProgram.
No nonterminal precision is relabelled terminal. The root RadiusChildren instance
below is deliberately restricted to K=0. Compiler absorption and RMS are separate. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open AcceleratedLogConcave Oracle Oracle.TapeLowering Kinetic
open scoped ENNReal ContDiff
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace AcceleratedLogConcave.Root.TerminalReferenceFamily

abbrev TerminalPrecision := Iic (1/2 : ℝ)
/-- Precision, (radius,width), and mean-coordinate center, all varying jointly. -/
abbrev Parameters (d : ℕ) := TerminalPrecision × ((ℝ × ℝ) × Point d)
variable {d : ℕ}

/-- The existing one-query source branch, not a substitute sampler. -/
def retainedRun (origin : Origin) (G : Point d → Point d) (a : ℝ)
    (theta : Parameters d) (p z : Point d) : Result d .point × Point d :=
  terminalMeanRetained origin G a theta.2.1.1 theta.2.1.2 theta.2.2 p z

@[simp] theorem retainedRun_reference (origin : Origin) (G : Point d → Point d) (a : ℝ)
    (theta : Parameters d) (p z : Point d) :
    (retainedRun origin G a theta p z).2 = p := rfl

/-- Literal terminal retained reference, as a JOINT parameter/input kernel. -/
def referenceKernel (d : ℕ) : Kernel (Parameters d × Point d) (Point d) :=
  Kernel.deterministic Prod.snd measurable_snd

instance referenceKernel_markov : IsMarkovKernel (referenceKernel d) := by
  unfold referenceKernel
  infer_instance

/-- The transition is identified with the actual source retained coordinate for EVERY auxiliary. -/
theorem referenceKernel_eq_source (origin : Origin) (G : Point d → Point d) (a : ℝ)
    (theta : Parameters d) (p z : Point d) :
    referenceKernel d (theta,p) = Measure.dirac (retainedRun origin G a theta p z).2 := rfl

theorem referenceKernel_section (theta : Parameters d) :
    (referenceKernel d).comap (fun p => (theta,p)) measurable_prodMk_left = Kernel.id := by
  ext p : 1
  rfl

theorem referenceKernel_invariant (theta : Parameters d) :
    (referenceKernel d).comap (fun p => (theta,p)) measurable_prodMk_left ∘ₘ
      stdGaussian (Point d) = stdGaussian (Point d) := by
  rw [referenceKernel_section]
  exact Measure.id_comp

/-- Full retained pair law from the actual source branch, uniformly in every parameter. -/
theorem retained_pair_law (origin : Origin) (G : Point d → Point d) (a : ℝ)
    (theta : Parameters d) :
    (terminalGaussianPairLaw d).map (fun pz => (pz.1, (retainedRun origin G a theta pz.1 pz.2).2)) =
      stdGaussian (Point d) ⊗ₘ
        (referenceKernel d).comap (fun p => (theta,p)) measurable_prodMk_left := by
  rw [referenceKernel_section]
  change (terminalGaussianPairLaw d).map (fun pz => (pz.1,pz.1)) = _
  rw [terminalMean_retained_diagonal]
  exact (Measure.compProd_deterministic measurable_id).symm

/-- Joint regularity of the actual executed value and retained coordinate, not just fixed-data sections. -/
theorem continuous_retainedRun (origin : Origin) {G : Point d → Point d}
    (hG : Continuous G) (a : ℝ) :
    Continuous (fun z : (Parameters d × Point d) × Point d =>
      ((show Point d from (retainedRun origin G a z.1.1 z.1.2 z.2).1.value),
       (retainedRun origin G a z.1.1 z.1.2 z.2).2)) := by
  change Continuous (fun z : (Parameters d × Point d) × Point d =>
    (a • G (a • (z.1.1.2.2 + z.1.1.2.1.1 • z.2)) + z.1.1.2.1.2 • z.1.2, z.1.2))
  fun_prop

/-- Concrete all-parameter actual-run/reference coupling on the one real auxiliary block. -/
def runReferenceKernel (origin : Origin) (G : Point d → Point d) (a : ℝ) :
    Kernel (Parameters d × Point d) (Point d × Point d) :=
  ((Kernel.id : Kernel (Parameters d × Point d) (Parameters d × Point d)) ×ₖ
    Kernel.const (Parameters d × Point d) (stdGaussian (Point d))).map
      (fun z => ((show Point d from (retainedRun origin G a z.1.1 z.1.2 z.2).1.value),
        (retainedRun origin G a z.1.1 z.1.2 z.2).2))

theorem runReferenceKernel_markov (origin : Origin) {G : Point d → Point d}
    (hG : Continuous G) (a : ℝ) : IsMarkovKernel (runReferenceKernel origin G a) :=
  Kernel.IsMarkovKernel.map _ (continuous_retainedRun origin hG a).measurable

/-- The source potential really is the original potential at the specified linear scale. -/
theorem retainedRun_scaled_value {V : Point d → ℝ} (hV : ContDiff ℝ 1 V)
    (origin : Origin) (a : ℝ) (theta : Parameters d) (p z : Point d) :
    (retainedRun origin (gradient V) a theta p z).1.value =
      gradient (scaledPotential V a) (theta.2.2 + theta.2.1.1 • z) + theta.2.1.2 • p := by
  change a • gradient V (a • (theta.2.2 + theta.2.1.1 • z)) + theta.2.1.2 • p = _
  rw [gradient_scaled_potential hV]

/-- C1 regularity of the original potential supplies the actual gradient continuity. -/
theorem continuous_source_gradient {V : Point d → ℝ} (hV : ContDiff ℝ 1 V) :
    Continuous (gradient V) := by
  exact (InnerProductSpace.toDual ℝ (Point d)).symm.continuous.comp
    (hV.continuous_fderiv (by norm_num))

theorem sourceRunReferenceKernel_markov {V : Point d → ℝ} (hV : ContDiff ℝ 1 V)
    (origin : Origin) (a : ℝ) : IsMarkovKernel (runReferenceKernel origin (gradient V) a) :=
  runReferenceKernel_markov origin (continuous_source_gradient hV) a

/-- The actual terminal branch has no uniform residual coordinate. -/
instance terminalResidual_subsingleton (origin : Origin) :
    Subsingleton (ResidualTape (terminalMeanProgram origin)) := by
  dsimp [terminalMeanProgram, terminalMeanBody, ResidualTape, InstrResidualTape]
  infer_instance

/-- All source Gaussian slots are retained; there is exactly one. -/
theorem terminal_gaussian_count (origin : Origin) :
    Fintype.card (GaussianSlot (terminalMeanProgram origin)) = 1 := by
  rw [card_gaussianSlot, terminalMeanProgram_tapeShape]

/-- Fixed source enumeration, unique because the terminal source has one Gaussian slot. -/
def terminalEnumeration (origin : Origin) : GaussianSlot (terminalMeanProgram origin) ≃ Fin 1 :=
  gaussianSlotEquiv (terminalMeanProgram origin)

theorem terminalEnumeration_unique (origin : Origin)
    (e : GaussianSlot (terminalMeanProgram origin) ≃ Fin 1) : e = terminalEnumeration origin := by
  apply Equiv.ext
  intro s
  exact Subsingleton.elim _ _

/-- The actual one-Gaussian source encoding covers EVERY terminal execution tape. -/
theorem terminal_full_tape (origin : Origin) (tape : Tape d (terminalMeanProgram origin)) :
    terminalMeanTapeEquiv d origin ((terminalMeanTapeEquiv d origin).symm tape) = tape :=
  (terminalMeanTapeEquiv d origin).apply_symm_apply tape

section SourceBase
open ClockBackwardKernel

/-- Actual terminal parameters for the normalized-root source's precision-zero child. -/
def sourceParameters (h : ℝ) (r : RadiusBand h) (c : Point d) : Parameters d :=
  (⟨0, by norm_num⟩, ((r, sourceWidth h), c))

theorem sourceWidth_pos {h : ℝ} (hh : 0 < h) : 0 < sourceWidth h := by
  unfold sourceWidth
  positivity

theorem band_radius_pos {h : ℝ} (hh : 0 < h) (r : RadiusBand h) : 0 < (r : ℝ) :=
  lt_of_lt_of_le (by positivity) r.2.1

/-- Source precision K=0 is genuinely terminal. No instance is supplied for K≥1. -/
def sourceRadiusChildren (d : ℕ) (h : ℝ) : RadiusChildren (Fin d) h 0 where
  kernel _ := (referenceKernel d).comap
    (fun z => (sourceParameters h z.1.1 z.1.2,z.2)) (by
      unfold sourceParameters
      fun_prop)
  markov _ := by infer_instance
  invariant _ r c := by
    have he : (((referenceKernel d).comap
        (fun z => (sourceParameters h z.1.1 z.1.2,z.2)) (by unfold sourceParameters; fun_prop)).comap
        (fun p => ((r,c),p)) measurable_prodMk_left) = Kernel.id := by
      ext p : 1
      rfl
    rw [he]
    exact Measure.id_comp

/-- Every actual root child slot is the prescribed terminal reference, at its real source parameters. -/
theorem sourceRadiusChildren_eq_source (h : ℝ)
    (i : Fin (ClockSchedule.sourceCells h * ClockSchedule.sourceOrder 0))
    (origin : Origin) (V : Point d → ℝ) (r : RadiusBand h) (c p z : Point d) :
    (sourceRadiusChildren d h).kernel i ((r,c),p) =
      Measure.dirac (terminalMeanRetained origin (gradient V) (Real.sqrt h)
        r (sourceWidth h) c p z).2 := rfl

variable (F : Analysis.Poisson.ReferencePoissonFamily (EuclideanSpace ℝ (Fin d)) 0 (1/2))
  (h : ℝ) (hh : 0 < h)

/-- Actual radius and inverse-flow mean center on the unchanged GL inventory. -/
def sourceNodeParameters
    (i : Fin (ClockSchedule.sourceCells h * ClockSchedule.sourceOrder 0))
    (z : ClockLaw.Clock × (Point d × Point d)) : Parameters d :=
  sourceParameters h (radiusParameter h hh 0 i z.1)
    ((Real.sqrt h)⁻¹ • center F (Real.sqrt (2*h^2)) _ _
      (ClockSchedule.sourceCells_pos hh) i z)

theorem continuous_sourceNodeParameters
    (i : Fin (ClockSchedule.sourceCells h * ClockSchedule.sourceOrder 0)) :
    Continuous (sourceNodeParameters F h hh i) := by
  have hc := continuous_center F (Real.sqrt (2*h^2))
    (ClockSchedule.sourceCells h) (ClockSchedule.sourceOrder 0)
    (ClockSchedule.sourceCells_pos hh) i
  have hr := (continuous_radiusParameter h hh 0 i).subtype_val
  unfold sourceNodeParameters sourceParameters
  fun_prop

/-- The original-gradient terminal execution varies measurably along the REAL parent/node schedule. -/
theorem continuous_sourceNodeRetained {V : Point d → ℝ} (hV : ContDiff ℝ 1 V)
    (origin : Origin) (i : Fin (ClockSchedule.sourceCells h * ClockSchedule.sourceOrder 0)) :
    Continuous (fun z : (ClockLaw.Clock × (Point d × Point d)) × (Point d × Point d) =>
      ((show Point d from (retainedRun origin (gradient V) (Real.sqrt h)
        (sourceNodeParameters F h hh i z.1) z.2.1 z.2.2).1.value),
       (retainedRun origin (gradient V) (Real.sqrt h)
        (sourceNodeParameters F h hh i z.1) z.2.1 z.2.2).2)) := by
  have hi : Continuous (fun z : (ClockLaw.Clock × (Point d × Point d)) × (Point d × Point d) =>
      ((sourceNodeParameters F h hh i z.1, z.2.1), z.2.2)) :=
    (((continuous_sourceNodeParameters F h hh i).comp continuous_fst).prodMk
      continuous_snd.fst).prodMk continuous_snd.snd
  have ho := continuous_retainedRun origin (continuous_source_gradient hV) (Real.sqrt h)
  apply (ho.comp hi).congr
  intro z
  rfl

/-- The actual ClockLaw child field equals the retained coordinate of this prescribed source call. -/
theorem sourceNode_child_eq_source (origin : Origin) (V : Point d → ℝ)
    (i : Fin (ClockSchedule.sourceCells h * ClockSchedule.sourceOrder 0))
    (t : ClockLaw.Clock) (b : Point d × Point d) (p z : Point d) :
    (data F (Real.sqrt (2*h^2)) _ _ (ClockSchedule.sourceCells_pos hh)
      (ClockSchedule.sourceOrder_pos 0) (Real.sqrt h)⁻¹
      (sourceClockChildren h hh 0 (sourceRadiusChildren d h))).child i ((t,b),p) =
      Measure.dirac (retainedRun origin (gradient V) (Real.sqrt h)
        (sourceNodeParameters F h hh i (t,b)) p z).2 := rfl

/-- All-clock root with actual terminal children; no child-kernel or root-invariance premise. -/
def terminalRootKernel : Kernel (ClockLaw.Clock × GaussianPhase (Point d)) (Point d) :=
  sourceKernelFromRadiusFamily F h hh 0 (sourceRadiusChildren d h)

instance terminalRootKernel_markov : IsMarkovKernel (terminalRootKernel F h hh) := by
  unfold terminalRootKernel
  infer_instance

theorem terminalRootKernel_conditionallyInvariant (t : ClockLaw.Clock) :
    ∀ x s, MeasurableSet s →
      (∫⁻ p, terminalRootKernel F h hh (t,(x,p)) s ∂stdGaussian (Point d)) =
        stdGaussian (Point d) s :=
  sourceKernelFromRadiusFamily_conditionallyInvariant F h hh 0 (sourceRadiusChildren d h) t

/-- The integer-precision source cannot use this terminal constructor at positive precision. -/
theorem natural_terminal_iff (K : ℕ) : (K : ℝ) ≤ 1/2 ↔ K = 0 := by
  constructor
  · intro hK
    have : K < 1 := by exact_mod_cast (show (K : ℝ) < 1 by linarith)
    omega
  · rintro rfl
    norm_num
end SourceBase
end AcceleratedLogConcave.Root.TerminalReferenceFamily
