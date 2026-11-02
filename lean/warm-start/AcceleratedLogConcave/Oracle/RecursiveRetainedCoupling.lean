import AcceleratedLogConcave.Oracle.MeanStandaloneRetainedCoupling
import AcceleratedLogConcave.Oracle.TerminalSourceRetainedCoupling
import AcceleratedLogConcave.Oracle.MeanRecursiveChronologicalCoupling
import AcceleratedLogConcave.Oracle.PrivateRecursiveChronologicalCoupling
import AcceleratedLogConcave.Oracle.RecursiveExecutableInduction
import AcceleratedLogConcave.Oracle.PrescribedRecursiveStability

/-! Precision-recursive retained source kernels. Packages contain only source
and prescribed reference laws. Quantitative error is a separate property of
these same recursively selected kernels. References are normalized: the
physical target is primitiveMean F center radius + width • reference. -/
noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
namespace AcceleratedLogConcave.Oracle.RecursiveRetainedCoupling
open Numerics Numerics.AffineGraph TapeLowering CanonicalTapeLaw CanonicalTapeMeasurability
open RecursiveExecutable
local instance canonicalTapeSpace {d c : ℕ} {Γ : Ctx} {τ : Ty} (p : Prog c Γ τ) :
    MeasurableSpace (Tape d p) := tapeSpace d p
variable {d m : ℕ} (M : MeanGeometry m) (hm : 0<m)
  {F : Point d → ℝ} {ell : ℝ} (hF : ContDiff ℝ 2 F) (hell : 0≤ell)
  (hlo : ∀ z v,0≤fderiv ℝ (fderiv ℝ F) z v v)
  (hup : ∀ z v,fderiv ℝ (fderiv ℝ F) z v v≤ell*‖v‖^2)
  (t : ℝ) (ht : 0<t)

/-- One complete center-parameterized law package for the literal executable.
No accuracy, output moment, or current-call invariant is an input field. -/
structure Law (r σ q : ℝ) (hr : 0<r) (hσ : 0<σ) (hsmall : r^2*ell≤1/2)
    (E : ExecutableData) where
  joint : Kernel (Point d) ((Point d × Tape d E.program) × Point d)
  markov : IsMarkovKernel joint
  source : joint.fst=Kernel.const (Point d)
    (FreshChildRetainedCoupling.sourceLaw (Probability.CanonicalNativeTapeLaw.primitiveLaws d) E.program)
  retained : ∀ base,(joint base).map (fun z => (z.1.1,z.2))=
    (stdGaussian (Point d)) ⊗ₘ
      ((Conditional.RecursiveReference.referenceFamily hF hell hlo hup M hm t ht q).kernel.comap
        (fun p => (MeanCompletedReference.parentTheta r σ hr hσ hsmall base,p)) measurable_prodMk_left)

/-- Literal terminal origin used by RecursiveExecutable.terminal. -/
def terminalOrigin : Origin := [⟨.mean,.setup,0,0,0⟩]

/-- The terminal reference is the original designated Gaussian on the same
complete canonical seed, at every center. -/
def terminalLaw (scale r σ q : ℝ) (hr : 0<r) (hσ : 0<σ)
    (hsmall : r^2*ell≤1/2) (hq : q≤1/2) :
    Law M hm hF hell hlo hup t ht r σ q hr hσ hsmall (RecursiveExecutable.terminal scale r σ) where
  joint := TerminalSourceRetainedCoupling.joint terminalOrigin
  markov := TerminalSourceRetainedCoupling.joint_markov (d := d) terminalOrigin
  source := TerminalSourceRetainedCoupling.source_marginal terminalOrigin
  retained := by
    intro base
    have he : (Conditional.RecursiveReference.referenceFamily hF hell hlo hup M hm t ht q).kernel.comap
        (fun p => (MeanCompletedReference.parentTheta r σ hr hσ hsmall base,p)) measurable_prodMk_left =
        (Kernel.id : Kernel (Point d) (Point d)) := by
      ext p : 1
      exact Conditional.RecursiveReference.referenceFamily_terminal_apply hF hell hlo hup M hm t ht q hq _ p
    rw [he]
    exact TerminalSourceRetainedCoupling.reference_joint terminalOrigin base

/-- The public terminal package is exactly the existing canonical source
joint, with no new terminal coupling selected. -/
theorem terminalLaw_joint (scale r σ q : ℝ) (hr : 0<r) (hσ : 0<σ)
    (hsmall : r^2*ell≤1/2) (hq : q≤1/2) :
    (terminalLaw M hm hF hell hlo hup t ht scale r σ q hr hσ hsmall hq).joint=
      TerminalSourceRetainedCoupling.joint terminalOrigin := rfl

/-- Law package at admissible physical source parameters; its joint still
varies measurably in every actual external center. -/
abbrev At (theta : Conditional.SourceParameters (Point d) ell) (q : ℝ) (E : ExecutableData) :=
  Law M hm hF hell hlo hup t ht theta.radius theta.width q
    theta.radius_pos theta.width_pos theta.small E

/-- Equality transport changes only the dependent program presentation. -/
def castLaw {r σ q : ℝ} {hr : 0<r} {hσ : 0<σ} {hsmall : r^2*ell≤1/2}
    {E E' : ExecutableData} (h : E=E')
    (J : Law M hm hF hell hlo hup t ht r σ q hr hσ hsmall E) :
    Law M hm hF hell hlo hup t ht r σ q hr hσ hsmall E' := h ▸ J

section SourceStep
variable {n a h ns : ℕ} (nodes : Fin n ≃ M.MeanNode)
  (anchors : Fin a ≃ M.Anchor) (seeds : Fin h ≃ Fin m × M.Kernel)
  (mesh : IntervalMesh 0 (samplingEnd (M.R/backwardEnd M.R)))
  (snodes : Fin ns ≃ mesh.Source m)
  (Ds δ w : ℝ) (layers : ℕ) (htq : t≤1/4) (scale K : ℝ)
  (hDs : 0<Ds) (hδ : 0<δ) (hpsi : M.psi≤M.R^4)
  (inventory Hs : ℕ) (hcount : n + ns ≤ inventory) (hK : (1/2:ℝ)<K)
  (hHs : 8*K+4≤(Hs:ℝ)) (hbudget : sourceShiftBase layers inventory^(Hs+1)≤Ds)
  (theta : Conditional.SourceParameters (Point d) ell) (q : ℝ) (hqK : q≤K)
/-- Literal lower law packages for the source's main calls. The full source
kernel of each child, rather than an accuracy certificate, is used. -/
def meanMainLower
    (mainLaws : ∀ i,At M hm hF hell hlo hup t ht (MeanMainBatchCoupling.mainParameters M nodes theta.radius theta.width Ds δ t w ell theta.radius_pos theta.width_pos hDs hδ hell theta.small i (0 : Point d)) (q-1/4) ((MeanMainBatchCoupling.recursiveMain M nodes anchors seeds mesh snodes Ds δ t w layers ht htq scale theta.radius theta.width q) i))
    (k : ℕ) (hk : k<layers) :=
  MeanRecursiveChronologicalCoupling.mainLower M nodes anchors seeds mesh snodes Ds δ t w layers ht htq scale theta.radius theta.width q K hDs hpsi inventory Hs hcount hK hHs hbudget theta.radius_pos hqK (Probability.CanonicalNativeTapeLaw.primitiveLaws d) hF hell hlo hup hm theta.width_pos hδ theta.small
    (fun i => (mainLaws i).joint) (fun i => (mainLaws i).markov)
    (fun i => (mainLaws i).source) (fun i y => (mainLaws i).retained y) k hk

/-- Concrete private main conditionals from the strictly lower q−1/4 laws. -/
def privateMainLower
    (privateMainLaws : ∀ i,At M hm hF hell hlo hup t ht (PrivateRecursiveBatchBudget.mainParameters (privateGeometry M mesh) snodes theta.radius Ds ell hm theta.radius_pos hDs hell theta.small i (0 : Point d)) (q-1/4) ((PrivateRecursiveBatchBudget.main M nodes anchors seeds mesh snodes Ds δ t w layers ht htq scale theta.radius q) i))
    (k : ℕ) (hk : k<layers) :=
  PrivateRecursiveChronologicalCoupling.mainLower M nodes anchors seeds mesh snodes Ds δ t w layers ht htq scale theta.radius q K hDs hpsi inventory Hs hcount hK hHs hbudget theta.radius_pos hqK (Probability.CanonicalNativeTapeLaw.primitiveLaws d) hF hell hlo hup hm theta.small
    (fun i => (privateMainLaws i).joint) (fun i => (privateMainLaws i).markov)
    (fun i => (privateMainLaws i).source) (fun i y => (privateMainLaws i).retained y) k hk

/-- Actual last private batch at the reached finisher, from lower law packages. -/
def privateFinalLower
    (privateFinalLaws : ∀ i,At M hm hF hell hlo hup t ht (PrivateRecursiveBatchBudget.finalParameters (privateGeometry M mesh) snodes theta.radius ell theta.radius_pos hell theta.small i (0 : Point d)) (q-1/4) ((PrivateRecursiveBatchBudget.final M nodes anchors seeds mesh snodes Ds δ t w layers ht htq scale theta.radius q) i)) :=
  PrivateRecursiveFinalCoupling.lower M nodes anchors seeds mesh snodes Ds δ t w layers ht htq scale theta.radius q K hDs hpsi inventory Hs hcount hK hHs hbudget theta.radius_pos hqK
    (PrivateChronologicalCoupling.terminalCursor (privateGeometry M mesh) snodes theta.radius Ds (PrivateRecursiveBatchBudget.main M nodes anchors seeds mesh snodes Ds δ t w layers ht htq scale theta.radius q) (PrivateRecursiveBatchBudget.final M nodes anchors seeds mesh snodes Ds δ t w layers ht htq scale theta.radius q) layers).old
    (Probability.CanonicalNativeTapeLaw.primitiveLaws d) hF hell hlo hup hm theta.small
    (fun i => (privateFinalLaws i).joint) (fun i => (privateFinalLaws i).markov)
    (fun i => (privateFinalLaws i).source) (fun i y => (privateFinalLaws i).retained y)

/-- The active-final designated inputs remain the existing stored inputs. -/
def finalLower
    (finalLaws : ∀ i,At M hm hF hell hlo hup t ht (MeanMainBatchCoupling.finalParameters M theta.radius theta.width ell theta.radius_pos theta.width_pos hell theta.small (0 : Point d)) (q-t) ((MeanMainBatchCoupling.recursiveFinal M nodes anchors seeds mesh snodes Ds δ t w layers ht htq scale theta.radius theta.width q) i)) :
    DesignatedChildBatchCoupling.Lower (Probability.CanonicalNativeTapeLaw.primitiveLaws d)
      (MeanFinalBatchCoupling.recursiveData M nodes anchors seeds mesh snodes Ds δ t w layers ht htq scale theta.radius theta.width q K hDs hpsi inventory Hs hcount hK hHs hbudget theta.radius_pos hqK) :=
  ⟨(fun i => (finalLaws i).joint),(fun i => (finalLaws i).markov),(fun i => (finalLaws i).source)⟩

private theorem finalParameters_eq_child (base y : Point d) :
    MeanMainBatchCoupling.finalParameters M theta.radius theta.width ell
      theta.radius_pos theta.width_pos hell theta.small y =
      Conditional.RecursiveReference.childParameters hell M
        (MeanCompletedReference.parentTheta theta.radius theta.width theta.radius_pos theta.width_pos theta.small base) y := by
  apply Subtype.ext
  change (y,theta.radius*M.R,RecursiveMeanPublicTable.finalWidth M.R theta.width)=
    (y,theta.radius*M.R,M.R*Real.sqrt 3*theta.width/4)
  rw [SourceRecursiveRouting.finalWidth_eq]

variable (hm2 : 2≤m) (hδ1 : δ≤1) (hpsieq : M.psi=δ^(4*t)) (hhalf : δ^w≤1/2)
  (hback : M.backward=actualKernelInterval M.R (δ^w) M.R_pos M.R_le_half (Real.rpow_pos_of_pos hδ w))
  (G : Point d → Point d) (hG : Measurable G)

/-- Actual nonterminal source composition. Every stochastic input is a
strictly smaller mean-call law package, used through its exact joint kernel. -/
def step (hq : (1/2:ℝ)<q)
    (mainLaws : ∀ i,At M hm hF hell hlo hup t ht (MeanMainBatchCoupling.mainParameters M nodes theta.radius theta.width Ds δ t w ell theta.radius_pos theta.width_pos hDs hδ hell theta.small i (0 : Point d)) (q-1/4) ((MeanMainBatchCoupling.recursiveMain M nodes anchors seeds mesh snodes Ds δ t w layers ht htq scale theta.radius theta.width q) i))
    (finalLaws : ∀ i,At M hm hF hell hlo hup t ht (MeanMainBatchCoupling.finalParameters M theta.radius theta.width ell theta.radius_pos theta.width_pos hell theta.small (0 : Point d)) (q-t) ((MeanMainBatchCoupling.recursiveFinal M nodes anchors seeds mesh snodes Ds δ t w layers ht htq scale theta.radius theta.width q) i))
    (privateMainLaws : ∀ i,At M hm hF hell hlo hup t ht (PrivateRecursiveBatchBudget.mainParameters (privateGeometry M mesh) snodes theta.radius Ds ell hm theta.radius_pos hDs hell theta.small i (0 : Point d)) (q-1/4) ((PrivateRecursiveBatchBudget.main M nodes anchors seeds mesh snodes Ds δ t w layers ht htq scale theta.radius q) i))
    (privateFinalLaws : ∀ i,At M hm hF hell hlo hup t ht (PrivateRecursiveBatchBudget.finalParameters (privateGeometry M mesh) snodes theta.radius ell theta.radius_pos hell theta.small i (0 : Point d)) (q-1/4) ((PrivateRecursiveBatchBudget.final M nodes anchors seeds mesh snodes Ds δ t w layers ht htq scale theta.radius q) i)) :
    At M hm hF hell hlo hup t ht theta q
      (mean M nodes anchors seeds Ds δ t w ht htq layers mesh snodes scale theta.radius theta.width q) := by
  let main := MeanMainBatchCoupling.recursiveMain M nodes anchors seeds mesh snodes Ds δ t w layers ht htq scale theta.radius theta.width q
  let final := MeanMainBatchCoupling.recursiveFinal M nodes anchors seeds mesh snodes Ds δ t w layers ht htq scale theta.radius theta.width q
  let smain := PrivateRecursiveBatchBudget.main M nodes anchors seeds mesh snodes Ds δ t w layers ht htq scale theta.radius q
  let sfinal := PrivateRecursiveBatchBudget.final M nodes anchors seeds mesh snodes Ds δ t w layers ht htq scale theta.radius q
  let mainMass := MeanRecursiveChronologicalCoupling.mainMass M nodes anchors seeds mesh snodes Ds δ t w layers ht htq scale theta.radius theta.width q K hDs hpsi inventory Hs hcount hK hHs hbudget theta.radius_pos hqK
  let finalMass := (fun i => (MeanMainBatchCoupling.recursive_final_shift M nodes anchors seeds mesh snodes Ds δ t w layers ht htq scale theta.radius theta.width q K hDs hpsi inventory Hs hcount hK hHs hbudget theta.radius_pos hqK i).2)
  let privateMainMass := PrivateRecursiveChronologicalCoupling.mainMass M nodes anchors seeds mesh snodes Ds δ t w layers ht htq scale theta.radius q K hDs hpsi inventory Hs hcount hK hHs hbudget theta.radius_pos hqK
  let privateFinalMass := PrivateRecursiveChronologicalCoupling.finalMass M nodes anchors seeds mesh snodes Ds δ t w layers ht htq scale theta.radius q K hDs hpsi inventory Hs hcount hK hHs hbudget theta.radius_pos hqK
  let Jmain := meanMainLower M hm hF hell hlo hup t ht nodes anchors seeds mesh snodes Ds δ w layers htq scale K hDs hδ hpsi inventory Hs hcount hK hHs hbudget theta q hqK mainLaws
  let Jfinal := finalLower M hm hF hell hlo hup t ht nodes anchors seeds mesh snodes Ds δ w layers htq scale K hDs hpsi inventory Hs hcount hK hHs hbudget theta q hqK finalLaws
  let Jprivate := privateMainLower M hm hF hell hlo hup t ht nodes anchors seeds mesh snodes Ds δ w layers htq scale K hDs hpsi inventory Hs hcount hK hHs hbudget theta q hqK privateMainLaws
  let JprivateFinal := privateFinalLower M hm hF hell hlo hup t ht nodes anchors seeds mesh snodes Ds δ w layers htq scale K hDs hpsi inventory Hs hcount hK hHs hbudget theta q hqK privateFinalLaws
  let J := MeanStandaloneRetainedCoupling.kernel M nodes anchors seeds main final layers mesh snodes
    theta.radius Ds theta.width theta.radius_pos hDs theta.width_pos smain sfinal layers
    privateMainMass privateFinalMass (Probability.CanonicalNativeTapeLaw.primitiveLaws d) rfl hF hell hlo hup theta.small
    JprivateFinal Jprivate mainMass finalMass δ t w G hG Jmain Jfinal
  have he := MeanMainBatchCoupling.recursive_eq_build M nodes anchors seeds mesh snodes Ds δ t w layers ht htq scale theta.radius theta.width q hq
  refine castLaw M hm hF hell hlo hup t ht he.symm ?_
  refine ⟨J,?_,?_,?_⟩
  · exact MeanStandaloneRetainedCoupling.kernel_markov M nodes anchors seeds main final layers mesh snodes
      theta.radius Ds theta.width theta.radius_pos hDs theta.width_pos smain sfinal layers
      privateMainMass privateFinalMass (Probability.CanonicalNativeTapeLaw.primitiveLaws d) rfl hF hell hlo hup theta.small
      JprivateFinal Jprivate mainMass finalMass δ t w G hG Jmain Jfinal
  · exact MeanStandaloneRetainedCoupling.kernel_source M nodes anchors seeds main final layers mesh snodes
      theta.radius Ds theta.width theta.radius_pos hDs theta.width_pos smain sfinal layers
      privateMainMass privateFinalMass (Probability.CanonicalNativeTapeLaw.primitiveLaws d) rfl hF hell hlo hup theta.small
      JprivateFinal Jprivate mainMass finalMass δ t w G hG Jmain Jfinal
  · intro base
    apply MeanStandaloneRetainedCoupling.kernel_reference M nodes anchors seeds main final layers mesh snodes
      theta.radius Ds theta.width theta.radius_pos hDs theta.width_pos smain sfinal layers
      privateMainMass privateFinalMass (Probability.CanonicalNativeTapeLaw.primitiveLaws d) rfl hF hell hlo hup theta.small
      JprivateFinal Jprivate mainMass finalMass δ t w G hG Jmain Jfinal base hm ht q hq
    · intro i y
      rw [← finalParameters_eq_child M hell theta base y]
      exact (finalLaws i).retained y
    · exact MeanRecursiveChronologicalCoupling.row_pos δ t w theta.radius theta.width theta.radius_pos theta.width_pos hδ
    · exact MeanRecursiveChronologicalCoupling.actual_rows M nodes mesh snodes Ds δ t w layers ht
        theta.radius theta.width theta.radius_pos theta.width_pos hδ hm2 hδ1 hpsieq hhalf hback

/-- Actual recursive law construction. The four recursive arguments have
strictly smaller precision rank. No future accuracy proof or arbitrary kernel
choice is used to determine the parent or any child joint. -/
def core (theta₀ : Conditional.SourceParameters (Point d) ell) (precision : ℝ)
    (hprecision : precision≤K) : At M hm hF hell hlo hup t ht theta₀ precision (mean M nodes anchors seeds Ds δ t w ht htq layers mesh snodes scale theta₀.radius theta₀.width precision) := by
  classical
  by_cases hterminal : precision≤1/2
  · have he := RecursiveExecutable.mean_terminal M nodes anchors seeds (privateGeometry M mesh) snodes
      Ds δ t w ht htq layers scale theta₀.radius theta₀.width precision hterminal
    exact castLaw M hm hF hell hlo hup t ht he.symm
      (terminalLaw M hm hF hell hlo hup t ht scale theta₀.radius theta₀.width precision
        theta₀.radius_pos theta₀.width_pos theta₀.small hterminal)
  · let mainLaws : ∀ i,At M hm hF hell hlo hup t ht (MeanMainBatchCoupling.mainParameters M nodes theta₀.radius theta₀.width Ds δ t w ell theta₀.radius_pos theta₀.width_pos hDs hδ hell theta₀.small i (0 : Point d)) (precision-1/4) ((MeanMainBatchCoupling.recursiveMain M nodes anchors seeds mesh snodes Ds δ t w layers ht htq scale theta₀.radius theta₀.width precision) i) :=
      fun i => core (MeanMainBatchCoupling.mainParameters M nodes theta₀.radius theta₀.width Ds δ t w ell theta₀.radius_pos theta₀.width_pos hDs hδ hell theta₀.small i (0 : Point d)) (precision-1/4) (by linarith)
    let finalLaws : ∀ i,At M hm hF hell hlo hup t ht (MeanMainBatchCoupling.finalParameters M theta₀.radius theta₀.width ell theta₀.radius_pos theta₀.width_pos hell theta₀.small (0 : Point d)) (precision-t) ((MeanMainBatchCoupling.recursiveFinal M nodes anchors seeds mesh snodes Ds δ t w layers ht htq scale theta₀.radius theta₀.width precision) i) :=
      fun _ => core (MeanMainBatchCoupling.finalParameters M theta₀.radius theta₀.width ell theta₀.radius_pos theta₀.width_pos hell theta₀.small (0 : Point d)) (precision-t) (by linarith)
    let privateMainLaws : ∀ i,At M hm hF hell hlo hup t ht (PrivateRecursiveBatchBudget.mainParameters (privateGeometry M mesh) snodes theta₀.radius Ds ell hm theta₀.radius_pos hDs hell theta₀.small i (0 : Point d)) (precision-1/4) ((PrivateRecursiveBatchBudget.main M nodes anchors seeds mesh snodes Ds δ t w layers ht htq scale theta₀.radius precision) i) :=
      fun i => core (PrivateRecursiveBatchBudget.mainParameters (privateGeometry M mesh) snodes theta₀.radius Ds ell hm theta₀.radius_pos hDs hell theta₀.small i (0 : Point d)) (precision-1/4) (by linarith)
    let privateFinalLaws : ∀ i,At M hm hF hell hlo hup t ht (PrivateRecursiveBatchBudget.finalParameters (privateGeometry M mesh) snodes theta₀.radius ell theta₀.radius_pos hell theta₀.small i (0 : Point d)) (precision-1/4) ((PrivateRecursiveBatchBudget.final M nodes anchors seeds mesh snodes Ds δ t w layers ht htq scale theta₀.radius precision) i) :=
      fun i => core (PrivateRecursiveBatchBudget.finalParameters (privateGeometry M mesh) snodes theta₀.radius ell theta₀.radius_pos hell theta₀.small i (0 : Point d)) (precision-1/4) (by linarith)
    exact step M hm hF hell hlo hup t ht nodes anchors seeds mesh snodes Ds δ w layers htq scale K hDs hδ hpsi inventory Hs hcount hK hHs hbudget theta₀ precision hprecision hm2 hδ1 hpsieq hhalf hback G hG (lt_of_not_ge hterminal) mainLaws finalLaws privateMainLaws privateFinalLaws
termination_by Precision.precisionRank t precision
decreasing_by
  all_goals
    apply Nat.lt_of_succ_le
    apply Precision.precisionRank_drop ht (lt_of_not_ge hterminal)
    first | exact le_rfl | linarith

/-- The actual precision-recursive full-seed retained kernel, jointly
measurable in its external center. -/
def kernel (theta₀ : Conditional.SourceParameters (Point d) ell) (precision : ℝ)
    (hprecision : precision≤K) :=
  (core M hm hF hell hlo hup t ht nodes anchors seeds mesh snodes Ds δ w layers htq scale K hDs hδ hpsi inventory Hs hcount hK hHs hbudget hm2 hδ1 hpsieq hhalf hback G hG theta₀ precision hprecision).joint

theorem kernel_markov (theta₀ : Conditional.SourceParameters (Point d) ell) (precision : ℝ)
    (hprecision : precision≤K) : IsMarkovKernel (kernel M hm hF hell hlo hup t ht nodes anchors seeds mesh snodes Ds δ w layers htq scale K hDs hδ hpsi inventory Hs hcount hK hHs hbudget hm2 hδ1 hpsieq hhalf hback G hG theta₀ precision hprecision) :=
  (core M hm hF hell hlo hup t ht nodes anchors seeds mesh snodes Ds δ w layers htq scale K hDs hδ hpsi inventory Hs hcount hK hHs hbudget hm2 hδ1 hpsieq hhalf hback G hG theta₀ precision hprecision).markov

theorem kernel_source (theta₀ : Conditional.SourceParameters (Point d) ell) (precision : ℝ)
    (hprecision : precision≤K) :
    (kernel M hm hF hell hlo hup t ht nodes anchors seeds mesh snodes Ds δ w layers htq scale K hDs hδ hpsi inventory Hs hcount hK hHs hbudget hm2 hδ1 hpsieq hhalf hback G hG theta₀ precision hprecision).fst = Kernel.const (Point d)
      (FreshChildRetainedCoupling.sourceLaw (Probability.CanonicalNativeTapeLaw.primitiveLaws d)
        (mean M nodes anchors seeds Ds δ t w ht htq layers mesh snodes scale theta₀.radius theta₀.width precision).program) :=
  (core M hm hF hell hlo hup t ht nodes anchors seeds mesh snodes Ds δ w layers htq scale K hDs hδ hpsi inventory Hs hcount hK hHs hbudget hm2 hδ1 hpsieq hhalf hback G hG theta₀ precision hprecision).source

theorem kernel_reference (theta₀ : Conditional.SourceParameters (Point d) ell) (precision : ℝ)
    (hprecision : precision≤K) (base : Point d) :
    ((kernel M hm hF hell hlo hup t ht nodes anchors seeds mesh snodes Ds δ w layers htq scale K hDs hδ hpsi inventory Hs hcount hK hHs hbudget hm2 hδ1 hpsieq hhalf hback G hG theta₀ precision hprecision) base).map (fun z => (z.1.1,z.2)) =
      (stdGaussian (Point d)) ⊗ₘ
        ((Conditional.RecursiveReference.referenceFamily hF hell hlo hup M hm t ht precision).kernel.comap
          (fun p => (MeanCompletedReference.parentTheta theta₀.radius theta₀.width
            theta₀.radius_pos theta₀.width_pos theta₀.small base,p)) measurable_prodMk_left) :=
  (core M hm hF hell hlo hup t ht nodes anchors seeds mesh snodes Ds δ w layers htq scale K hDs hδ hpsi inventory Hs hcount hK hHs hbudget hm2 hδ1 hpsieq hhalf hback G hG theta₀ precision hprecision).retained base

theorem kernel_measurable (theta₀ : Conditional.SourceParameters (Point d) ell) (precision : ℝ)
    (hprecision : precision≤K) : Measurable (kernel M hm hF hell hlo hup t ht nodes anchors seeds mesh snodes Ds δ w layers htq scale K hDs hδ hpsi inventory Hs hcount hK hHs hbudget hm2 hδ1 hpsieq hhalf hback G hG theta₀ precision hprecision) :=
  Kernel.measurable _

/-- At a terminal precision this same recursively selected package is exactly
its original terminal package, transported only along the executable equality. -/
theorem core_terminal (theta₀ : Conditional.SourceParameters (Point d) ell) (precision : ℝ)
    (hprecision : precision≤K) (hterminal : precision≤1/2) :
    core M hm hF hell hlo hup t ht nodes anchors seeds mesh snodes Ds δ w layers htq scale K hDs hδ hpsi inventory Hs hcount hK hHs hbudget hm2 hδ1 hpsieq hhalf hback G hG theta₀ precision hprecision = castLaw M hm hF hell hlo hup t ht
      (RecursiveExecutable.mean_terminal M nodes anchors seeds (privateGeometry M mesh) snodes
        Ds δ t w ht htq layers scale theta₀.radius theta₀.width precision hterminal).symm
      (terminalLaw M hm hF hell hlo hup t ht scale theta₀.radius theta₀.width precision
        theta₀.radius_pos theta₀.width_pos theta₀.small hterminal) := by
  rw [core]
  simp only [dite_eq_left hterminal]

end SourceStep

end AcceleratedLogConcave.Oracle.RecursiveRetainedCoupling
