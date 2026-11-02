import AcceleratedLogConcave.Oracle.DesignatedChildRetainedCoupling
import AcceleratedLogConcave.Oracle.FreshChildBatchCoupling

/-! Finite actual designated-child reference augmentation. The pair of each
stored Pi and its appended reference is retained jointly. No fresh Pi draw
is substituted for the program's existing input. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
set_option backward.isDefEq.respectTransparency false
namespace AcceleratedLogConcave.Oracle.DesignatedChildBatchCoupling
open TapeLowering NoisyLayer CanonicalTapeLaw CanonicalTapeMeasurability
open Conditional.MeanReferenceLayer
local instance canonicalTapeSpace (d : ℕ) (p : Prog c Γ τ) :
    MeasurableSpace (Tape d p) := tapeSpace d p

structure Data (N C : ℕ) (Γ : Ctx) where
  child : Fin N → ExecutableData
  slot : ∀ i, Fin ((tapeShape (child i).program).gaussianBlocks * (tapeShape (child i).program).gaussianBlocks + (child i).size) → Fin C
  old : Fin N → Ref Γ .point
  designated : Fin N → Ref Γ .point
  auxiliary : ∀ i, Fin (tapeShape (child i).program).gaussianBlocks → Origin
  rho : Fin N → ℝ
  radius : Fin N → ℝ
  Ds : ℝ
  rho_nonneg : ∀ i, 0 ≤ rho i
  radius_pos : ∀ i, 0 < radius i
  Ds_pos : 0 < Ds
  shift_budget : ∀ i, CovarianceSetup.shiftSq (child i).shiftVector ≤ Ds^2
  small : ∀ i, rho i ≤ radius i/(2*Ds)

variable {d N C : ℕ} {Γ : Ctx}
def program (B : Data N C Γ) (i : Fin N) : Prog C Γ .point :=
  RetainedMeanFinalBatch.designatedChild (B.child i).program (B.child i).enumeration
    (B.slot i) (B.old i) (B.designated i) (B.auxiliary i)
abbrev Raw (d : ℕ) (B : Data N C Γ) (i : Fin N) :=
  Point d × (Point d × Tape d (program B i))
def rawLaw (L : PrimitiveLaws d) (B : Data N C Γ) (i : Fin N) : Measure (Raw d B i) :=
  DesignatedChildRetainedCoupling.originalLaw L (B.child i).program (B.child i).enumeration
    (B.slot i) (B.old i) (B.designated i) (B.auxiliary i)
instance rawLaw_probability (L : PrimitiveLaws d) (B : Data N C Γ) (i : Fin N) :
    IsProbabilityMeasure (rawLaw L B i) :=
  DesignatedChildRetainedCoupling.originalLaw_probability L
    (B.child i).program (B.child i).enumeration (B.slot i)
    (B.old i) (B.designated i) (B.auxiliary i)

/-- Only the actual lower full-seed joint law is supplied. Its retained
Pi/reference projection, rather than an independent Gaussian shortcut, will
be the exact batch conclusion. -/
structure Lower (L : PrimitiveLaws d) (B : Data N C Γ) where
  joint : ∀ i, Kernel (Point d) ((Point d × Tape d (B.child i).program) × Point d)
  markov : ∀ i, IsMarkovKernel (joint i)
  source : ∀ i, (joint i).fst = Kernel.const (Point d)
    (DesignatedChildRetainedCoupling.sourceLaw L (B.child i).program)
instance lower_markov (L : PrimitiveLaws d) (B : Data N C Γ) (J : Lower L B) (i : Fin N) :
    IsMarkovKernel (J.joint i) := J.markov i

variable (L : PrimitiveLaws d) (hL : L.pointDraw = stdGaussian (Point d))
  (B : Data N C Γ) (J : Lower L B)
def childConditional (i : Fin N) : Kernel (Point d × Raw d B i) (Point d) :=
  DesignatedChildRetainedCoupling.conditional L hL (B.child i).program (B.child i).enumeration
    (B.slot i) (B.old i) (B.designated i) (B.auxiliary i)
    (B.rho i) (B.radius i) B.Ds (B.child i).shiftVector
    (B.rho_nonneg i) (B.radius_pos i) B.Ds_pos (B.shift_budget i) (B.small i) (J.joint i)
instance childConditional_markov (i : Fin N) : IsMarkovKernel (childConditional L hL B J i) := by
  exact DesignatedChildRetainedCoupling.conditional_markov L hL
    (B.child i).program (B.child i).enumeration (B.slot i)
    (B.old i) (B.designated i) (B.auxiliary i)
    (B.rho i) (B.radius i) B.Ds (B.child i).shiftVector
    (B.rho_nonneg i) (B.radius_pos i) B.Ds_pos (B.shift_budget i) (B.small i) (J.joint i)

def childPaired (i : Fin N) : Kernel (Point d × Raw d B i) (Point d × Point d) :=
  (Kernel.deterministic (fun z => z.2.2.1) (by fun_prop)) ×ₖ childConditional L hL B J i
instance childPaired_markov (i : Fin N) : IsMarkovKernel (childPaired L hL B J i) := by
  unfold childPaired
  infer_instance

theorem childPaired_law (i : Fin N) (x : Point d) :
    (childPaired L hL B J i).comap (fun w => (x,w)) measurable_prodMk_left ∘ₘ rawLaw L B i =
      (J.joint i x).map (fun z => (z.1.1,z.2)) := by
  have hp := DesignatedChildRetainedCoupling.designated_reference_law L hL
    (B.child i).program (B.child i).enumeration (B.slot i) (B.old i) (B.designated i) (B.auxiliary i)
    (B.rho i) (B.radius i) B.Ds (B.child i).shiftVector
    (B.rho_nonneg i) (B.radius_pos i) B.Ds_pos (B.shift_budget i) (B.small i)
    (J.joint i) (J.source i) x
  change (rawLaw L B i ⊗ₘ (childConditional L hL B J i).comap
    (fun w => (x,w)) measurable_prodMk_left).map (fun z => (z.1.2.1,z.2)) = _ at hp
  rw [Measure.compProd_eq_comp_prod, Measure.map_comp _ _ (by fun_prop)] at hp
  convert hp using 1
  congr 1
  ext w s hs
  rw [Kernel.comap_apply, childPaired, Kernel.prod_apply, Kernel.deterministic_apply,
    Kernel.map_apply _ (by fun_prop), Kernel.prod_apply, Kernel.id_apply,
    Measure.dirac_prod, Measure.dirac_prod, Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

variable {H : Type*} [MeasurableSpace H]
  (center : Fin N → H → Point d) (hcenter : ∀ i, Measurable (center i))
def referenceBatch : Kernel (H × (∀ i, Raw d B i)) (Fin N → Point d) :=
  finiteProduct N (fun i => (childConditional L hL B J i).comap
    (fun z => (center i z.1,z.2 i))
    (((hcenter i).comp measurable_fst).prodMk ((measurable_pi_apply i).comp measurable_snd)))
instance referenceBatch_markov : IsMarkovKernel (referenceBatch L hL B J center hcenter) := by
  apply finiteProduct_markov
  intro i
  infer_instance

/-- Keep all original coarse data and raw occurrence samples. -/
def retainedBatch := (Kernel.id : Kernel (H × (∀ i, Raw d B i)) _) ×ₖ
  referenceBatch L hL B J center hcenter
instance retainedBatch_markov : IsMarkovKernel (retainedBatch L hL B J center hcenter) := by
  unfold retainedBatch
  infer_instance
theorem original_preserved : (retainedBatch L hL B J center hcenter).fst = Kernel.id :=
  Kernel.fst_prod _ _

/-- Joint stored-input/reference observation; no original sample is deleted
from retainedBatch itself. -/
def pairedBatch : Kernel (H × (∀ i, Raw d B i)) (Fin N → Point d × Point d) :=
  (retainedBatch L hL B J center hcenter).map (fun z i => ((z.1.2 i).2.1,z.2 i))
instance pairedBatch_markov : IsMarkovKernel (pairedBatch L hL B J center hcenter) := by
  unfold pairedBatch
  exact Kernel.IsMarkovKernel.map _ (by fun_prop)

theorem pairedBatch_apply (z : H × (∀ i, Raw d B i)) :
    pairedBatch L hL B J center hcenter z =
      Measure.pi (fun i => childPaired L hL B J i (center i z.1,z.2 i)) := by
  rw [pairedBatch, Kernel.map_apply _ (by fun_prop), retainedBatch,
    Kernel.prod_apply, Kernel.id_apply, Measure.dirac_prod,
    Measure.map_map (by fun_prop) (by fun_prop), referenceBatch,
    finiteProduct_apply N _ (fun _ => inferInstance)]
  have h := Measure.pi_map_pi (μ := fun i => childConditional L hL B J i (center i z.1,z.2 i)) (fun i =>
    (show Measurable (Prod.mk ((z.2 i).2.1) : Point d → Point d × Point d) from
      measurable_prodMk_left).aemeasurable)
  simp only [Kernel.comap_apply] at h ⊢
  change (Measure.pi (fun i => childConditional L hL B J i (center i z.1,z.2 i))).map
    (fun x i => ((z.2 i).2.1,x i)) = _
  rw [h]
  congr 1
  funext i
  rw [childPaired, Kernel.prod_apply, Kernel.deterministic_apply, Measure.dirac_prod]

/-- Exact product of LOWER retained-pair laws, derived from the actual
conditional kernels. This includes the empty active-final inventory. -/
theorem pairedBatch_law (h : H) :
    (pairedBatch L hL B J center hcenter).comap (fun w => (h,w)) measurable_prodMk_left ∘ₘ
      Measure.pi (rawLaw L B) =
      Measure.pi (fun i => (J.joint i (center i h)).map (fun z => (z.1.1,z.2))) := by
  let k := (pairedBatch L hL B J center hcenter).comap (fun w => (h,w)) measurable_prodMk_left
  apply (Measure.pi_eq fun s hs => ?_).symm
  rw [Measure.bind_apply (MeasurableSet.univ_pi hs) k.aemeasurable]
  have he : ∀ w, k w (Set.univ.pi s) =
      ∏ i, childPaired L hL B J i (center i h,w i) (s i) := by
    intro w
    rw [Kernel.comap_apply, pairedBatch_apply, Measure.pi_pi]
  simp_rw [he]
  have hf : ∀ i, Measurable (fun w : Raw d B i =>
      childPaired L hL B J i (center i h,w) (s i)) := fun i =>
    ((childPaired L hL B J i).measurable_coe (hs i)).comp measurable_prodMk_left
  have hi := iIndepFun_pi (μ := rawLaw L B) (fun i => (hf i).aemeasurable)
  rw [lintegral_prod_eq_prod_lintegral_of_indepFun Finset.univ _ hi
    (fun i => (hf i).comp (measurable_pi_apply i))]
  apply Finset.prod_congr rfl
  intro i _
  rw [(measurePreserving_eval (rawLaw L B) i).lintegral_comp (hf i)]
  change (∫⁻ w, ((childPaired L hL B J i).comap
    (fun w => (center i h,w)) measurable_prodMk_left) w (s i) ∂rawLaw L B i) = _
  rw [← Measure.bind_apply (hs i) (Kernel.aemeasurable _), childPaired_law]

end AcceleratedLogConcave.Oracle.DesignatedChildBatchCoupling
