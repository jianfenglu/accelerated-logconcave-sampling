import Mathlib.Probability.Kernel.Disintegration.StandardBorel
import Mathlib.Probability.Kernel.Composition.Lemmas

/-! A chronological extension by a lower-depth child coupling. The input `joint`
is the already constructed joint law of the consumed source seed and the child
reference output, conditional on the host. It is not a correctness or accuracy
assumption for the current parent call. Disintegration adds the reference output
conditional on the SAME consumed seed. The entire unread suffix is retained and
the extension cannot inspect it. No independence of a retained host coordinate
from its consumed seed is required. -/

noncomputable section
open MeasureTheory ProbabilityTheory MeasurableSpace

namespace AcceleratedLogConcave.Probability.CausalRetainedExtension

variable {A B C T : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace C] [MeasurableSpace T]
    [StandardBorelSpace C] [Nonempty C] [CountableOrCountablyGenerated A B]
    (joint : Kernel A (B × C)) [IsMarkovKernel joint]

/-- The reference output is sampled from the conditional of the lower-depth
joint coupling, at the actual host and actual consumed source seed. -/
def childConditional : Kernel (A × B) C := joint.condKernel

instance childConditional_markov : IsMarkovKernel (childConditional joint) := by
  unfold childConditional
  infer_instance

/-- Preserve the actual host and source seed while adjoining the child output. -/
def retainedStep : Kernel (A × B) ((A × B) × C) :=
  Kernel.id ×ₖ childConditional joint

instance retainedStep_markov : IsMarkovKernel (retainedStep joint) := by
  unfold retainedStep
  infer_instance

/-- The suffix is copied in full; the child conditional reads no suffix data. -/
def fullStep : Kernel ((A × B) × T) (((A × B) × C) × T) :=
  retainedStep joint ∥ₖ Kernel.id

instance fullStep_markov : IsMarkovKernel (fullStep (T := T) joint) := by
  unfold fullStep
  infer_instance

theorem childConditional_measurable : Measurable (childConditional joint) :=
  (childConditional joint).measurable

theorem fullStep_measurable : Measurable (fullStep (T := T) joint) :=
  (fullStep (T := T) joint).measurable

/-- The only marginal input is the source-seed law of the LOWER child coupling. -/
theorem disintegrate_source (source : Kernel A B) (hsource : joint.fst = source) :
    source ⊗ₖ childConditional joint = joint := by
  rw [← hsource, childConditional]
  exact joint.disintegrate _

/-- Joint measurability includes both the host and the consumed seed. -/
theorem childConditional_apply_measurable (s : Set C) (hs : MeasurableSet s) :
    Measurable (fun z : A × B => childConditional joint z s) :=
  (childConditional joint).measurable_coe hs

/-- Before adding an unread suffix, the constructed law is exactly the given
lower-depth joint coupling, with the original host retained. -/
theorem retainedStep_law (source : Kernel A B) (hsource : joint.fst = source)
    (host : Measure A) [SFinite host] [IsSFiniteKernel source] :
    retainedStep joint ∘ₘ (host ⊗ₘ source) =
      (host ⊗ₘ joint).map MeasurableEquiv.prodAssoc.symm := by
  rw [retainedStep, ← Measure.compProd_eq_comp_prod,
    ← Measure.compProd_assoc, disintegrate_source joint source hsource]

/-- The fresh WHOLE unread suffix remains a product factor after extension. -/
theorem fullStep_fresh_suffix (source : Kernel A B)
    (host : Measure A) [SFinite host] [IsSFiniteKernel source]
    (suffix : Measure T) [SFinite suffix] :
    fullStep joint ∘ₘ ((host ⊗ₘ source).prod suffix) =
      ((host ⊗ₘ source) ⊗ₘ childConditional joint).prod suffix := by
  rw [fullStep, ← Measure.prod_comp_left, retainedStep,
    ← Measure.compProd_eq_comp_prod]

/-- The same full-sample construction realizes the lower-depth joint law and
retains all unread coordinates with their original product law. -/
theorem fullStep_joint_law (source : Kernel A B) (hsource : joint.fst = source)
    (host : Measure A) [SFinite host] [IsSFiniteKernel source]
    (suffix : Measure T) [SFinite suffix] :
    fullStep joint ∘ₘ ((host ⊗ₘ source).prod suffix) =
      ((host ⊗ₘ joint).map MeasurableEquiv.prodAssoc.symm).prod suffix := by
  rw [fullStep, ← Measure.prod_comp_left,
    retainedStep_law joint source hsource host]

/-- Forgetting only the adjoined output recovers the ORIGINAL full sample,
including its actual host, consumed seed and every unread suffix coordinate. -/
theorem fullStep_original_projection (source : Kernel A B)
    (host : Measure A) [SFinite host] [IsSFiniteKernel source]
    (suffix : Measure T) [SFinite suffix] :
    (fullStep joint ∘ₘ ((host ⊗ₘ source).prod suffix)).map
      (fun z => (z.1.1,z.2)) = (host ⊗ₘ source).prod suffix := by
  rw [fullStep_fresh_suffix]
  change (_ : Measure (((A × B) × C) × T)).map (Prod.map Prod.fst id) = _
  rw [← Measure.map_prod_map _ _ measurable_fst measurable_id]
  simp only [Measure.map_id]
  change ((host ⊗ₘ source ⊗ₘ childConditional joint).fst).prod suffix = _
  rw [Measure.fst_compProd]

/-- Projecting the entire suffix away leaves exactly the consumed lower-depth
coupling with its original host, after the canonical reassociation. -/
theorem fullStep_consumed_projection (source : Kernel A B) (hsource : joint.fst = source)
    (host : Measure A) [SFinite host] [IsSFiniteKernel source]
    (suffix : Measure T) [IsProbabilityMeasure suffix] :
    (fullStep joint ∘ₘ ((host ⊗ₘ source).prod suffix)).map
      (fun z => (z.1.1.1,(z.1.1.2,z.1.2))) = host ⊗ₘ joint := by
  rw [fullStep_joint_law joint source hsource]
  have h : (fun z : (((A × B) × C) × T) => (z.1.1.1,(z.1.1.2,z.1.2))) =
      MeasurableEquiv.prodAssoc ∘ Prod.fst := rfl
  rw [h, ← Measure.map_map (by fun_prop) measurable_fst]
  change ((((host ⊗ₘ joint).map MeasurableEquiv.prodAssoc.symm).prod suffix).fst).map
    MeasurableEquiv.prodAssoc = _
  rw [Measure.fst_prod]
  simp

/-- A child retained-pair identity is needed only almost everywhere in the
host. It transports through this constructed extension; it is not promoted to
a pointwise conditional identity on exceptional seeds. -/
theorem fullStep_child_marginal_ae {D : Type*} [MeasurableSpace D]
    (source : Kernel A B) (hsource : joint.fst = source)
    (host : Measure A) [SFinite host] [IsSFiniteKernel source]
    (suffix : Measure T) [IsProbabilityMeasure suffix]
    (retained : B × C → D) (hretained : Measurable retained)
    (target : Kernel A D) [IsSFiniteKernel target]
    (hchild : joint.map retained =ᵐ[host] target) :
    (fullStep joint ∘ₘ ((host ⊗ₘ source).prod suffix)).map
      (fun z => (z.1.1.1,retained (z.1.1.2,z.1.2))) = host ⊗ₘ target := by
  have hm : Measurable (Prod.map (id : A → A) retained) := measurable_id.prodMap hretained
  have he : (fun z : (((A × B) × C) × T) =>
      (z.1.1.1,retained (z.1.1.2,z.1.2))) =
      Prod.map id retained ∘ (fun z => (z.1.1.1,(z.1.1.2,z.1.2))) := rfl
  rw [he, ← Measure.map_map hm (by fun_prop),
    fullStep_consumed_projection joint source hsource host suffix,
    ← Measure.compProd_map hretained]
  exact Measure.compProd_congr hchild

end AcceleratedLogConcave.Probability.CausalRetainedExtension
