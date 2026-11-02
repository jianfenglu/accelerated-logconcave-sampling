import AcceleratedLogConcave.Root.ConditionalLaw
import AcceleratedLogConcave.Oracle.Syntax

/-!
Construct the law extension, rather than assume a root coupling exists. The
extension keeps its entire execution-space coordinate and applies the existing
finite product of exact child kernels to the observed host. The next module
uses the literal root tape as this execution space.

`ConditionalLaw.Data` is an explicit LOWER-LEVEL reference-kernel supplier.
It says nothing about executable child accuracy. The canonical lift here is a
law-correct coupling, not the accuracy-bearing coupling needed by the manuscript.
-/
noncomputable section
set_option autoImplicit false

namespace AcceleratedLogConcave.Root.LocalRootLawReferenceLift
open MeasureTheory ProbabilityTheory
open Conditional
open Oracle
open scoped BigOperators

variable {B : Type*} [MeasurableSpace B] {d m : ℕ}

abbrev Host := ConditionalLaw.Host (B := B) (ι := Fin d) (m := m)
abbrev Reference := ConditionalLaw.Execution (B := B) (ι := Fin d) (m := m)

def hostLaw (μ : Measure B) : Measure (Host (B := B) (d := d) (m := m)) :=
  (μ.prod (stdGaussian (Point d))).prod (RetainedLaw.noiseLaw (ι := Fin d) (m := m))

instance hostLaw_probability (μ : Measure B) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (hostLaw (d := d) (m := m) μ) := by
  unfold hostLaw
  infer_instance

def referenceLaw (D : ConditionalLaw.Data B (Fin d) m) (μ : Measure B) :
    Measure (Reference (B := B) (d := d) (m := m)) :=
  hostLaw μ ⊗ₘ ConditionalLaw.childrenKernel D

instance referenceLaw_probability (D : ConditionalLaw.Data B (Fin d) m)
    (μ : Measure B) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (referenceLaw D μ) := by
  unfold referenceLaw
  infer_instance

theorem referenceLaw_eq_joint (D : ConditionalLaw.Data B (Fin d) m)
    (μ : Measure B) [IsProbabilityMeasure μ] :
    referenceLaw D μ = ConditionalLaw.jointKernel D ∘ₘ
      (μ.prod (stdGaussian (Point d))) := by
  rw [ConditionalLaw.jointKernel, ← Measure.comp_assoc,
    ConditionalLaw.freshKernel, ← Measure.compProd_eq_comp_prod,
    ← Measure.compProd_eq_comp_prod, Measure.compProd_const]
  all_goals rfl

/-- Parent and the old dormant input are retained jointly with the new output. -/
theorem referenceLaw_retained (D : ConditionalLaw.Data B (Fin d) m)
    (μ : Measure B) [IsProbabilityMeasure μ] :
    (referenceLaw D μ).map (fun z => (z.1.1, ConditionalLaw.output D z)) =
      (μ.prod (stdGaussian (Point d))) ⊗ₘ ConditionalLaw.rootKernel D := by
  have hm : Measurable (fun z : Reference (B := B) (d := d) (m := m) =>
      (z.1.1, ConditionalLaw.output D z)) :=
    measurable_fst.fst.prodMk (ConditionalLaw.measurable_output D)
  apply Measure.ext_of_lintegral
  intro f hf
  have hF : Measurable (fun z : Reference (B := B) (d := d) (m := m) =>
      f (z.1.1, ConditionalLaw.output D z)) := hf.comp hm
  rw [lintegral_map hf hm, referenceLaw_eq_joint,
    Measure.lintegral_bind (Kernel.aemeasurable _) hF.aemeasurable,
    Measure.lintegral_compProd hf]
  apply lintegral_congr
  intro x
  have hfx : Measurable (fun q : Point d => f (x,q)) :=
    hf.comp measurable_prodMk_left
  have hM : Measurable (fun z : Reference (B := B) (d := d) (m := m) =>
      f (x, ConditionalLaw.output D z)) :=
    hf.comp (measurable_const.prodMk (ConditionalLaw.measurable_output D))
  rw [ConditionalLaw.lintegral_jointKernel D x.1 x.2 _ hF,
    ConditionalLaw.rootKernel, Kernel.map_apply _ (ConditionalLaw.measurable_output D),
    lintegral_map hfx (ConditionalLaw.measurable_output D),
    ConditionalLaw.lintegral_jointKernel D x.1 x.2 _ hM]

/-- The relevant conditional Gaussian statement retains the parent, but does
not add the old dormant input to the conditioning field. -/
theorem referenceLaw_parent_output (D : ConditionalLaw.Data B (Fin d) m)
    (μ : Measure B) [IsProbabilityMeasure μ] :
    (referenceLaw D μ).map (fun z => (z.1.1.1, ConditionalLaw.output D z)) =
      μ.prod (stdGaussian (Point d)) := by
  let g : (B × Point d) × Point d → B × Point d := fun z => (z.1.1,z.2)
  have hg : Measurable g := measurable_fst.fst.prodMk measurable_snd
  have hk :
      ((Kernel.id : Kernel (B × Point d) (B × Point d)) ×ₖ
        ConditionalLaw.rootKernel D).map g =
      (Kernel.deterministic Prod.fst measurable_fst) ×ₖ ConditionalLaw.rootKernel D := by
    ext x : 1
    apply Measure.ext_of_lintegral
    intro f hf
    rw [Kernel.map_apply _ hg, lintegral_map hf hg,
      Kernel.lintegral_id_prod (show Measurable (fun z => f (g z)) from hf.comp hg),
      Kernel.lintegral_deterministic_prod measurable_fst _ _ hf]
  have he := congrArg (fun ν => ν.map g) (referenceLaw_retained D μ)
  rw [Measure.map_map hg
    (measurable_fst.fst.prodMk (ConditionalLaw.measurable_output D)),
    Measure.compProd_eq_comp_prod, Measure.map_comp _ _ hg, hk,
    ConditionalLaw.parent_output_law D μ] at he
  exact he

section Lift
variable {Ω : Type*} [MeasurableSpace Ω]
  (D : ConditionalLaw.Data B (Fin d) m) (μΩ : Measure Ω)
  (host : Ω → Host (B := B) (d := d) (m := m)) (hhost : Measurable host)

/-- The only added randomness consists of exact child-reference transitions.
The `Ω` coordinate is never modified, replaced, or resampled. -/
def liftKernel : Kernel Ω (Fin m → Point d) :=
  (ConditionalLaw.childrenKernel D).comap host hhost

instance liftKernel_markov : IsMarkovKernel (liftKernel D host hhost) := by
  unfold liftKernel
  infer_instance

def liftLaw : Measure (Ω × (Fin m → Point d)) := μΩ ⊗ₘ liftKernel D host hhost

instance liftLaw_probability [IsProbabilityMeasure μΩ] :
    IsProbabilityMeasure (liftLaw D μΩ host hhost) := by
  unfold liftLaw
  infer_instance

/-- Stronger than an output marginal: the entire execution coordinate survives. -/
theorem liftLaw_original [IsProbabilityMeasure μΩ] :
    (liftLaw D μΩ host hhost).map Prod.fst = μΩ :=
  Measure.fst_compProd μΩ (liftKernel D host hhost)

/-- Every measurable execution observable therefore has its original law. -/
theorem liftLaw_observable [IsProbabilityMeasure μΩ]
    {A : Type*} [MeasurableSpace A] (f : Ω → A) (hf : Measurable f) :
    (liftLaw D μΩ host hhost).map (fun z => f z.1) = μΩ.map f := by
  calc
    _ = ((liftLaw D μΩ host hhost).map Prod.fst).map f :=
      (Measure.map_map hf measurable_fst).symm
    _ = _ := congrArg (fun ν => ν.map f) (liftLaw_original D μΩ host hhost)

/-- Actual pushforward calculation for the constructed lift. It is not a
premise asserting existence of a root coupling. -/
theorem liftLaw_reference [IsProbabilityMeasure μΩ]
    (μ : Measure B) [IsProbabilityMeasure μ]
    (hLaw : μΩ.map host = hostLaw (d := d) (m := m) μ) :
    (liftLaw D μΩ host hhost).map (fun z => (host z.1,z.2)) = referenceLaw D μ := by
  rw [liftLaw, liftKernel, MeanReferenceLayer.compProd_comap_push, hLaw]
  rfl

/-- Full reference joint, including the exact parent and old dormant input. -/
theorem liftLaw_retained_reference [IsProbabilityMeasure μΩ]
    (μ : Measure B) [IsProbabilityMeasure μ]
    (hLaw : μΩ.map host = hostLaw (d := d) (m := m) μ) :
    (liftLaw D μΩ host hhost).map
      (fun z => ((host z.1).1, ConditionalLaw.output D (host z.1,z.2))) =
      (μ.prod (stdGaussian (Point d))) ⊗ₘ ConditionalLaw.rootKernel D := by
  have he := congrArg (fun ν => ν.map
    (fun z : Reference (B := B) (d := d) (m := m) =>
      (z.1.1, ConditionalLaw.output D z)))
    (liftLaw_reference D μΩ host hhost μ hLaw)
  rw [Measure.map_map
    (measurable_fst.fst.prodMk (ConditionalLaw.measurable_output D))
    (show Measurable (fun z : Ω × (Fin m → Point d) => (host z.1,z.2)) from
      (hhost.comp measurable_fst).prodMk measurable_snd), referenceLaw_retained] at he
  exact he

theorem liftLaw_parent_output [IsProbabilityMeasure μΩ]
    (μ : Measure B) [IsProbabilityMeasure μ]
    (hLaw : μΩ.map host = hostLaw (d := d) (m := m) μ) :
    (liftLaw D μΩ host hhost).map
      (fun z => ((host z.1).1.1, ConditionalLaw.output D (host z.1,z.2))) =
      μ.prod (stdGaussian (Point d)) := by
  have he := congrArg (fun ν => ν.map
    (fun z : Reference (B := B) (d := d) (m := m) =>
      (z.1.1.1, ConditionalLaw.output D z)))
    (liftLaw_reference D μΩ host hhost μ hLaw)
  rw [Measure.map_map
    (measurable_fst.fst.fst.prodMk (ConditionalLaw.measurable_output D))
    (show Measurable (fun z : Ω × (Fin m → Point d) => (host z.1,z.2)) from
      (hhost.comp measurable_fst).prodMk measurable_snd), referenceLaw_parent_output] at he
  exact he
end Lift

section Replacement
variable {Ω : Type*} [MeasurableSpace Ω] {A : Type*} [MeasurableSpace A]

/-- Handoff for a later, accuracy-bearing extension. This is CONDITIONAL:
the quantitative writer must construct `jointLaw` and prove its whole-execution
marginal, not merely the marginal of one final value. No existence is assumed. -/
theorem extension_observable (jointLaw : Measure (Ω × (Fin m → Point d)))
    (μΩ : Measure Ω) (hOriginal : jointLaw.map Prod.fst = μΩ)
    (f : Ω → A) (hf : Measurable f) :
    jointLaw.map (fun z => f z.1) = μΩ.map f := by
  calc
    _ = (jointLaw.map Prod.fst).map f := (Measure.map_map hf measurable_fst).symm
    _ = _ := congrArg (fun ν => ν.map f) hOriginal

/-- A microscopic host/child-reference joint suffices for every retained
reference observable. It does not assume the final accuracy estimate. -/
theorem extension_reference_observable
    (D : ConditionalLaw.Data B (Fin d) m) (μ : Measure B)
    (jointLaw : Measure (Ω × (Fin m → Point d)))
    (host : Ω → Host (B := B) (d := d) (m := m)) (hhost : Measurable host)
    (hReference : jointLaw.map (fun z => (host z.1,z.2)) = referenceLaw D μ)
    (f : Reference (B := B) (d := d) (m := m) → A) (hf : Measurable f) :
    jointLaw.map (fun z => f (host z.1,z.2)) = (referenceLaw D μ).map f := by
  calc
    _ = (jointLaw.map (fun z => (host z.1,z.2))).map f :=
      (Measure.map_map hf ((hhost.comp measurable_fst).prodMk measurable_snd)).symm
    _ = _ := congrArg (fun ν => ν.map f) hReference
end Replacement

/-- Empty active inventory: the same H0 returns for every reference execution. -/
theorem reference_output_zero_slots (D : ConditionalLaw.Data B (Fin d) 0)
    (z : Reference (B := B) (d := d) (m := 0)) :
    ConditionalLaw.output D z = z.1.1.2 := by
  have h := RetainedLaw.innovation (ConditionalLaw.atParent D z.1.1.1)
    ((z.1.1.2,z.1.2),z.2)
  change ConditionalLaw.output D z - z.1.1.2 = _ at h
  simpa only [Fin.sum_univ_zero, sub_eq_zero] using h

/-- Zero weights need no omitted-child convention: all slots still exist. -/
theorem reference_output_zero_weights (D : ConditionalLaw.Data B (Fin d) m)
    (hzero : ∀ b i, D.weight b i = 0)
    (z : Reference (B := B) (d := d) (m := m)) :
    ConditionalLaw.output D z = z.1.1.2 := by
  have h := RetainedLaw.innovation (ConditionalLaw.atParent D z.1.1.1)
    ((z.1.1.2,z.1.2),z.2)
  change ConditionalLaw.output D z - z.1.1.2 =
    ∑ i, (-D.weight z.1.1.1 i) •
      (z.2 i - RetainedLaw.active (ConditionalLaw.atParent D z.1.1.1)
        (z.1.1.2,z.1.2) i) at h
  simpa only [hzero, neg_zero, zero_smul, Finset.sum_const_zero, sub_eq_zero] using h

end AcceleratedLogConcave.Root.LocalRootLawReferenceLift
