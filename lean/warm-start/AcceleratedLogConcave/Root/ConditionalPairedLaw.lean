import AcceleratedLogConcave.Root.BackwardParentLaw
import AcceleratedLogConcave.Root.LocalRootLawReferenceLift
import AcceleratedLogConcave.Conditional.MeanReferenceSeedLaw

/-! Exact full retained-pair disintegration for the constructed conditional
root. Original dormant input is reconstructed as a correlated graph coordinate,
never adjoined as an independent conditional Gaussian. -/
noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace AcceleratedLogConcave.Root.ConditionalPairedLaw
open Conditional Conditional.MeanReferenceLayer
variable {B : Type*} [MeasurableSpace B] {d m : ℕ}
local notation "E" => Oracle.Point d
variable (D : ConditionalLaw.Data B (Fin d) m)
local instance child_markov (i : Fin m) : IsMarkovKernel (D.child i) := D.markov i

def stateChildren : Kernel ((B × E) × (Fin m → E)) (Fin m → E) :=
  finiteProduct m (fun i => (D.child i).comap (fun z => (z.1.1,z.2 i))
    (measurable_fst.fst.prodMk ((measurable_pi_apply i).comp measurable_snd)))
instance stateChildren_markov : IsMarkovKernel (stateChildren D) :=
  finiteProduct_markov m _ (fun _ => inferInstance)
theorem stateChildren_apply (z : (B × E) × (Fin m → E)) :
    stateChildren D z=Measure.pi (fun i => D.child i (z.1.1,z.2 i)) :=
  finiteProduct_apply m _ (fun _ => inferInstance) z

/-- Average the actual independent designated inputs, retaining each together
with its returned reference. -/
def pairedChildren : Kernel ((B × E)) (Fin m → E × E) :=
  (((Kernel.id : Kernel (((B × E) × (Fin m → E))) _) ×ₖ stateChildren D).map
    (fun z i => (z.1.2 i,z.2 i))) ∘ₖ
      ((Kernel.id : Kernel ((B × E)) _) ×ₖ
        Kernel.const _ (Measure.pi fun _ : Fin m => stdGaussian E))
instance pairedChildren_markov : IsMarkovKernel (pairedChildren D) := by
  let : IsMarkovKernel (((Kernel.id : Kernel (((B × E) × (Fin m → E))) _) ×ₖ stateChildren D).map
      (fun z i => (z.1.2 i,z.2 i))) := Kernel.IsMarkovKernel.map _ (by fun_prop)
  unfold pairedChildren
  infer_instance

private def childPair (i : Fin m) : Kernel ((B × E) × E) (E × E) :=
  (Kernel.deterministic Prod.snd measurable_snd) ×ₖ
    (D.child i).comap (fun z => (z.1.1,z.2))
      (measurable_fst.fst.prodMk measurable_snd)
private instance childPair_markov (i : Fin m) : IsMarkovKernel (childPair D i) := by
  let := D.markov i
  unfold childPair
  infer_instance

private theorem childPair_average (i : Fin m) (b : (B × E)) :
    (childPair D i).comap (fun p => (b,p)) measurable_prodMk_left ∘ₘ stdGaussian E =
      (stdGaussian E) ⊗ₘ (D.child i).comap (fun p => (b.1,p)) measurable_prodMk_left := by
  rw [Measure.compProd_eq_comp_prod]
  congr 1
  ext p s hs
  rw [Kernel.comap_apply,childPair,Kernel.prod_apply,Kernel.deterministic_apply,
    Kernel.prod_apply,Kernel.id_apply]
  rfl

private theorem pairedChildren_before (z : ((B × E) × (Fin m → E))) :
    (((Kernel.id : Kernel (((B × E) × (Fin m → E))) _) ×ₖ stateChildren D).map
      (fun z i => (z.1.2 i,z.2 i))) z =
        Measure.pi (fun i => childPair D i (z.1,z.2 i)) := by
  rw [Kernel.map_apply _ (by fun_prop),Kernel.prod_apply,Kernel.id_apply,
    Measure.dirac_prod,Measure.map_map (by fun_prop) (by fun_prop),stateChildren_apply]
  have h := Measure.pi_map_pi (μ := fun i => D.child i (z.1.1,z.2 i))
    (fun i => (show Measurable (Prod.mk (z.2 i) : E → E × E) from measurable_prodMk_left).aemeasurable)
  change (Measure.pi fun i => D.child i (z.1.1,z.2 i)).map
    (fun q i => (z.2 i,q i)) = _
  rw [h]
  congr 1
  funext i
  rw [childPair,Kernel.prod_apply,Kernel.deterministic_apply,Measure.dirac_prod]
  rfl

/-- Full product of retained designated-input/reference pairs. -/
theorem pairedChildren_apply (b : (B × E)) :
    pairedChildren D b = Measure.pi (fun i =>
      (stdGaussian E) ⊗ₘ (D.child i).comap
        (fun p => (b.1,p)) measurable_prodMk_left) := by
  rw [pairedChildren,Kernel.comp_apply,Kernel.prod_apply,Kernel.id_apply,
    Kernel.const_apply,Measure.dirac_prod,bind_map_input _ _ _ measurable_prodMk_left]
  let k := (((Kernel.id : Kernel (((B × E) × (Fin m → E))) _) ×ₖ stateChildren D).map
    (fun z i => (z.1.2 i,z.2 i))).comap (fun p => (b,p)) measurable_prodMk_left
  change k ∘ₘ (Measure.pi fun _ : Fin m => stdGaussian E) = _
  apply (Measure.pi_eq fun s hs => ?_).symm
  rw [Measure.bind_apply (MeasurableSet.univ_pi hs) k.aemeasurable]
  have he : ∀ p, k p (Set.univ.pi s) = ∏ i,childPair D i (b,p i) (s i) := by
    intro p
    rw [Kernel.comap_apply,pairedChildren_before,Measure.pi_pi]
  simp_rw [he]
  rw [lintegral_pi_product (fun i p => childPair D i (b,p) (s i))
    (fun i => ((childPair D i).measurable_coe (hs i)).comp measurable_prodMk_left)]
  apply Finset.prod_congr rfl
  intro i _
  change (∫⁻ p,((childPair D i).comap (fun p => (b,p)) measurable_prodMk_left) p (s i) ∂stdGaussian E) = _
  rw [← Measure.bind_apply (hs i) (Kernel.aemeasurable _),childPair_average]

private theorem retained_average {B P Q : Type*} [MeasurableSpace B] [MeasurableSpace P] [MeasurableSpace Q]
    (μ : Measure B) [IsProbabilityMeasure μ] (ν : Measure P) [IsProbabilityMeasure ν]
    (k : Kernel (B × P) Q) [IsMarkovKernel k] :
    ((Kernel.deterministic Prod.fst measurable_fst) ×ₖ k) ∘ₘ (μ.prod ν) =
      μ ⊗ₘ (k ∘ₖ ((Kernel.id : Kernel B B) ×ₖ Kernel.const B ν)) := by
  apply Measure.ext_prod
  intro s t hs ht
  rw [Measure.bind_apply (hs.prod ht) (Kernel.aemeasurable _),Measure.compProd_apply_prod hs ht]
  simp_rw [Kernel.prod_apply_prod,Kernel.deterministic_apply]
  have hD : Measurable (fun b : B => (Measure.dirac b) s) :=
    (Measure.measurable_coe hs).comp Measure.measurable_dirac
  have hM : Measurable (fun a : B × P => (Measure.dirac a.1) s*k a t) :=
    (hD.comp measurable_fst).mul (k.measurable_coe ht)
  rw [lintegral_prod _ hM.aemeasurable]
  have he : ∀ b, (∫⁻ p, (Measure.dirac b) s*k (b,p) t ∂ν) =
      (Measure.dirac b) s*(k ∘ₖ ((Kernel.id : Kernel B B) ×ₖ Kernel.const B ν)) b t := by
    intro b
    have hm : Measurable (fun p : P => k (b,p) t) :=
      (k.measurable_coe ht).comp measurable_prodMk_left
    rw [lintegral_const_mul _ hm]
    congr 1
    rw [Kernel.comp_apply' _ _ _ ht,Kernel.lintegral_id_prod (k.measurable_coe ht)]
    rfl
  simp_rw [he]
  simp only [Measure.dirac_apply' _ hs]
  rw [← lintegral_indicator hs]
  apply lintegral_congr
  intro b
  by_cases hb : b ∈ s <;> simp [hb]



def splitState (z : ConditionalLaw.Host (B := B) (ι := Fin d) (m := m)) :
    (B × E) × (Fin m → E) :=
  (((BackwardParentLaw.splitState D z).1,(BackwardParentLaw.splitState D z).2.1),
    (BackwardParentLaw.splitState D z).2.2)

theorem splitState_measurable : Measurable (splitState D) :=
  ((BackwardParentLaw.measurable_splitState D).fst.prodMk
    (BackwardParentLaw.measurable_splitState D).snd.fst).prodMk
      (BackwardParentLaw.measurable_splitState D).snd.snd

theorem splitState_preserving (μ : Measure B) [IsProbabilityMeasure μ] :
    MeasurePreserving (splitState D) (LocalRootLawReferenceLift.hostLaw (d := d) (m := m) μ)
      ((μ.prod (stdGaussian E)).prod (RetainedLaw.noiseLaw (ι := Fin d) (m := m))) :=
  (measurePreserving_prodAssoc μ (stdGaussian E) (RetainedLaw.noiseLaw (ι := Fin d) (m := m))).symm.comp
    (BackwardParentLaw.splitState_preserving D μ)

theorem children_eq_comap : ConditionalLaw.childrenKernel D=
    (stateChildren D).comap (splitState D) (splitState_measurable D) := by
  ext z : 1
  rw [ConditionalLaw.childrenKernel,finiteProduct_apply m _ (fun _ => inferInstance),
    Kernel.comap_apply,stateChildren_apply]
  rfl

/-- Parent, reserve, original designated inputs and reference outputs jointly. -/
theorem split_paired_law (μ : Measure B) [IsProbabilityMeasure μ] :
    (LocalRootLawReferenceLift.referenceLaw D μ).map (fun z =>
      ((splitState D z.1).1,fun i => ((splitState D z.1).2 i,z.2 i))) =
        (μ.prod (stdGaussian E)) ⊗ₘ pairedChildren D := by
  have hp := compProd_comap_push (LocalRootLawReferenceLift.hostLaw (d := d) (m := m) μ)
    (stateChildren D) (splitState D) (splitState_measurable D)
  rw [← children_eq_comap,(splitState_preserving D μ).map_eq] at hp
  have hm : Measurable (fun z : ((B × E) × (Fin m → E)) × (Fin m → E) =>
      (z.1.1,fun i => (z.1.2 i,z.2 i))) := by fun_prop
  have h := congrArg (fun ν : Measure (((B × E) × (Fin m → E)) × (Fin m → E)) => ν.map
    (fun z => (z.1.1,fun i => (z.1.2 i,z.2 i)))) hp
  have hs : Measurable (fun z : ConditionalLaw.Execution (B := B) (ι := Fin d) (m := m) =>
      (splitState D z.1,z.2)) :=
    ((splitState_measurable D).comp measurable_fst).prodMk measurable_snd
  rw [Measure.map_map hm hs] at h
  refine h.trans ?_
  rw [Measure.compProd_eq_comp_prod,Measure.map_comp _ _ hm]
  have hk : ((Kernel.id ×ₖ stateChildren D).map
      (fun z : ((B × E) × (Fin m → E)) × (Fin m → E) => (z.1.1,fun i => (z.1.2 i,z.2 i)))) =
      (Kernel.deterministic Prod.fst measurable_fst) ×ₖ
        (((Kernel.id : Kernel ((B × E) × (Fin m → E)) _) ×ₖ stateChildren D).map
          (fun z i => (z.1.2 i,z.2 i))) := by
    ext z s hs
    rw [Kernel.map_apply _ hm,Kernel.prod_apply,Kernel.id_apply,
      Kernel.prod_apply,Kernel.deterministic_apply,Kernel.map_apply _ (by fun_prop),
      Kernel.prod_apply,Kernel.id_apply,Measure.dirac_prod,Measure.dirac_prod,
      Measure.map_map (by fun_prop) (by fun_prop),Measure.map_map (by fun_prop) (by fun_prop),
      Measure.map_map (by fun_prop) (by fun_prop)]
    rfl
  rw [hk]
  let : IsMarkovKernel (((Kernel.id : Kernel ((B × E) × (Fin m → E)) _) ×ₖ stateChildren D).map
      (fun z i => (z.1.2 i,z.2 i))) := Kernel.IsMarkovKernel.map _ (by fun_prop)
  exact retained_average (μ.prod (stdGaussian E)) (Measure.pi fun _ : Fin m => stdGaussian E)
    (((Kernel.id : Kernel ((B × E) × (Fin m → E)) _) ×ₖ stateChildren D).map
      (fun z i => (z.1.2 i,z.2 i)))

def originalInput (z : (B × E) × (Fin m → E × E)) : E :=
  (∑ i,-D.weight z.1.1 i • (z.2 i).1) +
    GaussianAssembly.reserve (fun i => -D.weight z.1.1 i) • z.1.2

def referenceOutput (z : (B × E) × (Fin m → E × E)) : E :=
  (∑ i,-D.weight z.1.1 i • (z.2 i).2) +
    GaussianAssembly.reserve (fun i => -D.weight z.1.1 i) • z.1.2

theorem originalInput_measurable : Measurable (originalInput D) := by
  have hw := D.measurable_weight
  unfold originalInput GaussianAssembly.reserve GaussianAssembly.mass
  fun_prop

theorem referenceOutput_measurable : Measurable (referenceOutput D) := by
  have hw := D.measurable_weight
  unfold referenceOutput GaussianAssembly.reserve GaussianAssembly.mass
  fun_prop

/-- Original dormant input is a graph over the paired split, not an
independent variable after conditioning on the designated inputs. -/
theorem originalInput_split (z : ConditionalLaw.Host (B := B) (ι := Fin d) (m := m))
    (q : Fin m → E) :
    originalInput D ((splitState D z).1,fun i => ((splitState D z).2 i,q i))=z.1.2 :=
  BackwardParentLaw.split_reconstruct D z

/-- Full retained original-input/root-output law for the constructed root. -/
theorem paired_retained_root (μ : Measure B) [IsProbabilityMeasure μ] :
    ((μ.prod (stdGaussian E)) ⊗ₘ pairedChildren D).map
      (fun z => ((z.1.1,originalInput D z),referenceOutput D z)) =
        (μ.prod (stdGaussian E)) ⊗ₘ ConditionalLaw.rootKernel D := by
  rw [← split_paired_law]
  have hm : Measurable (fun z => ((z.1.1,originalInput D z),referenceOutput D z)) :=
    (measurable_fst.fst.prodMk (originalInput_measurable D)).prodMk (referenceOutput_measurable D)
  have hs : Measurable (fun z : ConditionalLaw.Execution (B := B) (ι := Fin d) (m := m) =>
      ((splitState D z.1).1,fun i => ((splitState D z.1).2 i,z.2 i))) := by
    have hh := (splitState_measurable D).comp
      (measurable_fst : Measurable (Prod.fst : ConditionalLaw.Execution (B := B) (ι := Fin d) (m := m) → _))
    exact hh.fst.prodMk (Measurable.of_eval fun i =>
      ((measurable_pi_apply i).comp hh.snd).prodMk ((measurable_pi_apply i).comp measurable_snd))
  rw [Measure.map_map hm hs]
  have he : (fun z : ConditionalLaw.Execution (B := B) (ι := Fin d) (m := m) =>
      (((splitState D z.1).1.1,originalInput D ((splitState D z.1).1,fun i => ((splitState D z.1).2 i,z.2 i))),
        referenceOutput D ((splitState D z.1).1,fun i => ((splitState D z.1).2 i,z.2 i)))) =
      (fun z => (z.1.1,ConditionalLaw.output D z)) := by
    funext z
    rw [originalInput_split]
    rfl
  change (LocalRootLawReferenceLift.referenceLaw D μ).map (fun z =>
      (((splitState D z.1).1.1,originalInput D ((splitState D z.1).1,fun i => ((splitState D z.1).2 i,z.2 i))),
        referenceOutput D ((splitState D z.1).1,fun i => ((splitState D z.1).2 i,z.2 i))))=_
  rw [he]
  exact LocalRootLawReferenceLift.referenceLaw_retained D μ
end AcceleratedLogConcave.Root.ConditionalPairedLaw
