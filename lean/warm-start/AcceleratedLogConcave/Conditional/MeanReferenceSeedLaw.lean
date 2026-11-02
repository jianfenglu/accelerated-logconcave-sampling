import AcceleratedLogConcave.Conditional.RecursiveReferenceFamily
import AcceleratedLogConcave.Probability.MixedResidualAbsorption

/-! Exact full-seed retained reference law. The assembly reserve, initial
phase and designated child inputs remain jointly present. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace AcceleratedLogConcave.Conditional.MeanReferenceSeedLaw
open Numerics Numerics.MeanFlowLp MeanReferenceLayer
variable {d m : ℕ}
local notation "E" => Oracle.Point d
variable (D : Data (Fin d) m) (C : Children D)
local instance child_markov (i : Fin m) : IsMarkovKernel (C.kernel i) := C.markov i

/-- Average the actual independent designated inputs, retaining each together
with its returned reference. -/
def pairedChildren : Kernel (BaseState (Fin d)) (Fin m → E × E) :=
  (((Kernel.id : Kernel (SplitState (Fin d) m) _) ×ₖ stateChildren D C).map
    (fun z i => (z.1.2 i,z.2 i))) ∘ₖ
      ((Kernel.id : Kernel (BaseState (Fin d)) _) ×ₖ
        Kernel.const _ (Measure.pi fun _ : Fin m => stdGaussian E))
instance pairedChildren_markov : IsMarkovKernel (pairedChildren D C) := by
  let : IsMarkovKernel (((Kernel.id : Kernel (SplitState (Fin d) m) _) ×ₖ stateChildren D C).map
      (fun z i => (z.1.2 i,z.2 i))) := Kernel.IsMarkovKernel.map _ (by fun_prop)
  unfold pairedChildren
  infer_instance

private def childPair (i : Fin m) : Kernel (BaseState (Fin d) × E) (E × E) :=
  (Kernel.deterministic Prod.snd measurable_snd) ×ₖ
    (C.kernel i).comap (fun z => (stateCenter D i z.1,z.2))
      (((continuous_stateCenter D i).measurable.comp measurable_fst).prodMk measurable_snd)
private instance childPair_markov (i : Fin m) : IsMarkovKernel (childPair D C i) := by
  let := C.markov i
  unfold childPair
  infer_instance

private theorem childPair_average (i : Fin m) (b : BaseState (Fin d)) :
    (childPair D C i).comap (fun p => (b,p)) measurable_prodMk_left ∘ₘ stdGaussian E =
      (stdGaussian E) ⊗ₘ (C.kernel i).comap (fun p => (stateCenter D i b,p)) measurable_prodMk_left := by
  rw [Measure.compProd_eq_comp_prod]
  congr 1
  ext p s hs
  rw [Kernel.comap_apply,childPair,Kernel.prod_apply,Kernel.deterministic_apply,
    Kernel.prod_apply,Kernel.id_apply]
  rfl

private theorem pairedChildren_before (z : SplitState (Fin d) m) :
    (((Kernel.id : Kernel (SplitState (Fin d) m) _) ×ₖ stateChildren D C).map
      (fun z i => (z.1.2 i,z.2 i))) z =
        Measure.pi (fun i => childPair D C i (z.1,z.2 i)) := by
  rw [Kernel.map_apply _ (by fun_prop),Kernel.prod_apply,Kernel.id_apply,
    Measure.dirac_prod,Measure.map_map (by fun_prop) (by fun_prop),stateChildren_apply]
  have h := Measure.pi_map_pi (μ := fun i => C.kernel i (stateCenter D i z.1,z.2 i))
    (fun i => (show Measurable (Prod.mk (z.2 i) : E → E × E) from measurable_prodMk_left).aemeasurable)
  change (Measure.pi fun i => C.kernel i (stateCenter D i z.1,z.2 i)).map
    (fun q i => (z.2 i,q i)) = _
  rw [h]
  congr 1
  funext i
  rw [childPair,Kernel.prod_apply,Kernel.deterministic_apply,Measure.dirac_prod]
  rfl

/-- Full product of retained designated-input/reference pairs. -/
theorem pairedChildren_apply (b : BaseState (Fin d)) :
    pairedChildren D C b = Measure.pi (fun i =>
      (stdGaussian E) ⊗ₘ (C.kernel i).comap
        (fun p => (stateCenter D i b,p)) measurable_prodMk_left) := by
  rw [pairedChildren,Kernel.comp_apply,Kernel.prod_apply,Kernel.id_apply,
    Kernel.const_apply,Measure.dirac_prod,bind_map_input _ _ _ measurable_prodMk_left]
  let k := (((Kernel.id : Kernel (SplitState (Fin d) m) _) ×ₖ stateChildren D C).map
    (fun z i => (z.1.2 i,z.2 i))).comap (fun p => (b,p)) measurable_prodMk_left
  change k ∘ₘ (Measure.pi fun _ : Fin m => stdGaussian E) = _
  apply (Measure.pi_eq fun s hs => ?_).symm
  rw [Measure.bind_apply (MeasurableSet.univ_pi hs) k.aemeasurable]
  have he : ∀ p, k p (Set.univ.pi s) = ∏ i,childPair D C i (b,p i) (s i) := by
    intro p
    rw [Kernel.comap_apply,pairedChildren_before,Measure.pi_pi]
  simp_rw [he]
  rw [lintegral_pi_product (fun i p => childPair D C i (b,p) (s i))
    (fun i => ((childPair D C i).measurable_coe (hs i)).comp measurable_prodMk_left)]
  apply Finset.prod_congr rfl
  intro i _
  change (∫⁻ p,((childPair D C i).comap (fun p => (b,p)) measurable_prodMk_left) p (s i) ∂stdGaussian E) = _
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

/-- The exact designated inputs and returned references of the original
parent reference family, with its entire initial phase and reserve retained. -/
theorem split_paired_law :
    (averagedJoint D C).map (fun z =>
      ((splitState D C z.1).1,fun i => ((splitState D C z.1).2 i,z.2 i))) =
        (MeanReferenceLayer.baseLaw D) ⊗ₘ pairedChildren D C := by
  have hp := compProd_comap_push ((stdGaussian E).prod (freshLaw D))
    (stateChildren D C) (splitState D C) (measurable_splitState D C)
  rw [← children_eq_state_comap,← averagedJoint_eq,splitState_law] at hp
  have hm : Measurable (fun z : SplitState (Fin d) m × (Fin m → E) =>
      (z.1.1,fun i => (z.1.2 i,z.2 i))) := by fun_prop
  have h := congrArg (fun ν : Measure (SplitState (Fin d) m × (Fin m → E)) => ν.map
    (fun z => (z.1.1,fun i => (z.1.2 i,z.2 i)))) hp
  have hs : Measurable (fun z : Host (Fin d) m × (Fin m → E) => (splitState D C z.1,z.2)) :=
    ((measurable_splitState D C).comp measurable_fst).prodMk measurable_snd
  rw [Measure.map_map hm hs] at h
  refine h.trans ?_
  rw [Measure.compProd_eq_comp_prod,Measure.map_comp _ _ hm]
  have hk : ((Kernel.id ×ₖ stateChildren D C).map
      (fun z : SplitState (Fin d) m × (Fin m → E) => (z.1.1,fun i => (z.1.2 i,z.2 i)))) =
      (Kernel.deterministic Prod.fst measurable_fst) ×ₖ
        (((Kernel.id : Kernel (SplitState (Fin d) m) _) ×ₖ stateChildren D C).map
          (fun z i => (z.1.2 i,z.2 i))) := by
    ext z s hs
    rw [Kernel.map_apply _ hm,Kernel.prod_apply,Kernel.id_apply,
      Kernel.prod_apply,Kernel.deterministic_apply,Kernel.map_apply _ (by fun_prop),
      Kernel.prod_apply,Kernel.id_apply,Measure.dirac_prod,Measure.dirac_prod,
      Measure.map_map (by fun_prop) (by fun_prop),Measure.map_map (by fun_prop) (by fun_prop),
      Measure.map_map (by fun_prop) (by fun_prop)]
    rfl
  rw [hk]
  let : IsMarkovKernel (((Kernel.id : Kernel (SplitState (Fin d) m) _) ×ₖ stateChildren D C).map
      (fun z i => (z.1.2 i,z.2 i))) := Kernel.IsMarkovKernel.map _ (by fun_prop)
  exact retained_average (MeanReferenceLayer.baseLaw D) (Measure.pi fun _ : Fin m => stdGaussian E)
    (((Kernel.id : Kernel (SplitState (Fin d) m) _) ×ₖ stateChildren D C).map
      (fun z i => (z.1.2 i,z.2 i)))

def originalInput (z : BaseState (Fin d) × (Fin m → E × E)) : E :=
  (∑ i : Option (Fin m), coefficients D C i •
    (i.elim z.1.1.2 (fun j => (z.2 j).1))) +
      GaussianAssembly.reserve (coefficients D C) • z.1.2

def referenceOutput (z : BaseState (Fin d) × (Fin m → E × E)) : E :=
  D.sigma⁻¹ • ((D.sigma/2) •
    (CenteringFlowLp.phase (kernelData D) (D.sigma/2) (half_pos D.hsigma) 1
      (WithLp.toLp 2 z.1.1)).snd +
        (∑ i,(GaussLegendre.weight m i*C.scale i) • (z.2 i).2) + C.beta • z.1.2)

theorem originalInput_measurable : Measurable (originalInput D C) := by
  unfold originalInput
  have hopt : ∀ i : Option (Fin m), Measurable (fun z : BaseState (Fin d) × (Fin m → E × E) =>
      i.elim z.1.1.2 (fun j => (z.2 j).1)) := by
    intro i
    cases i <;> simp only [Option.elim_none,Option.elim_some] <;> fun_prop
  fun_prop

theorem referenceOutput_measurable : Measurable (referenceOutput D C) := by
  have hphase := (CenteringFlowLp.continuous_phase (kernelData D) (D.sigma/2) (half_pos D.hsigma))
  unfold referenceOutput
  have hc : Measurable (fun z : BaseState (Fin d) × (Fin m → E × E) =>
      (CenteringFlowLp.phase (kernelData D) (D.sigma/2) (half_pos D.hsigma) 1
        (WithLp.toLp 2 z.1.1)).snd) :=
    ((WithLp.prod_continuous_ofLp 2 E E).snd.comp (hphase.comp
      (continuous_const.prodMk ((WithLp.prod_continuous_toLp 2 E E).comp continuous_fst.fst)))).measurable
  fun_prop

private theorem originalInput_split (h : Host (Fin d) m) (p : Fin m → E) :
    originalInput D C ((splitState D C h).1,fun i => ((splitState D C h).2 i,p i))=h.1 := by
  unfold originalInput
  have he : ∀ i : Option (Fin m), i.elim ((splitState D C h).1.1.2)
      (fun j => ((splitState D C h).2 j,p j).1) = active D C h i := by
    intro i
    cases i <;> rfl
  simp_rw [he]
  exact (GaussianAssembly.residual_reconstruction (budget_admissible D C) h.1 h.2.2).symm

/-- Exact parent retained law in the genuine initial-phase/reserve/child-pair
coordinates, before any source tape coupling is introduced. -/
theorem retained_law :
    ((MeanReferenceLayer.baseLaw D) ⊗ₘ pairedChildren D C).map
      (fun z => (originalInput D C z,referenceOutput D C z)) =
        (stdGaussian E) ⊗ₘ parentKernel D C := by
  rw [← split_paired_law]
  have hm : Measurable (fun z => (originalInput D C z,referenceOutput D C z)) :=
    (originalInput_measurable D C).prodMk (referenceOutput_measurable D C)
  have hs : Measurable (fun z : Host (Fin d) m × (Fin m → E) =>
      ((splitState D C z.1).1,fun i => ((splitState D C z.1).2 i,z.2 i))) := by
    have hh := (measurable_splitState D C).comp
      (measurable_fst : Measurable (Prod.fst : Host (Fin d) m × (Fin m → E) → _))
    exact hh.fst.prodMk (Measurable.of_eval fun i =>
      ((measurable_pi_apply i).comp hh.snd).prodMk ((measurable_pi_apply i).comp measurable_snd))
  rw [Measure.map_map hm hs]
  have he : (fun z : Host (Fin d) m × (Fin m → E) =>
      (originalInput D C ((splitState D C z.1).1,fun i => ((splitState D C z.1).2 i,z.2 i)),
        referenceOutput D C ((splitState D C z.1).1,fun i => ((splitState D C z.1).2 i,z.2 i)))) =
      (fun z => (z.1.1,recombine D C z.1 z.2)) := by
    apply funext
    intro z
    exact Prod.ext (originalInput_split D C z.1 z.2) rfl
  change (averagedJoint D C).map (fun z =>
    (originalInput D C ((splitState D C z.1).1,fun i => ((splitState D C z.1).2 i,z.2 i)),
      referenceOutput D C ((splitState D C z.1).1,fun i => ((splitState D C z.1).2 i,z.2 i))))=_
  rw [he]
  exact retained_joint D C

/-- The genuine initial phase and reserve in a full mean seed. The original
conditional-flow seeds are present in the source measure and merely projected. -/
def seedBase (z : E × Seed D) : BaseState (Fin d) := (z.2.1.ofLp,z.1)

theorem seedBase_measurable : Measurable (seedBase D) :=
  (((WithLp.prod_continuous_ofLp 2 E E).measurable.comp measurable_snd.fst).prodMk measurable_fst)

theorem seedBase_preserving : MeasurePreserving (seedBase D)
    ((stdGaussian E).prod (seedMeasure D)) (MeanReferenceLayer.baseLaw D) := by
  have he : MeasurePreserving (MeasurableEquiv.toLp 2 (E × E))
      ((MeanBenchmarkCoupling.positionLaw D).prod (stdGaussian E))
      (KernelFlowLp.seedMeasure (kernelData D)) :=
    ⟨(MeasurableEquiv.toLp 2 (E × E)).measurable,rfl⟩
  have hphase := he.symm.comp (phase_projection_preserving D)
  exact (hphase.prod (MeasurePreserving.id (stdGaussian E))).comp
    (Measure.measurePreserving_swap (μ := stdGaussian E) (ν := seedMeasure D))

/-- The reserve and full original phase/flow seed feed the actual child-pair
kernel; the source flow seed array is not Gaussianized or replaced. -/
def seedPairs : Kernel (E × Seed D) (Fin m → E × E) :=
  (pairedChildren D C).comap (seedBase D) (seedBase_measurable D)
instance seedPairs_markov : IsMarkovKernel (seedPairs D C) := by
  unfold seedPairs
  infer_instance

/-- Exact retained output law in full mean-seed coordinates. -/
theorem seed_retained_law :
    (((stdGaussian E).prod (seedMeasure D)) ⊗ₘ seedPairs D C).map
      (fun z => (originalInput D C (seedBase D z.1,z.2),
        referenceOutput D C (seedBase D z.1,z.2))) =
          (stdGaussian E) ⊗ₘ parentKernel D C := by
  have hp := compProd_comap_push ((stdGaussian E).prod (seedMeasure D))
    (pairedChildren D C) (seedBase D) (seedBase_measurable D)
  rw [(seedBase_preserving D).map_eq] at hp
  have hm : Measurable (fun z => (originalInput D C z,referenceOutput D C z)) :=
    (originalInput_measurable D C).prodMk (referenceOutput_measurable D C)
  have hg : Measurable (fun z : (E × Seed D) × (Fin m → E × E) => (seedBase D z.1,z.2)) :=
    ((seedBase_measurable D).comp measurable_fst).prodMk measurable_snd
  have h := congrArg (fun ν : Measure (BaseState (Fin d) × (Fin m → E × E)) =>
    ν.map (fun z => (originalInput D C z,referenceOutput D C z))) hp
  rw [Measure.map_map hm hg,retained_law] at h
  simpa only [seedPairs,Function.comp_def] using h

end AcceleratedLogConcave.Conditional.MeanReferenceSeedLaw
