import AcceleratedLogConcave.Root.ConditionalLaw
import AcceleratedLogConcave.Kinetic.ReferenceFlow

/-!
# Exact backward parent centers and retained dormant split

Only the exact coupled parent state is used as a conditioning parameter. The
original entering momentum is retained as a graph coordinate, NOT added to the
sigma-algebra on which Gaussian product structure is asserted. No statement
about approximate/executable centers or transformed compiler tapes is made.
-/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open AcceleratedLogConcave.Conditional
open AcceleratedLogConcave.Kinetic AcceleratedLogConcave.Analysis.Poisson
open scoped ENNReal
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace AcceleratedLogConcave.Root.BackwardParentLaw
variable {ι : Type*} [Fintype ι] {m : ℕ}
local notation "E" => EuclideanSpace ℝ ι

section Parent
variable {a b : ℝ} (F : AcceleratedLogConcave.Analysis.Poisson.ReferencePoissonFamily (EuclideanSpace ℝ ι) a b) (ell : ℝ)

def parentLaw (t : ℝ) : Measure (E × E) := (F.law t).prod (stdGaussian E)
instance parentLaw_probability (t : ℝ) : IsProbabilityMeasure (parentLaw F t) := by
  unfold parentLaw
  infer_instance

/-- Recover the actual earlier pair from the terminal exact pair. -/
def backwardPair (t u : Icc a b) (z : E × E) : E × E :=
  referenceCoupledPairFlow F ell u ((referenceCoupledPairFlow F ell t).symm z)

/-- Actual earlier physical center, not an independently resampled center. -/
def backwardCenter (t u : Icc a b) (z : E × E) : E :=
  (backwardPair F ell t u z).1

lemma measurable_backwardPair (t u : Icc a b) : Measurable (backwardPair F ell t u) :=
  (referenceCoupledPairFlow F ell u).measurable.comp
    (referenceCoupledPairFlow F ell t).symm.measurable
lemma measurable_backwardCenter (t u : Icc a b) : Measurable (backwardCenter F ell t u) :=
  (measurable_backwardPair F ell t u).fst

/-- Every backward node belongs to the SAME forward trajectory. -/
theorem backwardPair_forward (t u : Icc a b) (z : E × E) :
    backwardPair F ell t u (referenceCoupledPairFlow F ell t z) =
      referenceCoupledPairFlow F ell u z := by
  simp only [backwardPair, Homeomorph.symm_apply_apply]

/-- True earlier joint law; no fresh child momenta occur in this transport. -/
theorem backwardPair_preserving (t u : Icc a b) :
    MeasurePreserving (backwardPair F ell t u) (parentLaw F t) (parentLaw F u) :=
  (referenceCoupledPairFlow_measurePreserving F ell u).comp
    ((referenceCoupledPairFlow_measurePreserving F ell t).symm
      (referenceCoupledPairFlow F ell t).toMeasurableEquiv)

/-- The exact parent flow leaves dormant input and every raw split seed unchanged. -/
def hostFlow (t : Icc a b) (z : ConditionalLaw.Host (B := E × E) (ι := ι) (m := m)) :=
  ((referenceCoupledPairFlow F ell t z.1.1, z.1.2), z.2)

lemma measurable_hostFlow (t : Icc a b) :
    Measurable (hostFlow (m := m) F ell t) :=
  (((referenceCoupledPairFlow F ell t).measurable.comp measurable_fst.fst).prodMk
    measurable_fst.snd).prodMk measurable_snd

/-- Independence from dormant/split Gaussian coordinates does not require a stationary
parent. In particular the parent input may have law δ_x × γ at a fixed source center x. -/
theorem hostFlow_preserving_arbitrary (t : Icc a b) (μ : Measure (E × E)) [IsProbabilityMeasure μ] :
    MeasurePreserving (hostFlow (m := m) F ell t)
      ((μ.prod (stdGaussian E)).prod (RetainedLaw.noiseLaw (m := m)))
      (((μ.map (referenceCoupledPairFlow F ell t)).prod (stdGaussian E)).prod
        (RetainedLaw.noiseLaw (m := m))) := by
  have h : MeasurePreserving (referenceCoupledPairFlow F ell t) μ
      (μ.map (referenceCoupledPairFlow F ell t)) :=
    ⟨(referenceCoupledPairFlow F ell t).measurable, rfl⟩
  exact (h.prod (MeasurePreserving.id (stdGaussian E))).prod (MeasurePreserving.id _)

theorem hostFlow_preserving (t : Icc a b) :
    MeasurePreserving (hostFlow (m := m) F ell t)
      (((parentLaw F a).prod (stdGaussian E)).prod (RetainedLaw.noiseLaw (m := m)))
      (((parentLaw F t).prod (stdGaussian E)).prod (RetainedLaw.noiseLaw (m := m))) :=
  ((referenceCoupledPairFlow_measurePreserving F ell t).prod
    (MeasurePreserving.id (stdGaussian E))).prod (MeasurePreserving.id _)

/-- The original entering momentum as a graph coordinate over the final exact parent
and old dormant input. Conditioning on this graph coordinate is NOT permitted when
claiming independent standard child inputs. -/
def entering (s n : ℝ) (t : Icc a b) (z : (E × E) × E) : E :=
  s • ((referenceCoupledPairFlow F ell t).symm z.1).2 + n • z.2

lemma measurable_entering (s n : ℝ) (t : Icc a b) : Measurable (entering F ell s n t) := by
  unfold entering
  fun_prop

theorem entering_forward (s n : ℝ) (t : Icc a b) (z : (E × E) × E) :
    entering F ell s n t (referenceCoupledPairFlow F ell t z.1, z.2) =
      s • z.1.2 + n • z.2 := by
  simp only [entering, Homeomorph.symm_apply_apply]
/-- Adding original P to the conditioning field fixes H0 exactly, rather than
leaving a standard Gaussian conditional distribution. -/
theorem entering_determines_dormant (s n : ℝ) (hn : n ≠ 0) (t : Icc a b)
    (z : (E × E) × E) :
    n⁻¹ • (entering F ell s n t z - s • ((referenceCoupledPairFlow F ell t).symm z.1).2) = z.2 := by
  simp only [entering, add_sub_cancel_left, inv_smul_smul₀ hn]
end Parent

section Split
variable {B : Type*} [MeasurableSpace B]

abbrev SplitState := B × (E × (Fin m → E))
def splitState (d : ConditionalLaw.Data B ι m)
    (z : ConditionalLaw.Host (B := B) (ι := ι) (m := m)) : SplitState (B := B) (ι := ι) (m := m) :=
  (z.1.1, RetainedLaw.split (ConditionalLaw.atParent d z.1.1) (z.1.2, z.2))
lemma measurable_splitState (d : ConditionalLaw.Data B ι m) : Measurable (splitState d) :=
  measurable_fst.fst.prodMk ((ConditionalLaw.measurable_reserve d).prodMk
    (ConditionalLaw.measurable_active d))

/-- Explicit sigma-algebra statement: the exact parent remains independent of the
reserve and active child array, even with measurable parent-dependent weights. -/
theorem splitState_preserving (d : ConditionalLaw.Data B ι m)
    (μ : Measure B) [IsProbabilityMeasure μ] :
    MeasurePreserving (splitState d)
      ((μ.prod (stdGaussian E)).prod (RetainedLaw.noiseLaw (ι := ι) (m := m)))
      (μ.prod ((stdGaussian E).prod (RetainedLaw.noiseLaw (ι := ι) (m := m)))) := by
  let f : B → RetainedLaw.Host (ι := ι) (m := m) → E × (Fin m → E) :=
    fun b z => RetainedLaw.split (ConditionalLaw.atParent d b) z
  have hm : Measurable (Function.uncurry f) := by
    have h := (measurable_splitState d).snd.comp
      (measurable_fst.prodMk measurable_snd.fst |>.prodMk measurable_snd.snd)
    exact h
  have hp := (MeasurePreserving.id μ).skew_product hm
    (Filter.Eventually.of_forall fun b => (RetainedLaw.split_preserving (ConditionalLaw.atParent d b)).map_eq)
  exact hp.comp (measurePreserving_prodAssoc μ (stdGaussian E) (RetainedLaw.noiseLaw (m := m)))

/-- Children at their own designated active inputs, with the exact parent and reserve retained. -/
def splitChildren (d : ConditionalLaw.Data B ι m) :
    Kernel (SplitState (B := B) (ι := ι) (m := m)) (Fin m → E) :=
  MeanReferenceLayer.finiteProduct m (fun i => (d.child i).comap
    (fun z => (z.1, z.2.2 i))
    (measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd.snd)))
instance splitChildren_markov (d : ConditionalLaw.Data B ι m) : IsMarkovKernel (splitChildren d) := by
  let : ∀ i, IsMarkovKernel (d.child i) := d.markov
  exact MeanReferenceLayer.finiteProduct_markov m _ (fun _ => inferInstance)

lemma childrenKernel_eq_comap (d : ConditionalLaw.Data B ι m) :
    ConditionalLaw.childrenKernel d = (splitChildren d).comap (splitState d) (measurable_splitState d) := by
  let : ∀ i, IsMarkovKernel (d.child i) := d.markov
  ext z : 1
  rw [ConditionalLaw.childrenKernel, Kernel.comap_apply, splitChildren,
    MeanReferenceLayer.finiteProduct_apply m _ (fun _ => inferInstance),
    MeanReferenceLayer.finiteProduct_apply m _ (fun _ => inferInstance)]
  rfl

/-- Exact retained joint law, not merely a returned-output marginal. It retains the
parent, reserve, designated inputs and corresponding reference child outputs. -/
theorem split_child_joint (d : ConditionalLaw.Data B ι m)
    (μ : Measure B) [IsProbabilityMeasure μ] :
    (((μ.prod (stdGaussian E)).prod (RetainedLaw.noiseLaw (ι := ι) (m := m))) ⊗ₘ
      ConditionalLaw.childrenKernel d).map (fun z => (splitState d z.1, z.2)) =
    (μ.prod ((stdGaussian E).prod (RetainedLaw.noiseLaw (ι := ι) (m := m)))) ⊗ₘ splitChildren d := by
  rw [childrenKernel_eq_comap]
  rw [MeanReferenceLayer.compProd_comap_push, (splitState_preserving d μ).map_eq]

/-- Same H0 is reconstructed from retained reserve and active child inputs. -/
theorem split_reconstruct (d : ConditionalLaw.Data B ι m)
    (z : ConditionalLaw.Host (B := B) (ι := ι) (m := m)) :
    RetainedLaw.recombine (ConditionalLaw.atParent d (splitState d z).1) (splitState d z).2 =
      z.1.2 :=
  RetainedLaw.reconstruct (ConditionalLaw.atParent d z.1.1) (z.1.2,z.2)
end Split

section ExactParent
variable {a b : ℝ} (F : AcceleratedLogConcave.Analysis.Poisson.ReferencePoissonFamily (EuclideanSpace ℝ ι) a b) (ell : ℝ)
  (d : ConditionalLaw.Data ((EuclideanSpace ℝ ι) × (EuclideanSpace ℝ ι)) ι m)

/-- Product law is valid at the actual terminal exact parent, because its transport
reads neither H0 nor the split seed. No such assertion is made for executable centers. -/
theorem backward_parent_split_law (t : Icc a b) :
    MeasurePreserving (splitState d ∘ hostFlow F ell t)
      (((parentLaw F a).prod (stdGaussian E)).prod (RetainedLaw.noiseLaw (m := m)))
      ((parentLaw F t).prod ((stdGaussian E).prod (RetainedLaw.noiseLaw (m := m)))) :=
  (splitState_preserving d (parentLaw F t)).comp (hostFlow_preserving F ell t)

/-- The same exact split independence for arbitrary initial parent law, including fixed x.
Only at stationary input is the terminal parent law identified with π_Ut × γ. -/
theorem backward_parent_split_law_arbitrary (t : Icc a b)
    (μ : Measure (E × E)) [IsProbabilityMeasure μ] :
    MeasurePreserving (splitState d ∘ hostFlow F ell t)
      ((μ.prod (stdGaussian E)).prod (RetainedLaw.noiseLaw (m := m)))
      ((μ.map (referenceCoupledPairFlow F ell t)).prod
        ((stdGaussian E).prod (RetainedLaw.noiseLaw (m := m)))) :=
  (splitState_preserving d (μ.map (referenceCoupledPairFlow F ell t))).comp
    (hostFlow_preserving_arbitrary F ell t μ)

/-- Attaching the original P uses the inverse parent trajectory and same-input
Gaussian reconstruction. There is no fresh replacement P. -/
def enteringSplit (s n : ℝ) (t : Icc a b)
    (z : SplitState (B := E × E) (ι := ι) (m := m)) : E :=
  entering F ell s n t (z.1, RetainedLaw.recombine (ConditionalLaw.atParent d z.1) z.2)

lemma measurable_enteringSplit (s n : ℝ) (t : Icc a b) :
    Measurable (enteringSplit F ell d s n t) := by
  have hw := d.measurable_weight
  apply (measurable_entering F ell s n t).comp
  apply measurable_fst.prodMk
  simp only [RetainedLaw.recombine, RetainedLaw.beta, GaussianAssembly.reserve,
    GaussianAssembly.mass, RetainedLaw.coefficient, ConditionalLaw.atParent]
  fun_prop

theorem enteringSplit_reconstruct (s n : ℝ) (t : Icc a b)
    (z : ConditionalLaw.Host (B := E × E) (ι := ι) (m := m)) :
    enteringSplit F ell d s n t (splitState d (hostFlow F ell t z)) =
      s • z.1.1.2 + n • z.1.2 := by
  unfold enteringSplit
  rw [split_reconstruct]
  exact entering_forward F ell s n t z.1

/-- The real earlier centers can instantiate the child family by a measurable
comap. Its only Gaussian input is the original designated child momentum. -/
def childAtBackwardCenter (t u : Icc a b) (k : Kernel (E × E) E) :
    Kernel ((E × E) × E) E :=
  k.comap (fun z => (backwardCenter F ell t u z.1, z.2))
    (((measurable_backwardCenter F ell t u).comp measurable_fst).prodMk measurable_snd)

lemma childAtBackwardCenter_section (t u : Icc a b) (k : Kernel (E × E) E) (z : E × E) :
    (childAtBackwardCenter F ell t u k).comap (fun p => (z,p)) measurable_prodMk_left =
      k.comap (fun p => (backwardCenter F ell t u z,p)) measurable_prodMk_left := by
  ext p : 1
  rfl

/-- Only the lower-level exact child invariance is supplied. Root invariance is not a premise. -/
theorem childAtBackwardCenter_invariant (t u : Icc a b) (k : Kernel (E × E) E)
    (hk : ∀ center, k.comap (fun p => (center,p)) measurable_prodMk_left ∘ₘ stdGaussian E = stdGaussian E)
    (z : E × E) :
    (childAtBackwardCenter F ell t u k).comap (fun p => (z,p)) measurable_prodMk_left ∘ₘ
      stdGaussian E = stdGaussian E := by
  rw [childAtBackwardCenter_section]
  exact hk _
/-- The source-side exact child kernel evaluates after the actual parent flow.
This is a child reference update, NOT an executable recursive compiler. -/
def flowedChildren (t : Icc a b) :
    Kernel (ConditionalLaw.Host (B := E × E) (ι := ι) (m := m)) (Fin m → E) :=
  (ConditionalLaw.childrenKernel d).comap (hostFlow F ell t) (measurable_hostFlow F ell t)
instance flowedChildren_markov (t : Icc a b) : IsMarkovKernel (flowedChildren F ell d t) := by
  unfold flowedChildren
  infer_instance

/-- Complete retained exact-reference law from the initial parent and original dormant
input to the final parent, reserve, designated inputs, and child outputs. -/
theorem backward_parent_child_joint (t : Icc a b) :
    ((((parentLaw F a).prod (stdGaussian E)).prod (RetainedLaw.noiseLaw (ι := ι) (m := m))) ⊗ₘ
      flowedChildren F ell d t).map
        (fun z => (splitState d (hostFlow F ell t z.1), z.2)) =
    ((parentLaw F t).prod ((stdGaussian E).prod (RetainedLaw.noiseLaw (ι := ι) (m := m)))) ⊗ₘ
      splitChildren d := by
  have he : flowedChildren F ell d t =
      (splitChildren d).comap (splitState d ∘ hostFlow F ell t)
        ((measurable_splitState d).comp (measurable_hostFlow F ell t)) := by
    rw [flowedChildren, childrenKernel_eq_comap]
    ext z : 1
    rfl
  rw [he]
  have h := MeanReferenceLayer.compProd_comap_push
    (((parentLaw F a).prod (stdGaussian E)).prod (RetainedLaw.noiseLaw (ι := ι) (m := m)))
    (splitChildren d) (splitState d ∘ hostFlow F ell t)
    ((measurable_splitState d).comp (measurable_hostFlow F ell t))
  rw [(backward_parent_split_law F ell d t).map_eq] at h
  exact h

/-- Original P can be retained in the exact child-joint equality, by a deterministic
 graph map. This does NOT assert product structure after conditioning on P. -/
theorem backward_parent_child_joint_retaining_input (s n : ℝ) (t : Icc a b) :
    ((((parentLaw F a).prod (stdGaussian E)).prod (RetainedLaw.noiseLaw (ι := ι) (m := m))) ⊗ₘ
      flowedChildren F ell d t).map
        (fun z => (s • z.1.1.1.2 + n • z.1.1.2,
          (splitState d (hostFlow F ell t z.1), z.2))) =
    (((parentLaw F t).prod ((stdGaussian E).prod (RetainedLaw.noiseLaw (ι := ι) (m := m)))) ⊗ₘ
      splitChildren d).map (fun z => (enteringSplit F ell d s n t z.1, z)) := by
  have hg : Measurable (fun z : SplitState (B := E × E) (ι := ι) (m := m) × (Fin m → E) =>
      (enteringSplit F ell d s n t z.1, z)) :=
    ((measurable_enteringSplit F ell d s n t).comp measurable_fst).prodMk measurable_id
  have hf : Measurable (fun z : ConditionalLaw.Host (B := E × E) (ι := ι) (m := m) × (Fin m → E) =>
      (splitState d (hostFlow F ell t z.1),z.2)) :=
    ((measurable_splitState d).comp ((measurable_hostFlow F ell t).comp measurable_fst)).prodMk measurable_snd
  have h := congrArg (fun μ => μ.map (fun z => (enteringSplit F ell d s n t z.1,z)))
    (backward_parent_child_joint F ell d t)
  rw [Measure.map_map hg hf] at h
  rw [← h]
  congr 1
  funext z
  simp only [Function.comp_apply, enteringSplit_reconstruct]
end ExactParent
section Constructor
variable {a b : ℝ}
  (F : AcceleratedLogConcave.Analysis.Poisson.ReferencePoissonFamily (EuclideanSpace ℝ ι) a b)
  (ell : ℝ)

/-- Construct the parent-indexed exact child data at genuine backward centers.
`child i` is the prescribed recursive child, parameterized by PHYSICAL center;
its radius, width and precision tree are fixed in that kernel. Rescaling to the
manuscript mean coordinates belongs in that lower-level kernel's definition.
This constructor does not identify any executable child with it. -/
def backwardData (t : Icc a b) (node : Fin m → Icc a b) (weight : Fin m → ℝ)
    (ha : GaussianAssembly.mass (fun i => -weight i) < 1)
    (child : Fin m → Kernel (E × E) E) (hm : ∀ i, IsMarkovKernel (child i))
    (hi : ∀ i center, (child i).comap (fun p => (center,p)) measurable_prodMk_left ∘ₘ
      stdGaussian E = stdGaussian E) : ConditionalLaw.Data (E × E) ι m where
  weight _ := weight
  measurable_weight := measurable_const
  admissible _ := ha
  child i := childAtBackwardCenter F ell t (node i) (child i)
  markov i := by let := hm i; unfold childAtBackwardCenter; infer_instance
  invariant i z := childAtBackwardCenter_invariant F ell t (node i) (child i) (hi i) z

/-- The routed input is exactly the supplied designated p, at the same backward node. -/
theorem backwardData_child_apply (t : Icc a b) (node : Fin m → Icc a b) (weight : Fin m → ℝ)
    (ha : GaussianAssembly.mass (fun i => -weight i) < 1)
    (child : Fin m → Kernel (E × E) E) (hm : ∀ i, IsMarkovKernel (child i))
    (hi : ∀ i center, (child i).comap (fun p => (center,p)) measurable_prodMk_left ∘ₘ
      stdGaussian E = stdGaussian E) (i : Fin m) (z : E × E) (p : E) :
    (backwardData F ell t node weight ha child hm hi).child i (z,p) =
      child i (backwardCenter F ell t (node i) z,p) := rfl

/-- Conditional root invariance at exact backward centers follows from genuine
lower-level child stationarity, not from a supplied root hK or hW. -/
theorem rootAtBackwardCenters_conditionallyInvariant
    (t : Icc a b) (node : Fin m → Icc a b) (weight : Fin m → ℝ)
    (ha : GaussianAssembly.mass (fun i => -weight i) < 1)
    (child : Fin m → Kernel (E × E) E) (hm : ∀ i, IsMarkovKernel (child i))
    (hi : ∀ i center, (child i).comap (fun p => (center,p)) measurable_prodMk_left ∘ₘ
      stdGaussian E = stdGaussian E) :
    ∀ z s, MeasurableSet s →
      (∫⁻ h, ConditionalLaw.rootKernel (backwardData F ell t node weight ha child hm hi) (z,h) s
        ∂stdGaussian E) = stdGaussian E s :=
  ConditionalLaw.rootKernel_conditionallyInvariant (backwardData F ell t node weight ha child hm hi)
end Constructor
end AcceleratedLogConcave.Root.BackwardParentLaw
