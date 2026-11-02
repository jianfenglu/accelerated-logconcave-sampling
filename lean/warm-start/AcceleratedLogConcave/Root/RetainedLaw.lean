import AcceleratedLogConcave.Conditional.MeanReferenceLayer

/-!
# Retained normalized sampling-root law at a fixed exact parent path

This is the dormant Gaussian part of warm-start.tex, lines 3077--3129.
The supplied child kernels are exact reference kernels, not executable outputs.
The coefficients are `-ω`; the input is the original `H₀`, and the recovered
reserve is `G_E = β H₀ + Σ ωᵢ Zᵢ`. All child updates share that same reserve.

This file constructs a kernel and its retained joint. It does not assume the
root's conditional invariance or the W12 norm. Exact child invariance is an
explicit lower-level input. Identification with recursively compiled means and
the covariance/Poisson estimate are separate obligations.
-/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open AcceleratedLogConcave.Conditional
open scoped ENNReal
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace AcceleratedLogConcave.Root.RetainedLaw
variable {ι : Type*} [Fintype ι] {m : ℕ}
local notation "E" => EuclideanSpace ℝ ι

/-- Fixed exact-parent-path data. No root invariant or root norm is a field. -/
structure Data (ι : Type*) [Fintype ι] (m : ℕ) where
  weight : Fin m → ℝ
  admissible : GaussianAssembly.mass (fun i => -weight i) < 1
  child : Fin m → Kernel (EuclideanSpace ℝ ι) (EuclideanSpace ℝ ι)
  markov : ∀ i, IsMarkovKernel (child i)
  invariant : ∀ i, child i ∘ₘ stdGaussian (EuclideanSpace ℝ ι) = stdGaussian (EuclideanSpace ℝ ι)

abbrev Noise := Fin m → E
abbrev Host := E × (Fin m → E)
abbrev Execution := (E × (Fin m → E)) × (Fin m → E)
def noiseLaw : Measure (Fin m → E) := Measure.pi (fun _ => stdGaussian E)
instance noiseLaw_probability : IsProbabilityMeasure (noiseLaw (ι := ι) (m := m)) := by
  unfold noiseLaw
  infer_instance
def coefficient (d : Data ι m) (i : Fin m) : ℝ := -d.weight i
def active (d : Data ι m) (h : Host (ι := ι) (m := m)) : Fin m → E :=
  GaussianAssembly.active (coefficient d) h.1 h.2
def reserve (d : Data ι m) (h : Host (ι := ι) (m := m)) : E :=
  GaussianAssembly.residual (coefficient d) h.1 h.2
def beta (d : Data ι m) : ℝ := GaussianAssembly.reserve (coefficient d)
def split (d : Data ι m) (h : Host (ι := ι) (m := m)) : E × (Fin m → E) :=
  (reserve d h, active d h)
def recombine (d : Data ι m) (z : E × (Fin m → E)) : E :=
  (∑ i, coefficient d i • z.2 i) + beta d • z.1

lemma measurable_active (d : Data ι m) : Measurable (active d) := by
  apply Measurable.of_eval
  intro i
  dsimp [active, GaussianAssembly.active, GaussianAssembly.noiseSum]
  fun_prop
lemma measurable_reserve (d : Data ι m) : Measurable (reserve d) := by
  unfold reserve GaussianAssembly.residual GaussianAssembly.noiseSum
  fun_prop
lemma measurable_split (d : Data ι m) : Measurable (split d) :=
  (measurable_reserve d).prodMk (measurable_active d)
lemma measurable_recombine (d : Data ι m) : Measurable (recombine d) := by
  unfold recombine
  fun_prop

/-- Literal same-input reconstruction, before any probability statement. -/
theorem reconstruct (d : Data ι m) (h : Host (ι := ι) (m := m)) :
    recombine d (split d h) = h.1 :=
  (GaussianAssembly.residual_reconstruction d.admissible h.1 h.2).symm

/-- Averaging only the independent standard input and fresh noise produces the
independent reserve/active product. No assertion conditions on an old child input. -/
theorem split_preserving (d : Data ι m) :
    MeasurePreserving (split d) ((stdGaussian E).prod (noiseLaw (ι := ι) (m := m)))
      ((stdGaussian E).prod (noiseLaw (ι := ι) (m := m))) := by
  have hs : MeasurePreserving
      (fun h : Host (ι := ι) (m := m) => fun j : Option (Fin m) =>
        j.elim (reserve d h) (active d h))
      ((stdGaussian E).prod (noiseLaw (ι := ι) (m := m)))
      (Measure.pi (fun _ : Option (Fin m) => stdGaussian E)) := by
    refine ⟨?_, GaussianAssembly.literal_split_joint_law d.admissible⟩
    apply Measurable.of_eval
    intro j
    cases j
    · exact measurable_reserve d
    · exact (measurable_pi_apply _).comp (measurable_active d)
  exact (MeanReferenceLayer.option_split (ι := ι) (J := Fin m)).comp hs

/-- The reconstruction row maps independent reserve/children back to standard Gaussian. -/
theorem recombine_preserving (d : Data ι m) :
    MeasurePreserving (recombine d)
      ((stdGaussian E).prod (noiseLaw (ι := ι) (m := m))) (stdGaussian E) := by
  refine ⟨measurable_recombine d, ?_⟩
  rw [← (split_preserving d).map_eq,
    Measure.map_map (measurable_recombine d) (measurable_split d)]
  have he : recombine d ∘ split d = Prod.fst := funext (reconstruct d)
  rw [he]
  exact measurePreserving_fst.map_eq

def stateChildren (d : Data ι m) : Kernel (E × (Fin m → E)) (Fin m → E) :=
  MeanReferenceLayer.finiteProduct m (fun i => (d.child i).comap (fun z => z.2 i)
    ((measurable_pi_apply i).comp measurable_snd))
instance stateChildren_markov (d : Data ι m) : IsMarkovKernel (stateChildren d) := by
  let : ∀ i, IsMarkovKernel (d.child i) := d.markov
  exact MeanReferenceLayer.finiteProduct_markov m _ (fun _ => inferInstance)

theorem stateChildren_invariant (d : Data ι m) (g : E) :
    (stateChildren d).comap (fun p => (g,p)) measurable_prodMk_left ∘ₘ
      noiseLaw (ι := ι) (m := m) = noiseLaw (ι := ι) (m := m) := by
  let : ∀ i, IsMarkovKernel (d.child i) := d.markov
  have he : (stateChildren d).comap (fun p => (g,p)) measurable_prodMk_left =
      MeanReferenceLayer.finiteProduct m (fun i => (d.child i).comap
        (fun p : Fin m → E => p i) (measurable_pi_apply i)) := by
    ext p : 1
    rw [Kernel.comap_apply, stateChildren,
      MeanReferenceLayer.finiteProduct_apply m _ (fun _ => inferInstance),
      MeanReferenceLayer.finiteProduct_apply m _ (fun _ => inferInstance)]
    rfl
  rw [he]
  exact MeanReferenceLayer.finiteProduct_invariant d.child d.markov d.invariant

def childrenKernel (d : Data ι m) : Kernel (Host (ι := ι) (m := m)) (Fin m → E) :=
  (stateChildren d).comap (split d) (measurable_split d)
instance childrenKernel_markov (d : Data ι m) : IsMarkovKernel (childrenKernel d) := by
  unfold childrenKernel
  infer_instance

def freshKernel : Kernel E (Host (ι := ι) (m := m)) :=
  (Kernel.id : Kernel E E) ×ₖ Kernel.const E (noiseLaw (ι := ι) (m := m))
instance freshKernel_markov : IsMarkovKernel (freshKernel (ι := ι) (m := m)) := by
  unfold freshKernel
  infer_instance

def jointKernel (d : Data ι m) : Kernel E (Execution (ι := ι) (m := m)) :=
  ((Kernel.id : Kernel (Host (ι := ι) (m := m)) _) ×ₖ childrenKernel d) ∘ₖ freshKernel
instance jointKernel_markov (d : Data ι m) : IsMarkovKernel (jointKernel d) := by
  unfold jointKernel
  infer_instance

def output (d : Data ι m) (z : Execution (ι := ι) (m := m)) : E :=
  recombine d (reserve d z.1, z.2)
lemma measurable_output (d : Data ι m) : Measurable (output d) :=
  (measurable_recombine d).comp
    (((measurable_reserve d).comp measurable_fst).prodMk measurable_snd)
def rootKernel (d : Data ι m) : Kernel E E := (jointKernel d).map (output d)
instance rootKernel_markov (d : Data ι m) : IsMarkovKernel (rootKernel d) :=
  Kernel.IsMarkovKernel.map _ (measurable_output d)
def averagedJoint (d : Data ι m) : Measure (Execution (ι := ι) (m := m)) :=
  jointKernel d ∘ₘ stdGaussian E

lemma averagedJoint_eq (d : Data ι m) :
    averagedJoint d = ((stdGaussian E).prod (noiseLaw (ι := ι) (m := m))) ⊗ₘ childrenKernel d := by
  rw [averagedJoint, jointKernel, ← Measure.comp_assoc, freshKernel,
    ← Measure.compProd_eq_comp_prod, ← Measure.compProd_eq_comp_prod, Measure.compProd_const]

/-- Exact fresh-child update preserves the joint reserve/children product law. -/
theorem updated_split_law (d : Data ι m) :
    (averagedJoint d).map (fun z => (reserve d z.1, z.2)) =
      (stdGaussian E).prod (noiseLaw (ι := ι) (m := m)) := by
  let μ := (stdGaussian E).prod (noiseLaw (ι := ι) (m := m))
  have hp := MeanReferenceLayer.compProd_comap_push μ (stateChildren d) (split d)
    (measurable_split d)
  change (μ ⊗ₘ childrenKernel d).map (fun z => (split d z.1,z.2)) = _ at hp
  rw [← averagedJoint_eq, (split_preserving d).map_eq] at hp
  have hm : Measurable (fun z : (E × (Fin m → E)) × (Fin m → E) => (z.1.1,z.2)) :=
    measurable_fst.fst.prodMk measurable_snd
  have he := congrArg (fun ν => ν.map
    (fun z : (E × (Fin m → E)) × (Fin m → E) => (z.1.1,z.2))) hp
  have hg : Measurable (fun z : Execution (ι := ι) (m := m) => (split d z.1,z.2)) :=
    ((measurable_split d).comp measurable_fst).prodMk measurable_snd
  rw [Measure.map_map hm hg] at he
  refine he.trans ?_
  have hu := MeanReferenceLayer.retained_update (stdGaussian E)
    (noiseLaw (ι := ι) (m := m)) (noiseLaw (ι := ι) (m := m))
    (stateChildren d) (stateChildren_invariant d)
  rw [Measure.compProd_eq_comp_prod, Measure.map_comp _ _ hm, ← hu]
  congr 1
  ext z s hs
  rw [Kernel.map_apply' _ hm _ hs, Kernel.id_prod_apply' _ _ (hs.preimage hm),
    Kernel.deterministic_prod_apply' measurable_fst _ _ hs]
  rfl

/-- Root invariance is a conclusion of literal assembly and independent exact children. -/
theorem rootKernel_invariant (d : Data ι m) :
    rootKernel d ∘ₘ stdGaussian E = stdGaussian E := by
  have he := congrArg (fun ν => ν.map (recombine d)) (updated_split_law d)
  have hm : Measurable (fun z : Execution (ι := ι) (m := m) => (reserve d z.1, z.2)) :=
    ((measurable_reserve d).comp measurable_fst).prodMk measurable_snd
  rw [Measure.map_map (measurable_recombine d) hm,
    (recombine_preserving d).map_eq] at he
  rw [rootKernel, ← Measure.map_comp _ _ (measurable_output d)]
  exact he

/-- Innovation is a weighted sum of the *same retained* child increments. -/
theorem innovation (d : Data ι m) (z : Execution (ι := ι) (m := m)) :
    output d z - z.1.1 = ∑ i, (-d.weight i) • (z.2 i - active d z.1 i) := by
  rw [← reconstruct d z.1]
  simp only [output, recombine, split, smul_sub, Finset.sum_sub_distrib, coefficient]
  abel

lemma lintegral_jointKernel (d : Data ι m) (p : E)
    (f : Execution (ι := ι) (m := m) → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ z, f z ∂jointKernel d p) =
      ∫⁻ a, ∫⁻ q, f ((p,a),q) ∂childrenKernel d (p,a) ∂noiseLaw := by
  rw [jointKernel, Kernel.lintegral_comp _ _ _ hf]
  simp_rw [Kernel.lintegral_id_prod hf]
  rw [freshKernel, Kernel.lintegral_id_prod hf.lintegral_kernel_prod_right']
  rfl

/-- The actual joint retains the original H₀ rather than drawing a replacement input. -/
theorem retained_joint (d : Data ι m) :
    (averagedJoint d).map (fun z => (z.1.1, output d z)) =
      (stdGaussian E) ⊗ₘ rootKernel d := by
  have hm : Measurable (fun z : Execution (ι := ι) (m := m) => (z.1.1,output d z)) :=
    measurable_fst.fst.prodMk (measurable_output d)
  apply Measure.ext_of_lintegral
  intro f hf
  have hF : Measurable (fun z : Execution (ι := ι) (m := m) => f (z.1.1,output d z)) := hf.comp hm
  rw [lintegral_map hf hm, averagedJoint,
    Measure.lintegral_bind (Kernel.aemeasurable _) hF.aemeasurable,
    Measure.lintegral_compProd hf]
  apply lintegral_congr
  intro p
  have hfp : Measurable (fun b : E => f (p,b)) := hf.comp measurable_prodMk_left
  rw [lintegral_jointKernel d p _ hF, rootKernel,
    Kernel.map_apply _ (measurable_output d), lintegral_map hfp (measurable_output d)]
  have hM : Measurable (fun z : Execution (ι := ι) (m := m) => f (p,output d z)) :=
    hf.comp (measurable_const.prodMk (measurable_output d))
  rw [lintegral_jointKernel d p _ hM]

end AcceleratedLogConcave.Root.RetainedLaw
