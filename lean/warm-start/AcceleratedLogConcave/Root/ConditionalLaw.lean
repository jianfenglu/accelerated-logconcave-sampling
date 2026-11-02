import AcceleratedLogConcave.Root.RetainedLaw

/-!
# Jointly measurable, conditionally invariant normalized dormant reference kernel

`B` contains the exact parent-path data and may include the clock. Weights and
centers may depend on `B`, but not on the dormant/child Gaussian inputs. A child
kernel may encode a measurable center map from `B` in its first coordinate.
The final conditional-invariance conclusion is proved for every `b`, not merely
after averaging the parent. No approximate-output invariance is claimed.
-/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open AcceleratedLogConcave.Conditional
open scoped ENNReal
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace AcceleratedLogConcave.Root.ConditionalLaw
variable {ι B : Type*} [Fintype ι] [MeasurableSpace B] {m : ℕ}
local notation "E" => EuclideanSpace ℝ ι

structure Data (B ι : Type*) [MeasurableSpace B] [Fintype ι] (m : ℕ) where
  weight : B → Fin m → ℝ
  measurable_weight : Measurable weight
  admissible : ∀ b, GaussianAssembly.mass (fun i => -weight b i) < 1
  child : Fin m → Kernel (B × EuclideanSpace ℝ ι) (EuclideanSpace ℝ ι)
  markov : ∀ i, IsMarkovKernel (child i)
  invariant : ∀ i b,
    (child i).comap (fun p => (b,p)) measurable_prodMk_left ∘ₘ stdGaussian (EuclideanSpace ℝ ι) =
      stdGaussian (EuclideanSpace ℝ ι)

def atParent (d : Data B ι m) (b : B) : RetainedLaw.Data ι m where
  weight := d.weight b
  admissible := d.admissible b
  child i := (d.child i).comap (fun p => (b,p)) measurable_prodMk_left
  markov i := by let := d.markov i; infer_instance
  invariant i := d.invariant i b

abbrev Host := (B × E) × (Fin m → E)
abbrev Execution := ((B × E) × (Fin m → E)) × (Fin m → E)
def active (d : Data B ι m) (z : Host (B := B) (ι := ι) (m := m)) : Fin m → E :=
  RetainedLaw.active (atParent d z.1.1) (z.1.2,z.2)
def reserve (d : Data B ι m) (z : Host (B := B) (ι := ι) (m := m)) : E :=
  RetainedLaw.reserve (atParent d z.1.1) (z.1.2,z.2)
def output (d : Data B ι m) (z : Execution (B := B) (ι := ι) (m := m)) : E :=
  RetainedLaw.output (atParent d z.1.1.1) ((z.1.1.2,z.1.2),z.2)

lemma measurable_active (d : Data B ι m) : Measurable (active d) := by
  have hw := d.measurable_weight
  unfold active RetainedLaw.active GaussianAssembly.active GaussianAssembly.noiseSum
    RetainedLaw.coefficient atParent GaussianAssembly.reserve GaussianAssembly.mass
  fun_prop
lemma measurable_reserve (d : Data B ι m) : Measurable (reserve d) := by
  have hw := d.measurable_weight
  unfold reserve RetainedLaw.reserve GaussianAssembly.residual GaussianAssembly.noiseSum
    RetainedLaw.coefficient atParent GaussianAssembly.reserve GaussianAssembly.mass
  fun_prop
lemma measurable_output (d : Data B ι m) : Measurable (output d) := by
  have hw := d.measurable_weight
  unfold output RetainedLaw.output RetainedLaw.recombine RetainedLaw.reserve
    GaussianAssembly.residual GaussianAssembly.noiseSum RetainedLaw.beta
    RetainedLaw.coefficient atParent GaussianAssembly.reserve GaussianAssembly.mass
  fun_prop

def childrenKernel (d : Data B ι m) : Kernel (Host (B := B) (ι := ι) (m := m)) (Fin m → E) :=
  MeanReferenceLayer.finiteProduct m (fun i => (d.child i).comap
    (fun z => (z.1.1,active d z i))
    (measurable_fst.fst.prodMk ((measurable_pi_apply i).comp (measurable_active d))))
instance childrenKernel_markov (d : Data B ι m) : IsMarkovKernel (childrenKernel d) := by
  let : ∀ i, IsMarkovKernel (d.child i) := d.markov
  exact MeanReferenceLayer.finiteProduct_markov m _ (fun _ => inferInstance)

def freshKernel : Kernel (B × E) (Host (B := B) (ι := ι) (m := m)) :=
  (Kernel.id : Kernel (B × E) _) ×ₖ Kernel.const (B × E) (RetainedLaw.noiseLaw (ι := ι) (m := m))
instance freshKernel_markov : IsMarkovKernel (freshKernel (B := B) (ι := ι) (m := m)) := by
  unfold freshKernel
  infer_instance

def jointKernel (d : Data B ι m) : Kernel (B × E) (Execution (B := B) (ι := ι) (m := m)) :=
  ((Kernel.id : Kernel (Host (B := B) (ι := ι) (m := m)) _) ×ₖ childrenKernel d) ∘ₖ freshKernel
instance jointKernel_markov (d : Data B ι m) : IsMarkovKernel (jointKernel d) := by
  unfold jointKernel
  infer_instance

def rootKernel (d : Data B ι m) : Kernel (B × E) E := (jointKernel d).map (output d)
instance rootKernel_markov (d : Data B ι m) : IsMarkovKernel (rootKernel d) :=
  Kernel.IsMarkovKernel.map _ (measurable_output d)

lemma childrenKernel_at_parent (d : Data B ι m) (b : B) (h : E) (z : Fin m → E) :
    childrenKernel d ((b,h),z) = RetainedLaw.childrenKernel (atParent d b) (h,z) := by
  let : ∀ i, IsMarkovKernel (d.child i) := d.markov
  let : ∀ i, IsMarkovKernel ((atParent d b).child i) := (atParent d b).markov
  rw [childrenKernel, MeanReferenceLayer.finiteProduct_apply m _ (fun _ => inferInstance),
    RetainedLaw.childrenKernel, Kernel.comap_apply, RetainedLaw.stateChildren,
    MeanReferenceLayer.finiteProduct_apply m _ (fun _ => inferInstance)]
  rfl

lemma lintegral_jointKernel (d : Data B ι m) (b : B) (p : E)
    (f : Execution (B := B) (ι := ι) (m := m) → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ z, f z ∂jointKernel d (b,p)) =
      ∫⁻ a, ∫⁻ q, f (((b,p),a),q) ∂childrenKernel d ((b,p),a) ∂RetainedLaw.noiseLaw := by
  rw [jointKernel, Kernel.lintegral_comp _ _ _ hf]
  simp_rw [Kernel.lintegral_id_prod hf]
  rw [freshKernel, Kernel.lintegral_id_prod hf.lintegral_kernel_prod_right']
  rfl

/-- The section of the measurable family is exactly the fixed-path retained construction. -/
theorem rootKernel_section (d : Data B ι m) (b : B) :
    (rootKernel d).comap (fun p => (b,p)) measurable_prodMk_left =
      RetainedLaw.rootKernel (atParent d b) := by
  ext p : 1
  apply Measure.ext_of_lintegral
  intro f hf
  have hF : Measurable (fun z : Execution (B := B) (ι := ι) (m := m) => f (output d z)) :=
    hf.comp (measurable_output d)
  have hR : Measurable (fun z : RetainedLaw.Execution (ι := ι) (m := m) =>
      f (RetainedLaw.output (atParent d b) z)) := hf.comp (RetainedLaw.measurable_output _)
  rw [Kernel.comap_apply, rootKernel, Kernel.map_apply _ (measurable_output d),
    lintegral_map hf (measurable_output d),
    lintegral_jointKernel d b p _ hF,
    RetainedLaw.rootKernel, Kernel.map_apply _ (RetainedLaw.measurable_output _),
    lintegral_map hf (RetainedLaw.measurable_output _),
    RetainedLaw.lintegral_jointKernel _ p _ hR]
  simp_rw [childrenKernel_at_parent]
  rfl

/-- Conditional stationarity at every exact parent parameter, not only marginal stationarity. -/
theorem rootKernel_invariant (d : Data B ι m) (b : B) :
    (rootKernel d).comap (fun p => (b,p)) measurable_prodMk_left ∘ₘ stdGaussian E =
      stdGaussian E := by
  rw [rootKernel_section]
  exact RetainedLaw.rootKernel_invariant (atParent d b)

/-- Literal `ConditionallyInvariant` formula required by DormantKernel, without importing
its unavailable cached operator layer. The operator-layer adapter is only definitional. -/
theorem rootKernel_conditionallyInvariant (d : Data B ι m) :
    ∀ b s, MeasurableSet s → (∫⁻ h, rootKernel d (b,h) s ∂stdGaussian E) = stdGaussian E s := by
  intro b s hs
  have he := congrArg (fun μ : Measure E => μ s) (rootKernel_invariant d b)
  rw [Measure.bind_apply hs (Kernel.aemeasurable _)] at he
  exact he

/-- Under any parent law, the old input is independent Gaussian and the root output
is independent Gaussian from that same parent. This gives the relevant sigma-algebra
statement without falsely conditioning on the old child momenta. -/
theorem parent_output_law (d : Data B ι m) (μ : Measure B) [IsProbabilityMeasure μ] :
    ((Kernel.deterministic Prod.fst measurable_fst) ×ₖ rootKernel d) ∘ₘ
      (μ.prod (stdGaussian E)) = μ.prod (stdGaussian E) :=
  MeanReferenceLayer.retained_update μ (stdGaussian E) (stdGaussian E)
    (rootKernel d) (rootKernel_invariant d)

end AcceleratedLogConcave.Root.ConditionalLaw
